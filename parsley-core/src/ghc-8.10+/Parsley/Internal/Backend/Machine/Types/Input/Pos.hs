{-# LANGUAGE RecordWildCards, UnboxedTuples, PatternSynonyms, DerivingStrategies #-}
module Parsley.Internal.Backend.Machine.Types.Input.Pos (
    StaPos, DynPos,
    fromDynPos, toDynPos, fromStaPos,
    force, update
  ) where

import Data.Bits ((.|.), (.&.))
import Parsley.Internal.Common.Utils (Code)
import Parsley.Internal.Core.CharPred (CharPred, pattern Specific, apply)
import Parsley.Internal.Backend.Machine.PosOps (CharClass(..), liftPos)

import qualified Parsley.Internal.Backend.Machine.PosOps as Ops (updatePosQ, updatePos, tabWidth)
import qualified Parsley.Internal.Backend.Machine.Types.Base as Base (Pos)

type DynPos = Code Base.Pos

data Pos = Static (Word, Word) | Dynamic DynPos

data StaPos = StaPos {
    dynPos :: !Pos,
    alignment :: !Alignment,
    contributing :: ![StaChar]
  }

data Alignment = Unknown | Unaligned {-# UNPACK #-} !Word deriving stock Show

pattern Aligned :: Alignment
pattern Aligned = Unaligned 0

data StaChar = StaChar {
    char :: !(Code Char),
    predicate :: !CharPred
  }

mkStaPos :: Pos -> StaPos
mkStaPos pos = StaPos { dynPos = pos, alignment = alignment pos, contributing = [] }
  where
    alignment Dynamic{} = Unknown
    alignment (Static (_, col)) = Unaligned (col - 1 `mod` Ops.tabWidth)

fromDynPos :: DynPos -> StaPos
fromDynPos = mkStaPos . Dynamic

fromStaPos :: (Word, Word) -> StaPos
fromStaPos = mkStaPos . Static

fromPos :: Pos -> DynPos
fromPos (Static p) = liftPos p
fromPos (Dynamic p) = p

force :: StaPos -> (DynPos -> StaPos -> Code r) -> Code r
force p k
  | null (contributing p) = k (fromPos (dynPos p)) p
  | otherwise = case collapse p of
    p'@Static{} -> k (fromPos p') (newPos p')
    Dynamic qpos -> [||
        let pos = $$qpos
        in $$(k [||pos||] (newPos (Dynamic [||pos||])))
      ||]
  where
    newPos pos = StaPos {
      dynPos = pos,
      alignment = updateAlignment (contributing p) (alignment p),
      contributing = []
    }

update :: StaPos -> Code Char -> CharPred -> StaPos
update pos c p = pos { contributing = StaChar c p : contributing pos }

updateAlignment :: [StaChar] -> Alignment -> Alignment
updateAlignment cs a = foldr (updateAlignment' . knownChar . predicate) a cs

updateAlignment' :: Maybe CharClass -> Alignment -> Alignment
updateAlignment' Nothing        _             = Unknown
updateAlignment' (Just Regular) Aligned       = Unaligned 1
updateAlignment' (Just Regular) (Unaligned n)
  | n == Ops.tabWidth - 1                     = Aligned
  | otherwise                                 = Unaligned (n + 1)
updateAlignment' (Just Regular) Unknown       = Unknown
updateAlignment' _              _             = Aligned

-- TODO: we want to collapse into a single update statically!
-- TODO: take into account initial alignment
{-
1) Use a similar strategy from Scala Parsley: use this to create an updater up to the next unknown character
   BUT: use the initial alignment to guide the first updater
2) Build a list of updaters to apply: sequences of static updates and dynamic ones
3) Apply these updaters to the static or dynamic position - this involves translating an updater
   to optimised form.
4) profit
-}
collapse :: StaPos -> Pos
collapse StaPos{..} = foldr f dynPos contributing
  where
    f StaChar{..} =
      let charClass = knownChar predicate
      in throughEither (Ops.updatePos charClass char)
                       (Ops.updatePosQ charClass char)

    throughEither :: ((Word, Word) -> Either DynPos (Word, Word)) -> (DynPos -> DynPos) -> Pos -> Pos
    throughEither sta _ (Static p)  = either Dynamic Static (sta p)
    throughEither _ dyn (Dynamic p) = Dynamic (dyn p)

data ColUpdater = Set {-# UNPACK #-} !Word
                | Offset {-# UNPACK #-} !Word
                | OffsetAlignOffset {-# UNPACK #-} !Word {-# UNPACK #-} !Word

updateTab :: ColUpdater -> ColUpdater
updateTab (Set n) = Set ((n + Ops.tabWidth - 1) .&. Ops.tabWidth .|. 1)
updateTab (Offset n) = OffsetAlignOffset n 0
updateTab (OffsetAlignOffset firstBy thenBy) = OffsetAlignOffset firstBy (toNextTabFromKnownAlignment thenBy)

toNextTabFromKnownAlignment :: Word -> Word
toNextTabFromKnownAlignment x = (x .|. Ops.tabWidth - 1) + 1

updateRegular :: ColUpdater -> ColUpdater
updateRegular (Set n) = Set (n + 1)
updateRegular (Offset n) = Set (n + 1)
updateRegular (OffsetAlignOffset firstBy thenBy) = OffsetAlignOffset firstBy (thenBy + 1)

data Updater = Updater {
    lineUpdate :: {-# UNPACK #-} !Word,
    colUpdate :: !ColUpdater
  }

pattern NoUpdate :: Updater
pattern NoUpdate = Updater { lineUpdate = 0, colUpdate = Offset 0 }

pattern ColOnly :: ColUpdater -> Updater
pattern ColOnly colUpdate = Updater 0 colUpdate

{-| Takes the initial alignment and contributing characters and
    return the list of updaters (in order from left-to-right)
    that must be applied to update the position properly -}
-- TODO: A line-update removes all previous static updaters: dynamic ones need to remain, in case
--       they update the line. But these can actually be converted to a no-op in the non-line case!
buildUpdaters :: Alignment -> [StaChar] -> [Maybe Updater]
buildUpdaters alignment = applyAlignment alignment . reverse . uncurry combine . foldr f (NoUpdate, [])
  where
    -- The known initial alignment can affect the /first/ updater
    applyAlignment :: Alignment -> [Maybe Updater] -> [Maybe Updater]
    applyAlignment (Unaligned n) (Just (ColOnly (OffsetAlignOffset firstBy thenBy)) : updaters) =
      -- We know what the current alignment boundary is, so can eliminate the Align
      let pre = n + firstBy
          nextTabIn = toNextTabFromKnownAlignment pre
      in Just (ColOnly (Offset (nextTabIn + thenBy))) : updaters
    applyAlignment _ updaters = updaters

    combine :: Updater -> [Maybe Updater] -> [Maybe Updater]
    combine NoUpdate updaters = updaters
    combine updater updaters = Just updater : updaters

    f :: StaChar -> (Updater, [Maybe Updater]) -> (Updater, [Maybe Updater])
    f StaChar{..} (updater, updaters) =
      let charClass = knownChar predicate
      in case charClass of
        Nothing -> (NoUpdate, Nothing : combine updater updaters)
        Just Tab -> (updater { colUpdate = updateTab (colUpdate updater) }, updaters)
        Just Newline -> (updater { lineUpdate = lineUpdate updater + 1, colUpdate = Set 0 }, updaters)
        Just Regular -> (updater { colUpdate = updateRegular (colUpdate updater) }, updaters)

toDynPos :: StaPos -> DynPos
toDynPos = fromPos . collapse

knownChar :: CharPred -> Maybe CharClass
knownChar (Specific '\t')         = Just Tab
knownChar (Specific '\n')         = Just Newline
knownChar p | not (apply p '\t'),
              not (apply p '\n')  = Just Regular
knownChar _                       = Nothing

instance Show StaPos where
  show StaPos{..} = "StaPos { dynPos = ?, alignment = " ++ show alignment ++ ", contributing = " ++ show contributing ++ "}"

instance Show StaChar where
  show StaChar{..} = "StaChar { char = ?, predicate = " ++ show predicate ++ "}"