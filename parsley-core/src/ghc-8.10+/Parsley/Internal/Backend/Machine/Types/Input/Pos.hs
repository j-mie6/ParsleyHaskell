{-# LANGUAGE RecordWildCards, UnboxedTuples, PatternSynonyms, DerivingStrategies #-}
module Parsley.Internal.Backend.Machine.Types.Input.Pos (
    StaPos, DynPos,
    fromDynPos, toDynPos, fromStaPos,
    force, update
  ) where

import Data.Bits ((.|.))
import Data.List (foldl')
import Parsley.Internal.Common.Utils (Code)
import Parsley.Internal.Core.CharPred (CharPred, pattern Specific, apply)
import Parsley.Internal.Backend.Machine.PosOps (CharClass(..), liftPos)

import qualified Parsley.Internal.Backend.Machine.PosOps as Ops (updatePosQ, updatePos, shiftLineAndSetColQ, shiftColQ, shiftAlignAndShiftColQ, toNextTab, tabWidth)
import qualified Parsley.Internal.Backend.Machine.Types.Base as Base (Pos)

type DynPos = Code Base.Pos

-- TODO: This could be more fine-grained, for instance a partially static position.
data Pos = Static {-# UNPACK #-} !Word {-# UNPACK #-} !Word | Dynamic DynPos

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
    alignment (Static _ col) = Unaligned (col - 1 `mod` Ops.tabWidth)

fromDynPos :: DynPos -> StaPos
fromDynPos = mkStaPos . Dynamic

toDynPos :: StaPos -> DynPos
toDynPos = fromPos . collapse

fromStaPos :: (Word, Word) -> StaPos
fromStaPos = mkStaPos . uncurry Static

fromPos :: Pos -> DynPos
fromPos (Static l c) = liftPos l c
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
  where
    updateAlignment' Nothing           _             = Unknown
    updateAlignment' (Just Regular)    Aligned       = Unaligned 1
    updateAlignment' (Just Regular)    (Unaligned n)
      | n == Ops.tabWidth - 1                        = Aligned
      | otherwise                                    = Unaligned (n + 1)
    updateAlignment' (Just Regular)    Unknown       = Unknown
    updateAlignment' (Just NonNewline) _             = Unknown
    updateAlignment' _                 _             = Aligned

collapse :: StaPos -> Pos
collapse StaPos{..} = applyUpdaters dynPos (buildUpdaters alignment contributing)

throughEither :: (Word -> Word -> Either DynPos (Word, Word)) -> (DynPos -> DynPos) -> Pos -> Pos
throughEither sta _ (Static l c)  = either Dynamic (uncurry Static) (sta l c)
throughEither _ dyn (Dynamic p) = Dynamic (dyn p)

data ColUpdater = Set {-# UNPACK #-} !Word
                | Offset {-# UNPACK #-} !Word
                | OffsetAlignOffset {-# UNPACK #-} !Word {-# UNPACK #-} !Word
                deriving stock Show

updateTab :: ColUpdater -> ColUpdater
updateTab (Set n) = Set (Ops.toNextTab n)
updateTab (Offset n) = OffsetAlignOffset n 0
updateTab (OffsetAlignOffset firstBy thenBy) = OffsetAlignOffset firstBy (toNextTabFromKnownAlignment thenBy)

toNextTabFromKnownAlignment :: Word -> Word
toNextTabFromKnownAlignment x = (x .|. Ops.tabWidth - 1) + 1

updateRegular :: ColUpdater -> ColUpdater
updateRegular (Set n) = Set (n + 1)
updateRegular (Offset n) = Offset (n + 1)
updateRegular (OffsetAlignOffset firstBy thenBy) = OffsetAlignOffset firstBy (thenBy + 1)

data Updater = Updater {
    lineUpdate :: {-# UNPACK #-} !Word,
    colUpdate :: !ColUpdater
  } deriving stock Show

pattern NoUpdate :: Updater
pattern NoUpdate = Updater { lineUpdate = 0, colUpdate = Offset 0 }

pattern ColOnly :: ColUpdater -> Updater
pattern ColOnly colUpdate = Updater 0 colUpdate

{-| Takes the initial alignment and contributing characters and
    return the list of updaters (in order from left-to-right)
    that must be applied to update the position properly -}
-- TODO: A line-update removes all previous static updaters: dynamic ones need to remain, in case
--       they update the line. But these can actually be converted to a no-op in the non-line case!
buildUpdaters :: Alignment -> [StaChar] -> [Either (Code Char) Updater]
buildUpdaters alignment = applyAlignment alignment . removeDeadUpdates . uncurry combine . foldr f (NoUpdate, [])
  where
    -- The known initial alignment can affect the /first/ updater
    applyAlignment :: Alignment -> [Either (Code Char) Updater] -> [Either (Code Char) Updater]
    applyAlignment (Unaligned n) (Right (ColOnly (OffsetAlignOffset firstBy thenBy)) : updaters) =
      -- We know what the current alignment boundary is, so can eliminate the Align
      let pre = n + firstBy
          nextTabIn = toNextTabFromKnownAlignment pre
      in Right (ColOnly (Offset (nextTabIn + thenBy))) : updaters
    applyAlignment _ updaters = updaters

    combine :: Updater -> [Either (Code Char) Updater] -> [Either (Code Char) Updater]
    combine NoUpdate updaters = updaters
    combine updater updaters = Right updater : updaters

    f :: StaChar -> (Updater, [Either (Code Char) Updater]) -> (Updater, [Either (Code Char) Updater])
    f StaChar{..} (updater, updaters) =
      let charClass = knownChar predicate
      in case charClass of
        Just Tab -> (updater { colUpdate = updateTab (colUpdate updater) }, updaters)
        Just Newline -> (updater { lineUpdate = lineUpdate updater + 1, colUpdate = Set 1 }, updaters)
        Just Regular -> (updater { colUpdate = updateRegular (colUpdate updater) }, updaters)
        -- TODO: This should be refined to account for non-newline updates, which can be dropped below
        _ -> (NoUpdate, Left char : combine updater updaters)

    -- This function should reverse the list, and also remove any redundant updaters:
    -- when a newline is known, any updater before it is only useful for the newlines.
    removeDeadUpdates :: [Either (Code Char) Updater] -> [Either (Code Char) Updater]
    removeDeadUpdates = fst . foldl' g ([], True)
      where
        g :: ([Either (Code Char) Updater], Bool) -> Either (Code Char) Updater -> ([Either (Code Char) Updater], Bool)
        -- TODO: This should be refined from Left to a specialised line-only updater
        g (updaters, keep) updater@Left{} = (updater : updaters, keep)
        g res@(updaters, keep) updater@(Right (Updater 0 _))
          | keep      = (updater : updaters, True)
          | otherwise = res
        -- This is a line updater, no tab or regular updaters matter anymore
        g (updaters, _) updater = (updater : updaters, False)

applyUpdaters :: Pos -> [Either (Code Char) Updater] -> Pos
applyUpdaters = foldl' applyUpdater
  where
    applyUpdater pos (Left c) = throughEither (Ops.updatePos Nothing c) (Ops.updatePosQ Nothing c) pos
    applyUpdater pos (Right updater) = applyUpdaterSta pos updater

    -- TODO: Illegal states should be unrepresentable
    applyUpdaterSta (Static line _)   (Updater n (Set m))                            = Static (line + n) m
    applyUpdaterSta (Static line col) (Updater 0 (Offset n))                         = Static line (col + n)
    applyUpdaterSta (Static line col) (Updater 0 (OffsetAlignOffset firstBy thenBy)) = Static line (Ops.toNextTab (col + firstBy) + thenBy)
    applyUpdaterSta (Dynamic pos)     (Updater n (Set m))                            = Dynamic (Ops.shiftLineAndSetColQ n m pos)
    applyUpdaterSta (Dynamic pos)     (Updater 0 (Offset n))                         = Dynamic (Ops.shiftColQ n pos)
    applyUpdaterSta (Dynamic pos)     (Updater 0 (OffsetAlignOffset firstBy thenBy)) = Dynamic (Ops.shiftAlignAndShiftColQ firstBy thenBy pos)
    applyUpdaterSta _ _ = error "Illegal updater state, lines increased but without a Set"

knownChar :: CharPred -> Maybe CharClass
knownChar (Specific '\t')         = Just Tab
knownChar (Specific '\n')         = Just Newline
knownChar p | not (apply p '\n')  = Just $ if not (apply p '\t') then Regular else NonNewline
knownChar _                       = Nothing

instance Show StaPos where
  show StaPos{..} = "StaPos { dynPos = ?, alignment = " ++ show alignment ++ ", contributing = " ++ show contributing ++ "}"

instance Show StaChar where
  show StaChar{..} = "StaChar { char = ?, predicate = " ++ show predicate ++ "}"