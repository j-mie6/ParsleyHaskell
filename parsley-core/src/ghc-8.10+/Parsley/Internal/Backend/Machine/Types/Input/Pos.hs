{-# LANGUAGE RecordWildCards, UnboxedTuples, PatternSynonyms, DerivingStrategies #-}
module Parsley.Internal.Backend.Machine.Types.Input.Pos (
    StaPos, DynPos,
    fromDynPos, toDynPos, fromStaPos,
    force, update
  ) where

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

data Alignment = Unknown | Unaligned Word | Aligned deriving stock Show

data StaChar = StaChar {
    char :: !(Code Char),
    predicate :: !CharPred
  }

mkStaPos :: Pos -> StaPos
mkStaPos pos = StaPos { dynPos = pos, alignment = alignment pos, contributing = [] }
  where
    alignment Dynamic{} = Unknown
    alignment (Static (_, col))
      | trailingBehindBoundary == 0 = Aligned
      | otherwise                   = Unaligned trailingBehindBoundary
      where
        trailingBehindBoundary = col - 1 `mod` Ops.tabWidth

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
  where
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
collapse :: StaPos -> Pos
collapse StaPos{..} = foldr f dynPos contributing
  where
    f StaChar{..} = let charClass = knownChar predicate in throughEither (Ops.updatePos charClass char) (Ops.updatePosQ charClass char)

    throughEither :: ((Word, Word) -> Either DynPos (Word, Word)) -> (DynPos -> DynPos) -> Pos -> Pos
    throughEither sta _ (Static p)  = either Dynamic Static (sta p)
    throughEither _ dyn (Dynamic p) = Dynamic (dyn p)

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