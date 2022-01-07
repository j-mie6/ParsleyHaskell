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

isStatic :: StaPos -> Bool
isStatic (StaPos Static{} _ _) = True
isStatic _ = False

data Alignment = Unknown | Unaligned Int | Aligned deriving stock Show

data StaChar = StaChar {
    char :: !(Code Char),
    predicate :: !CharPred
  }

mkStaPos :: Pos -> StaPos
mkStaPos pos = StaPos { dynPos = pos, alignment = alignment pos, contributing = [] }
  where
    alignment Dynamic{} = Unknown
    alignment (Static _) = Unknown

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
  | isStatic p = k (toDynPos p) p
  | otherwise = [||
        let pos = $$(toDynPos p)
        in $$(k [||pos||] (StaPos {
            dynPos = Dynamic [||pos||],
            alignment = alignment p,
            contributing = []
          }))
      ||]

update :: StaPos -> Code Char -> CharPred -> StaPos
update pos c p = pos { contributing = StaChar c p : contributing pos
                     ,  alignment = updateAlignment (knownChar p) (alignment pos)
                     }
  where
    updateAlignment Nothing        _             = Unknown
    updateAlignment (Just Regular) Aligned       = Unaligned 1
    updateAlignment (Just Regular) (Unaligned n)
      | n == Ops.tabWidth - 1                    = Aligned
      | otherwise                                = Unaligned (n + 1)
    updateAlignment (Just Regular) Unknown       = Unknown
    updateAlignment _              _             = Aligned

-- TODO: we want to collapse into a single update statically!
-- TODO: take into account initial alignment
toDynPos :: StaPos -> DynPos
toDynPos StaPos{..} = fromPos $ foldr f dynPos contributing
  where
    f StaChar{..} = let charClass = knownChar predicate in throughEither (Ops.updatePos charClass char) (Ops.updatePosQ charClass char)

    throughEither :: ((Word, Word) -> Either DynPos (Word, Word)) -> (DynPos -> DynPos) -> Pos -> Pos
    throughEither sta _ (Static p)  = either Dynamic Static (sta p)
    throughEither _ dyn (Dynamic p) = Dynamic (dyn p)

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