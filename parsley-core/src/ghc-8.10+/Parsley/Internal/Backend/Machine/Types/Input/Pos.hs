{-# LANGUAGE RecordWildCards, UnboxedTuples, PatternSynonyms #-}
module Parsley.Internal.Backend.Machine.Types.Input.Pos (
    StaPos, DynPos,
    fromDynPos, toDynPos,
    force, update
  ) where

import Parsley.Internal.Common.Utils (Code)
import Parsley.Internal.Core.CharPred (CharPred, pattern Specific, apply)
import Parsley.Internal.Backend.Machine.PosOps (CharClass(..))

import qualified Parsley.Internal.Backend.Machine.PosOps as Ops (updatePos)
import qualified Parsley.Internal.Backend.Machine.Types.Base as Base (Pos)

type DynPos = Code Base.Pos

data StaPos = StaPos {
    -- TODO: What about the case where dynPos == initialPos? We could mark this statically
    dynPos :: !DynPos,
    contributing :: ![StaChar]
  }

data StaChar = StaChar {
    char :: !(Code Char),
    predicate :: !CharPred
  }

fromDynPos :: DynPos -> StaPos
fromDynPos pos = StaPos { dynPos = pos, contributing = [] }

-- TODO: This should preserve any alignment information we have statically on the forward
force :: StaPos -> (DynPos -> StaPos -> Code r) -> Code r
force p k
  | null (contributing p) = k (dynPos p) p
  | otherwise = [||
        let pos = $$(toDynPos p)
        in $$(k [||pos||] (fromDynPos [||pos||]))
      ||]

update :: StaPos -> Code Char -> CharPred -> StaPos
update pos c p = pos { contributing = StaChar c p : contributing pos }

-- TODO: we want to collapse into a single update statically!
toDynPos :: StaPos -> DynPos
toDynPos StaPos{..} = foldr f dynPos contributing
  where
    f StaChar{..} p = Ops.updatePos (knownChar predicate) p char

    knownChar (Specific '\t')         = Just Tab
    knownChar (Specific '\n')         = Just Newline
    knownChar p | not (apply p '\t'),
                  not (apply p '\n')  = Just Regular
    knownChar _                       = Nothing

instance Show StaPos where
  show (StaPos{..}) = "StaPos { dynPos = ?, contributing = " ++ show contributing ++ "}"

instance Show StaChar where
  show (StaChar{..}) = "StaChar { char = ?, predicate = " ++ show predicate ++ "}"