{-# LANGUAGE RecordWildCards, UnboxedTuples, PatternSynonyms #-}
module Parsley.Internal.Backend.Machine.Types.Input.Pos (
    StaPos, DynPos,
    fromDynPos, toDynPos,
    contribute, force, update
  ) where

import Parsley.Internal.Common.Utils (Code)
import Parsley.Internal.Core.CharPred (CharPred, pattern Specific, andPred)

import qualified Parsley.Internal.Backend.Machine.PosOps as Ops (updatePos)
import qualified Parsley.Internal.Backend.Machine.Types.Base as Base (Pos)

type DynPos = Code Base.Pos

data StaPos = StaPos {
    -- TODO: What about the case where dynPos == initialPos? We could mark this statically
    dynPos :: DynPos,
    contributing :: [StaChar]
  }

data StaChar = StaChar {
    char :: Code Char,
    predicate :: Maybe CharPred
  }

fromDynPos :: DynPos -> StaPos
fromDynPos pos = StaPos { dynPos = pos, contributing = [] }

contribute :: StaPos -> Code Char -> StaPos
contribute pos c = pos { contributing = StaChar c Nothing : contributing pos }

-- TODO: This should preserve any alignment information we have statically on the forward
force :: StaPos -> (DynPos -> StaPos -> Code r) -> Code r
force p k
  | null (contributing p) = k (dynPos p) p
  | otherwise = [||
        let pos = $$(toDynPos p)
        in $$(k [||pos||] (fromDynPos [||pos||]))
      ||]

update :: StaPos -> CharPred -> StaPos
update pos p =
  let sc@StaChar{..} : cs = contributing pos
  in pos { contributing = sc { predicate = Just (maybe p (andPred p) predicate) } : cs }

-- TODO: The knownChar thing is see specific, and besides, we want to collapse into a single update statically!
toDynPos :: StaPos -> DynPos
toDynPos StaPos{..} = foldr f dynPos contributing
  where
    f StaChar{..} p = Ops.updatePos (predicate >>= knownChar) p char

    knownChar (Specific c) = Just c
    knownChar _            = Nothing