{-# LANGUAGE RecordWildCards #-}
module Parsley.Internal.Backend.Machine.Types.Input.Pos (module Parsley.Internal.Backend.Machine.Types.Input.Pos) where

import Parsley.Internal.Common.Utils (Code)
import Parsley.Internal.Core.CharPred (CharPred(Specific), andPred)

import qualified Parsley.Internal.Backend.Machine.PosOps as Ops (updatePos)
import qualified Parsley.Internal.Backend.Machine.Types.Base as Base (Pos)

data Pos = Pos {
    dynPos :: Code Base.Pos,
    contributing :: [StaChar]
  }

data StaChar = StaChar {
    char :: Code Char,
    predicate :: Maybe CharPred
  }

fromDynPos :: Code Base.Pos -> Pos
fromDynPos pos = Pos { dynPos = pos, contributing = [] }

contribute :: Pos -> Code Char -> Pos
contribute pos c = pos { contributing = StaChar c Nothing : contributing pos }

-- TODO: This should preserve any alignment information we have statically on the forward
force :: Pos -> (Code Base.Pos -> Pos -> Code r) -> Code r
force p k
  | null (contributing p) = k (dynPos p) p
  | otherwise = [||
        let pos = $$(toDynPos p)
        in $$(k [||pos||] (fromDynPos [||pos||]))
      ||]

update :: Pos -> CharPred -> Pos
update pos p =
  let sc@StaChar{..} : cs = contributing pos
  in pos { contributing = sc { predicate = Just (maybe p (andPred p) predicate) } : cs }

toDynPos :: Pos -> Code Base.Pos
toDynPos Pos{..} = foldr f dynPos contributing
  where
    f StaChar{..} p = Ops.updatePos (predicate >>= knownChar) p char

    knownChar (Specific c) = Just c
    knownChar _            = Nothing