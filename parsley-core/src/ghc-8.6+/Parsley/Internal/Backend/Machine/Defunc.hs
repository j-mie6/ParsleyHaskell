{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
module Parsley.Internal.Backend.Machine.Defunc (module Parsley.Internal.Backend.Machine.Defunc) where

import Parsley.Internal.Backend.Machine.InputOps (PositionOps(same))
import Parsley.Internal.Common.Utils             (Code)
import Parsley.Internal.Core.Lam                 (Lam, normaliseGen, normalise)

import qualified Parsley.Internal.Core.Defunc as Core (Defunc, lamTerm)
import qualified Parsley.Internal.Core.Lam    as Lam  (Lam(..))

data Defunc a where
  LAM     :: Lam a -> Defunc a
  BOTTOM  :: Defunc a
  SAME    :: PositionOps o => Defunc (o -> o -> Bool)

user :: Core.Defunc a -> Defunc a
user = LAM . Core.lamTerm

userBool :: Core.Defunc (a -> Bool) -> Defunc (a -> Bool)
userBool = LAM . Core.lamTermBool

ap2 :: Defunc (a -> b -> c) -> Defunc a -> Defunc b -> Defunc c
ap2 f x y = LAM (Lam.App (Lam.App (seal f) (seal x)) (seal y))
  where
    seal :: Defunc a -> Lam a
    seal (LAM x) = x
    seal x       = Lam.Var False (genDefunc x)

genDefunc :: Defunc a -> Code a
genDefunc (LAM x) = normaliseGen x
genDefunc BOTTOM  = [||undefined||]
genDefunc SAME    = same

genDefunc1 :: Defunc (a -> b) -> Code a -> Code b
genDefunc1 (LAM f) qx = normaliseGen (Lam.App f (Lam.Var True qx))
genDefunc1 f qx       = [|| $$(genDefunc f) $$qx ||]

pattern NormLam :: Lam a -> Defunc a
pattern NormLam t <- LAM (normalise -> t)

pattern FREEVAR :: Code a -> Defunc a
pattern FREEVAR v <- NormLam (Lam.Var True v)
  where
    FREEVAR v = LAM (Lam.Var True v)

instance Show (Defunc a) where
  show (LAM x) = show x
  show SAME = "same"
  show BOTTOM = "[[irrelevant]]"