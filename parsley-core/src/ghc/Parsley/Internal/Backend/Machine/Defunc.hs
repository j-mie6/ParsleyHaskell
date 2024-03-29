{-# LANGUAGE ImplicitParams, PatternSynonyms, StandaloneKindSignatures, TypeApplications, ViewPatterns #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Defunc
Description : Machine-level defunctionalisation
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the infrastructure and definitions of defunctionalised
terms used solely within the machine.

@since 1.0.0.0
-}
module Parsley.Internal.Backend.Machine.Defunc (
    Defunc(..),
    user,
    ap, ap2,
    _if,
    genDefunc,
    pattern NormLam, pattern FREEVAR
  ) where

import Parsley.Internal.Backend.Machine.Types.Input (Input(off))
import Parsley.Internal.Common.Utils                (Code)
import Parsley.Internal.Core.Lam                    (Lam, normaliseGen, normalise)

import qualified Parsley.Internal.Core.Defunc as Core (Defunc, lamTerm)
import qualified Parsley.Internal.Core.Lam    as Lam  (Lam(..))

import qualified Parsley.Internal.Opt   as Opt

{-|
Machine level defunctionalisation, for terms that can only be introduced by
the code generator, and that do not require value level representations.

@since 1.4.0.0
-}
data Defunc a where
  {-|
  Wraps `Lam` terms so that they can be used within the machine.

  @since 1.1.0.0
  -}
  LAM     :: Lam a -> Defunc a
  {-|
  Represents Haskell's @undefined@, which may be used by high-level
  optimisers to replace redundant values whilst preserving the types.

  @since 1.0.0.0
  -}
  BOTTOM  :: Defunc a
  {-|
  Allows the static `Input`s to be pushed onto the operand stack, which
  is the easiest way to get them to persist as arguments to handlers, and
  interact with `Parsley.Internal.Backend.Machine.Instructions.Seek` and
  `Parsley.Internal.Backend.Machine.Instructions.Tell`.

  @since 1.8.0.0
  -}
  INPUT  :: Input o -> Defunc o

{-|
Promotes a @Defunc@ value from the Frontend API into a Backend one.

@since 1.1.0.0
-}
user :: Core.Defunc a -> Defunc a
user = LAM . Core.lamTerm

{-|
Applies a function to a value when both are `Defunc`.

@since 1.3.0.0
-}
ap :: (?flags :: Opt.Flags) => Defunc (a -> b) -> Defunc a -> Defunc b
ap f x = LAM (Lam.App (unliftDefunc f) (unliftDefunc x))

{-|
Applies a function to two values when all are `Defunc`.

@since 1.3.0.0
-}
ap2 :: (?flags :: Opt.Flags) => Defunc (a -> b -> c) -> Defunc a -> Defunc b -> Defunc c
ap2 f x = ap (ap f x)

{-|
Acts as an @if@-expression lifted to the `Defunc` level.

@since 1.3.0.0
-}
_if :: (?flags :: Opt.Flags) => Defunc Bool -> Code a -> Code a -> Code a
_if c t e = normaliseGen (Lam.If (unliftDefunc c) (Lam.Var False t) (Lam.Var False e))

unliftDefunc :: (?flags :: Opt.Flags) => Defunc a -> Lam a
unliftDefunc (LAM x) = x
unliftDefunc x       = Lam.Var False (genDefunc x)

{-|
Generate the Haskell code that represents this defunctionalised value.

@since 1.0.0.0
-}
genDefunc :: (?flags :: Opt.Flags) => Defunc a -> Code a
genDefunc (LAM x) = normaliseGen x
genDefunc BOTTOM  = [||undefined||]
genDefunc INPUT{} = error "Cannot materialise an input in the regular way"

{-|
Pattern that normalises a `Lam` before returning it.

@since 1.1.0.0
-}
pattern NormLam :: (?flags :: Opt.Flags) => Lam a -> Defunc a
pattern NormLam t <- LAM (normalise -> t)

{-|
Pattern that represents simple `Lam` variables,
post-normalisation.

@since 1.1.0.0
-}
pattern FREEVAR :: (?flags :: Opt.Flags) => Code a -> Defunc a
pattern FREEVAR v <- NormLam (Lam.Var True v)
  where
    FREEVAR v = LAM (Lam.Var True v)

instance Show (Defunc a) where
  show (LAM x) = show x
  show BOTTOM = "[[irrelevant]]"
  show (INPUT inp)  = "input " ++ show (off inp)
