{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE DerivingStrategies,
             GeneralizedNewtypeDeriving #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Identifiers
Description : frontend specific identifiers.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module defines "identifiers", which are used to uniquely identify different
nodes in the combinator tree (and abstract machine).

@since 1.0.0.0
-}
module Parsley.Internal.Core.Identifiers (
    MVar(..), IMVar,
    ΣVar(..), IΣVar, SomeΣVar(..), getIΣVar
  ) where

import Data.Array        (Ix)
import Data.Function     (on)
import Data.GADT.Compare (GEq, GCompare, gcompare, geq, GOrdering(..))
import Data.Kind         (Type)
import Data.Typeable     ((:~:)(Refl))
import Data.Word         (Word64)
import Unsafe.Coerce     (unsafeCoerce)

{-|
An identifier representing concrete registers and mutable state.

@since 0.1.0.0
-}
newtype ΣVar (a :: Type) = ΣVar IΣVar
{-|
An identifier representing let-bound parsers, recursion, and iteration.

@since 0.1.0.0
-}
newtype MVar (a :: Type) = MVar IMVar

{-|
Underlying untyped identifier, which is numeric but otherwise opaque.

@since 0.1.0.0
-}
newtype IMVar = IMVar Word64 deriving newtype (Ord, Eq, Num, Enum, Show, Ix)

{-|
Underlying untyped identifier, which is numeric but otherwise opaque.

@since 0.1.0.0
-}
newtype IΣVar = IΣVar Word64 deriving newtype (Ord, Eq, Num, Enum, Show, Ix)

instance Show (MVar a) where show (MVar μ) = "μ" ++ show μ
instance Show (ΣVar a) where show (ΣVar σ) = "σ" ++ show σ

instance GEq ΣVar where
  geq (ΣVar u) (ΣVar v)
    | u == v    = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance GCompare ΣVar where
  gcompare σ1@(ΣVar u) σ2@(ΣVar v) = case compare u v of
    LT -> GLT
    EQ -> case geq σ1 σ2 of Just Refl -> GEQ
    GT -> GGT

{-|
An identifier representing some concrete register, but where the type is existential.

@since 0.1.0.0
-}
data SomeΣVar = forall r. SomeΣVar (ΣVar r)
instance Eq SomeΣVar where (==) = (==) `on` getIΣVar
instance Ord SomeΣVar where compare = compare `on` getIΣVar
instance Show SomeΣVar where show (SomeΣVar σ) = show σ

{-|
Fetch the untyped identifier from under the existential.

@since 0.1.0.0
-}
getIΣVar :: SomeΣVar -> IΣVar
getIΣVar (SomeΣVar (ΣVar σ)) = σ

instance GEq MVar where
  geq (MVar u) (MVar v)
    | u == v    = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance GCompare MVar where
  gcompare μ1@(MVar u) μ2@(MVar v) = case compare u v of
    LT -> GLT
    EQ -> case geq μ1 μ2 of Just Refl -> GEQ
    GT -> GGT
