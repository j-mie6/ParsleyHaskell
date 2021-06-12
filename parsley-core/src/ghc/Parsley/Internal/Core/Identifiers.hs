{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE DerivingStrategies,
             GeneralizedNewtypeDeriving #-}
module Parsley.Internal.Core.Identifiers (
    MVar(..), IMVar,
    ΣVar(..), IΣVar,
  ) where

import Data.Array        (Ix)
import Data.GADT.Compare (GEq, GCompare, gcompare, geq, GOrdering(..))
import Data.Kind         (Type)
import Data.Typeable     ((:~:)(Refl))
import Data.Word         (Word64)
import Unsafe.Coerce     (unsafeCoerce)

newtype ΣVar (a :: Type) = ΣVar IΣVar
newtype MVar (a :: Type) = MVar IMVar
newtype IMVar = IMVar Word64 deriving newtype (Ord, Eq, Num, Enum, Show, Ix)
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

instance GEq MVar where
  geq (MVar u) (MVar v)
    | u == v    = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance GCompare MVar where
  gcompare μ1@(MVar u) μ2@(MVar v) = case compare u v of
    LT -> GLT
    EQ -> case geq μ1 μ2 of Just Refl -> GEQ
    GT -> GGT