{-# LANGUAGE KindSignatures,
             GeneralizedNewtypeDeriving,
             DerivingStrategies #-}
module Parsley.Core.Identifiers (
    MVar(..), IMVar,
    ΣVar(..), IΣVar,
  ) where

import Data.GADT.Compare (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))
import Data.Word         (Word64)
import Unsafe.Coerce     (unsafeCoerce)

newtype ΣVar (a :: *) = ΣVar IΣVar
newtype MVar (a :: *) = MVar IMVar
newtype IMVar = IMVar Word64 deriving newtype (Ord, Eq, Num, Enum, Show)
newtype IΣVar = IΣVar Word64 deriving newtype (Ord, Eq, Num, Enum, Show)

instance Show (MVar a) where show (MVar μ) = "μ" ++ show μ
instance Show (ΣVar a) where show (ΣVar σ) = "σ" ++ show σ

instance GEq ΣVar where
  geq (ΣVar u) (ΣVar v)
    | u == v    = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance GCompare ΣVar where
  gcompare (ΣVar u) (ΣVar v) = case compare u v of
    LT -> unsafeCoerce GLT
    EQ -> unsafeCoerce GEQ
    GT -> unsafeCoerce GGT

instance GEq MVar where
  geq (MVar u) (MVar v)
    | u == v    = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance GCompare MVar where
  gcompare (MVar u) (MVar v) = case compare u v of
    LT -> unsafeCoerce GLT
    EQ -> unsafeCoerce GEQ
    GT -> unsafeCoerce GGT