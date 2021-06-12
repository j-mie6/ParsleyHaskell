{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE DerivingStrategies,
             GeneralizedNewtypeDeriving #-}
module Parsley.Internal.Backend.Machine.Identifiers (
    ΦVar(..), IΦVar,
    module Parsley.Internal.Core.Identifiers,
  ) where

import Data.GADT.Compare                 (GEq, GCompare, gcompare, geq, GOrdering(..))
import Data.Kind                         (Type)
import Data.Typeable                     ((:~:)(Refl))
import Data.Word                         (Word64)
import Parsley.Internal.Core.Identifiers -- for re-export
import Unsafe.Coerce                     (unsafeCoerce)

newtype ΦVar (a :: Type) = ΦVar IΦVar
newtype IΦVar = IΦVar Word64 deriving newtype (Ord, Eq, Num, Enum, Show)

instance Show (ΦVar a) where show (ΦVar φ) = "φ" ++ show φ

instance GEq ΦVar where
  geq (ΦVar u) (ΦVar v)
    | u == v    = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance GCompare ΦVar where
  gcompare φ1@(ΦVar u) φ2@(ΦVar v) = case compare u v of
    LT -> GLT
    EQ -> case geq φ1 φ2 of Just Refl -> GEQ
    GT -> GGT