{-# LANGUAGE KindSignatures,
             GeneralizedNewtypeDeriving,
             DerivingStrategies #-}
module Parsley.Backend.Machine.Identifiers (
    ΦVar(..), IΦVar,
    module Parsley.Core.Identifiers,
  ) where

import Data.GADT.Compare        (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))
import Data.Word                (Word64)
import Parsley.Core.Identifiers
import Unsafe.Coerce            (unsafeCoerce)

newtype ΦVar (a :: *) = ΦVar IΦVar
newtype IΦVar = IΦVar Word64 deriving newtype (Ord, Eq, Num, Enum, Show)

instance Show (ΦVar a) where show (ΦVar φ) = "φ" ++ show φ

instance GEq ΦVar where
  geq (ΦVar u) (ΦVar v)
    | u == v    = Just (unsafeCoerce Refl)
    | otherwise = Nothing

instance GCompare ΦVar where
  gcompare (ΦVar u) (ΦVar v) = case compare u v of
    LT -> unsafeCoerce GLT
    EQ -> unsafeCoerce GEQ
    GT -> unsafeCoerce GGT