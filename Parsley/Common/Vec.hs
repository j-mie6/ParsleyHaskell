{-# LANGUAGE TypeOperators,
             TypeFamilies,
             DataKinds,
             GADTs #-}
module Parsley.Common.Vec where

import Parsley.Common.Indexed (Nat(..))

data Vec n a where
  VNil :: Vec Zero a
  VCons :: a -> Vec n a -> Vec (Succ n) a

data SNat (n :: Nat) where
  SZero :: SNat Zero
  SSucc :: SNat n -> SNat (Succ n)

replicateVec :: SNat n -> a -> Vec n a
replicateVec SZero _     = VNil
replicateVec (SSucc n) x = VCons x (replicateVec n x)

zipWithVec :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWithVec _ VNil         VNil         = VNil
zipWithVec f (VCons x xs) (VCons y ys) = VCons (f x y) (zipWithVec f xs ys)

class SingNat (n :: Nat) where sing :: SNat n
instance SingNat Zero where sing = SZero
instance SingNat n => SingNat (Succ n) where sing = SSucc sing