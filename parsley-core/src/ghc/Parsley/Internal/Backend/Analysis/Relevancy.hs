{-# LANGUAGE MultiParamTypeClasses,
             TypeFamilies,
             UndecidableInstances #-}
{-|
Module      : Parsley.Internal.Backend.Analysis.Relevancy
Description : Value relevancy analysis.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes an analysis that can determine whether each of the values present on the stack for a
given machine are actually used or not. This information may be useful in the future to calculate
whether a register is "dead" or not.

@since 1.5.0.0
-}
module Parsley.Internal.Backend.Analysis.Relevancy (relevancy, Length) where

import Data.Kind                        (Type)
import Parsley.Internal.Backend.Machine (Instr(..), Handler(..))
import Parsley.Internal.Common.Indexed  (cata4, Fix4)
import Parsley.Internal.Common.Vec      (Vec(..), Nat(..), SNat(..), SingNat(..), zipWithVec, replicateVec)

{-|
Provides a conservative estimate on whether or not each of the elements of the stack on
entry to a machine are actually used in the computation.

@since 1.5.0.0
-}
relevancy :: SingNat (Length xs) => Fix4 (Instr o) xs n m r -> Vec (Length xs) Bool
relevancy = ($ sing) . getStack . cata4 (RelevancyStack . alg)

{-|
Computes the length of a type-level list. Used to index a `Vec`.

@since 1.5.0.0
-}
type family Length (xs :: [Type]) :: Nat where
  Length '[] = Zero
  Length (_ : xs) = Succ (Length xs)

newtype RelevancyStack xs (n :: Nat) (m :: Nat) r = RelevancyStack { getStack :: SNat (Length xs) -> Vec (Length xs) Bool }

zipRelevancy :: Vec n Bool -> Vec n Bool -> Vec n Bool
zipRelevancy = zipWithVec (||)

-- This algorithm is over-approximating: join and ret aren't _always_ relevant
alg :: Instr o RelevancyStack xs n m r -> SNat (Length xs) -> Vec (Length xs) Bool
alg Ret                _         = VCons True VNil
alg (Push _ k)         n         = let VCons _ xs = getStack k (SSucc n) in xs
alg (Pop k)            (SSucc n) = VCons False (getStack k n)
alg (Lift2 _ k)        (SSucc n) = let VCons rel xs = getStack k n in VCons rel (VCons rel xs)
alg (Sat _ k)          n         = let VCons _ xs = getStack k (SSucc n) in xs
alg (Call _ k)         n         = let VCons _ xs = getStack k (SSucc n) in xs
alg (Jump _)           _         = VNil
alg (Commit k)         n         = getStack k n
alg (Catch k _)        n         = getStack k n
alg (Tell k)           n         = let VCons _ xs = getStack k (SSucc n) in xs
alg (Seek k)           (SSucc n) = VCons True (getStack k n)
alg (Case p q)         n         = VCons True (let VCons _ xs = zipRelevancy (getStack p n) (getStack q n) in xs)
alg (Choices _ ks def) (SSucc n) = VCons True (foldr (zipRelevancy . (`getStack` n)) (getStack def n) ks)
alg (Iter _ _ h)       n         = let VCons _ xs = algHandler h (SSucc n) in xs
alg (Join _)           (SSucc n) = VCons True (replicateVec n False)
alg (MkJoin _ b _)     n         = let VCons _ xs = getStack b (SSucc n) in xs
alg (Swap k)           n         = let VCons rel1 (VCons rel2 xs) = getStack k n in VCons rel2 (VCons rel1 xs)
alg (Dup k)            n         = let VCons rel1 (VCons rel2 xs) = getStack k (SSucc n) in VCons (rel1 || rel2) xs
alg (Make _ _ k)       (SSucc n) = VCons False (getStack k n)
alg (Get _ _ k)        n         = let VCons _ xs = getStack k (SSucc n) in xs
alg (Put _ _ k)        (SSucc n) = VCons False (getStack k n)
alg (SelectPos _ k)    n         = let VCons _ xs = getStack k (SSucc n) in xs
alg Empt               n         = replicateVec n False
alg Raise              n         = replicateVec n False
alg (MergeErrors k)    n         = getStack k n
alg (PopError k)       n         = getStack k n
alg (ErrorToGhost k)   n         = getStack k n
alg (SaveGhosts _ k)   n         = getStack k n
alg (PopGhosts k)      n         = getStack k n
alg (MergeGhosts k)    n         = getStack k n
alg (LogEnter _ k)     n         = getStack k n
alg (LogExit _ k)      n         = getStack k n
alg (MetaInstr _ k)    n         = getStack k n

algHandler :: Handler o RelevancyStack xs n m r -> SNat (Length xs) -> Vec (Length xs) Bool
algHandler (Same _ yes _ no) (SSucc n) = VCons True (let VCons _ xs = zipRelevancy (VCons False (getStack yes n)) (getStack no (SSucc n)) in xs)
algHandler (Always _ k) n = getStack k n
