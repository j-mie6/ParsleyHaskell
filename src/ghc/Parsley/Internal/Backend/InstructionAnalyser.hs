{-# LANGUAGE MultiParamTypeClasses,
             TypeFamilies,
             UndecidableInstances #-}
module Parsley.Internal.Backend.InstructionAnalyser (coinsNeeded, relevancy, Length) where

import Data.Kind                        (Type)
import Parsley.Internal.Backend.Machine (Instr(..), MetaInstr(..))
import Parsley.Internal.Common.Indexed  (cata4, Fix4, Const4(..))
import Parsley.Internal.Common.Vec      (Vec(..), Nat(..), SNat(..), SingNat(..), zipWithVec, replicateVec)

coinsNeeded :: Fix4 (Instr o) xs n r a -> Int
coinsNeeded = fst . getConst4 . cata4 (Const4 . alg)
  where
    algCatch :: (Int, Bool) -> (Int, Bool) -> (Int, Bool)
    algCatch k (_, True) = k
    algCatch (_, True) k = k
    algCatch (k1, _) (k2, _) = (min k1 k2, False)

    alg :: Instr o (Const4 (Int, Bool)) xs n r a -> (Int, Bool)
    alg Ret                                    = (0, False)
    alg (Push _ (Const4 k))                    = (fst k, False)
    alg (Pop k)                                = getConst4 k
    alg (Lift2 _ k)                            = getConst4 k
    alg (Sat _ (Const4 k))                     = (fst k + 1, snd k)
    alg (Call _ (Const4 k))                    = (0, snd k)
    alg (Jump _)                               = (0, False)
    alg Empt                                   = (0, True)
    alg (Commit k)                             = getConst4 k
    alg (Catch k h)                            = algCatch (getConst4 k) (getConst4 h)
    alg (Tell k)                               = getConst4 k
    alg (Seek k)                               = getConst4 k
    alg (Case p q)                             = algCatch (getConst4 p) (getConst4 q)
    alg (Choices _ ks def)                     = foldr (algCatch . getConst4) (getConst4 def) ks
    alg (Iter _ _ (Const4 k))                  = (0, snd k)
    alg (Join _)                               = (0, False)
    alg (MkJoin _ (Const4 b) (Const4 k))       = (fst k + fst b, snd k || snd b)
    alg (Swap k)                               = getConst4 k
    alg (Dup k)                                = getConst4 k
    alg (Make _ _ k)                           = getConst4 k
    alg (Get _ _ k)                            = getConst4 k
    alg (Put _ _ k)                            = getConst4 k
    alg (LogEnter _ k)                         = getConst4 k
    alg (LogExit _ k)                          = getConst4 k
    alg (MetaInstr (AddCoins _) (Const4 k))    = k
    alg (MetaInstr (RefundCoins n) (Const4 k)) = (max (fst k - n) 0, snd k) -- These were refunded, so deduct
    alg (MetaInstr (DrainCoins _) (Const4 k))  = (fst k, False)

{- TODO
  Live Value Analysis
  -------------------

  This analysis is designed to clean up dead registers:
    * Instead of the state laws on the Combinator AST, this should catch these cases
    * By performing it here we have ready access to the control flow information
    * We'll perform global register analysis

  State Laws:
    * get *> get = get = get <* get
    * put (pure x) *> get = put (pure x) *> pure x
    * put get = pure ()
    * put x *> put (pure y) = x *> put (pure y) = put x <* put (pure y)
    -->
    * Get . Pop . Get = Get = Get . Get . Pop -- Captured by relevancy analysis
    * Get . Get = Get . Dup Subsumes the above (Dup . Pop = id, Dup . Swap = Dup)
    * px . Put . Push () . Pop . Get = px . Dup . Put . Push () . Pop -- ??? (this law is better than above)
    * Get . Put . Push () = Push () -- ??? Improved relevancy analysis?
    * px . Put . Push () . Pop . py . Put . Push () = px . Pop . Push () . Pop . py . Put . Push () = px . Put . Push () . py . Put . Push () . Pop -- Captured by dead register analysis

  Best case scenario is that we can capture all of the above optimisations
  without a need to explicitly implement them.

  Idea 1) recurse through the machine and mark branches with their liveIn set
          if a register is not liveIn after a Put instruction it can be removed
          Get r gens r
          Put r kills r
  Idea 2) recurse through the machine and collect relevancy data:
          a value on the stack is relevant if it is consumed by `Lift2` or `Case`, etc
          it is irrelevant if consumed by Pop
          if Get produces an irrelevant operand, it can be replaced by Push BOTTOM
          Dup disjoins the relevancy of the top two elements of the stack
          Swap switches the relevancy of the top two elements of the stack
  Idea 3) recurse through the machine and collect everUsed information
          if a register is never used, then the Make instruction can be removed
-}

type family Length (xs :: [Type]) :: Nat where
  Length '[] = Zero
  Length (_ : xs) = Succ (Length xs)

newtype RelevancyStack xs (n :: Nat) r a = RelevancyStack { getStack :: SNat (Length xs) -> Vec (Length xs) Bool }

relevancy :: SingNat (Length xs) => Fix4 (Instr o) xs n r a -> Vec (Length xs) Bool
relevancy = ($ sing) . getStack . cata4 (RelevancyStack . alg)
  where
    zipRelevancy = zipWithVec (||)

    -- This algorithm is over-approximating: join and ret aren't _always_ relevant
    alg :: Instr o RelevancyStack xs n r a -> SNat (Length xs) -> Vec (Length xs) Bool
    alg Ret                _         = VCons True VNil
    alg (Push _ k)         n         = let VCons _ xs = getStack k (SSucc n) in xs
    alg (Pop k)            (SSucc n) = VCons False (getStack k n)
    alg (Lift2 _ k)        (SSucc n) = let VCons rel xs = getStack k n in VCons rel (VCons rel xs)
    alg (Sat _ k)          n         = let VCons _ xs = getStack k (SSucc n) in xs
    alg (Call _ k)         n         = let VCons _ xs = getStack k (SSucc n) in xs
    alg (Jump _)           _         = VNil
    alg Empt               n         = replicateVec n False
    alg (Commit k)         n         = getStack k n
    alg (Catch k _)        n         = getStack k n
    alg (Tell k)           n         = let VCons _ xs = getStack k (SSucc n) in xs
    alg (Seek k)           (SSucc n) = VCons True (getStack k n)
    alg (Case p q)         n         = VCons True (let VCons _ xs = zipRelevancy (getStack p n) (getStack q n) in xs)
    alg (Choices _ ks def) (SSucc n) = VCons True (foldr (zipRelevancy . (`getStack` n)) (getStack def n) ks)
    alg (Iter _ _ k)       n         = let VCons _ xs = getStack k (SSucc n) in xs
    alg (Join _)           (SSucc n) = VCons True (replicateVec n False)
    alg (MkJoin _ b _)     n         = let VCons _ xs = getStack b (SSucc n) in xs
    alg (Swap k)           n         = let VCons rel1 (VCons rel2 xs) = getStack k n in VCons rel2 (VCons rel1 xs)
    alg (Dup k)            n         = let VCons rel1 (VCons rel2 xs) = getStack k (SSucc n) in VCons (rel1 || rel2) xs
    alg (Make _ _ k)       (SSucc n) = VCons False (getStack k n)
    alg (Get _ _ k)        n         = let VCons _ xs = getStack k (SSucc n) in xs
    alg (Put _ _ k)        (SSucc n) = VCons False (getStack k n)
    alg (LogEnter _ k)     n         = getStack k n
    alg (LogExit _ k)      n         = getStack k n
    alg (MetaInstr _ k)    n         = getStack k n