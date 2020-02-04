{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
module MachineAnalyser where

import Machine
import MachineAST
import Indexed

constInput :: Fix3 (M o) xs r a -> Int
constInput = fst . getConst3 . cata3 (Const3 . alg)
  where
    algCatch :: (Int, Bool) -> (Int, Bool) -> (Int, Bool)
    algCatch k1 (k2, True) = k1
    algCatch (k1, True) k2 = k2
    algCatch (k1, _) (k2, _) = (min k1 k2, False)

    alg :: M o (Const3 (Int, Bool)) xs r a -> (Int, Bool)
    alg Halt                               = (0, False)
    alg Ret                                = (0, False)
    alg (Push _ (Const3 k))                = (fst k, False)
    alg (Pop k)                            = getConst3 k
    alg (Lift2 f k)                        = getConst3 k
    alg (Sat _ (Const3 k))                 = (fst k + 1, snd k)
    alg (Call _ (Const3 k))                = (0, snd k)
    alg (Jump _)                           = (0, False)
    alg Empt                               = (0, True)
    alg (Commit k)                         = getConst3 k
    alg (SoftFork p q)                     = algCatch (getConst3 p) (getConst3 q)
    alg (HardFork p q)                     = algCatch (getConst3 p) (getConst3 q)
    alg (Attempt k)                        = getConst3 k
    alg (Tell k)                           = getConst3 k
    alg (Seek k)                           = getConst3 k
    alg (Case p q)                         = algCatch (getConst3 p) (getConst3 q)
    alg (Choices _ ks def)                 = foldr (algCatch . getConst3) (getConst3 def) ks
    alg (ChainIter _ _)                    = (0, False)
    alg (ChainInit _ _ _ _)                = (0, False)
    alg (Join _)                           = (0, False)
    alg (MkJoin _ (Const3 b) (Const3 k))   = (fst k + fst b, snd k || snd b)
    alg (Swap k)                           = getConst3 k
    alg (Make _ k)                         = getConst3 k
    alg (Get _ k)                          = getConst3 k
    alg (Put _ k)                          = getConst3 k
    alg (LogEnter _ k)                     = getConst3 k
    alg (LogExit _ k)                      = getConst3 k
    alg (MetaM (AddCoins n) (Const3 k))    = (n, snd k)
    alg (MetaM (FreeCoins n) (Const3 k))   = (n, snd k)
    alg (MetaM (RefundCoins n) (Const3 k)) = (max (fst k - n) 0, snd k) -- These were refunded, so deduct
    alg (MetaM (DrainCoins n) (Const3 k))  = (fst k, False)