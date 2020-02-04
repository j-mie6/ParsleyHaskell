{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
module MachineAnalyser where

import Machine
import MachineAST
import Indexed

constInput :: Fix3 (M o) xs r a -> Int
constInput = fst . cata3 (fromPair . alg)
  where
    fst :: (Const3 x :**: Const3 y) (xs :: [*]) r a -> x
    fst = getConst3 . ifst3
    snd :: (Const3 x :**: Const3 y) (xs :: [*]) r a -> y
    snd = getConst3 . isnd3
    fromPair :: (x, y) -> (Const3 x :**: Const3 y) (xs :: [*]) r a 
    fromPair (x, b) = Const3 x :**: Const3 b
    toPair :: (Const3 x :**: Const3 y) (xs :: [*]) r a -> (x, y)
    toPair (x :**: y) = (getConst3 x, getConst3 y)

    algCatch :: (Int, Bool) -> (Int, Bool) -> (Int, Bool)
    algCatch k1 (k2, True) = k1
    algCatch (k1, True) k2 = k2
    algCatch (k1, _) (k2, _) = (min k1 k2, False)

    alg :: M o (Const3 Int :**: Const3 Bool) xs r a -> (Int, Bool)
    alg Halt                      = (0, False)
    alg Ret                       = (0, False)
    alg (Push _ k)                = (fst k, False)
    alg (Pop k)                   = toPair k
    alg (Lift2 f k)               = toPair k
    alg (Sat _ k)                 = (fst k + 1, snd k)
    alg (Call _ k)                = (0, snd k)
    alg (Jump _)                  = (0, False)
    alg Empt                      = (0, True)
    alg (Commit k)                = toPair k
    alg (SoftFork p q)            = algCatch (toPair p) (toPair q)
    alg (HardFork p q)            = algCatch (toPair p) (toPair q)
    alg (Attempt k)               = toPair k
    alg (Tell k)                  = toPair k
    alg (Seek k)                  = toPair k
    alg (Case p q)                = algCatch (toPair p) (toPair q)
    alg (Choices _ ks def)        = foldr (algCatch . toPair) (toPair def) ks
    alg (ChainIter _ _)           = (0, False)
    alg (ChainInit _ _ _ _)       = (0, False)
    alg (Join _)                  = (0, False)
    alg (MkJoin _ b k)            = (fst k + fst b, snd k || snd b)
    alg (Swap k)                  = toPair k
    alg (Make _ k)                = toPair k
    alg (Get _ k)                 = toPair k
    alg (Put _ k)                 = toPair k
    alg (LogEnter _ k)            = toPair k
    alg (LogExit _ k)             = toPair k
    alg (MetaM (AddCoins n) k)    = (n, snd k)
    alg (MetaM (FreeCoins n) k)   = (n, snd k)
    alg (MetaM (RefundCoins n) k) = (max (fst k - n) 0, snd k) -- These were refunded, so deduct
    alg (MetaM (DrainCoins n) k)  = (fst k, False)