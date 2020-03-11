{-# LANGUAGE GADTs #-}
module MachineAnalyser where

import Machine
import MachineAST
import Indexed

coinsNeeded :: Fix3 (M q o) xs r a -> Int
coinsNeeded = fst . getConst3 . cata3 (Const3 . alg)
  where
    algCatch :: (Int, Bool) -> (Int, Bool) -> (Int, Bool)
    algCatch k1 (k2, True) = k1
    algCatch (k1, True) k2 = k2
    algCatch (k1, _) (k2, _) = (min k1 k2, False)

    alg :: M q o (Const3 (Int, Bool)) xs r a -> (Int, Bool)
    alg Ret                                = (0, False)
    alg (Push _ (Const3 k))                = (fst k, False)
    alg (Pop k)                            = getConst3 k
    alg (Lift2 f k)                        = getConst3 k
    alg (Sat _ (Const3 k))                 = (fst k + 1, snd k)
    alg (Call _ (Const3 k))                = (0, snd k)
    alg (Jump _)                           = (0, False)
    alg Empt                               = (0, True)
    alg (Commit k)                         = getConst3 k
    alg (Catch k h)                        = algCatch (getConst3 k) (getConst3 h)
    alg (Tell k)                           = getConst3 k
    alg (Seek k)                           = getConst3 k
    alg (Case p q)                         = algCatch (getConst3 p) (getConst3 q)
    alg (Choices _ ks def)                 = foldr (algCatch . getConst3) (getConst3 def) ks
    alg (ChainIter _ _)                    = (0, False)
    alg (ChainInit _ _ _ (Const3 k))       = (0, snd k)
    alg (Join _)                           = (0, False)
    alg (MkJoin _ (Const3 b) (Const3 k))   = (fst k + fst b, snd k || snd b)
    alg (Swap k)                           = getConst3 k
    alg (Make _ k)                         = getConst3 k
    alg (Get _ k)                          = getConst3 k
    alg (Put _ k)                          = getConst3 k
    alg (LogEnter _ k)                     = getConst3 k
    alg (LogExit _ k)                      = getConst3 k
    alg (Handler (Parsec h))               = getConst3 h
    alg (Handler _)                        = (0, False)
    alg (MetaM (AddCoins n) (Const3 k))    = k
    alg (MetaM (FreeCoins n) (Const3 k))   = (n, snd k)
    alg (MetaM (RefundCoins n) (Const3 k)) = (max (fst k - n) 0, snd k) -- These were refunded, so deduct
    alg (MetaM (DrainCoins n) (Const3 k))  = (fst k, False)