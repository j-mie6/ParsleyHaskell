{-# LANGUAGE GADTs #-}
module InstructionAnalyser where

import Instructions
import Indexed

coinsNeeded :: Fix4 (Instr q o) xs n r a -> Int
coinsNeeded = fst . getConst4 . cata4 (Const4 . alg)
  where
    algCatch :: (Int, Bool) -> (Int, Bool) -> (Int, Bool)
    algCatch k1 (k2, True) = k1
    algCatch (k1, True) k2 = k2
    algCatch (k1, _) (k2, _) = (min k1 k2, False)

    alg :: Instr q o (Const4 (Int, Bool)) xs n r a -> (Int, Bool)
    alg Ret                                    = (0, False)
    alg (Push _ (Const4 k))                    = (fst k, False)
    alg (Pop k)                                = getConst4 k
    alg (Lift2 f k)                            = getConst4 k
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
    alg (Make _ k)                             = getConst4 k
    alg (Get _ k)                              = getConst4 k
    alg (Put _ k)                              = getConst4 k
    alg (LogEnter _ k)                         = getConst4 k
    alg (LogExit _ k)                          = getConst4 k
    alg (MetaInstr (AddCoins n) (Const4 k))    = k
    alg (MetaInstr (FreeCoins n) (Const4 k))   = (n, snd k)
    alg (MetaInstr (RefundCoins n) (Const4 k)) = (max (fst k - n) 0, snd k) -- These were refunded, so deduct
    alg (MetaInstr (DrainCoins n) (Const4 k))  = (fst k, False)