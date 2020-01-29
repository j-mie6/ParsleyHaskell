{-# LANGUAGE GADTs #-}
module MachineAnalyser where

import Machine
import MachineAST
import Indexed

constInput :: Free3 (M o) Void3 xs r a -> Int
constInput = getConst3 . fold3 absurd (Const3 . alg)
  where
    alg :: M o (Const3 Int) xs r a -> Int
    alg Halt                = 0
    alg Ret                 = 0
    alg (Call μ k)          = 0
    alg (Jump μ)            = 0
    alg (Push _ k)          = getConst3 k
    alg (Pop k)             = getConst3 k
    alg (Lift2 f k)         = getConst3 k
    alg (Sat _ k)           = 1 + getConst3 k
    alg Empt                = 0
    alg (Commit k)          = getConst3 k
    alg (SoftFork p q)      = max (getConst3 p) (getConst3 q)
    alg (HardFork p q)      = max (getConst3 p) (getConst3 q)
    alg (Attempt k)         = getConst3 k
    alg (Tell k)            = getConst3 k
    alg (Seek k)            = getConst3 k
    alg (Case p q)          = max (getConst3 p) (getConst3 q)
    alg (Choices _ ks def)  = maximum (map getConst3 (def:ks))
    alg (ChainIter σ μ)     = 0
    alg (ChainInit σ m μ k) = 0
    alg (Join φ)            = 0
    alg (MkJoin φ p k)      = getConst3 k
    alg (Swap k)            = getConst3 k
    alg (Make σ k)          = getConst3 k
    alg (Get σ k)           = getConst3 k
    alg (Put σ k)           = getConst3 k
    alg (LogEnter _ k)      = getConst3 k
    alg (LogExit _ k)       = getConst3 k
    alg (MetaM m k)         = getConst3 k