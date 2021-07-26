module Parsley.Internal.Backend.Analysis.Coins (coinsNeeded) where

import Parsley.Internal.Backend.Machine (Instr(..), MetaInstr(..), Handler(..))
import Parsley.Internal.Common.Indexed  (cata4, Fix4, Const4(..))

coinsNeeded :: Fix4 (Instr o) xs n r a -> Int
coinsNeeded = fst . getConst4 . cata4 (Const4 . alg)

first :: (a -> b) -> (a, x) -> (b, x)
first = flip bimap id

bimap :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
bimap = curry (bilift2 ($) ($))

bilift2 :: (a -> b -> c) -> (x -> y -> z) -> (a, x) -> (b, y) -> (c, z)
bilift2 f g (x1, y1) (x2, y2) = (f x1 x2, g y1 y2)


algCatch :: (Int, Bool) -> (Int, Bool) -> (Int, Bool)
algCatch k (_, True) = k
algCatch (_, True) k = k
algCatch (k1, _) (k2, _) = (min k1 k2, False)

-- Bool represents if an empty is found in a branch (of a Catch)
-- This helps to get rid of `min` being used for `Try` where min is always 0
-- (The input is needed to _succeed_, so if one branch is doomed to fail it doesn't care about coins)
alg :: Instr o (Const4 (Int, Bool)) xs n r a -> (Int, Bool)
alg Ret                                    = (0, False)
alg (Push _ k)                             = getConst4 k -- was const False on the second parameter, I think that's probably right but a bit presumptive
alg (Pop k)                                = getConst4 k
alg (Lift2 _ k)                            = getConst4 k
alg (Sat _ (Const4 k))                     = first (+ 1) k
alg (Call _ (Const4 k))                    = (0, snd k)
alg (Jump _)                               = (0, False)
alg Empt                                   = (0, True)
alg (Commit k)                             = getConst4 k
alg (Catch k h)                            = algCatch (getConst4 k) (algHandler h)
alg (Tell k)                               = getConst4 k
alg (Seek k)                               = getConst4 k
alg (Case p q)                             = algCatch (getConst4 p) (getConst4 q)
alg (Choices _ ks def)                     = foldr (algCatch . getConst4) (getConst4 def) ks
alg (Iter _ _ h)                           = (0, snd (algHandler h))
alg (Join _)                               = (0, False)
alg (MkJoin _ (Const4 b) (Const4 k))       = bilift2 (+) (||) k b
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

algHandler :: Handler o (Const4 (Int, Bool)) xs n r a -> (Int, Bool)
algHandler (Same yes no) = algCatch (getConst4 yes) (getConst4 no)
algHandler (Always k) = getConst4 k