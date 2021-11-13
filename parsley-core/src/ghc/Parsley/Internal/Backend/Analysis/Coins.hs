{-|
Module      : Parsley.Internal.Backend.Analysis.Coins
Description : Coins analysis.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Implements the analysis path required to determine how many tokens of input a given parser
is known to consume at /least/ in order to successfully execute. This provides the needed
metadata to perform the piggybank algorithm in the machine (see
"Parsley.Internal.Backend.Machine.Types.Context" for more information.)

@since 1.5.0.0
-}
module Parsley.Internal.Backend.Analysis.Coins (coinsNeeded, reclaimable) where

import Data.Bifunctor                   (first)
import Parsley.Internal.Backend.Machine (Instr(..), MetaInstr(..), Handler(..), Coins, plus1, minCoins, maxCoins, zero, minus, plusNotReclaim, willConsume)
import Parsley.Internal.Common.Indexed  (cata4, Fix4, Const4(..))

{-|
Calculate the number of tokens that will be consumed by a given machine.

@since 1.5.0.0
-}
coinsNeeded :: Fix4 (Instr o) xs n r a -> Coins
coinsNeeded = fst . getConst4 . cata4 (Const4 . alg True)

{-|
Calculate the number of tokens can be reclaimed by a lookAhead

@since 1.7.2.0
-}
reclaimable :: Fix4 (Instr o) xs n r a -> Coins
reclaimable = fst . getConst4 . cata4 (Const4 . alg False)

bilift2 :: (a -> b -> c) -> (x -> y -> z) -> (a, x) -> (b, y) -> (c, z)
bilift2 f g (x1, y1) (x2, y2) = (f x1 x2, g y1 y2)

algCatch :: (Coins, Bool) -> (Coins, Bool) -> (Coins, Bool)
algCatch k (_, True) = k
algCatch (_, True) k = k
algCatch (k1, _) (k2, _) = (minCoins k1 k2, False)

-- Bool represents if an empty is found in a branch (of a Catch)
-- This helps to get rid of `min` being used for `Try` where min is always 0
-- (The input is needed to /succeed/, so if one branch is doomed to fail it doesn't care about coins)
alg :: Bool -> Instr o (Const4 (Coins, Bool)) xs n r a -> (Coins, Bool)
alg _     Ret                                     = (zero, False)
alg _     (Push _ k)                              = getConst4 k -- was const False on the second parameter, I think that's probably right but a bit presumptive
alg _     (Pop k)                                 = getConst4 k
alg _     (Lift2 _ k)                             = getConst4 k
alg _     (Sat _ (Const4 k))                      = first plus1 k
alg _     (Call _ (Const4 k))                     = first (const zero) k
alg _     (Jump _)                                = (zero, False)
alg _     Empt                                    = (zero, True)
alg _     (Commit k)                              = getConst4 k
alg _     (Catch k h)                             = algCatch (getConst4 k) (algHandler h)
alg _     (Tell k)                                = getConst4 k
alg _     (Seek k)                                = getConst4 k
alg _     (Case p q)                              = algCatch (getConst4 p) (getConst4 q)
alg _     (Choices _ ks def)                      = foldr (algCatch . getConst4) (getConst4 def) ks
alg _     (Iter _ _ h)                            = first (const zero) (algHandler h)
alg _     (Join _)                                = (zero, False)
alg _     (MkJoin _ (Const4 b) (Const4 k))        = bilift2 (flip plusNotReclaim . willConsume) (||) b k
alg _     (Swap k)                                = getConst4 k
alg _     (Dup k)                                 = getConst4 k
alg _     (Make _ _ k)                            = getConst4 k
alg _     (Get _ _ k)                             = getConst4 k
alg _     (Put _ _ k)                             = getConst4 k
alg _     (SelectPos _ k)                         = getConst4 k
alg _     (LogEnter _ k)                          = getConst4 k
alg _     (LogExit _ k)                           = getConst4 k
alg _     (MetaInstr (AddCoins _) (Const4 k))     = k
alg _     (MetaInstr (RefundCoins n) (Const4 k))  = first (maxCoins zero . (`minus` n)) k -- These were refunded, so deduct
alg _     (MetaInstr (DrainCoins n) _)            = (n, False)                            -- Used to be `second (const False) k`, but these should be additive?
alg _     (MetaInstr (GiveBursary n) _)           = (n, False)                            -- We know that `n` is the required for `k`
alg _     (MetaInstr (PrefetchChar _) (Const4 k)) = k
alg True  (MetaInstr BlockCoins (Const4 k))       = first (const zero) k
alg False (MetaInstr BlockCoins (Const4 k))       = k

algHandler :: Handler o (Const4 (Coins, Bool)) xs n r a -> (Coins, Bool)
algHandler (Same _ yes _ no) = algCatch (getConst4 yes) (getConst4 no)
algHandler (Always _ k) = getConst4 k