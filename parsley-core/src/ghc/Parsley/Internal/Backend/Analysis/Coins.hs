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
module Parsley.Internal.Backend.Analysis.Coins (coinsNeeded) where

import Parsley.Internal.Backend.Machine (Instr(..), MetaInstr(..), Handler(..), Coins(..), plus1, plus, minCoins, zero)
import Parsley.Internal.Common.Indexed  (cata4, Fix4, Const4(..))

{-|
Calculate the number of tokens that will be consumed by a given machine.

@since 1.5.0.0
-}
coinsNeeded :: Fix4 (Instr o) xs n r a -> Int
coinsNeeded = willConsume . fst . getConst4 . cata4 (Const4 . alg)

first :: (a -> b) -> (a, x) -> (b, x)
first = flip bimap id

second :: (a -> b) -> (x, a) -> (x, b)
second = bimap id

bimap :: (a -> b) -> (c -> d) -> (a, c) -> (b, d)
bimap = curry (bilift2 ($) ($))

bilift2 :: (a -> b -> c) -> (x -> y -> z) -> (a, x) -> (b, y) -> (c, z)
bilift2 f g (x1, y1) (x2, y2) = (f x1 x2, g y1 y2)

algCatch :: (Coins, Bool) -> (Coins, Bool) -> (Coins, Bool)
algCatch k (_, True) = k
algCatch (_, True) k = k
algCatch (k1, _) (k2, _) = (minCoins k1 k2, False)

-- Bool represents if an empty is found in a branch (of a Catch)
-- This helps to get rid of `min` being used for `Try` where min is always 0
-- (The input is needed to /succeed/, so if one branch is doomed to fail it doesn't care about coins)
alg :: Instr o (Const4 (Coins, Bool)) xs n r a -> (Coins, Bool)
alg Ret                                    = (zero, False)
alg (Push _ k)                             = getConst4 k -- was const False on the second parameter, I think that's probably right but a bit presumptive
alg (Pop k)                                = getConst4 k
alg (Lift2 _ k)                            = getConst4 k
alg (Sat _ (Const4 k))                     = first plus1 k
alg (Call _ (Const4 k))                    = first (const zero) k
alg (Jump _)                               = (zero, False)
alg Empt                                   = (zero, True)
alg (Commit k)                             = getConst4 k
alg (Catch k h)                            = algCatch (getConst4 k) (algHandler h)
alg (Tell k)                               = getConst4 k
alg (Seek k)                               = getConst4 k
alg (Case p q)                             = algCatch (getConst4 p) (getConst4 q)
alg (Choices _ ks def)                     = foldr (algCatch . getConst4) (getConst4 def) ks
alg (Iter _ _ h)                           = first (const zero) (algHandler h)
alg (Join _)                               = (zero, False)
alg (MkJoin _ (Const4 b) (Const4 k))       = bilift2 plus (||) k b
alg (Swap k)                               = getConst4 k
alg (Dup k)                                = getConst4 k
alg (Make _ _ k)                           = getConst4 k
alg (Get _ _ k)                            = getConst4 k
alg (Put _ _ k)                            = getConst4 k
alg (LogEnter _ k)                         = getConst4 k
alg (LogExit _ k)                          = getConst4 k
alg (MetaInstr (AddCoins _) (Const4 k))    = k
alg (MetaInstr (RefundCoins n) (Const4 k)) = first adjust k -- These were refunded, so deduct
  where
    adjust :: Coins -> Coins
    adjust (Coins k r) = Coins (min 0 (k - n)) r
alg (MetaInstr (DrainCoins _) (Const4 k))  = second (const False) k

algHandler :: Handler o (Const4 (Coins, Bool)) xs n r a -> (Coins, Bool)
algHandler (Same yes no) = algCatch (getConst4 yes) (getConst4 no)
algHandler (Always k) = getConst4 k