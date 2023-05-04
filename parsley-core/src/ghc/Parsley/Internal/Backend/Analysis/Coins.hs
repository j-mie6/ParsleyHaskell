{-# LANGUAGE PatternSynonyms #-}
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
import Parsley.Internal.Backend.Machine (Instr(..), MetaInstr(..), Handler(..), Coins, plus1, minCoins, pattern Zero, minus, items)
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

algCatch :: (Coins, Bool) -> (Coins, Bool) -> (Coins, Bool)
-- if either of the two halves have an empty, then skip it
-- TODO: perhaps this should be checked to ensure it is 0 as well?
algCatch k (_, True) = k
algCatch (_, True) k = k
-- take the smaller of the two branches
algCatch (k1, _) (k2, _) = (minCoins k1 k2, False)

algHandler :: Handler o (Const4 (Coins, Bool)) xs n r a -> (Coins, Bool)
algHandler (Same _ yes _ no) = algCatch (getConst4 yes) (getConst4 no)
algHandler (Always _ k) = getConst4 k

-- Bool represents if an empty is found in a branch (of a Catch)
-- This helps to get rid of `min` being used for `Try` where min is always 0
-- (The input is needed to /succeed/, so if one branch is doomed to fail it doesn't care about coins)
alg :: Bool -> Instr o (Const4 (Coins, Bool)) xs n r a -> (Coins, Bool)
-- All of these move control flow to somewhere else, and this means that there can be no factoring of
-- input across them, return or not: the properties of the foreign call are not known.
alg _     Ret                                    = (Zero, False)
alg _     Call{}                                 = (Zero, False)
alg _     Jump{}                                 = (Zero, False)
alg _     Iter{}                                 = (Zero, False)
alg _     Join{}                                 = (Zero, False) -- this is zero because a DrainCoins is generated just in front!
alg _     Empt                                   = (Zero, True)
-- all of these instructions have no effect on the coins of their continuation, and are just transitive
alg _     (Push _ (Const4 k))                    = k
alg _     (Pop (Const4 k))                       = k
alg _     (Lift2 _ (Const4 k))                   = k
alg _     (Commit (Const4 k))                    = k
alg _     (Tell (Const4 k))                      = k
alg _     (Seek (Const4 k))                      = k
alg _     (MkJoin _ _ (Const4 k))                = k
alg _     (Swap (Const4 k))                      = k
alg _     (Dup (Const4 k))                       = k
alg _     (Make _ _ (Const4 k))                  = k
alg _     (Get _ _ (Const4 k))                   = k
alg _     (SelectPos _ (Const4 k))               = k
alg _     (LogEnter _ (Const4 k))                = k
alg _     (LogExit _ (Const4 k))                 = k
alg _     (MetaInstr (AddCoins _) (Const4 k))    = k
-- cannot allow factoring through a put, because it could stop it from executing
-- but this is done in code gen via a Block, which can be disabled
alg _     (Put _ _ (Const4 k))                   = k
-- reading a character obviously contributes a single coin to the total along with its predicate
alg _     (Sat p (Const4 k))                     = first (plus1 p) k
alg _     (Catch k h)                            = algCatch (getConst4 k) (algHandler h)
alg _     (Case p q)                             = algCatch (getConst4 p) (getConst4 q)
alg _     (Choices _ ks def)                     = foldr (algCatch . getConst4) (getConst4 def) ks
-- as these coins are refunded in `k`, they should be deducted from the required coins for `k`
alg _     (MetaInstr (RefundCoins n) (Const4 k)) = first (`minus` n) k -- TODO: minus could actually keep the predicate knowledge for intersection?
-- we want these propagated out so that they commute across a factored boundary
-- FIXME: ideally, they should have no items with them: they cannot be used in the binding, so no point pulling them out
--       if two branches merge, perhaps [Maybe CharPred] and use zipWith (<|>)?
alg _     (MetaInstr (DrainCoins n) _)           = (items n, False)
-- no point in propagating forward, these are at the front of a binding
alg _     (MetaInstr (GiveBursary _) _)          = (Zero, False)
-- this is the instruction that actions a cut by blocking all coins from traversing it
-- however, this can be disabled when processing a lookahead
alg True  (MetaInstr BlockCoins (Const4 k))      = first (const Zero) k
alg False (MetaInstr BlockCoins (Const4 k))      = k
