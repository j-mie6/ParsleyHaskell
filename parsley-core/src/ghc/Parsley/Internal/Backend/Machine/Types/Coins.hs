{-# LANGUAGE DerivingStrategies #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Types.Coins
Description : Meta-data associated with input consumption optimisations.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : unstable

This module exposes `Coins` and the relevant operations. These are used by
constant input analysis to side-step unnecessary length checks and character
reads (in the case of lookahead).

@since 1.5.0.0
-}
module Parsley.Internal.Backend.Machine.Types.Coins (
    Coins(..),
    int, zero,
    minCoins, {-maxCoins,-}
    plus1, plus, minus,
    plusNotReclaim,
  ) where

{-|
Packages together the known input that can be consumed after a length-check with the number of
characters that can be rewound on a lookahead backtrack.

@since 1.5.0.0
-}
data Coins = Coins {
    -- | The number of tokens we know must be consumed along the path to succeed.
    willConsume :: !Int,
    -- | The number of tokens we can reclaim if the parser backtracks.
    canReclaim :: !Int
  } deriving stock Show

{-|
Makes a `Coins` value with equal quantities of coins and characters.

@since 1.5.0.0
-}
int :: Int -> Coins
int n = Coins n n

{-|
Makes a `Coins` value of 0.

@since 1.5.0.0
-}
zero :: Coins
zero = int 0

zipCoins :: (Int -> Int -> Int) -> Coins -> Coins -> Coins
zipCoins f (Coins k1 r1) (Coins k2 r2) = Coins (f k1 k2) (f r1 r2)

{-|
Takes the pairwise min of two `Coins` values.

@since 1.5.0.0
-}
minCoins :: Coins -> Coins -> Coins
minCoins = zipCoins min

{-|
Takes the pairwise max of two `Coins` values.

@since 1.5.0.0
-}
maxCoins :: Coins -> Coins -> Coins
maxCoins = zipCoins max

{-|
Adds 1 to all the `Coins` values.

@since 1.5.0.0
-}
plus1 :: Coins -> Coins
plus1 = plus (int 1)

{-|
Performs the pairwise addition of two `Coins` values.

@since 1.5.0.0
-}
plus :: Coins -> Coins -> Coins
plus = zipCoins (+)

{-|
Performs the pairwise subtraction of two `Coins` values.

@since 1.5.0.0
-}
minus :: Coins -> Coins -> Coins
minus c1 c2 = maxCoins zero (zipCoins (-) c1 c2)

{-|
A verson of plus where the reclaim value remains constant.

@since 1.5.0.0
-}
plusNotReclaim :: Coins -> Int -> Coins
plusNotReclaim (Coins k r) n = Coins (k + n) r
