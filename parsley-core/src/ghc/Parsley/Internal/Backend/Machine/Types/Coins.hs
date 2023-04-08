{-# LANGUAGE DerivingStrategies, PatternSynonyms #-}
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
    minCoins,
    plus1, minus, canReclaim,
    pattern Zero
  ) where

import Parsley.Internal.Core (CharPred)
import Parsley.Internal.Core.CharPred (mergePreds)

{-|
Packages together the known input that can be consumed after a length-check with the number of
characters that can be rewound on a lookahead backtrack.

@since 1.5.0.0
-}
data Coins = Coins {
    -- | The number of tokens we know must be consumed along the path to succeed.
    willConsume :: {-# UNPACK #-} !Int,
    knownPreds :: ![CharPred]
  } deriving stock Show

canReclaim :: Coins -> Int
canReclaim = willConsume

{-|
Makes a `Coins` value of 0.

@since 1.5.0.0
-}
pattern Zero :: Coins
pattern Zero = Coins 0 []

zipCoins :: (Int -> Int -> Int) -> ([CharPred] -> [CharPred] -> [CharPred]) -> Coins -> Coins -> Coins
zipCoins f g (Coins k1 cs1) (Coins k2 cs2)
  | length cs' /= k' = error "the number of coins must always equal the number of predicates"
  | otherwise        = Coins k' cs'
  where
    k' = f k1 k2
    cs' = g cs1 cs2

{-|
Takes the pairwise min of two `Coins` values.

@since 1.5.0.0
-}
minCoins :: Coins -> Coins -> Coins
minCoins = zipCoins min (zipWith mergePreds)

{-|
Adds 1 to all the `Coins` values.

@since 1.5.0.0
-}
plus1 :: CharPred -> Coins -> Coins
plus1 p =  zipCoins (+) (++) (Coins 1 [p])

{-|
Performs the pairwise subtraction of two `Coins` values.

@since 1.5.0.0
-}
minus :: Coins -> Coins -> Coins
-- FIXME: just awful lol
minus = zipCoins (\m n -> max 0 (m - n)) (\cs1 cs2 -> drop (length cs2) cs1)
