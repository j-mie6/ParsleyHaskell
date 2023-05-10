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
    pattern Zero, one, items
  ) where

import Control.Applicative (liftA2)
import Parsley.Internal.Core.CharPred (CharPred, mergePreds)

{-|
Packages together the known input that can be consumed after a length-check with the number of
characters that can be rewound on a lookahead backtrack.

@since 1.5.0.0
-}
data Coins = Coins {
    -- | The number of tokens we know must be consumed along the path to succeed.
    willConsume :: {-# UNPACK #-} !Int,
    willCache   :: {-# UNPACK #-} !Int,
    knownPreds  :: !(Maybe CharPred)
  } deriving stock Show

canReclaim :: Coins -> Int
canReclaim = willConsume

{-|
Makes a `Coins` value of 0.

@since 1.5.0.0
-}
pattern Zero :: Coins
pattern Zero = Coins 0 0 Nothing

one :: CharPred -> Coins
one p = Coins 1 1 (Just p)

items :: Int -> Coins
items n = Coins n n Nothing

zipCoins :: (Int -> Int -> Int) -> (Int -> Int -> Int) -> (Maybe CharPred -> Maybe CharPred -> Maybe CharPred) -> Coins -> Coins -> Coins
zipCoins f g h (Coins k1 c1 cs1) (Coins k2 c2 cs2) = Coins k' c' cs'
  where
    k' = f k1 k2
    c' = g c1 c2
    cs' = h cs1 cs2

{-|
Takes the pairwise min of two `Coins` values.

@since 1.5.0.0
-}
minCoins :: Coins -> Coins -> Coins
minCoins = zipCoins min min (liftA2 mergePreds)

{-|
Adds 1 to all the `Coins` values.

@since 1.5.0.0
-}
plus1 :: CharPred -> Coins -> Coins
plus1 p =  zipCoins (+) (+) const (one p)

{-|
@since 1.5.0.0
-}
minus :: Coins -> Int -> Coins
minus c 0 = c
minus (Coins n c _) m = Coins (max (n - m) 0) (max (c - m) 0) Nothing
