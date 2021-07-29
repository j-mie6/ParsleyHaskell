{-# LANGUAGE DerivingStrategies #-}
-- TODO: doc
module Parsley.Internal.Backend.Machine.Types.Coins (module Parsley.Internal.Backend.Machine.Types.Coins) where

data Coins = Coins {
    -- | The number of tokens we know must be consumed along the path to succeed.
    willConsume :: Int,
    -- | The number of tokens we can reclaim if another branch must be taken.
    canReclaim :: Int
  } deriving stock Show

int :: Int -> Coins
int n = Coins n n

zero :: Coins
zero = int 0

zipCoins :: (Int -> Int -> Int) -> Coins -> Coins -> Coins
zipCoins f (Coins k1 r1) (Coins k2 r2) = Coins (f k1 k2) (f r1 r2)

minCoins :: Coins -> Coins -> Coins
minCoins = zipCoins min

maxCoins :: Coins -> Coins -> Coins
maxCoins = zipCoins max

plus1 :: Coins -> Coins
plus1 = plus (Coins 1 1)

plus :: Coins -> Coins -> Coins
plus = zipCoins (+)

minus :: Coins -> Coins -> Coins
minus = zipCoins (-)

plusNotReclaim :: Coins -> Int -> Coins
plusNotReclaim (Coins k r) n = Coins (k + n) r