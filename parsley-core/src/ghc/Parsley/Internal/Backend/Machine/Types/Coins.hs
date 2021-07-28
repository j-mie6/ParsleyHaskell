-- TODO: doc
module Parsley.Internal.Backend.Machine.Types.Coins (module Parsley.Internal.Backend.Machine.Types.Coins) where

data Coins = Coins {
    -- | The number of tokens we know must be consumed along the path to succeed.
    willConsume :: Int,
    -- | The number of tokens we can reclaim if another branch must be taken.
    canReclaim :: Int
  }

int :: Int -> Coins
int n = Coins n n

zero :: Coins
zero = int 0

minCoins :: Coins -> Coins -> Coins
minCoins (Coins k1 r1) (Coins k2 r2) = Coins (min k1 k2) (min r1 r2)

plus1 :: Coins -> Coins
plus1 = plus (Coins 1 1)

plus :: Coins -> Coins -> Coins
plus (Coins k1 r1) (Coins k2 r2) = Coins (k1 + k2) (r1 + r2)