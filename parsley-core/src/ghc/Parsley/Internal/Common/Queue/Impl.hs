{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE DerivingStrategies, ViewPatterns #-}
{-|
Module      : Parsley.Internal.Common.Queue.Impl
Description : Implementation of a queue.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Implementation of a FIFO queue structure, with amortized operations.

@since 1.5.0.0
-}
module Parsley.Internal.Common.Queue.Impl (
    module Parsley.Internal.Common.Queue.Impl
  ) where

import Prelude hiding (null, foldr)
import Data.List (foldl')

import qualified Prelude (foldr)

{-|
Concrete FIFO Queue, with amortized constant operations.

@since 1.5.0.0
-}
data Queue a = Queue {
  outsz :: Int,
  outs  :: [a],
  insz  :: Int,
  ins   :: [a]
} deriving stock Eq

{-|
Construct an empty queue.

@since 1.5.0.0
-}
empty :: Queue a
empty = Queue 0 [] 0 []

{-|
Adds an element onto the end of the queue.

@since 1.5.0.0
-}
enqueue :: a -> Queue a -> Queue a
enqueue x q = q {insz = insz q + 1, ins = x : ins q}

{-|
Adds each of the elements onto the queue, from left-to-right.

@since 1.5.0.0
-}
enqueueAll :: [a] -> Queue a -> Queue a
enqueueAll xs q = q { insz = insz q + length xs, ins = foldl' (flip (:)) (ins q) xs }

{-|
Removes an element from the front of the queue.

@since 1.5.0.0
-}
dequeue :: Queue a -> (a, Queue a)
dequeue q@(outs -> (x:outs')) = (x, q {outsz = outsz q - 1, outs = outs'})
dequeue q@(outs -> [])
  | insz q /= 0 = dequeue (Queue (insz q) (reverse (ins q)) 0 [])
  | otherwise   = error "dequeue of empty queue"

{-|
modifies the head of the queue, without removal. Returns the old head

@since 2.1.0.0
-}
poke :: (a -> a) -> Queue a -> (a, Queue a)
poke f q@(outs -> (x:outs')) = (x, q {outs = f x : outs'})
poke f q@(outs -> [])
  | insz q /= 0 = poke f (Queue (insz q) (reverse (ins q)) 0 [])
  | otherwise   = error "poke of empty queue"

{-|
Is the queue empty?

@since 1.5.0.0
-}
null :: Queue a -> Bool
null (Queue 0 [] 0 []) = True
null _ = False

{-|
Returns how many elements are in the queue.

@since 1.5.0.0
-}
size :: Queue a -> Int
size q = insz q + outsz q

{-|
Folds the values in the queue.

@since 1.5.0.0
-}
foldr :: (a -> b -> b) -> b -> Queue a -> b
foldr f k = Prelude.foldr f k . toList

instance Show a => Show (Queue a) where
  show = show . toList

{-|
Converts this queue into a list.

@since 1.5.0.0
-}
toList :: Queue a -> [a]
toList q = outs q ++ reverse (ins q)