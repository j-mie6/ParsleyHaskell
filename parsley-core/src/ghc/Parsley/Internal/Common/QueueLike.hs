{-|
Module      : Parsley.Internal.Common.QueueLike
Description : Operations to work with Queue-like things.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes the core shared operations of queue implementations.

@since 1.5.0.0
-}
module Parsley.Internal.Common.QueueLike (module Parsley.Internal.Common.QueueLike) where

{-|
Operations on a queue-like structure @q@. These operations should be
efficient, with amortized constant complexity for all of them except `enqueueAll`.

@since 1.5.0.0
-}
class QueueLike q where
  {-|
  Construct an empty queue.

  @since 1.5.0.0
  -}
  empty      :: q a
  {-|
  Is the queue empty?

  @since 1.5.0.0
  -}
  null       :: q a -> Bool
  {-|
  Returns how many elements are in the queue.

  @since 1.5.0.0
  -}
  size       :: q a -> Int
  {-|
  Adds an element onto the end of the queue.

  @since 1.5.0.0
  -}
  enqueue    :: a -> q a -> q a
  {-|
  Removes an element from the front of the queue.

  @since 1.5.0.0
  -}
  dequeue    :: q a -> (a, q a)
  {-|
  Adds each of the elements onto the queue, from left-to-right.

  @since 1.5.0.0
  -}
  enqueueAll :: [a] -> q a -> q a