{-# LANGUAGE DerivingStrategies, RecordWildCards #-}
{-|
Module      : Parsley.Internal.Common.Queue.Impl
Description : Implementation of a queue which can be rewound.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Implementation of a FIFO queue structure, with amortized operations that also supports a rewinding
operation backed by a LIFO stack.

@since 1.5.0.0
-}
module Parsley.Internal.Common.RewindQueue.Impl (module Parsley.Internal.Common.RewindQueue.Impl) where

import Prelude hiding (null, foldr)
import Data.List (foldl')
import Parsley.Internal.Common.Queue.Impl as Queue (Queue(..), toList)

import qualified Parsley.Internal.Common.Queue.Impl as Queue (
    empty, enqueue, enqueueAll, dequeue, null, size, foldr
  )

{-|
Concrete FIFO Queue, with amortized constant operations.

Also keeps history of dequeued values, which can be undone
in a LIFO manner.

@since 1.5.0.0
-}
data RewindQueue a = RewindQueue {
    queue :: Queue a,
    undo :: [a],
    undosz :: Int
  } deriving stock (Eq, Show)

{-|
Construct an empty queue.

@since 1.5.0.0
-}
empty :: RewindQueue a
empty = RewindQueue Queue.empty [] 0

{-|
Adds an element onto the end of the queue.

@since 1.5.0.0
-}
enqueue :: a -> RewindQueue a -> RewindQueue a
enqueue x q = q { queue = Queue.enqueue x (queue q) }

{-|
Adds each of the elements onto the queue, from left-to-right.

@since 1.5.0.0
-}
enqueueAll :: [a] -> RewindQueue a -> RewindQueue a
enqueueAll xs q = q { queue = Queue.enqueueAll xs (queue q) }

{-|
Removes an element from the front of the queue.

@since 1.5.0.0
-}
dequeue :: RewindQueue a -> (a, RewindQueue a)
dequeue RewindQueue{..} =
  let (x, queue') = Queue.dequeue queue
  in (x, RewindQueue { queue = queue', undo = x : undo, undosz = undosz + 1 })

{-|
Undoes the last \(n\) `dequeue` operations but /only/ if there are that many
available undos. Otherwise, it will throw an error.

@since 1.5.0.0
-}
rewind :: Int -> RewindQueue a -> RewindQueue a
rewind n RewindQueue{..}
  | n <= undosz = let (rs, undo') = splitAt n undo
                  in RewindQueue { queue = queue { outsz = outsz queue + length rs,
                                                   outs = foldl' (flip (:)) (outs queue) rs },
                                   undo = undo',
                                   undosz = undosz - n }
  | otherwise   = error $ "Cannot rewind more than " ++ show undosz ++ " elements, but tried " ++ show n

{-|
Is the queue empty?

@since 1.5.0.0
-}
null :: RewindQueue a -> Bool
null = Queue.null . queue

{-|
Returns how many elements are in the queue.

@since 1.5.0.0
-}
size :: RewindQueue a -> Int
size = Queue.size . queue

{-|
Folds the values in the queue. Undo history is not included.

@since 1.5.0.0
-}
foldr :: (a -> b -> b) -> b -> RewindQueue a -> b
foldr f k = Queue.foldr f k . queue

{-|
Converts this queue into a list. Undo history is discarded.

@since 1.5.0.0
-}
toList :: RewindQueue a -> [a]
toList = Queue.toList . queue