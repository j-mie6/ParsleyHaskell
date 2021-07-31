module Parsley.Internal.Common.QueueLike (module Parsley.Internal.Common.QueueLike) where

class QueueLike q where
  empty      :: q a
  null       :: q a -> Bool
  size       :: q a -> Int
  enqueue    :: a -> q a -> q a
  dequeue    :: q a -> (a, q a)
  enqueueAll :: [a] -> q a -> q a
  peek       :: q a -> (a, q a)
  modifyHead :: (a -> a) -> q a -> q a
