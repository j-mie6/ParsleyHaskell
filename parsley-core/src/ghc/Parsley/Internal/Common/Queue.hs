{-# OPTIONS_GHC -Wno-orphans #-}
module Parsley.Internal.Common.Queue (module Queue) where

import Parsley.Internal.Common.Queue.Impl as Queue (
    Queue, empty, enqueue, dequeue, null, size, foldr, enqueueAll, peek, modifyHead
  )
import Parsley.Internal.Common.QueueLike  (QueueLike(empty, null, size, enqueue, dequeue, enqueueAll, peek, modifyHead))

instance QueueLike Queue where
  empty      = Queue.empty
  null       = Queue.null
  size       = Queue.size
  enqueue    = Queue.enqueue
  dequeue    = Queue.dequeue
  enqueueAll = Queue.enqueueAll
  peek       = Queue.peek
  modifyHead = Queue.modifyHead
