{-# OPTIONS_GHC -Wno-orphans #-}
module Parsley.Internal.Common.RewindQueue (module RewindQueue) where

import Parsley.Internal.Common.RewindQueue.Impl as RewindQueue (
    RewindQueue, empty, enqueue, dequeue, rewind, null, size, foldr, enqueueAll, peek, modifyHead
  )
import Parsley.Internal.Common.QueueLike  (QueueLike(empty, null, size, enqueue, dequeue, enqueueAll, peek, modifyHead))

instance QueueLike RewindQueue where
  empty      = RewindQueue.empty
  null       = RewindQueue.null
  size       = RewindQueue.size
  enqueue    = RewindQueue.enqueue
  dequeue    = RewindQueue.dequeue
  enqueueAll = RewindQueue.enqueueAll
  peek       = RewindQueue.peek
  modifyHead = RewindQueue.modifyHead
