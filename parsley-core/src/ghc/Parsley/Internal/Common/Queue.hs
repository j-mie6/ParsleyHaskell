{-# OPTIONS_GHC -Wno-orphans #-}
{-|
Module      : Parsley.Internal.Common.Queue
Description : Queue operations.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes the instance of `QueueLike` for `Queue`.

@since 1.5.0.0
-}
module Parsley.Internal.Common.Queue (module Queue) where

import Parsley.Internal.Common.Queue.Impl as Queue (
    Queue, empty, enqueue, dequeue, null, size, foldr, enqueueAll
  )
import Parsley.Internal.Common.QueueLike  (QueueLike(empty, null, size, enqueue, dequeue, enqueueAll))

instance QueueLike Queue where
  empty      = Queue.empty
  null       = Queue.null
  size       = Queue.size
  enqueue    = Queue.enqueue
  dequeue    = Queue.dequeue
  enqueueAll = Queue.enqueueAll
