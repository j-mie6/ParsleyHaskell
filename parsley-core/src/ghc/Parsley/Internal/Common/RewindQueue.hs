{-# OPTIONS_GHC -Wno-orphans #-}
{-|
Module      : Parsley.Internal.Common.RewindQueue
Description : RewindQueue operations.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes the instance of `QueueLike` for `RewindQueue`.

@since 1.5.0.0
-}
module Parsley.Internal.Common.RewindQueue (module RewindQueue) where

import Parsley.Internal.Common.RewindQueue.Impl as RewindQueue (
    RewindQueue, empty, enqueue, dequeue, rewind, null, size, foldr, enqueueAll, poke
  )
import Parsley.Internal.Common.QueueLike  (QueueLike(empty, null, size, enqueue, dequeue, enqueueAll, poke))

instance QueueLike RewindQueue where
  empty      = RewindQueue.empty
  null       = RewindQueue.null
  size       = RewindQueue.size
  enqueue    = RewindQueue.enqueue
  dequeue    = RewindQueue.dequeue
  enqueueAll = RewindQueue.enqueueAll
  poke       = RewindQueue.poke
