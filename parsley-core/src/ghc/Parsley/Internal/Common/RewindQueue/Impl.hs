{-# LANGUAGE DerivingStrategies, RecordWildCards #-}
module Parsley.Internal.Common.RewindQueue.Impl (module Parsley.Internal.Common.RewindQueue.Impl) where

import Prelude hiding (null, foldr)
import Data.List (foldl')
import Parsley.Internal.Common.Queue.Impl as Queue (Queue(..), toList)

import qualified Parsley.Internal.Common.Queue.Impl as Queue (
    empty, enqueue, enqueueAll, dequeue, null, size, foldr, peek, modifyHead
  )

data RewindQueue a = RewindQueue {
    queue :: Queue a,
    undo :: [a],
    undosz :: Int
  } deriving stock (Eq, Show)

empty :: RewindQueue a
empty = RewindQueue Queue.empty [] 0

enqueue :: a -> RewindQueue a -> RewindQueue a
enqueue x q = q { queue = Queue.enqueue x (queue q) }

enqueueAll :: [a] -> RewindQueue a -> RewindQueue a
enqueueAll xs q = q { queue = Queue.enqueueAll xs (queue q) }

dequeue :: RewindQueue a -> (a, RewindQueue a)
dequeue RewindQueue{..} =
  let (x, queue') = Queue.dequeue queue
  in (x, RewindQueue { queue = queue', undo = x : undo, undosz = undosz + 1 })

rewind :: Int -> RewindQueue a -> RewindQueue a
rewind n RewindQueue{..}
  | n <= undosz = let (rs, undo') = splitAt n undo
                  in RewindQueue { queue = queue { outsz = outsz queue + length rs,
                                                   outs = foldl' (flip (:)) (outs queue) rs },
                                   undo = undo',
                                   undosz = undosz - n }
  | otherwise   = error $ "Cannot rewind more than " ++ show undosz ++ " elements, but tried " ++ show n

peek :: RewindQueue a -> (a, RewindQueue a)
peek rw@RewindQueue{..} =
  let (x, queue') = Queue.peek queue
  in (x, rw { queue = queue' })

modifyHead :: (a -> a) -> RewindQueue a -> RewindQueue a
modifyHead f rw@RewindQueue{..} = rw { queue = Queue.modifyHead f queue }

null :: RewindQueue a -> Bool
null = Queue.null . queue

size :: RewindQueue a -> Int
size = Queue.size . queue

foldr :: (a -> b -> b) -> b -> RewindQueue a -> b
foldr f k = Queue.foldr f k . queue

toList :: RewindQueue a -> [a]
toList = Queue.toList . queue