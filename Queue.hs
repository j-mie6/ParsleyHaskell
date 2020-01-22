module Queue (Queue, empty, enqueue, dequeue, null) where
import Prelude hiding (null)

data Queue a = Queue {
  outsz :: Int,
  outs  :: [a],
  insz  :: Int,
  ins   :: [a]
}

empty :: Queue a
empty = Queue 0 [] 0 []

enqueue :: a -> Queue a -> Queue a
enqueue = undefined

dequeue :: Queue a -> (a, Queue a)
dequeue = undefined

null :: Queue a -> Bool
null (Queue 0 [] 0 []) = True
null _ = False
