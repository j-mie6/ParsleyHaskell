{-# LANGUAGE ViewPatterns #-}
module Queue (Queue, empty, enqueue, dequeue, null) where
import Prelude hiding (null)

data Queue a = Queue {
  outsz :: Int,
  outs  :: [a],
  insz  :: Int,
  ins   :: [a]
} deriving Eq

empty :: Queue a
empty = Queue 0 [] 0 []

enqueue :: a -> Queue a -> Queue a
enqueue x q = q {insz = insz q + 1, ins = x : ins q}

dequeue :: Queue a -> (a, Queue a)
dequeue q@(outs -> (x:outs')) = (x, q {outsz = outsz q - 1, outs = outs'})
dequeue q@(outs -> []) = dequeue (Queue (insz q) (reverse (ins q)) 0 [])

null :: Queue a -> Bool
null (Queue 0 [] 0 []) = True
null _ = False

size :: Queue a -> Int
size q = insz q + outsz q

instance Show a => Show (Queue a) where
  show q = show (outs q ++ reverse (ins q))
