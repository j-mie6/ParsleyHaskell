{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE DerivingStrategies, ViewPatterns #-}
module Parsley.Internal.Common.Queue.Impl (
    module Parsley.Internal.Common.Queue.Impl
  ) where

import Prelude hiding (null, foldr)
import Data.List (foldl')

import qualified Prelude (foldr)

data Queue a = Queue {
  outsz :: Int,
  outs  :: [a],
  insz  :: Int,
  ins   :: [a]
} deriving stock Eq

empty :: Queue a
empty = Queue 0 [] 0 []

enqueue :: a -> Queue a -> Queue a
enqueue x q = q {insz = insz q + 1, ins = x : ins q}

enqueueAll :: [a] -> Queue a -> Queue a
enqueueAll xs q = q { insz = insz q + length xs, ins = foldl' (flip (:)) (ins q) xs }

dequeue :: Queue a -> (a, Queue a)
dequeue q@(outs -> (x:outs')) = (x, q {outsz = outsz q - 1, outs = outs'})
dequeue q@(outs -> [])
  | insz q /= 0 = dequeue (Queue (insz q) (reverse (ins q)) 0 [])
  | otherwise   = error "dequeue of empty queue"

peek :: Queue a -> (a, Queue a)
peek q =
  let (x, q') = dequeue q
  in (x, q' { outsz = outsz q' + 1, outs = x : outs q' })

modifyHead :: (a -> a) -> Queue a -> Queue a
modifyHead f q =
  let (x, q') = dequeue q
  in q' { outsz = outsz q' + 1, outs = f x : outs q' }

null :: Queue a -> Bool
null (Queue 0 [] 0 []) = True
null _ = False

size :: Queue a -> Int
size q = insz q + outsz q

foldr :: (a -> b -> b) -> b -> Queue a -> b
foldr f k = Prelude.foldr f k . toList

instance Show a => Show (Queue a) where
  show = show . toList

toList :: Queue a -> [a]
toList q = outs q ++ reverse (ins q)