{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE ViewPatterns,
             DerivingStrategies #-}
module Parsley.Internal.Common.Queue (Queue, empty, enqueue, dequeue, null, size, foldr) where

import Prelude hiding (null, foldr)

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

dequeue :: Queue a -> (a, Queue a)
dequeue q@(outs -> (x:outs')) = (x, q {outsz = outsz q - 1, outs = outs'})
dequeue q@(outs -> [])        = dequeue (Queue (insz q) (reverse (ins q)) 0 [])

null :: Queue a -> Bool
null (Queue 0 [] 0 []) = True
null _ = False

size :: Queue a -> Int
size q = insz q + outsz q

toList :: Queue a -> [a]
toList q = outs q ++ reverse (ins q)

foldr :: (a -> b -> b) -> b -> Queue a -> b
foldr f k = Prelude.foldr f k . toList

instance Show a => Show (Queue a) where
  show = show . toList
