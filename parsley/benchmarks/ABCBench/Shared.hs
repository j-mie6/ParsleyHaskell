module ABCBench.Shared where

import Data.Monoid


toCayley :: Monoid m => m -> Endo m
toCayley x = Endo (x <>)

fromCayley :: Monoid m => Endo m -> m 
fromCayley (Endo cx) = cx mempty

type Diff a = Endo [a] 

diffSnoc :: a -> Diff a -> Diff a
diffSnoc x dxs = dxs <> Endo (x:)