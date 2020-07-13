{-# LANGUAGE GADTs #-}
module Parsley.Backend.Optimiser where

import Data.GADT.Compare                    (geq, (:~:)(Refl))
import Parsley.Backend.Machine
import Parsley.Common.Indexed

-- We'll come back here later ;)
optimise :: Instr o (Fix4 (Instr o)) xs n r a -> Fix4 (Instr o) xs n r a
optimise (Push _ (In4 (Pop m))) = m
optimise (Dup (In4 (Pop m))) = m
optimise (Dup (In4 (Swap m))) = In4 (Dup m)
optimise (Get r1 a (In4 (Get r2 _ m))) | Just Refl <- r1 `geq` r2 = In4 (Get r1 a (In4 (Dup m)))
optimise (Put r1 a (In4 (Get r2 _ m))) | Just Refl <- r1 `geq` r2 = In4 (Dup (In4 (Put r1 a m)))
optimise (Get r1 _ (In4 (Put r2 _ m))) | Just Refl <- r1 `geq` r2 = m