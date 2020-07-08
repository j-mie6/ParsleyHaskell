{-# LANGUAGE GADTs #-}
module Parsley.Backend.Optimiser where

import Parsley.Backend.Machine.Instructions
import Parsley.Common.Indexed
import Data.GADT.Compare (geq, (:~:)(Refl))

-- We'll come back here later ;)
optimise :: Instr o (Fix4 (Instr o)) xs n r a -> Fix4 (Instr o) xs n r a
optimise (Push _ (In4 (Pop m))) = m
optimise (Dup (In4 (Pop m))) = m
optimise (Dup (In4 (Swap m))) = In4 (Dup m)
optimise (Get r1 (In4 (Get r2 m))) | Just Refl <- r1 `geq` r2 = In4 (Get r1 (In4 (Dup m)))
optimise (Put r1 (In4 (Get r2 m))) | Just Refl <- r1 `geq` r2 = In4 (Dup (In4 (Put r1 m)))
optimise (Get r1 (In4 (Put r2 m))) | Just Refl <- r1 `geq` r2 = m