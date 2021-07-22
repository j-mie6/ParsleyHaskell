{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Parsley.Internal.Backend.Machine.LetBindings
Description : Let-binding and free registers.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Definitions for various encapsulating datatypes for machines, and defining
free registers.

@since 1.0.0.0
-}
module Parsley.Internal.Backend.Machine.LetBindings (
    LetBinding(..),
    Regs(..),
    makeLetBinding,
    Binding
  ) where

import Prelude hiding                                (foldr)
import Data.Kind                                     (Type)
import Data.Set                                      (Set, foldr)
import Data.Some                                     (Some, pattern Some)
import Parsley.Internal.Backend.Machine.Identifiers  (ΣVar, SomeΣVar(..))
import Parsley.Internal.Backend.Machine.Instructions (Instr)
import Parsley.Internal.Common                       (Fix4, One)

{-|
Type represents a binding, which is a completed parser that can
be refered to by other parsers. This is characterised by requiring
no initial stack and exactly one handler. The top-level binding is
the one of type @`Binding` o a a@.

@since 1.0.0.0
-}
type Binding o a x = Fix4 (Instr o) '[] One x a

{-|
Packages a binding along with its free registers that are required
for it, which are left existential. This is possible since the `Regs`
datatype serves as a singleton-style witness of the original registers
and their types.

@since 1.4.0.0
-}
data LetBinding o a x = LetBinding (Binding o a x) (Some Regs)

{-|
Given a `Binding` and a set of existential `ΣVar`s, produces a
`LetBinding` instance.

@since 1.4.0.0
-}
makeLetBinding :: Binding o a x -> Set SomeΣVar -> LetBinding o a x
makeLetBinding m rs = LetBinding m (makeRegs rs)

{-|
Represents a collection of free registers, preserving their type
information as a heterogeneous list.

@since 1.0.0.0
-}
data Regs (rs :: [Type]) where
  NoRegs :: Regs '[]
  FreeReg :: ΣVar r -> Regs rs -> Regs (r : rs)

{-|
Converts a set of existential `ΣVar`s into an existential
heterogeneous list of free registers.

@since 1.4.0.0
-}
makeRegs :: Set SomeΣVar -> Some Regs
makeRegs = foldr (\(SomeΣVar σ) (Some rs) -> Some (FreeReg σ rs)) (Some NoRegs)