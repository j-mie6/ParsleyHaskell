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
    LetBinding(..), Metadata,
    Regs(..),
    makeLetBinding, newMeta,
    successInputCharacteristic, failureInputCharacteristic,
    Binding
  ) where

import Prelude hiding                                             (foldr)
import Data.Kind                                                  (Type)
import Data.Set                                                   (Set, foldr)
import Data.Some                                                  (Some, pattern Some)
import Parsley.Internal.Backend.Machine.Identifiers               (ΣVar, SomeΣVar(..))
import Parsley.Internal.Backend.Machine.Instructions              (Instr)
import Parsley.Internal.Backend.Machine.Types.InputCharacteristic (InputCharacteristic(..))
import Parsley.Internal.Common                                    (Fix3, One)

{-|
Type represents a binding, which is a completed parser that can
be refered to by other parsers. This is characterised by requiring
no initial stack and exactly one handler. The top-level binding is
the one of type @`Binding` o a a@.

@since 1.0.0.0
-}
type Binding o x = Fix3 (Instr o) '[] One x

{-|
Packages a binding along with its free registers that are required
for it, which are left existential. This is possible since the `Regs`
datatype serves as a singleton-style witness of the original registers
and their types. It also requires `Metadata` to be provided, sourced
from analysis.

@since 1.5.0.0
-}
data LetBinding o x = LetBinding {
    body :: Binding o x,
    freeRegs :: Some Regs,
    meta :: Metadata
  }

{- |
This is used to store useful static information that can be
used to guide code generation.

See `successInputCharacteristic`, and `failureInputCharacteristic`.

@since 1.5.0.0
-}
data Metadata = Metadata {
    {- |
    Characterises the way that a binding consumes input on success.

    @since 1.5.0.0
    -}
    successInputCharacteristic :: InputCharacteristic,
    {- |
    Characterises the way that a binding consumes input on failure.

    @since 1.5.0.0
    -}
    failureInputCharacteristic :: InputCharacteristic
  }

{-|
Given a `Binding` , a set of existential `ΣVar`s, and some `Metadata`, produces a
`LetBinding` instance.

@since 1.5.0.0
-}
makeLetBinding :: Binding o x -> Set SomeΣVar -> Metadata -> LetBinding o x
makeLetBinding m rs = LetBinding m (makeRegs rs)

{-|
Produces a new `Metadata` object, with fields initialised to sensible conservative
defaults.

@since 1.5.0.0
-}
newMeta :: Metadata
newMeta = Metadata {
    successInputCharacteristic = MayConsume,
    failureInputCharacteristic = MayConsume
  }

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
