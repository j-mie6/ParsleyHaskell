{-# LANGUAGE MagicHash, UnboxedTuples #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Types.Dynamics
Description : Representation of components that cross function boundaries
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the types that represent information that crosses
a function boundary.

@since 1.4.0.0
-}
module Parsley.Internal.Backend.Machine.Types.Dynamics (
    module Parsley.Internal.Backend.Machine.Types.Dynamics
  ) where

import Data.Kind                                   (Type)
import Parsley.Internal.Backend.Machine.Types.Base (Handler#, Cont#, Subroutine#, Func)
import Parsley.Internal.Common.Utils               (Code)

{-|
Template Haskell representation of `Parsley.Internal.Backend.Machine.Types.Base.Handler#`

@since 1.4.0.0
-}
type DynHandler s o err a = Code (Handler# s o err a)

{-|
Template Haskell representation of `Parsley.Internal.Backend.Machine.Types.Base.Cont#`

@since 1.4.0.0
-}
type DynCont s o err a x = Code (Cont# s o err a x)

{-|
Template Haskell representation of `Parsley.Internal.Backend.Machine.Types.Base.Subroutine#`

@since 1.4.0.0
-}
type DynSubroutine s o err a x = Code (Subroutine# s o err a x)

{-|
Template Haskell representation of `Parsley.Internal.Backend.Machine.Types.Base.Func#`

@since 1.4.0.0
-}
type DynFunc (rs :: [Type]) s o err a x = Code (Func rs s o err a x)
