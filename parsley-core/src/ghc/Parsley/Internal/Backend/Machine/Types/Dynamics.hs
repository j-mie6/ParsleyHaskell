{-# LANGUAGE MagicHash #-}
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

import Parsley.Internal.Backend.Machine.Types.Base (Handler#, Cont#, Subroutine#, Func, RegisterStack#)
import Parsley.Internal.Common.Utils               (Code)

{-|
Template Haskell representation of `Parsley.Internal.Backend.Machine.Types.Base.RegisterStack#`
-}
type DynRegisterStack rs x = Code (RegisterStack# rs x)

{-|
Template Haskell representation of `Parsley.Internal.Backend.Machine.Types.Base.Handler#`

@since 1.4.0.0
-}
type DynHandler hs s o a = Code (Handler# hs s o a)


{-|
Template Haskell representation of `Parsley.Internal.Backend.Machine.Types.Base.Cont#`

@since 1.4.0.0
-}
type DynCont xs s o a x = Code (Cont# xs s o a x)

{-|
Template Haskell representation of `Parsley.Internal.Backend.Machine.Types.Base.Subroutine#`

@since 1.4.0.0
-}
type DynSubroutine xs hs ys s o a x = Code (Subroutine# xs hs ys s o a x)

{-|
Template Haskell representation of `Parsley.Internal.Backend.Machine.Types.Base.Func#`

@since 1.4.0.0
-}
type DynFunc rs hs ys s o a x = Code (Func rs hs ys s o a x)
