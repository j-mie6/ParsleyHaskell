{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-|
Module      : Parsley.Internal.Verbose
Description : Contains instance that enables verbose debugging output for Parsley compiler
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains a single orphan instance that enables debugging output on the Parsley compiler.
This output is not useful for the user, but may potentially serve as useful additional information
when submitting a bug report.

@since 0.1.0.0
-}

module Parsley.Internal.Verbose () where

import Parsley.Internal.Trace (Trace(trace))
import qualified Debug.Trace (trace)

{-|
This instance, when in scope, will enable additional debug output from the Parsley compilation
process. It will always superscede the default instance defined in "Parsley".

@since 0.1.0.0
-}
instance Trace where
  trace = Debug.Trace.trace