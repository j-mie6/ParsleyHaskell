{-# LANGUAGE MultiParamTypeClasses #-}
{-|
Module      : Parsley.Internal.Trace
Description : Definition of `Trace` class for debugging internals
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains the defintion of the `Trace` class, used to print additional debug information
from the internals.

@since 0.1.0.0
-}
module Parsley.Internal.Trace (Trace, trace, traceShow) where

{-|
Used to produce debug output within parsley.

@since 0.1.0.0
-}
class Trace where
  -- | Print a string to the console.
  trace :: String -> a -> a

-- | Print a value to the console.
traceShow :: (Trace, Show a) => a -> a
traceShow = show >>= trace
