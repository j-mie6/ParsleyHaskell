{-|
Module      : Parsley.Debug
Description : Debug combinators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains debugging combinators.

@since 2.0.0.0
-}
module Parsley.Debug (debug) where

import Parsley.Internal (Parser)

import qualified Parsley.Internal as Internal (debug)

{-|
This combinator can be used to debug parsers that have gone wrong. Simply
wrap a parser with @debug name@ and when that parser is executed it will
print a debug trace on entry and exit along with the current context of the
input.

@since 0.1.0.0
-}
debug :: String   -- ^ The name that identifies the wrapped parser in the debug trace
      -> Parser a -- ^ The parser to track during execution
      -> Parser a
debug = Internal.debug
