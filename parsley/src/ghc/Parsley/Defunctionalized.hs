{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Parsley.Defunctionalized
Description : Defunctionalised operators usable in place of plain Haskell equivalents
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module exports the `Defunc` type and associated patterns. These are by no means required
to use Parsley, however they can serve as useful shortcuts to their regular Haskell equivalents.
As they are in datatype form, they are inspectable by the internal Parsley machinery, which may
improve optimisation opportunities or code generation.

@since 0.1.0.0
-}
module Parsley.Defunctionalized (
    Defunc(..),
    pattern UNIT,
    pattern FLIP_CONST,
    pattern FLIP_H,
    pattern COMPOSE_H
  ) where

import Parsley.Internal (Defunc(..), pattern UNIT, pattern FLIP_CONST, pattern FLIP_H, pattern COMPOSE_H)