{-|
Module      : Parsley.InputExtras
Description : Extra datatypes that can be used to wrap input
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module exports the `Stream` datatype, which can be used as an infinite input to a
parser. It also exports `Text16` and `CharList`, which can be wrapped around
@Text@ and @String@ respectively to force them to be parsed faithfully to their
representation. By default, @String@s are converted to character arrays for performance,
but `CharList` will be uncoverted. On the other hand, `Text16` enables a faster, but
potentially less general processing of @Text@ data by assuming all characters
are exactly 16-bits in width.

@since 0.1.0.0
-}
module Parsley.InputExtras (
    module Parsley.Internal
  ) where

import Parsley.Internal (Text16(..), CharList(..), Stream(..), nomore)