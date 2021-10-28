{-# LANGUAGE CPP #-}
{-|
Module      : Parsley.Internal.Core
Description : The main AST and datatypes are found here
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : unstable

@since 0.1.0.0
-}
module Parsley.Internal.Core (
    Parser,
#if MIN_VERSION_parsley_core(2,0,0)
#else
    ParserOps,
#endif
    module Parsley.Internal.Core.Defunc,
    module Parsley.Internal.Core.InputTypes
  ) where

import Parsley.Internal.Core.Defunc hiding (lamTerm, lamTermBool)
import Parsley.Internal.Core.InputTypes
#if MIN_VERSION_parsley_core(2,0,0)
import Parsley.Internal.Core.Primitives (Parser)
#else
import Parsley.Internal.Core.Primitives (Parser, ParserOps)
#endif
