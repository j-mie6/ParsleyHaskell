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
    module Parsley.Internal.Core.Defunc,
    module Parsley.Internal.Core.InputTypes
  ) where

import Parsley.Internal.Core.Defunc hiding (lamTerm)
import Parsley.Internal.Core.InputTypes
import Parsley.Internal.Core.Primitives (Parser)