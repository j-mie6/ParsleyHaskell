{-|
Module      : Parsley.Internal.Backend
Description : The backend is concerned with code generation and control flow analysis
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

@since 0.1.0.0
-}
module Parsley.Internal.Backend (
    module Parsley.Internal.Backend.CodeGenerator,
    module Parsley.Internal.Backend.Machine
  ) where

import Parsley.Internal.Backend.CodeGenerator (codeGen)
import Parsley.Internal.Backend.Machine       (Input, eval)