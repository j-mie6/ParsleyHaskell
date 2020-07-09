module Parsley.Core (
    Parser,
    module Primitives,
    module Parsley.Core.Defunc,
    module Parsley.Core.InputTypes
  ) where

import Parsley.Core.Defunc hiding (genDefunc, genDefunc1, genDefunc2)
import Parsley.Core.Primitives    (Parser)
import Parsley.Core.InputTypes

import Parsley.Core.Primitives as Primitives hiding (Parser(..), unParser)