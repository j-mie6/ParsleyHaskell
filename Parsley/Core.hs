{-# LANGUAGE UndecidableInstances #-}
module Parsley.Core (
    Parser,
    ParserOps,
    Token,
    module Parsley.Core.Defunc,
    module Parsley.Core.InputTypes
  ) where

import Parsley.Common          (Lift)
import Parsley.Core.Defunc     hiding (genDefunc, genDefunc1, genDefunc2)
import Parsley.Core.InputTypes
import Parsley.Core.Primitives (Parser, ParserOps)
import GHC.TypeLits            (TypeError, ErrorMessage(Text))

class (Show t, Lift t, Eq t) => Token t

instance Token Char
instance {-# INCOHERENT #-} (Show t, Lift t, Eq t, TypeError (Text "Token types must have a `Token` instance and must not be polymorphic")) => Token t