module Parsley.Internal.Backend.Machine (
    Input, Rep, prepare, eval,
    PositionOps,
    module Parsley.Internal.Backend.Machine.Instructions,
    module Parsley.Internal.Backend.Machine.Defunc,
    module Parsley.Internal.Backend.Machine.Identifiers,
    module Parsley.Internal.Backend.Machine.LetBindings
  ) where

import Data.Array.Unboxed                            (UArray)
import Data.ByteString                               (ByteString)
import Data.Text                                     (Text)
import Parsley.Internal.Backend.Machine.Defunc       (Defunc(..))
import Parsley.Internal.Backend.Machine.Eval         (eval)
import Parsley.Internal.Backend.Machine.Identifiers
import Parsley.Internal.Backend.Machine.InputRep     (Rep)
import Parsley.Internal.Backend.Machine.InputOps     (InputPrep(..), PositionOps)
import Parsley.Internal.Backend.Machine.Instructions
import Parsley.Internal.Backend.Machine.LetBindings  (LetBinding, makeLetBinding)
import Parsley.Internal.Backend.Machine.Ops          (Ops)
import Parsley.Internal.Core.InputTypes

import qualified Data.ByteString.Lazy as Lazy (ByteString)

class (InputPrep input, Ops (Rep input)) => Input input
instance Input [Char]
instance Input (UArray Int Char)
instance Input Text16
instance Input ByteString
instance Input CharList
instance Input Text
--instance Input CacheText
instance Input Lazy.ByteString
--instance Input Lazy.ByteString
instance Input Stream