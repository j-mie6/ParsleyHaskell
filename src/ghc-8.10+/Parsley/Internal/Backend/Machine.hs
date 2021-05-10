module Parsley.Internal.Backend.Machine (
    Input, eval,
    PositionOps,
    module Parsley.Internal.Backend.Machine.Instructions,
    module Parsley.Internal.Backend.Machine.Defunc,
    module Parsley.Internal.Backend.Machine.Identifiers,
    module Parsley.Internal.Backend.Machine.LetBindings
  ) where

import Data.Array.Unboxed                            (UArray)
import Data.ByteString                               (ByteString)
import Data.Dependent.Map                            (DMap)
import Data.Text                                     (Text)
import Parsley.Internal.Backend.Machine.Defunc       (Defunc(..))
import Parsley.Internal.Backend.Machine.Identifiers
import Parsley.Internal.Backend.Machine.InputOps     (InputPrep(..), PositionOps)
import Parsley.Internal.Backend.Machine.Instructions
import Parsley.Internal.Backend.Machine.LetBindings  (LetBinding, makeLetBinding)
import Parsley.Internal.Backend.Machine.Ops          (Ops)
import Parsley.Internal.Common.Utils                 (Code)
import Parsley.Internal.Core.InputTypes
import Parsley.Internal.Trace                        (Trace)

import qualified Data.ByteString.Lazy as Lazy (ByteString)
import qualified Parsley.Internal.Backend.Machine.Eval as Eval (eval)

eval :: forall input a. (Input input, Trace) => Code input -> (LetBinding input a a, DMap MVar (LetBinding input a)) -> Code (Maybe a)
eval input (toplevel, bindings) = Eval.eval (prepare input) toplevel bindings

class (InputPrep input, Ops input) => Input input
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