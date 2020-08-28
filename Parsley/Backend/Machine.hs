module Parsley.Backend.Machine (
    Input, Item, prepare, eval,
    PositionOps,
    module Parsley.Backend.Machine.Instructions,
    module Parsley.Backend.Machine.Defunc,
    module Parsley.Backend.Machine.Identifiers,
    module Parsley.Backend.Machine.LetBindings
  ) where

import Data.Array.Unboxed                   (UArray)
import Data.ByteString                      (ByteString)
import Data.Text                            (Text)
import Parsley.Backend.Machine.Defunc       (Defunc(..))
import Parsley.Backend.Machine.Eval         (eval)
import Parsley.Backend.Machine.Identifiers
import Parsley.Backend.Machine.InputRep     (Rep, Item)
import Parsley.Backend.Machine.InputOps     (InputPrep(..), PositionOps)
import Parsley.Backend.Machine.Instructions
import Parsley.Backend.Machine.LetBindings  (LetBinding, makeLetBinding)
import Parsley.Backend.Machine.Ops          (Ops)
import Parsley.Core.InputTypes

import qualified Data.ByteString.Lazy as Lazy (ByteString)

class (InputPrep input, Ops (Rep input)) => Input input
instance Input [Char]
instance Input (UArray Int Char)
instance Input Text16
instance Input ByteString
instance Input (TokList t)
instance Input Text
--instance Input CacheText
instance Input Lazy.ByteString
--instance Input Lazy.ByteString
instance Input Stream