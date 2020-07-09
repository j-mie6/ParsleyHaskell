{-# LANGUAGE FlexibleContexts,
             FlexibleInstances #-}
module Parsley.Backend.Machine (
    Input, prepare, eval,
    PositionOps,
    Text16(..), CharList(..),
    module Parsley.Backend.Machine.Instructions
  ) where

import Parsley.Backend.Machine.Instructions
import Parsley.Backend.Machine.Eval (eval)
import Parsley.Backend.Machine.InputRep (Rep)
import Parsley.Backend.Machine.InputOps (InputPrep(..), PositionOps)
import Parsley.Common.InputTypes
import Parsley.Backend.Machine.Ops (Ops)
import Data.Text (Text)
import Data.Array.Unboxed (UArray)
import Data.ByteString (ByteString)
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