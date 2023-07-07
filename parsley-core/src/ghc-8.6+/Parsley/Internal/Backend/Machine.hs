{-# LANGUAGE ImplicitParams, PatternSynonyms #-}
{-# OPTIONS_GHC -Wno-deprecations #-} --FIXME: remove when Text16 is removed
{-|
Module      : Parsley.Internal.Backend.Machine
Description : The implementation of the low level parsing machinery is found here
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : unstable

@since 0.1.0.0
-}
module Parsley.Internal.Backend.Machine (
    Input, eval,
    module Parsley.Internal.Backend.Machine.Types.Coins,
    module Parsley.Internal.Backend.Machine.Instructions,
    module Parsley.Internal.Backend.Machine.Defunc,
    module Parsley.Internal.Backend.Machine.Identifiers,
    module Parsley.Internal.Backend.Machine.LetBindings
  ) where

import Data.Array.Unboxed                            (UArray)
import Data.ByteString                               (ByteString)
import Data.Dependent.Map                            (DMap)
import Data.Text                                     (Text)
import Parsley.Internal.Backend.Machine.Defunc       (user)
import Parsley.Internal.Backend.Machine.Identifiers
import Parsley.Internal.Backend.Machine.InputOps     (InputPrep(..))
import Parsley.Internal.Backend.Machine.InputRep     (Rep)
import Parsley.Internal.Backend.Machine.Instructions
import Parsley.Internal.Backend.Machine.LetBindings  (LetBinding, makeLetBinding, newMeta)
import Parsley.Internal.Backend.Machine.Ops          (Ops)
import Parsley.Internal.Backend.Machine.Types.Coins  (Coins(..), minCoins, plus1, minus, pattern Zero, items)
import Parsley.Internal.Common.Utils                 (Code)
import Parsley.Internal.Core.InputTypes
import Parsley.Internal.Trace                        (Trace)

import qualified Data.ByteString.Lazy as Lazy (ByteString)
import qualified Parsley.Internal.Backend.Machine.Eval as Eval (eval)
import qualified Parsley.Internal.Opt   as Opt

eval :: forall input a. (Input input, Trace, ?flags :: Opt.Flags) => Code input -> (LetBinding (Rep input) a a, DMap MVar (LetBinding (Rep input) a)) -> Code (Maybe a)
eval input (toplevel, bindings) = Eval.eval (prepare input) toplevel bindings

class (InputPrep input, Ops (Rep input)) => Input input
instance Input String
instance Input (UArray Int Char)
instance Input Text16
instance Input ByteString
instance Input CharList
instance Input Text
instance Input Lazy.ByteString
instance Input Stream
