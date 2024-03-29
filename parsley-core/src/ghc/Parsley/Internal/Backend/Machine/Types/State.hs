{-|
Module      : Parsley.Internal.Backend.Machine.Types.State
Description : Partially static components of a parser
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the runtime state of a parser, which is
is partially static, since there are many refinements that can be
used to improve it but ultimately, most of this exists at runtime
in some form or another.

@since 1.4.0.0
-}
module Parsley.Internal.Backend.Machine.Types.State (
    Γ(..), OpStack(..),
  ) where

import Parsley.Internal.Backend.Machine.Defunc        (Defunc)
import Parsley.Internal.Backend.Machine.Types.Input   (Input)
import Parsley.Internal.Backend.Machine.Types.Statics (StaCont, AugmentedStaHandler)
import Parsley.Internal.Common.Vec                    (Vec)

{-|
The stack that represents the applicative arguments to a parser.
These values, when converted to @Code@ will appear in the generated
code, but can be manipulated and combined using this stack, which will
not appear in the generated code.

@since 1.4.0.0
-}
data OpStack xs where
  -- | The empty stack, with no operands available.
  Empty :: OpStack '[]
  -- | A pushed item on the stack, which takes the form of a defunctionalised value.
  Op :: Defunc x -> OpStack xs -> OpStack (x ': xs)

{-|
A record that bundles together all of the runtime components
of a parser in their variously statically augmented forms.

@since 1.4.0.0
-}
data Γ s o xs n r a = Γ { operands :: !(OpStack xs)                        -- ^ The current values available for applicative application.
                        , retCont  :: !(StaCont s o a r)                   -- ^ The current return continuation when this parser is finished.
                        , input    :: !(Input o)                           -- ^ The current offset into the input of the parser.
                        , handlers :: !(Vec n (AugmentedStaHandler s o a)) -- ^ The failure handlers that are used to process failure during a parser.
                        }
