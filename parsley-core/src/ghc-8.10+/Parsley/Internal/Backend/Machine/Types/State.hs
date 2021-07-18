module Parsley.Internal.Backend.Machine.Types.State (
    Γ(..), OpStack(..),
  ) where

import Parsley.Internal.Backend.Machine.Defunc        (Defunc)
import Parsley.Internal.Backend.Machine.Types.Offset  (Offset)
import Parsley.Internal.Backend.Machine.Types.Statics (StaCont, StaHandler)
import Parsley.Internal.Common.Vec                    (Vec)

data OpStack xs where
  Empty :: OpStack '[]
  Op :: Defunc x -> OpStack xs -> OpStack (x ': xs)

data Γ s o xs n r a = Γ { operands :: OpStack xs
                        , retCont  :: StaCont s o a r
                        , input    :: Offset o
                        , handlers :: Vec n (StaHandler s o a) }