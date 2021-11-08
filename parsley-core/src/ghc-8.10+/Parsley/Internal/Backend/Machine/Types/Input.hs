module Parsley.Internal.Backend.Machine.Types.Input (module Parsley.Internal.Backend.Machine.Types.Input) where

import Parsley.Internal.Backend.Machine.Types.Base         (Pos)
import Parsley.Internal.Backend.Machine.Types.Input.Offset (Offset)
import Parsley.Internal.Backend.Machine.Types.Input.Pos    ()
import Parsley.Internal.Common.Utils                       (Code)

data Input o = Input {
    off  :: Offset o,
    pos :: Code Pos
  }