module Parsley.Internal.Backend.Machine.Offset (module Parsley.Internal.Backend.Machine.Offset) where

import Parsley.Internal.Backend.Machine.InputRep    (Rep)
import Parsley.Internal.Common                      (Code)

data Offset o = Offset {
    offset :: Code (Rep o),
    unique :: Word,
    moved  :: Word
  }
instance Eq (Offset o) where o1 == o2 = unique o1 == unique o2 && moved o1 == moved o2

moveOne :: Offset o -> Code (Rep o) -> Offset o
moveOne off o = off { offset = o, moved = moved off + 1 }

mkOffset :: Code (Rep o) -> Word -> Offset o
mkOffset offset unique = Offset offset unique 0