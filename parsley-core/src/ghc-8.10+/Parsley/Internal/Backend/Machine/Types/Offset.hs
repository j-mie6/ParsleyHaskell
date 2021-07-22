{-|
Module      : Parsley.Internal.Backend.Machine.Types.Offset
Description : Statically refined offsets.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the statically refined `Offset` type,
which can be used to reason about input in different parts of
a parser as it is evaluated.

@since 1.4.0.0
-}
module Parsley.Internal.Backend.Machine.Types.Offset (module Parsley.Internal.Backend.Machine.Types.Offset) where

import Parsley.Internal.Backend.Machine.InputRep    (Rep)
import Parsley.Internal.Common.Utils                (Code)

{-|
Augments a regular @'Code' ('Rep' o)@ with information about its origins and
how much input is known to have been consumed since it came into existence.
This can be used to statically evaluate handlers (see 
`Parsley.Internal.Backend.Machine.Types.Statics.staHandlerEval`).

@since 1.4.0.0
-}
data Offset o = Offset {
    -- | The underlying code that represents the current offset into the input.
    offset :: Code (Rep o),
    -- | The unique identifier that determines where this offset originated from.
    unique :: Word,
    -- | The amount of input that has been consumed on this offset since it was born.
    moved  :: Word
  }
instance Show (Offset o) where show o = show (unique o) ++ "+" ++ show (moved o)

{-|
Given two `Offset`s, this determines whether or not they represent the same
offset into the input stream at runtime. This comparison only makes sense when
both `Offset`s share the same origin, hence the @Maybe@.

@since 1.4.0.0
-}
same :: Offset o -> Offset o -> Maybe Bool
same o1 o2
  | unique o1 == unique o2 = Just (moved o1 == moved o2)
  | otherwise = Nothing

{-|
Updates an `Offset` with its new underlying representation of a real
runtime offset and records that another character has been consumed.

@since 1.4.0.0
-}
moveOne :: Offset o -> Code (Rep o) -> Offset o
moveOne off o = off { offset = o, moved = moved off + 1 }

{-|
Makes a fresh `Offset` that has not had any input consumed off of it
yet.

@since 1.4.0.0
-}
mkOffset :: Code (Rep o) -> Word -> Offset o
mkOffset offset unique = Offset offset unique 0