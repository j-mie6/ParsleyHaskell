{-# LANGUAGE DerivingStrategies, UnboxedTuples #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Types.Input.Offset
Description : Statically refined offsets.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the statically refined `Offset` type,
which can be used to reason about input in different parts of
a parser as it is evaluated.

@since 1.8.0.0
-}
module Parsley.Internal.Backend.Machine.Types.Input.Offset (
    Offset, mkOffset, offset, moveOne, moveN, same,
  ) where

import Parsley.Internal.Backend.Machine.InputRep   (Rep)
import Parsley.Internal.Common.Utils               (Code)

{-|
Augments a regular @'Code' ('Rep' o)@ with information about its origins and
how much input is known to have been consumed since it came into existence.
This can be used to statically evaluate handlers (see
`Parsley.Internal.Backend.Machine.Types.Statics.staHandlerEval`).

@since 1.5.0.0
-}
data Offset o = Offset {
    -- | The underlying code that represents the current offset into the input.
    offset :: Code (Rep o),
    -- | The unique identifier that determines where this offset originated from.
    unique :: Word,
    -- | The amount of input that has been consumed on this offset since it was born.
    moved  :: Amount
  }

data Amount = Amount Word {- ^ The multiplicity. -} Word {- ^ The additive offset. -}
  deriving stock Eq

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
moveOne = moveN (Just 1)

{-|
Updates an `Offset` with its new underlying representation of a real
runtime offset and records that several more characters have been consumed.
Here, `Nothing` represents an unknown but non-zero amount of characters.

@since 1.5.0.0
-}
moveN :: Maybe Word -> Offset o -> Code (Rep o) -> Offset o
moveN n off o = off { offset = o, moved = moved off `add` toAmount n }
  where
    toAmount :: Maybe Word -> Amount
    toAmount Nothing = Amount 1 0
    toAmount (Just n) = Amount 0 n

{-|
Makes a fresh `Offset` that has not had any input consumed off of it
yet.

@since 1.4.0.0
-}
mkOffset :: Code (Rep o) -> Word -> Offset o
mkOffset offset unique = Offset offset unique (Amount 0 0)

add :: Amount -> Amount -> Amount
add a1@(Amount n i) a2@(Amount m j)
  -- If the multiplicites don't match then this is _even_ more unknowable
  | n /= m, n /= 0, m /= 0 = Amount (n + m) 0
  -- This is a funny case, it shouldn't happen and it's not really clear what happens if it does
  | n /= 0, m /= 0         = error ("adding " ++ show a1 ++ " and " ++ show a2 ++ " makes no sense?")
  -- If one of the multiplicites is 0 then the offset can be added
  | otherwise              = Amount (max n m) (i + j)

-- Instances
instance Show (Offset o) where
  show o = show (unique o) ++ "+" ++ show (moved o)

instance Show Amount where
  show (Amount n m) = show n ++ "*n+" ++ show m