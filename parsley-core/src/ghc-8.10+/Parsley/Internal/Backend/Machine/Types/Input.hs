{-# LANGUAGE UnboxedTuples, MagicHash, RecordWildCards #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Types.Input
Description : Packaging of offsets and positions.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes abstractions for working with combined offset and position information. `Input` is used
for static augmented information, and `Input#` is a raw combination of the two components.

@since 1.8.0.0
-}
module Parsley.Internal.Backend.Machine.Types.Input (module Parsley.Internal.Backend.Machine.Types.Input) where

import Parsley.Internal.Backend.Machine.InputRep                  (Rep)
import Parsley.Internal.Backend.Machine.Types.Input.Offset        (Offset(offset), mkOffset, moveOne, moveN)
import Parsley.Internal.Backend.Machine.Types.Input.Pos           (toDynPos, fromDynPos, contribute, force, update)
import Parsley.Internal.Backend.Machine.Types.InputCharacteristic (InputCharacteristic(..))
import Parsley.Internal.Common.Utils                              (Code)
import Parsley.Internal.Core.CharPred                             (CharPred)

import Parsley.Internal.Backend.Machine.Types.Base as Dyn (Pos)
import Parsley.Internal.Backend.Machine.Types.Input.Pos as Sta (Pos)

{-|
Packages known static information about offsets (via `Offset`) with static information about positions
(currently unavailable).

@since 1.8.0.0
-}
data Input o = Input {
    off  :: Offset o,
    pos :: Sta.Pos
  }

{-|
Packages a dynamic offset with a dynamic position.

@since 1.8.0.0
-}
data Input# o = Input# {
    off#  :: Code (Rep o),
    pos#  :: Code Dyn.Pos
  }

mkInput :: Code (Rep o) -> Code Dyn.Pos -> Input o
mkInput off = toInput 0 . Input# off

consume :: Code Char -> Code (Rep o) -> Input o -> Input o
consume c offset' input = input {
    off = moveOne (off input) offset',
    pos = contribute (pos input) c
  }

forcePos :: Input o -> (Code Dyn.Pos -> Input o -> Code r) -> Code r
forcePos input k = force (pos input) (\dp sp -> k dp (input { pos = sp }))

updatePos :: Input o -> CharPred -> Input o
updatePos input p = input { pos = update (pos input) p }

chooseInput :: InputCharacteristic -> Word -> Input o -> Input# o -> Input o
chooseInput (AlwaysConsumes n) _ inp  inp#  = inp { off = moveN n (off inp) (off# inp#), pos = fromDynPos (pos# inp#) }
-- Technically, in this case, we know the whole input is unchanged. This essentially ignores the continuation arguments
-- hopefully GHC could optimise this better?
chooseInput NeverConsumes      _ inp  _inp# = inp -- { off = (off inp) {offset = off# inp# }, pos = pos# inp# }
chooseInput MayConsume         u _inp inp#  = toInput u inp#

{-|
Strips away static information, returning the raw dynamic components.

@since 1.8.0.0
-}
fromInput :: Input o -> Input# o
fromInput Input{..} = Input# (offset off) (toDynPos pos)

{-|
Given a unique identifier, forms a plainly annotated static combination of position and offset.

@since 1.8.0.0
-}
toInput :: Word -> Input# o -> Input o
toInput u Input#{..} = Input (mkOffset off# u) (fromDynPos pos#)