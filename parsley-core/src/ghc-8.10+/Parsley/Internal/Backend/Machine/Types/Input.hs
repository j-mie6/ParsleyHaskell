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

import Parsley.Internal.Backend.Machine.InputRep           (Rep)
import Parsley.Internal.Backend.Machine.Types.Base         (Pos)
import Parsley.Internal.Backend.Machine.Types.Input.Offset (Offset(offset), mkOffset)
--import Parsley.Internal.Backend.Machine.Types.Input.Pos    ()
import Parsley.Internal.Common.Utils                       (Code)

{-|
Packages known static information about offsets (via `Offset`) with static information about positions
(currently unavailable).

@since 1.8.0.0
-}
data Input o = Input {
    off  :: Offset o,
    pos :: Code Pos
  }

{-|
Packages a dynamic offset with a dynamic position.

@since 1.8.0.0
-}
data Input# o = Input# {
    off#  :: Code (Rep o),
    pos#  :: Code Pos
  }

{-|
Strips away static information, returning the raw dynamic components.

@since 1.8.0.0
-}
fromInput :: Input o -> Input# o
fromInput Input{..} = Input# (offset off) pos

{-|
Given a unique identifier, forms a plainly annotated static combination of position and offset.

@since 1.8.0.0
-}
toInput :: Word -> Input# o -> Input o
toInput u Input#{..} = Input (mkOffset off# u) pos#