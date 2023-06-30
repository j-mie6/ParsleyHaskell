{-# LANGUAGE UnboxedTuples, MagicHash, RecordWildCards, TypeApplications #-}
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
module Parsley.Internal.Backend.Machine.Types.Input (
    Input(off), Input#(..),
    mkInput, fromInput, toInput,
    forcePos, updatePos, updateOffset,
    chooseInput
  ) where

import Parsley.Internal.Backend.Machine.InputRep                  (StaRep, DynRep)
import Parsley.Internal.Backend.Machine.InputOps                  (DynOps, asSta, asDyn)
import Parsley.Internal.Backend.Machine.Types.Input.Offset        (Offset(offset), mkOffset, moveN)
import Parsley.Internal.Backend.Machine.Types.Input.Pos           (StaPos, DynPos, toDynPos, fromDynPos, fromStaPos, force, update)
import Parsley.Internal.Backend.Machine.Types.InputCharacteristic (InputCharacteristic(..))
import Parsley.Internal.Common.Utils                              (Code)
import Parsley.Internal.Core.CharPred                             (CharPred)
import Parsley.Internal.Core.CombinatorAST                        (PosSelector)

{-|
Packages known static information about offsets (via `Offset`) with static information about positions
(currently unavailable).

@since 2.1.0.0
-}
data Input o = Input {
    -- | The offset contained within the input
    off  :: !(Offset o),
    -- | The position contained within the input
    pos :: !StaPos
  }

{-|
Packages a dynamic offset with a dynamic position.

@since 1.8.0.0
-}
data Input# o = Input# {
    off#  :: !(Code (DynRep o)),
    pos#  :: !DynPos
  }

{-|
Constructs an `Input` given a dynamic offset and a static position.

@since 2.1.0.0
-}
mkInput :: StaRep o -> (Word, Word) -> Input o
mkInput off = Input (mkOffset off 0) . fromStaPos

{-|
Strips away static information, returning the raw dynamic components.

@since 1.8.0.0
-}
fromInput :: forall o. DynOps o => Input o -> Input# o
fromInput Input{..} = Input# (asDyn @o (offset off)) (toDynPos pos)

{-|
Given a unique identifier, forms a plainly annotated static combination of position and offset.

@since 1.8.0.0
-}
toInput :: forall o. DynOps o => Word -> Input# o -> Input o
toInput u Input#{..} = Input (mkOffset (asSta @o off#) u) (fromDynPos pos#)

updateOffset :: Offset o -> Input o -> Input o
updateOffset off inp = inp { off = off }

{-|
Collapse the position stored inside the input applying all updates to it. Once this has been completed,
the given `PosSelector` will be used to extract one of the line or column and return it to the given
continuation, along with the updated input post-collapse.

@since 2.1.0.0
-}
forcePos :: Input o -> PosSelector -> (Code Int -> Input o -> Code r) -> Code r
forcePos input sel k = force (pos input) sel (\dp sp -> k dp (input { pos = sp }))

{-|
Updates the position within the `Input` when a character has been consumed, providing it the
dynamic character that was produced as well as the static character-predicate that guarded it.

@since 2.1.0.0
-}
updatePos :: Input o -> Code Char -> CharPred -> Input o
updatePos input c p = input { pos = update (pos input) c p }

{-|
Given knowledge about how input has been consumed through a call boundary, this function can update
the input using statically acquired knowledge.

@since 2.1.0.0
-}
-- TODO: In future, we could adjust InputCharacteristic to provide information about the static behaviours of the positions too...
chooseInput :: forall o. DynOps o => InputCharacteristic -> Word -> Input o -> Input# o -> Input o
chooseInput (AlwaysConsumes (Just n)) _ inp  inp#  = inp { off = moveN n (off inp) (asSta @o (off# inp#)), pos = fromDynPos (pos# inp#) }
-- Technically, in this case, we know the whole input is unchanged. This essentially ignores the continuation arguments
-- hopefully GHC could optimise this better?
chooseInput NeverConsumes      _ inp  _inp# = inp -- { off = (off inp) {offset = off# inp# }, pos = pos# inp# }
-- This is safer right now, since we never need information about input greater than another
chooseInput (AlwaysConsumes Nothing) u _inp inp#  = toInput u inp#
chooseInput MayConsume               u _inp inp#  = toInput u inp#
