{-# LANGUAGE CPP, MagicHash, UnboxedTuples #-}
module Parsley.Internal.Backend.Machine.PosOps (module Parsley.Internal.Backend.Machine.PosOps) where

import Parsley.Internal.Backend.Machine.Types.Base (Pos)
import Parsley.Internal.Common                     (Code)
import GHC.Prim                                    (plusWord#, minusWord#, and#, or#)


#include "MachDeps.h"
#if WORD_SIZE_IN_BITS < 64
#define FULL_WIDTH_POSITIONS
#endif

initPos :: Code Pos
updatePos :: Pos -> Char -> Pos

#ifndef FULL_WIDTH_POSITIONS
initPos = [|| 0x00010001## ||]

updatePos pos '\n' = (pos `plusWord#` 0x10000##) `and#` 0xffff0001##
updatePos pos '\t' = ((pos `plusWord#` 3##) `and#` (0## `minusWord#` 4##)) `or#` 1##
updatePos pos _    = pos `plusWord#` 1##

#else
initPos = [|| (# 1##, 1## #) ||]

updatePos (# line, _ #)   '\n' = (# line `plusWord#` 1##, 1## #)
updatePos (# line, col #) '\t' = (# line, ((col `plusWord#` 3##) `and#` (0## `minusWord#` 4##)) `or#` 1## #) -- nearest tab boundary `c + (4 - (c - 1) % 4)`
updatePos (# line, col #) _    = (# line, col `plusWord#` 1## #)

#endif
