{-# LANGUAGE CPP, MagicHash, UnboxedTuples, NumericUnderscores #-}
module Parsley.Internal.Backend.Machine.PosOps (module Parsley.Internal.Backend.Machine.PosOps) where

#include "MachDeps.h"
#if WORD_SIZE_IN_BITS < 64
#define FULL_WIDTH_POSITIONS
#endif

import Parsley.Internal.Backend.Machine.Types.Base (Pos)
import Parsley.Internal.Common                     (Code)
import GHC.Exts                                    (Int(..))
import GHC.Prim                                    (plusWord#, and#, or#, word2Int#,
#ifdef FULL_WIDTH_POSITIONS
                                                    minusWord#
#else
                                                    uncheckedShiftRL#
#endif
                                                   )

initPos :: Code Pos
{-# INLINEABLE updatePos# #-}
updatePos# :: Pos -> Char -> Pos
extractLine :: Code Pos -> Code Int
extractCol :: Code Pos -> Code Int

#ifndef FULL_WIDTH_POSITIONS
initPos = [|| 0x00000001_00000001## ||]

updatePos# pos '\n' = (pos `plusWord#` 0x00000001_00000000##) `and#` 0xffffffff_00000001##
updatePos# pos '\t' = ((pos `plusWord#` 0x00000000_00000003##) `and#` 0xffffffff_fffffffc##) `or#` 0x00000000_00000001##
updatePos# pos _    = pos `plusWord#` 0x00000000_00000001##

extractLine qpos = [||I# (word2Int# ($$qpos `uncheckedShiftRL#` 32#))||]
extractCol qpos = [||I# (word2Int# ($$qpos `and#` 0x00000000_ffffffff##))||]

#else
initPos = [|| (# 1##, 1## #) ||]

updatePos# (# line, _ #)   '\n' = (# line `plusWord#` 1##, 1## #)
updatePos# (# line, col #) '\t' = (# line, ((col `plusWord#` 3##) `and#` (0## `minusWord#` 4##)) `or#` 1## #) -- nearest tab boundary `c + (4 - (c - 1) % 4)`
updatePos# (# line, col #) _    = (# line, col `plusWord#` 1## #)

extractLine qpos = [|| case $$qpos of (# line, _ #) -> I# (word2Int# line) ||]
extractCol qpos = [|| case $$qpos of (# _, col #) -> I# (word2Int# col) ||]
#endif

updatePos :: Code Pos -> Code Char -> Code Pos
updatePos pos c = [||updatePos# $$pos $$c||]