{-# LANGUAGE CPP, MagicHash, UnboxedTuples, NumericUnderscores #-}
{-# OPTIONS_GHC -Wno-overflowed-literals #-}
{-|
Module      : Parsley.Internal.Backend.Machine.PosOps
Description : Collection of platform dependent position operations
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the implementations of updates on positions: these depend on the number of
bits in a word, or if the @full-width-positions@ flag was set on the @parsley-core@ library.

@since 1.8.0.0
-}
module Parsley.Internal.Backend.Machine.PosOps (CharClass(..), initPos, updatePos, toNextTab, updatePosQ, shiftLineAndSetColQ, shiftColQ, shiftAlignAndShiftColQ, tabWidth, liftPos, extractLine, extractCol) where

#include "MachDeps.h"
#if WORD_SIZE_IN_BITS < 64
#define FULL_WIDTH_POSITIONS
#endif

import Data.Bits                                   ( (.&.)
#ifndef FULL_WIDTH_POSITIONS
                                                   , unsafeShiftL, (.|.)
#endif
                                                   )
import Parsley.Internal.Backend.Machine.Types.Base (Pos)
import Parsley.Internal.Common                     (Code)
import GHC.Exts                                    (Int(..), Word(W#))
import GHC.Prim                                    ( plusWord#, and#, or#, word2Int#
#ifdef FULL_WIDTH_POSITIONS
                                                   , minusWord#
#else
                                                   , uncheckedShiftRL#
#endif
                                                   )

data CharClass = Tab | Newline | Regular | NonNewline

toNextTab :: Word -> Word
toNextTab x = (x + tabWidth - 1) .&. negate tabWidth .|. 1

updatePos :: Maybe CharClass -> Code Char -> Word -> Word -> Either (Code Pos) (Word, Word)
updatePos Nothing           c line col = Left [||updatePos# $$(liftPos line col) $$c||]
updatePos (Just Tab)        _ line col = Right (line, toNextTab col)
updatePos (Just Newline)    _ line _   = Right (line + 1, 1)
updatePos (Just Regular)    _ line col = Right (line, col + 1)
updatePos (Just NonNewline) c line col = Left [||updatePosNonNewline# $$(liftPos line col) $$c||]

{-|
Given a position and a character, returns the representation of the updated position.

@since 2.1.0.0
-}
updatePosQ :: Maybe CharClass -> Code Char -> Code Pos -> Code Pos
updatePosQ Nothing           c pos = [||updatePos# $$pos $$c||]
updatePosQ (Just Tab)        _ pos = shiftAlignAndShiftColQ 0 0 pos
updatePosQ (Just Newline)    _ pos = shiftLineAndSetColQ 1 1 pos
updatePosQ (Just Regular)    _ pos = shiftColQ 1 pos
updatePosQ (Just NonNewline) c pos = [||updatePosNonNewline# $$pos $$c ||]

{-|
The initial position used by the parser. This is some representation of (1, 1).

@since 1.8.0.0
-}
initPos :: (Word, Word)
initPos = (1, 1)

tabWidth :: Num a => a
tabWidth = 4

{-# INLINEABLE updatePos# #-}
{-|
Updates a given position assuming the given character was read. Tab characters are aligned to the
nearest 4th space boundary.

@since 1.8.0.0
-}
updatePos# :: Pos -> Char -> Pos

{-# INLINEABLE updatePosNonNewline# #-}
updatePosNonNewline# :: Pos -> Char -> Pos

shiftColQ :: Word -> Code Pos -> Code Pos
shiftLineAndSetColQ :: Word -> Word -> Code Pos -> Code Pos
shiftAlignAndShiftColQ :: Word -> Word -> Code Pos -> Code Pos

--updatePosCode :: Code Pos -> Word -> Word -> Word -> Code Pos

{-|
Given the opaque representation of a position, extracts the line number out of it.

@since 1.8.0.0
-}
extractLine :: Code Pos -> Code Int

{-|
Given the opaque representation of a position, extracts the column number out of it.

@since 1.8.0.0
-}
extractCol :: Code Pos -> Code Int

liftPos :: Word -> Word -> Code Pos

#ifndef FULL_WIDTH_POSITIONS

-- This is refered to directly in generated code, leave optimised primitives
updatePos# pos '\n' = (pos `and#` 0xffffffff_00000000##) `plusWord#` 0x00000001_00000001##
updatePos# pos '\t' = ((pos `plusWord#` 0x00000000_00000003##) `and#` 0xffffffff_fffffffc##) `or#` 0x00000000_00000001##
updatePos# pos _    = pos `plusWord#` 0x00000000_00000001##

updatePosNonNewline# pos '\t' = ((pos `plusWord#` 0x00000000_00000003##) `and#` 0xffffffff_fffffffc##) `or#` 0x00000000_00000001##
updatePosNonNewline# pos _    = pos `plusWord#` 0x00000000_00000001##

shiftLineAndSetColQ n col qpos = [|| ($$qpos `and#` 0xffffffff_00000000##) `plusWord#` $$(liftPos n col) ||]
shiftColQ (W# n) qpos = [|| $$qpos `plusWord#` n ||]
shiftAlignAndShiftColQ firstBy thenBy qpos =
  let !(W# pre) = firstBy + 3 -- offset first, then add 3 to overshoot
      !(W# mask) = -4         -- constant fold this into raw literal
      !(W# post) = thenBy + 1 -- add the offset of tab boundary from power of two, then remaining positions
  in if thenBy == 0 then [|| (($$qpos `plusWord#` pre) `and#` mask) `or#` 0x00000000_00000001## ||] -- because tab widths are multiples of two
     else                [|| (($$qpos `plusWord#` pre) `and#` mask) `plusWord#` post ||]

extractLine qpos = [||I# (word2Int# ($$qpos `uncheckedShiftRL#` 32#))||]
extractCol qpos = [||I# (word2Int# ($$qpos `and#` 0x00000000_ffffffff##))||]

liftPos line col = let !(W# p) = (line `unsafeShiftL` 32) .|. col in [||p||]

#else
-- This is refered to directly in generated code, leave optimised primitives
updatePos# (# line, _ #)   '\n' = (# line `plusWord#` 1##, 1## #)
updatePos# (# line, col #) '\t' = (# line, ((col `plusWord#` 3##) `and#` (0## `minusWord#` 4##)) `or#` 1## #) -- nearest tab boundary `c + (4 - (c - 1) % 4)`
updatePos# (# line, col #) _    = (# line, col `plusWord#` 1## #)

updatePosNonNewline# (# line, col #) '\t' = (# line, ((col `plusWord#` 3##) `and#` (0## `minusWord#` 4##)) `or#` 1## #) -- nearest tab boundary `c + (4 - (c - 1) % 4)`
updatePosNonNewline# (# line, col #) _    = (# line, col `plusWord#` 1## #)

shiftLineAndSetColQ (W# n) (W# col) qpos = [|| case $$qpos of (# line, _ #) -> (# line `plusWord#` n, col #) ||]
shiftColQ (W# n) qpos = [|| case $$qpos of (# line, col #) -> (# line, col `plusWord#` n #) ||]
shiftAlignAndShiftColQ firstBy thenBy qpos =
  let !(W# pre) = firstBy + 3 -- offset first, then add 3 to overshoot
      !(W# mask) = -4         -- constant fold this into raw literal
      !(W# post) = thenBy + 1 -- add the offset of tab boundary from power of two, then remaining positions
  in [|| case $$qpos of
           (# line, col #) -> (# line,
             $$(if thenBy == 0 then [|| ((col `plusWord#` pre) `and#` mask) `or#` 1## ||] -- because tab widths are multiples of two
                else                [|| ((col `plusWord#` pre) `and#` mask) `plusWord#` post ||]) #) ||]

extractLine qpos = [|| case $$qpos of (# line, _ #) -> I# (word2Int# line) ||]
extractCol qpos = [|| case $$qpos of (# _, col #) -> I# (word2Int# col) ||]

liftPos (W# line) (W# col) = [||(# line, col #)||]
#endif