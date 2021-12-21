{-# LANGUAGE CPP, MagicHash, UnboxedTuples, NumericUnderscores #-}
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
module Parsley.Internal.Backend.Machine.PosOps (CharClass(..), initPos, updatePos, updatePosQ, tabWidth, liftPos, extractLine, extractCol) where

#include "MachDeps.h"
#if WORD_SIZE_IN_BITS < 64
#define FULL_WIDTH_POSITIONS
#endif

import Parsley.Internal.Backend.Machine.Types.Base (Pos)
import Parsley.Internal.Common                     (Code)
import GHC.Exts                                    (Int(..), Word(W#))
import GHC.Prim                                    (plusWord#, and#, or#, word2Int#,
#ifdef FULL_WIDTH_POSITIONS
                                                    minusWord#
#else
                                                    uncheckedShiftRL#, uncheckedShiftL#
#endif
                                                   )

data CharClass = Tab | Newline | Regular

updatePos :: Maybe CharClass -> Code Char -> (Word, Word) -> Either (Code Pos) (Word, Word)
updatePos Nothing        c pos         = Left [||updatePos# $$(liftPos pos) $$c||]
updatePos (Just Tab)     _ (line, col) = Right (line, col + (tabWidth - ((col - 1) `mod` tabWidth)))
updatePos (Just Newline) _ (line, _)   = Right (line + 1, 1)
updatePos (Just Regular) _ (line, col) = Right (line, col + 1)

{-|
Given a position and a character, returns the representation of the updated position.

@since 2.1.0.0
-}
updatePosQ :: Maybe CharClass -> Code Char -> Code Pos -> Code Pos
updatePosQ Nothing        c pos = [||updatePos# $$pos $$c||]
updatePosQ (Just Tab)     _ pos = tabQ pos
updatePosQ (Just Newline) _ pos = newlineQ pos
updatePosQ (Just Regular) _ pos = regularQ pos

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

newlineQ :: Code Pos -> Code Pos
tabQ :: Code Pos -> Code Pos
regularQ :: Code Pos -> Code Pos

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

liftPos :: (Word, Word) -> Code Pos

#ifndef FULL_WIDTH_POSITIONS

updatePos# pos '\n' = (pos `and#` 0xffffffff_00000000##) `plusWord#` 0x00000001_00000001##
updatePos# pos '\t' = ((pos `plusWord#` 0x00000000_00000003##) `and#` 0xffffffff_fffffffc##) `or#` 0x00000000_00000001##
updatePos# pos _    = pos `plusWord#` 0x00000000_00000001##

newlineQ qpos = [|| ($$qpos `and#` 0xffffffff_00000000##) `plusWord#` 0x00000001_00000001## ||]
tabQ qpos = [|| (($$qpos `plusWord#` 0x00000000_00000003##) `and#` 0xffffffff_fffffffc##) `or#` 0x00000000_00000001## ||]
regularQ qpos = [|| $$qpos `plusWord#` 0x00000000_00000001## ||]

--updatePosCode qpos (W# premask) (W# bitmask) (W# postmask) = qpos

extractLine qpos = [||I# (word2Int# ($$qpos `uncheckedShiftRL#` 32#))||]
extractCol qpos = [||I# (word2Int# ($$qpos `and#` 0x00000000_ffffffff##))||]

liftPos (W# line, W# col) = let p = (line `uncheckedShiftL#` 32#) `or#` col in [||p||]

#else
updatePos# (# line, _ #)   '\n' = (# line `plusWord#` 1##, 1## #)
updatePos# (# line, col #) '\t' = (# line, ((col `plusWord#` 3##) `and#` (0## `minusWord#` 4##)) `or#` 1## #) -- nearest tab boundary `c + (4 - (c - 1) % 4)`
updatePos# (# line, col #) _    = (# line, col `plusWord#` 1## #)

newlineQ qpos = [|| case $$qpos of (# line, _ #) -> (# line `plusWord#` 1##, 1## #) ||]
tabQ qpos = [|| case $$qpos of (# line, col #) -> (# line, ((col `plusWord#` 3##) `and#` (0## `minusWord#` 4##)) `or#` 1## #) ||]
regularQ qpos = [|| case $$qpos of (# line, col #) -> (# line, col `plusWord#` 1## #) ||]

--updatePosCode qpos (W# premask) (W# bitmask) (W# postmask) = qpos

extractLine qpos = [|| case $$qpos of (# line, _ #) -> I# (word2Int# line) ||]
extractCol qpos = [|| case $$qpos of (# _, col #) -> I# (word2Int# col) ||]

liftPos (W# line, W# col) = [||(# line, col #)||]
#endif