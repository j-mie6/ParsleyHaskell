{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE CPP,
             ImplicitParams,
             MagicHash,
             TypeApplications,
             UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant case" #-}
{-|
Module      : Parsley.Internal.Backend.Machine.ErrorOps
Description : Primitive operations for working with errors (and their interaction with input).
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the primitive operations required by the
parsing machinery to work with errors, including any information extracted from the input.

@since 2.3.0.0
-}
module Parsley.Internal.Backend.Machine.ErrorOps (
    updateGhostsWithErrorInt#,
    updateGhostsWithErrorOffWith,
    updateGhostsWithErrorText,
    updateGhostsWithErrorByteString,
    amendInt#,
    amendOffWith,
    amendText,
    amendByteString,
    mergeGhostsIfValid
  ) where

import Data.Text.Internal                (Text(..))
import Parsley.Internal.Backend.Machine.Types.Base (GhostOffset)
import Parsley.Internal.Backend.Machine.Types.Errors.Defunc (DefuncGhosts(EmptyGhosts), addGhost, mergeGhosts, DefuncError(offset), isExpectedEmpty, amend)
import GHC.Exts (isTrue#, Int(I#), (<#), Int#, (==#))
import Parsley.Internal.Backend.Machine.InputRep

-- this is where we keep the functions we'll quote in InputOps, that way we can control their
-- implementation and inlining closely
{-# INLINE updateGhostsWithError #-}
updateGhostsWithError :: DefuncGhosts -> DefuncError -> GhostOffset -> GhostOffset -> (# DefuncGhosts, GhostOffset #)
updateGhostsWithError !ghosts !err !off !validOffset
  | not (isExpectedEmpty err), I# off == offset err =
      if isTrue# (validOffset <# off) then (# addGhost EmptyGhosts err, off #)
      else (# addGhost ghosts err, validOffset #)
  | otherwise = (# ghosts, validOffset #)

{-# NOINLINE updateGhostsWithErrorInt# #-}
updateGhostsWithErrorInt# :: DefuncGhosts -> DefuncError -> Int# -> GhostOffset -> (# DefuncGhosts, GhostOffset #)
updateGhostsWithErrorInt# = updateGhostsWithError

{-# NOINLINE updateGhostsWithErrorOffWith #-}
updateGhostsWithErrorOffWith :: DefuncGhosts -> DefuncError -> OffWith t -> GhostOffset -> (# DefuncGhosts, GhostOffset #)
updateGhostsWithErrorOffWith !ghosts !err (# off, _ #) !validOffset = updateGhostsWithError ghosts err off validOffset

{-# NOINLINE updateGhostsWithErrorText #-}
updateGhostsWithErrorText :: DefuncGhosts -> DefuncError -> Text -> GhostOffset -> (# DefuncGhosts, GhostOffset #)
updateGhostsWithErrorText !ghosts !err (Text _ (I# off) _) !validOffset = updateGhostsWithError ghosts err off validOffset

{-# NOINLINE updateGhostsWithErrorByteString #-}
updateGhostsWithErrorByteString :: DefuncGhosts -> DefuncError -> UnpackedLazyByteString -> GhostOffset -> (# DefuncGhosts, GhostOffset #)
updateGhostsWithErrorByteString !ghosts !err (# off, _, _, _, _, _ #) !validOffset = updateGhostsWithError ghosts err off validOffset


{-# NOINLINE amendInt# #-}
amendInt# :: DefuncError -> Int# -> DefuncError
amendInt# !err !off# = amend err (I# off#)

{-# NOINLINE amendOffWith #-}
amendOffWith :: DefuncError -> OffWith t -> DefuncError
amendOffWith !err (# off, _ #) = amend err (I# off)

{-# NOINLINE amendText #-}
amendText :: DefuncError -> Text -> DefuncError
amendText !err (Text _ off _) = amend err off

{-# NOINLINE amendByteString #-}
amendByteString :: DefuncError -> UnpackedLazyByteString -> DefuncError
amendByteString !err (# off, _, _, _, _, _ #) = amend err (I# off)

{-# NOINLINE mergeGhostsIfValid #-}
mergeGhostsIfValid :: DefuncGhosts -> DefuncGhosts -> GhostOffset -> GhostOffset -> DefuncGhosts
mergeGhostsIfValid !gs1 !gs2 !off1 !off2 =
   if isTrue# (off1 ==# off2)
                         then mergeGhosts gs1 gs2
                         else gs1
