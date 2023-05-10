{-# LANGUAGE ImplicitParams,
             MagicHash,
             TypeApplications,
             UnboxedTuples #-}
{-# OPTIONS_GHC -Wno-deprecations #-} --FIXME: remove when Text16 is removed
module Parsley.Internal.Backend.Machine.InputOps (
    InputPrep(..), PositionOps(..), BoxOps(..), LogOps(..),
    InputOps(..), more, next,
    InputDependant(..),
  ) where

import Data.Array.Base                           (UArray(..), listArray)
import Data.ByteString.Internal                  (ByteString(..))
import Data.Text.Internal                        (Text(..))
import Data.Text.Unsafe                          (iter, Iter(..))
import GHC.Exts                                  (Int(..), Char(..))
import GHC.ForeignPtr                            (ForeignPtr(..))
import GHC.Prim                                  (indexWideCharArray#, readWord8OffAddr#, word2Int#, chr#, touch#, realWorld#, plusAddr#, (+#))
import Parsley.Internal.Backend.Machine.InputRep
import Parsley.Internal.Common.Utils             (Code)
import Parsley.Internal.Core.InputTypes          (Stream((:>)), CharList(..), Text16(..))

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString(..))

data InputDependant rep = InputDependant {-next-} (rep -> (# Char, rep #))
                                         {-more-} (rep -> Bool)
                                         {-init-} rep

{- Typeclasses -}
class InputPrep input where
  prepare :: Code input -> Code (InputDependant (Rep input))

class PositionOps rep where
  same :: Code (rep -> rep -> Bool)
  shiftRight :: Code (rep -> Int -> rep)

class BoxOps rep where
  box   :: Code (Unboxed rep -> rep)
  unbox :: Code (rep -> Unboxed rep)

class LogOps rep where
  shiftLeft :: Code (rep -> Int -> rep)
  offToInt  :: Code (rep -> Int)

data InputOps rep = InputOps { _more       :: Code (rep -> Bool)
                             , _next       :: Code (rep -> (# Char, rep #))
                             }
more :: (?ops :: InputOps rep) => Code (rep -> Bool)
more = _more ?ops
next :: (?ops :: InputOps rep) => Code rep -> (Code Char -> Code rep -> Code r) -> Code r
next ts k = [|| let !(# t, ts' #) = $$(_next ?ops) $$ts in $$(k [||t||] [||ts'||]) ||]

{- INSTANCES -}
-- InputPrep Instances
instance InputPrep [Char] where
  prepare input = prepare @(UArray Int Char) [||listArray (0, length $$input-1) $$input||]

instance InputPrep (UArray Int Char) where
  prepare qinput = [||
      let UArray _ _ size input# = $$qinput
          next (I# i#) = (# C# (indexWideCharArray# input# i#), I# (i# +# 1#) #)
      in InputDependant next (< size) 0
    ||]

instance InputPrep Text16 where prepare qinput = prepare @Text [|| let Text16 t = $$qinput in t ||]

instance InputPrep ByteString where
  prepare qinput = [||
      let PS (ForeignPtr addr# final) off size = $$qinput
          next i@(I# i#) =
            case readWord8OffAddr# (addr# `plusAddr#` i#) 0# realWorld# of
              (# s', x #) -> case touch# final s' of
                _ -> (# C# (chr# (word2Int# x)), i + 1 #)
      in InputDependant next (< size) off
    ||]

instance InputPrep CharList where
  prepare qinput = [||
      let CharList input = $$qinput
          next (OffWith i (c:cs)) = (# c, OffWith (i+1) cs #)
          more (OffWith _ []) = False
          more _              = True
      in InputDependant next more ($$offWith input)
    ||]

instance InputPrep Text where
  prepare qinput = [||
      let next t@(Text arr off unconsumed) = let !(Iter c d) = iter t 0 in (# c, Text arr (off+d) (unconsumed-d) #)
          more (Text _ _ unconsumed) = unconsumed > 0
      in InputDependant next more $$qinput
    ||]

instance InputPrep Lazy.ByteString where
  prepare qinput = [||
      let next (UnpackedLazyByteString i addr# final off@(I# off#) size cs) =
            case readWord8OffAddr# addr# off# realWorld# of
              (# s', x #) -> case touch# final s' of
                _ -> (# C# (chr# (word2Int# x)),
                    if size /= 1 then UnpackedLazyByteString (i+1) addr# final (off+1) (size-1) cs
                    else case cs of
                      Lazy.Chunk (PS (ForeignPtr addr'# final') off' size') cs' -> UnpackedLazyByteString (i+1) addr'# final' off' size' cs'
                      Lazy.Empty -> emptyUnpackedLazyByteString (i+1)
                  #)
          more (UnpackedLazyByteString _ _ _ _ 0 _) = False
          more _ = True
          initial = case $$qinput of
            Lazy.Chunk (PS (ForeignPtr addr# final) off size) cs -> UnpackedLazyByteString 0 addr# final off size cs
            Lazy.Empty -> emptyUnpackedLazyByteString 0
      in InputDependant next more initial
    ||]

instance InputPrep Stream where
  prepare qinput = [||
      let next (OffWith o (c :> cs)) = (# c, OffWith (o + 1) cs #)
      in InputDependant next (const True) ($$offWith $$qinput)
    ||]

-- PositionOps Instances
instance PositionOps Int where
  same = [||(==) @Int||]
  shiftRight = [||(+) @Int||]

instance PositionOps (OffWith String) where
  same = offWithSame
  shiftRight = offWithShiftRight [||drop||]

instance PositionOps (OffWith Stream) where
  same = offWithSame
  shiftRight = offWithShiftRight [||dropStream||]

instance PositionOps Text where
  same = [||\(Text _ i _) (Text _ j _) -> i == j||]
  shiftRight = [||textShiftRight||]

instance PositionOps UnpackedLazyByteString where
  same = [||\(UnpackedLazyByteString i _ _ _ _ _) (UnpackedLazyByteString j _ _ _ _ _) -> i == j||]
  shiftRight = [||byteStringShiftRight||]

-- BoxOps Instances
instance BoxOps Int where
  box = [||I#||]
  unbox = [||\(I# i#) -> i#||]

instance BoxOps (OffWith ts) where
  box = [||\(# i#, ts #) -> OffWith (I# i#) ts||]
  unbox = [||\(OffWith (I# i#) ts) -> (# i#, ts #)||]

instance BoxOps Text where
  box = [||id||]
  unbox = [||id||]

instance BoxOps UnpackedLazyByteString where
  box = [||\(# i#, addr#, final, off#, size#, cs #) -> UnpackedLazyByteString (I# i#) addr# final (I# off#) (I# size#) cs||]
  unbox = [||\(UnpackedLazyByteString (I# i#) addr# final (I# off#) (I# size#) cs) -> (# i#, addr#, final, off#, size#, cs #)||]

-- LogOps Instances
instance LogOps Int where
  shiftLeft = [||\o i -> max (o - i) 0||]
  offToInt = [||id||]

instance LogOps (OffWith ts) where
  shiftLeft = [||const||]
  offToInt = [||\(OffWith i _) -> i||]

instance LogOps Text where
  shiftLeft = [||textShiftLeft||]
  offToInt = [||\(Text _ off _) -> div off 2||]

instance LogOps UnpackedLazyByteString where
  shiftLeft = [||byteStringShiftLeft||]
  offToInt = [||\(UnpackedLazyByteString i _ _ _ _ _) -> i||]
