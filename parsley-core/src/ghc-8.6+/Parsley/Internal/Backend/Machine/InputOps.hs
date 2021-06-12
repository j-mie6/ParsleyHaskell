{-# LANGUAGE ImplicitParams,
             MagicHash,
             TypeApplications,
             UnboxedTuples #-}
module Parsley.Internal.Backend.Machine.InputOps (
    InputPrep(..), PositionOps(..), BoxOps(..), LogOps(..),
    InputOps(..), more, next,
    InputDependant(..),
  ) where

import Data.Array.Base                           (UArray(..), listArray)
import Data.ByteString.Internal                  (ByteString(..))
import Data.Text.Array                           (aBA{-, empty-})
import Data.Text.Internal                        (Text(..))
import Data.Text.Unsafe                          (iter, Iter(..){-, iter_, reverseIter_-})
import GHC.Exts                                  (Int(..), Char(..))
import GHC.ForeignPtr                            (ForeignPtr(..))
import GHC.Prim                                  (indexWideCharArray#, indexWord16Array#, readWord8OffAddr#, word2Int#, chr#, touch#, realWorld#, plusAddr#, (+#))
import Parsley.Internal.Backend.Machine.InputRep
import Parsley.Internal.Common.Utils             (Code)
import Parsley.Internal.Core.InputTypes

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString(..))
--import qualified Data.Text                     as Text (length, index)

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

instance InputPrep Text16 where
  prepare qinput = [||
      let Text16 (Text arr off size) = $$qinput
          arr# = aBA arr
          next (I# i#) = (# C# (chr# (word2Int# (indexWord16Array# arr# i#))), I# (i# +# 1#) #)
      in InputDependant next (< size) off
    ||]

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
          size = length input
          more (OffWith i _) = i < size
          --more (OffWith _ []) = False
          --more _              = True
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
  box = [||\i# -> I# i#||]
  unbox = [||\(I# i#) -> i#||]

instance BoxOps (OffWith ts) where
  box = [||\(# i#, ts #) -> OffWith (I# i#) ts||]
  unbox = [||\(OffWith (I# i#) ts) -> (# i#, ts #)||]

instance BoxOps Text where
  box = [||id||]
  unbox = [||id||]

instance BoxOps UnpackedLazyByteString where
  box = [||\(!(# i#, addr#, final, off#, size#, cs #)) -> UnpackedLazyByteString (I# i#) addr# final (I# off#) (I# size#) cs||]
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

{- Old Instances -}
{-instance Input CacheText (Text, Stream) where
  prepare qinput = [||
      let (CacheText input) = $$qinput
          next (t@(Text arr off unconsumed), _) = let !(Iter c d) = iter t 0 in (# c, (Text arr (off+d) (unconsumed-d), nomore) #)
          more (Text _ _ unconsumed, _) = unconsumed > 0
          same (Text _ i _, _) (Text _ j _, _) = i == j
          (Text arr off unconsumed, _) << i = go i off unconsumed
            where
              go 0 off' unconsumed' = (Text arr off' unconsumed', nomore)
              go n off' unconsumed'
                | off' > 0 = let !d = reverseIter_ (Text arr off' unconsumed') 0 in go (n-1) (off'+d) (unconsumed'-d)
                | otherwise = (Text arr off' unconsumed', nomore)
          (Text arr off unconsumed, _) >> i = go i off unconsumed
            where
              go 0 off' unconsumed' = (Text arr off' unconsumed', nomore)
              go n off' unconsumed'
                | unconsumed' > 0 = let !d = iter_ (Text arr off' unconsumed') 0 in go (n-1) (off'+d) (unconsumed'-d)
                | otherwise = (Text arr off' unconsumed', nomore)
          toInt (Text arr off unconsumed, _) = div off 2
          box (# text, cache #) = (text, cache)
          unbox (text, cache) = (# text, cache #)
          newCRef (Text _ i _, _) = newSTRefU i
          readCRef ref = fmap (\i -> (Text empty i 0, nomore)) (readSTRefU ref)
          writeCRef ref (Text _ i _, _) = writeSTRefU ref i
      in PreparedInput next more same (input, nomore) box unbox newCRef readCRef writeCRef s(<<) (>>) toInt
    ||]

instance Input Lazy.ByteString (OffWith Lazy.ByteString) where
  prepare qinput = [||
      let next (OffWith i (Lazy.Chunk (PS ptr@(ForeignPtr addr# final) off@(I# off#) size) cs)) =
            case readWord8OffAddr# addr# off# realWorld# of
              (# s', x #) -> case touch# final s' of
                _ -> (# C# (chr# (word2Int# x)), OffWith (i+1) (if size == 1 then cs
                                                                else Lazy.Chunk (PS ptr (off+1) (size-1)) cs) #)
          more (OffWith _ Lazy.Empty) = False
          more _ = True
          ow@(OffWith _ (Lazy.Empty)) << _ = ow
          OffWith o (Lazy.Chunk (PS ptr off size) cs) << i =
            let d = min off i
            in OffWith (o - d) (Lazy.Chunk (PS ptr (off - d) (size + d)) cs)
          ow@(OffWith _ Lazy.Empty) >> _ = ow
          OffWith o (Lazy.Chunk (PS ptr off size) cs) >> i
            | i < size  = OffWith (o + i) (Lazy.Chunk (PS ptr (off + i) (size - i)) cs)
            | otherwise = OffWith (o + size) cs >> (i - size)
          readCRef ref = fmap (\i -> OffWith i Lazy.Empty) (readSTRefU ref)
      in PreparedInput next more offWithSame (offWith $$qinput) offWithBox offWithUnbox offWithNewORef readCRef offWithWriteORef (<<) (>>) offWithToInt
    ||]-}