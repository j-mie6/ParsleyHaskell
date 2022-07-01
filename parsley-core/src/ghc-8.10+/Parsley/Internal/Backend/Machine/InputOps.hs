{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE CPP,
             ImplicitParams,
             MagicHash,
             TypeApplications,
             UnboxedTuples #-}
{-|
Module      : Parsley.Internal.Backend.Machine.InputOps
Description : Primitive operations for working with input.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the primitive operations required by the
parsing machinery to work with input.

@since 1.0.0.0
-}
module Parsley.Internal.Backend.Machine.InputOps (
    InputPrep(..), PositionOps(..), LogOps(..),
    InputOps(..), more, next,
#if __GLASGOW_HASKELL__ <= 900
    word8ToWord#, word16ToWord#
#endif
    InputDependant
  ) where

import Data.Array.Base                             (UArray(..), listArray)
import Data.ByteString.Internal                    (ByteString(..))
import Data.Text.Array                             (aBA{-, empty-})
import Data.Text.Internal                          (Text(..))
import Data.Text.Unsafe                            (iter, Iter(..){-, iter_, reverseIter_-})
import GHC.Exts                                    (Int(..), Char(..), TYPE, Int#)
import GHC.ForeignPtr                              (ForeignPtr(..))
import GHC.Prim                                    (indexWideCharArray#, indexWord16Array#, readWord8OffAddr#, word2Int#, chr#, touch#, realWorld#, plusAddr#, (+#), (-#))
#if __GLASGOW_HASKELL__ > 900
import GHC.Prim                                    (word16ToWord#, word8ToWord#)
#endif
import Parsley.Internal.Backend.Machine.InputRep   (Stream(..), CharList(..), Text16(..), Rep, UnpackedLazyByteString,
                                                    offWith, emptyUnpackedLazyByteString, intSame, intLess,
                                                    offsetText, offWithSame, offWithShiftRight, dropStream,
                                                    textShiftRight, textShiftLeft, byteStringShiftRight,
                                                    byteStringShiftLeft, max#)
import Parsley.Internal.Common.Utils               (Code)

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString(..))
--import qualified Data.Text                     as Text (length, index)


#if __GLASGOW_HASKELL__ <= 900
{-# INLINE word8ToWord# #-}
word8ToWord# :: Word# -> Word#
word8ToWord# x = x

{-# INLINE word16ToWord# #-}
word16ToWord# :: Word# -> Word#
word16ToWord# x = x
#endif

{- Auxillary Representation -}
{-|
Given some associated representation type, defines the operations
that work with a /closed over/ instance of that type. These are:

* @next@: extract the next character from the input (existence not included)
* @more@: query whether another character /can/ be read
* @init@: the initial state of the input.

@since 1.0.0.0
-}
type InputDependant (rep :: TYPE r) = (# {-next-} rep -> (# Char, rep #)
                                       , {-more-} rep -> Bool
                                       , {-init-} rep
                                       #)

{- Typeclasses -}
{-|
This class is responsible for converting the user's input into a form that
parsley can work with efficiently.

@since 1.0.0.0
-}
class InputPrep input where
  {-|
  Given the user's input to the parser, in its original form, this function
  distils it first into @`Rep` input@, which is parsley's internal representation,
  and then produces an `InputDependant` containing the core operations.

  @since 1.0.0.0
  -}
  prepare :: rep ~ Rep input => Code input -> Code (InputDependant rep)

{-|
Defines operations for manipulating offsets for regular use. These are not
tied to the original captured input but instead to the representation of its
offset.

@since 1.0.0.0
-}
class PositionOps (rep :: TYPE r) where
  {-|
  Compares two "input"s for equality. In reality this usually means an offset
  present in the @rep@.

  @since 1.0.0.0
  -}
  same :: Code rep -> Code rep -> Code Bool

  {-|
  Advances the input by several characters at a time (existence not included).
  This can be used to check if characters exist at a future point in the input
  in conjunction with `more`.

  @since 1.0.0.0
  -}
  shiftRight :: Code rep -> Code Int# -> Code rep

{-|
Defines operation used for debugging operations.

@since 1.0.0.0
-}
class LogOps (rep :: TYPE r) where
  {-|
  If possible, shifts the input back several characters.
  This is used to provide the previous input characters for the debugging combinator.

  @since 1.0.0.0
  -}
  shiftLeft :: Code rep -> Code Int# -> Code rep

  {-|
  Converts the represention of the input into an @Int@.

  @since 1.0.0.0
  -}
  offToInt  :: Code rep -> Code Int

{-|
This is a psuedo-typeclass, which depends directly on the values obtained from
`InputDependant`. Because this instance must depend on local information, it is
synthesised and passed around using @ImplicitParams@.

@since 1.0.0.0
-}
data InputOps (rep :: TYPE r) = InputOps { _more       :: Code (rep -> Bool)            -- ^ Does the input have any more characters?
                                         , _next       :: Code (rep -> (# Char, rep #)) -- ^ Read the next character (without checking existence)
                                         }
{-|
Wraps around `InputOps` and `_more`.

Queries the input to see if another character may be consumed.

@since 1.4.0.0
-}
more :: forall r (rep :: TYPE r). (?ops :: InputOps rep) => Code rep -> Code Bool
more qo# = [|| $$(_more ?ops) $$(qo#) ||]

{-|
Wraps around `InputOps` and `_next`.

Given some input and a continuation that accepts new input and a character, it will read
a character off (without checking that it exists!) and feeds it and the remaining input
to the continuation.

@since 1.0.0.0
-}
next :: forall r (rep :: TYPE r) a. (?ops :: InputOps rep) => Code rep -> (Code Char -> Code rep -> Code a) -> Code a
next ts k = [|| let !(# t, ts' #) = $$(_next ?ops) $$ts in $$(k [||t||] [||ts'||]) ||]

{- INSTANCES -}
-- InputPrep Instances
instance InputPrep [Char] where
  prepare input = prepare @(UArray Int Char) [||listArray (0, length $$input-1) $$input||]

instance InputPrep (UArray Int Char) where
  prepare qinput = [||
      let !(UArray _ _ (I# size#) input#) = $$qinput
          next i# = (# C# (indexWideCharArray# input# i#), i# +# 1# #)
      in (# next, \qi -> $$(intLess [||qi||] [||size#||]), 0# #)
    ||]

instance InputPrep Text16 where
  prepare qinput = [||
      let Text16 (Text arr (I# off#) (I# size#)) = $$qinput
          arr# = aBA arr
          next i# = (# C# (chr# (word2Int# (word16ToWord# (indexWord16Array# arr# i#)))), i# +# 1# #)
      in (# next, \qi -> $$(intLess [||qi||] [||size#||]), off# #)
    ||]

instance InputPrep ByteString where
  prepare qinput = [||
      let PS (ForeignPtr addr# final) (I# off#) (I# size#) = $$qinput
          next i# =
            case readWord8OffAddr# (addr# `plusAddr#` i#) 0# realWorld# of
              (# s', x #) -> case touch# final s' of
                _ -> (# C# (chr# (word2Int# (word8ToWord# x))), i# +# 1# #)
      in  (# next, \qi -> $$(intLess [||qi||] [||size#||]), off# #)
    ||]

instance InputPrep CharList where
  prepare qinput = [||
      let CharList input = $$qinput
          next :: (# Int#, [Char] #) -> (# Char, (# Int#, [Char] #) #)
          next (# i#, c:cs #) = (# c, (# i# +# 1#, cs #) #)
          more :: (# Int#, [Char] #) -> Bool
          more (# _, [] #) = False
          more _           = True
      in (# next, more, $$(offWith [||input||]) #)
    ||]

instance InputPrep Text where
  prepare qinput = [||
      let next t@(Text arr off unconsumed) = let !(Iter c d) = iter t 0 in (# c, Text arr (off + d) (unconsumed - d) #)
          more (Text _ _ unconsumed) = unconsumed > 0
      in (# next, more, $$qinput #)
    ||]

instance InputPrep Lazy.ByteString where
  prepare qinput = [||
      let next (# i#, addr#, final, off#, size#, cs #) =
            case readWord8OffAddr# addr# off# realWorld# of
              (# s', x #) -> case touch# final s' of
                _ -> (# C# (chr# (word2Int# (word8ToWord# x))),
                    if I# size# /= 1 then (# i# +# 1#, addr#, final, off# +# 1#, size# -# 1#, cs #)
                    else case cs of
                      Lazy.Chunk (PS (ForeignPtr addr'# final') (I# off'#) (I# size'#)) cs' ->
                        (# i# +# 1#, addr'#, final', off'#, size'#, cs' #)
                      Lazy.Empty -> $$(emptyUnpackedLazyByteString [||i# +# 1#||])
                  #)
          more :: UnpackedLazyByteString -> Bool
          more (# _, _, _, _, 0#, _ #) = False
          more (# _, _, _, _, _, _ #) = True

          initial :: UnpackedLazyByteString
          initial = case $$qinput of
            Lazy.Chunk (PS (ForeignPtr addr# final) (I# off#) (I# size#)) cs -> (# 0#, addr#, final, off#, size#, cs #)
            Lazy.Empty -> $$(emptyUnpackedLazyByteString [||0#||])
      in (# next, more, initial #)
    ||]

instance InputPrep Stream where
  prepare qinput = [||
      let next (# o#, c :> cs #) = (# c, (# o# +# 1#, cs #) #)
      in (# next, \_ -> True, $$(offWith qinput) #)
    ||]

shiftRightInt :: Code Int# -> Code Int# -> Code Int#
shiftRightInt qo# qi# = [||$$(qo#) +# $$(qi#)||]

-- PositionOps Instances
instance PositionOps Int# where
  same = intSame
  shiftRight = shiftRightInt

instance PositionOps (# Int#, [Char] #) where
  same = offWithSame
  shiftRight qo# qi# = offWithShiftRight [||drop||] qo# qi#

instance PositionOps (# Int#, Stream #) where
  same = offWithSame
  shiftRight qo# qi# = offWithShiftRight [||dropStream||] qo# qi#

instance PositionOps Text where
  same qt1 qt2 = [||$$(offsetText qt1) == $$(offsetText qt2)||]
  shiftRight qo# qi# = [||textShiftRight $$(qo#) (I# $$(qi#))||]

instance PositionOps UnpackedLazyByteString where
  same qx# qy# = [||
      case $$(qx#) of
        (# i#, _, _, _, _, _ #) -> case $$(qy#) of
          (# j#, _, _, _, _, _ #) -> $$(intSame [||i#||] [||j#||])
    ||]
  shiftRight qo# qi# = [||byteStringShiftRight $$(qo#) $$(qi#)||]

-- LogOps Instances
instance LogOps Int# where
  shiftLeft qo# qi# = [||max# ($$(qo#) -# $$(qi#)) 0#||]
  offToInt qi# = [||I# $$(qi#)||]

instance LogOps (# Int#, ts #) where
  shiftLeft qo# _ = qo#
  offToInt qo# = [||case $$(qo#) of (# i#, _ #) -> I# i#||]

instance LogOps Text where
  shiftLeft qo qi# = [||textShiftLeft $$qo (I# $$(qi#))||]
  offToInt qo = [||case $$qo of Text _ off _ -> div off 2||]

instance LogOps UnpackedLazyByteString where
  shiftLeft qo# qi# = [||byteStringShiftLeft $$(qo#) $$(qi#)||]
  offToInt qo# = [||case $$(qo#) of (# i#, _, _, _, _, _ #) -> I# i# ||]

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
