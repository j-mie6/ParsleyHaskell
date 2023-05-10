{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-deprecations #-} --FIXME: remove when Text16 is removed
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
    InputPrep, PositionOps(..), LogOps(..),
    InputOps, next, check, uncons,
#if __GLASGOW_HASKELL__ <= 900
    word8ToWord#,
#endif
    prepare
  ) where

import Data.Array.Base                             (UArray(..), listArray)
import Data.ByteString.Internal                    (ByteString(..))
import Data.Text.Internal                          (Text(..))
import Data.Text.Unsafe                            (iter, Iter(..))
import GHC.Exts                                    (Int(..), Char(..), TYPE, Int#)
import GHC.ForeignPtr                              (ForeignPtr(..))
import GHC.Prim                                    (indexWideCharArray#, readWord8OffAddr#, word2Int#, chr#, touch#, realWorld#, plusAddr#, (+#), (-#))
#if __GLASGOW_HASKELL__ > 900
import GHC.Prim                                    (word8ToWord#)
#else
import GHC.Prim                                    (Word#)
#endif
import Parsley.Internal.Backend.Machine.InputRep   (Stream(..), CharList(..), Text16(..), Rep, UnpackedLazyByteString,
                                                    offWith, emptyUnpackedLazyByteString, intSame, intLess, intAdd,
                                                    offsetText, offWithSame, offWithShiftRight, dropStream,
                                                    textShiftRight, textShiftLeft, byteStringShiftRight,
                                                    byteStringShiftLeft, byteStringNext, max#)
import Parsley.Internal.Common.Utils               (Code)

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString(..))

#if __GLASGOW_HASKELL__ <= 900
{-# INLINE word8ToWord# #-}
word8ToWord# :: Word# -> Word#
word8ToWord# x = x
#endif

prepare :: InputPrep input => Code input -> ((?ops :: InputOps (Rep input)) => Code (Rep input) -> Code r) -> Code r
prepare qinput k = _prepare qinput (\_ops -> let ?ops = _ops in k)

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
  _prepare :: rep ~ Rep input => Code input -> (InputOps rep -> Code rep -> Code r) -> Code r

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
Defines operation used for debugging operations.

@since 1.0.0.0
-}
class LogOps (rep :: TYPE r) where
  {-|
  If possible, shifts the input back several characters.
  This is used to provide the previous input characters for the debugging combinator.

  @since 1.0.0.0
  -}
  shiftLeft :: Code rep -> Int -> Code rep

  {-|
  Advances the input by several characters at a time (existence not included).
  This can be used to check if characters exist at a future point in the input
  in conjunction with `more`.

  @since 2.3.0.0
  -}
  shiftRight :: Code rep -> Int -> Code rep

  {-|
  Converts the represention of the input into an @Int@.

  @since 1.0.0.0
  -}
  offToInt  :: Code rep -> Code Int

{-|
This is a psuedo-typeclass, which depends directly on the values obtained from
`prepare`. Because this instance may depend on local information, it is
synthesised and passed around using @ImplicitParams@.

@since 1.0.0.0
-}
data InputOps (rep :: TYPE r) = InputOps { _next :: !(forall a. Code rep -> (Code Char -> Code rep -> Code a) -> Code a)              -- ^ Read the next character (without checking existence)
                                         , _uncons :: !(forall a. Code rep -> (Code Char -> Code rep -> Code a) -> Code a -> Code a)  -- ^ Read the next character, may check existence
                                         , _ensureN :: !(forall a. Int# -> Code rep -> (Code rep -> Code a) -> Code a -> Code a)      -- ^ Ensure that n characters exist
                                         , _ensureNIsFast :: !Bool                                                                    -- ^ _ensureN is O(1) and not O(n)
                                         }

checkImpl :: forall r (rep :: TYPE r) a. Bool                                    -- ^ is the ensureN argument O(1)?
          -> (Int -> Code rep -> (Code rep -> Code a) -> Code a -> Code a)       -- ^ ensures there are n characters available
          -> (Code rep -> (Code Char -> Code rep -> Code a) -> Code a -> Code a) -- ^ reads the next character if available
          -> (Int -> Int -> Code rep -> (Code rep -> [(Code Char, Code rep)] -> Code a) -> Code a -> Code a)
checkImpl fastEnsureN ensureN uncons n m qi good bad
  | fastEnsureN, n /= 0 = ensureN n qi (go n m qi id . Just) bad
  | otherwise           = go n m qi id Nothing
  where
    go :: Int -> Int -> Code rep -> ([(Code Char, Code rep)] -> [(Code Char, Code rep)]) -> Maybe (Code rep) -> Code a
    go 0 _ qi dcs _ = good qi (dcs [])
    -- Here, we want no more cached characters, so just verify the remaining with shiftRight
    go n 0 qi dcs Nothing = ensureN n qi (\qi' -> good qi' (dcs [])) bad
    -- We've already fastEnsured all the characters, so just feed forward the furthest to fill non-cached
    go _ 0 _ dcs (Just furthest) = good furthest (dcs [])
    -- Cached character wanted, so read it
    -- TODO: the first one can be subject to a sat if we wanted!
    go n m qi dcs furthest = uncons qi (\c qi' -> go (n - 1) (m - 1) qi' (dcs . ((c, qi') :)) furthest) bad

{-|
Wraps around `InputOps` and `_next`.

Given some input and a continuation that accepts new input and a character, it will read
a character off (without checking that it exists!) and feeds it and the remaining input
to the continuation.

@since 1.0.0.0
-}
next :: forall r (rep :: TYPE r) a. (?ops :: InputOps rep) => Code rep -> (Code Char -> Code rep -> Code a) -> Code a
next = _next ?ops

uncons :: forall r (rep :: TYPE r) a. (?ops :: InputOps rep) => Code rep -> (Code Char -> Code rep -> Code a) -> Code a -> Code a
uncons = _uncons ?ops

check :: forall r (rep :: TYPE r) a. (?ops :: InputOps rep) => Int -> Int -> Code rep -> (Code rep -> [(Code Char, Code rep)] -> Code a) -> Code a -> Code a
check = checkImpl (_ensureNIsFast ?ops)
                  (\(I# n) -> _ensureN ?ops n)
                  uncons

{- INSTANCES -}
-- InputPrep Instances
instance InputPrep [Char] where _prepare input = _prepare @(UArray Int Char) [||listArray (0, length $$input-1) $$input||]

instance InputPrep (UArray Int Char) where
  _prepare qinput k = [||
      let !(UArray _ _ (I# size#) input#) = $$qinput
      in $$(k (InputOps (\qi k -> k [||C# (indexWideCharArray# input# $$qi)||] [||$$qi +# 1#||])
                        (\qi k _ -> k [||C# (indexWideCharArray# input# $$qi)||] [||$$qi +# 1#||])
                        (\qn qi -> intLess (intAdd qi (qn -# 1#)) [||size#||])
                        True)
              [||0#||])
    ||]

instance InputPrep Text16 where _prepare qinput = _prepare @Text [|| let Text16 t = $$qinput in t ||]

instance InputPrep ByteString where
  _prepare qinput k = [||
      let PS (ForeignPtr addr# final) (I# off#) (I# size#) = $$qinput
          next i# =
            case readWord8OffAddr# (addr# `plusAddr#` i#) 0# realWorld# of
              (# s', x #) -> case touch# final s' of
                !_ -> (# C# (chr# (word2Int# (word8ToWord# x))), i# +# 1# #)
      in $$(k (InputOps (\qi k -> [|| let !(# c, qi' #) = next $$qi in $$(k [||c||] [||qi'||]) ||])
                        (\qi k _ -> [|| let !(# c, qi' #) = next $$qi in $$(k [||c||] [||qi'||]) ||])
                        (\qn qi -> intLess (intAdd qi (qn -# 1#)) [||size#||])
                        True)
              [||off#||])
    ||]

instance InputPrep CharList where
  _prepare qinput k =  [||
      let CharList input = $$qinput
      in $$(k (InputOps (\qi k -> [|| let !(# i#, c:cs #) = $$qi in $$(k [||c||] [||(# i# +# 1#, cs #)||]) ||])
                        (\qi good bad -> [||
                              case $$qi of
                                (# i#, c : cs #) -> $$(good [||c||] [||(# i# +# 1#, cs #)||])
                                (# _,  [] #)     -> $$bad
                            ||])
                        (\qn qi good bad -> [||
                              case $$(offWithShiftRight [||drop||] qi (qn -# 1#)) of
                                (# _, [] #) -> $$bad
                                cs          -> $$(good [||cs||])
                            ||])
                        False)
              (offWith [||input||]))
    ||]

instance InputPrep Text where
  _prepare qinput k = k (InputOps (\qi k -> [||
                                      let t@(Text arr off unconsumed) = $$qi
                                          !(Iter c d) = iter t 0
                                      in $$(k [||c||] [||Text arr (off + d) (unconsumed - d)||]) ||])
                                  (\qi good bad -> [||
                                      let t@(Text arr off unconsumed) = $$qi
                                      in if unconsumed > 0 then
                                           let !(Iter c d) = iter t 0
                                           in $$(good [||c||] [||Text arr (off + d) (unconsumed - d)||])
                                         else $$bad
                                    ||])
                                  (\qn qi good bad -> [||
                                      case $$(textShiftRight qi (qn -# 1#)) of
                                        Text _ _ 0 -> $$bad
                                        t          -> $$(good [||t||])
                                    ||])
                                  False)
                        qinput

instance InputPrep Lazy.ByteString where
  _prepare qinput k = [||
      let initial :: UnpackedLazyByteString
          initial = case $$qinput of
            Lazy.Chunk (PS (ForeignPtr addr# final) (I# off#) (I# size#)) cs -> (# 0#, addr#, final, off#, size#, cs #)
            Lazy.Empty -> $$(emptyUnpackedLazyByteString [||0#||])
      in $$(k (InputOps (\qi k -> [|| let !(# c, qi' #) = byteStringNext $$qi in $$(k [||c||] [||qi'||]) ||])
                        (\qi good bad -> [||
                            case $$qi of
                              (# _, _, _, _, 0#, _ #) -> $$bad
                              bs                      ->
                                let !(# c, qi' #) = byteStringNext bs in $$(good [||c||] [||qi'||])
                          ||])
                        (\qn qi good bad -> [||
                            case $$(byteStringShiftRight qi (qn -# 1#)) of
                              (# _, _, _, _, 0#, _ #) -> $$bad
                              bs                      -> $$(good [||bs||])
                          ||])
                        False)
              [||initial||])
    ||]

instance InputPrep Stream where
  _prepare qinput k = k (InputOps (\qi k -> [|| let !(# o#, c :> cs #) = $$qi in $$(k [||c||] [||(# o# +# 1#, cs #)||]) ||])
                                  (\qi k _ -> [|| let !(# o#, c :> cs #) = $$qi in $$(k [||c||] [||(# o# +# 1#, cs #)||]) ||])
                                  (\qn qi good _ -> good (offWithShiftRight [||dropStream||] qi (qn -# 1#)))
                                  True)
                        (offWith qinput)

shiftRightInt :: Code Int# -> Int -> Code Int#
shiftRightInt qo# (I# qi#) = [||$$(qo#) +# qi#||]

-- PositionOps Instances
instance PositionOps Int# where same = intSame
instance PositionOps (# Int#, [Char] #) where same = offWithSame
instance PositionOps (# Int#, Stream #) where same = offWithSame
instance PositionOps Text where same qt1 qt2 = [||$$(offsetText qt1) == $$(offsetText qt2)||]
instance PositionOps UnpackedLazyByteString where
  same qx# qy# = [||
      case $$(qx#) of
        (# i#, _, _, _, _, _ #) -> case $$(qy#) of
          (# j#, _, _, _, _, _ #) -> $$(intSame [||i#||] [||j#||])
    ||]

-- LogOps Instances
instance LogOps Int# where
  shiftLeft qo# (I# qi#) = [||max# ($$(qo#) -# qi#) 0#||]
  shiftRight = shiftRightInt
  offToInt qi# = [||I# $$(qi#)||]

instance LogOps (# Int#, [Char] #) where
  shiftLeft qo# _ = qo#
  shiftRight qo# (I# qi#) = offWithShiftRight [||drop||] qo# qi#
  offToInt qo# = [||case $$(qo#) of (# i#, _ #) -> I# i#||]

instance LogOps (# Int#, Stream #) where
  shiftLeft qo# _ = qo#
  shiftRight qo# (I# qi#) = offWithShiftRight [||dropStream||] qo# qi#
  offToInt qo# = [||case $$(qo#) of (# i#, _ #) -> I# i#||]

instance LogOps Text where
  shiftLeft qo (I# qi#) = textShiftLeft qo qi#
  shiftRight qo# (I# qi#) = textShiftRight qo# qi#
  offToInt = offsetText

instance LogOps UnpackedLazyByteString where
  shiftLeft qo# (I# qi#) = byteStringShiftLeft qo# qi#
  shiftRight qo# (I# qi#) = byteStringShiftRight qo# qi#
  offToInt qo# = [||case $$(qo#) of (# i#, _, _, _, _, _ #) -> I# i# ||]
