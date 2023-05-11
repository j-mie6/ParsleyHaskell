{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-deprecations #-} --FIXME: remove when Text16 is removed
{-# LANGUAGE AllowAmbiguousTypes,
             CPP,
             ConstraintKinds,
             FunctionalDependencies,
             ImplicitParams,
             MagicHash,
             RecordWildCards,
             TypeApplications,
             UnboxedTuples #-}
{-# LANGUAGE InstanceSigs #-}
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
    InputPrep, PositionOps(..), LogOps(..), DynOps, asDyn, asSta,
    InputOps, next, check, uncons,
#if __GLASGOW_HASKELL__ <= 900
    word8ToWord#,
#endif
    prepare
  ) where

import Data.Array.Base                             (UArray(..){-, listArray-})
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
import Parsley.Internal.Backend.Machine.InputRep   (Stream(..), CharList(..), Text16(..), DynRep, StaRep, UnpackedLazyByteString,
                                                    StaText(..), PartialStaText(..), staText,
                                                    offWith, emptyUnpackedLazyByteString, intSame, intLess, intAdd,
                                                    offWithShiftRight, dropStream,
                                                    textShiftRight, textShiftLeft, byteStringShiftRight,
                                                    byteStringShiftLeft, byteStringNext, max#)
import Parsley.Internal.Common.Utils               (Code)

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString(..))

#if __GLASGOW_HASKELL__ <= 900
{-# INLINE word8ToWord# #-}
word8ToWord# :: Word# -> Word#
word8ToWord# x = x
#endif

prepare :: InputPrep input => Code input -> ((?ops :: InputOps (StaRep input)) => StaRep input -> Code r) -> Code r
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
  _prepare :: starep ~ StaRep input => Code input -> (InputOps starep -> starep -> Code r) -> Code r

{-|
Defines operations for manipulating offsets for regular use. These are not
tied to the original captured input but instead to the representation of its
offset.

@since 1.0.0.0
-}
class PositionOps rep where
  {-|
  Compares two "input"s for equality. In reality this usually means an offset
  present in the @rep@.

  @since 1.0.0.0
  -}
  same :: rep -> rep -> Code Bool

type DynOps o = DynOps_ (DynRep o) (StaRep o)

asDyn :: forall input. DynOps input => StaRep input -> Code (DynRep input)
asDyn = _asDyn

asSta :: forall input a. DynOps input => Code (DynRep input) -> (StaRep input -> Code a) -> Code a
asSta = _asSta

class DynOps_ (dynrep :: TYPE r) starep | dynrep -> starep, starep -> dynrep where
  _asDyn :: starep -> Code dynrep
  _asSta :: Code dynrep -> (starep -> Code a) -> Code a

{-|
Defines operation used for debugging operations.

@since 1.0.0.0
-}
class LogOps rep where
  {-|
  If possible, shifts the input back several characters.
  This is used to provide the previous input characters for the debugging combinator.

  @since 1.0.0.0
  -}
  shiftLeft :: rep -> Int -> (rep -> Code a) -> Code a

  {-|
  Advances the input by several characters at a time (existence not included).
  This can be used to check if characters exist at a future point in the input
  in conjunction with `more`.

  @since 2.3.0.0
  -}
  shiftRight :: rep -> Int -> (rep -> Code a) -> Code a

  {-|
  Converts the represention of the input into an @Int@.

  @since 1.0.0.0
  -}
  offToInt  :: rep -> Code Int

{-|
This is a psuedo-typeclass, which depends directly on the values obtained from
`prepare`. Because this instance may depend on local information, it is
synthesised and passed around using @ImplicitParams@.

@since 1.0.0.0
-}
data InputOps rep = InputOps { _next :: !(forall a. rep -> (Code Char -> rep -> Code a) -> Code a)              -- ^ Read the next character (without checking existence)
                             , _uncons :: !(forall a. rep -> (Code Char -> rep -> Code a) -> Code a -> Code a)  -- ^ Read the next character, may check existence
                             , _ensureN :: !(forall a. Int# -> rep -> (rep -> Code a) -> Code a -> Code a)      -- ^ Ensure that n characters exist
                             , _ensureNIsFast :: !Bool                                                                    -- ^ _ensureN is O(1) and not O(n)
                             }

checkImpl :: forall rep a. Bool                                        -- ^ is the ensureN argument O(1)?
          -> (Int -> rep -> (rep -> Code a) -> Code a -> Code a)       -- ^ ensures there are n characters available
          -> (rep -> (Code Char -> rep -> Code a) -> Code a -> Code a) -- ^ reads the next character if available
          -> (Int -> Int -> rep -> Maybe (Code Char -> Code a -> Code a) -> (rep -> [(Code Char, rep)] -> Code a) -> Code a -> Code a)
checkImpl fastEnsureN ensureN uncons n m qi headCheck good bad
  | fastEnsureN, n /= 0 = ensureN n qi (go n m qi id headCheck . Just) bad
  | otherwise           = go n m qi id headCheck Nothing
  where
    go :: Int -> Int -> rep -> ([(Code Char, rep)] -> [(Code Char, rep)]) -> Maybe (Code Char -> Code a -> Code a) -> Maybe rep -> Code a
    go 0 _ qi dcs _ _ = good qi (dcs [])
    -- Here, we want no more cached characters, so just verify the remaining with shiftRight
    go n 0 qi dcs _ Nothing = ensureN n qi (\qi' -> good qi' (dcs [])) bad
    -- We've already fastEnsured all the characters, so just feed forward the furthest to fill non-cached
    go _ 0 _ dcs _ (Just furthest) = good furthest (dcs [])
    -- Cached character wanted, so read it
    go n m qi dcs headCheck furthest = flip (uncons qi) bad $ \c qi' ->
      maybe id ($ c) headCheck $ -- if there is a headCheck available, perform it here DON'T pass it on
      go (n - 1) (m - 1) qi' (dcs . ((c, qi') :)) Nothing furthest

{-|
Wraps around `InputOps` and `_next`.

Given some input and a continuation that accepts new input and a character, it will read
a character off (without checking that it exists!) and feeds it and the remaining input
to the continuation.

@since 1.0.0.0
-}
next :: forall rep a. (?ops :: InputOps rep) => rep -> (Code Char -> rep -> Code a) -> Code a
next = _next ?ops

uncons :: forall rep a. (?ops :: InputOps rep) => rep -> (Code Char -> rep -> Code a) -> Code a -> Code a
uncons = _uncons ?ops

check :: forall rep a. (?ops :: InputOps rep) => Int -> Int -> rep -> Maybe (Code Char -> Code a -> Code a) -> (rep -> [(Code Char, rep)] -> Code a) -> Code a -> Code a
check = checkImpl (_ensureNIsFast ?ops)
                  (\(I# n) -> _ensureN ?ops n)
                  uncons

{- INSTANCES -}
-- InputPrep Instances
instance InputPrep String where
  _prepare qinput k = _asSta (offWith qinput) $
    k (InputOps (\(qi, qcs) k -> [|| let c:cs' = $$qcs in $$(k [||c||] ([||$$qi +# 1#||], [||cs'||])) ||])
                (\(qi, qcs) good bad -> [||
                      case $$qcs of
                        c : cs' -> $$(good [||c||] ([||$$qi +# 1#||], [||cs'||]))
                        []     -> $$bad
                    ||])
                (\qn qinput good bad -> let (qi', qcs') = offWithShiftRight [||drop||] qinput (qn -# 1#) in [||
                      case $$qcs' of
                        [] -> $$bad
                        cs -> $$(good (qi', [||cs||]))
                    ||])
                False)

instance InputPrep ByteString where
  _prepare qinput k = [||
      let PS (ForeignPtr addr# final) (I# off#) (I# size#) = $$qinput
          next i# =
            case readWord8OffAddr# (addr# `plusAddr#` i#) 0# realWorld# of
              (# s', x #) -> case touch# final s' of
                !_ -> (# C# (chr# (word2Int# (word8ToWord# x))), i# +# 1# #)
      in $$(k (InputOps (\qi k -> [|| let !(# c, qi' #) = next $$qi in $$(k [||c||] [||qi'||]) ||])
                        (\qi k _ -> [|| let !(# c, qi' #) = next $$qi in $$(k [||c||] [||qi'||]) ||]) -- always guarded by fastEnsureN
                        (\qn qi -> intLess (intAdd qi (qn -# 1#)) [||size#||])
                        True)
              [||off#||])
    ||]

instance InputPrep Text where
  _prepare qinput k = _asSta qinput $
    k (InputOps (\pt k -> staText pt $ \t@StaText{..} -> [||
                    let !(Iter c d) = iter $$origText 0
                        !unconsumed' = $$unconsumedText - d
                        !off'        = $$offText + d
                    in $$(k [||c||] (StaT $ t {origText = [||Text $$arrText off' unconsumed'||],
                                               offText = [||off'||],
                                               unconsumedText = [||unconsumed'||]})) ||])
                (\pt good bad -> staText pt $ \t@StaText{..} -> [||
                    if $$unconsumedText > 0 then
                      let !(Iter c d) = iter $$origText 0
                          !unconsumed' = $$unconsumedText - d
                          !off'        = $$offText + d
                      in $$(good [||c||] (StaT $ t {origText = [||Text $$arrText off' unconsumed'||],
                                                    offText = [||off'||],
                                                    unconsumedText = [||unconsumed'||]}))
                    else $$bad
                  ||])
                (\qn pt good bad -> staText pt $ \StaText{..} -> [|| -- could be improved, I guess?
                    case $$(textShiftRight origText (qn -# 1#)) of
                      Text _ _ 0                -> $$bad
                      t@(Text _ off unconsumed) -> $$(good (StaT $ StaText [||t||] arrText [||off||] [||unconsumed||]))
                  ||])
                False)

--instance InputPrep String where _prepare input = _prepare @(UArray Int Char) [||listArray (0, length $$input-1) $$input||]
instance InputPrep (UArray Int Char) where
  _prepare qinput k = [||
      let !(UArray _ _ (I# size#) input#) = $$qinput
      in $$(k (InputOps (\qi k -> k [||C# (indexWideCharArray# input# $$qi)||] [||$$qi +# 1#||])
                        (\qi k _ -> k [||C# (indexWideCharArray# input# $$qi)||] [||$$qi +# 1#||]) -- always guarded by fastEnsureN
                        (\qn qi -> intLess (intAdd qi (qn -# 1#)) [||size#||])
                        True)
              [||0#||])
    ||]

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
  _prepare qinput k = _asSta (offWith qinput) $
    k (InputOps (\(qo, qcs) k -> [|| let c :> cs' = $$qcs in $$(k [||c||] ([||$$qo +# 1#||], [||cs'||])) ||])
                (\(qo, qcs) k _ -> [|| let c :> cs' = $$qcs in $$(k [||c||] ([||$$qo +# 1#||], [||cs'||])) ||])
                (\qn qinput good _ -> good (offWithShiftRight [||dropStream||] qinput (qn -# 1#)))
                True)


instance InputPrep Text16 where _prepare qinput = _prepare @Text [|| let Text16 t = $$qinput in t ||]
instance InputPrep CharList where _prepare qinput = _prepare @String [|| let CharList cs = $$qinput in cs ||]

shiftRightInt :: Code Int# -> Int -> Code Int#
shiftRightInt qo# (I# qi#) = [||$$(qo#) +# qi#||]

-- PositionOps Instances
instance PositionOps (Code Int#) where same = intSame
instance PositionOps (Code Int#, ts) where same (o1, _) (o2, _) = intSame o1 o2
--instance PositionOps (Code Int#, Code Stream) where same = offWithSame
instance PositionOps PartialStaText where
  same pt1 pt2 = staText pt1 $ \qt1 -> staText pt2 $ \qt2 -> [||$$(offText qt1) == $$(offText qt2)||]
instance PositionOps (Code UnpackedLazyByteString) where
  same qx# qy# = [||
      case $$(qx#) of
        (# i#, _, _, _, _, _ #) -> case $$(qy#) of
          (# j#, _, _, _, _, _ #) -> $$(intSame [||i#||] [||j#||])
    ||]

-- DynOps Instances
instance DynOps_ Int# (Code Int#) where
  _asDyn = id
  _asSta = flip ($)

instance DynOps_ (# Int#, ts #) (Code Int#, Code ts) where
  _asDyn (qo, qcs) = [||(# $$qo, $$qcs #)||]
  _asSta qi k = [|| let (# o, cs #) = $$qi in $$(k ([||o||], [||cs||])) ||]

instance DynOps_ Text PartialStaText where
  _asDyn (StaT t) = origText t
  _asDyn (DynT t) = t
  _asSta qt k = k (DynT qt)

instance DynOps_ UnpackedLazyByteString (Code UnpackedLazyByteString) where
  _asDyn = id
  _asSta = flip ($)

-- LogOps Instances
instance LogOps (Code Int#) where
  shiftLeft qo# (I# qi#) k = k [||max# ($$(qo#) -# qi#) 0#||]
  shiftRight qo# qi# k = k (shiftRightInt qo# qi#)
  offToInt qi# = [||I# $$(qi#)||]

instance LogOps (Code Int#, Code String) where
  shiftLeft qinput _ k = k qinput
  shiftRight qinput (I# qi#) k = k (offWithShiftRight [||drop||] qinput qi#)
  offToInt (qo, _) = [||I# $$qo||]

instance LogOps (Code Int#, Code Stream) where
  shiftLeft qinput _ k = k qinput
  shiftRight qinput (I# qi#) k = k (offWithShiftRight [||dropStream||] qinput qi#)
  offToInt (qo, _) = [||I# $$qo||]

instance LogOps PartialStaText where
  shiftLeft pt (I# qi#) k = staText pt $ \StaText{..} -> k (DynT (textShiftLeft origText qi#))
  shiftRight pt (I# qi#) k = staText pt $ \StaText{..} -> k (DynT (textShiftRight origText qi#))
  offToInt pt = staText pt offText

instance LogOps (Code UnpackedLazyByteString) where
  shiftLeft qo# (I# qi#) k = k (byteStringShiftLeft qo# qi#)
  shiftRight qo# (I# qi#) k = k (byteStringShiftRight qo# qi#)
  offToInt qo# = [||case $$(qo#) of (# i#, _, _, _, _, _ #) -> I# i# ||]
