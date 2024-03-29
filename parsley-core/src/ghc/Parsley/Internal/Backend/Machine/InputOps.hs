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
import GHC.Prim                                    (indexWideCharArray#, readWord8OffAddr#, word2Int#, chr#, touch#, realWorld#, plusAddr#, (-#))
#if __GLASGOW_HASKELL__ > 900
import GHC.Prim                                    (word8ToWord#)
#else
import GHC.Prim                                    (Word#)
#endif
import Parsley.Internal.Backend.Machine.InputRep   (Stream(..), CharList(..), Text16(..), DynRep, StaRep, UnpackedLazyByteString,
                                                    StaText(..), PartialStaText(..), staText, PartialStaOffWith(..), staOffWith,
                                                    PartialStaOffset(..), dynOffset,
                                                    emptyUnpackedLazyByteString, intSame, intLess, intAdd, intSubNonNeg,
                                                    offWithShiftRight, dropStream,
                                                    textShiftRight, textShiftLeft, byteStringShiftRight, offsetText,
                                                    byteStringShiftLeft, byteStringNext)
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

asSta :: forall input. DynOps input => Code (DynRep input) -> StaRep input
asSta = _asSta

class DynOps_ (dynrep :: TYPE r) starep | dynrep -> starep, starep -> dynrep where
  _asDyn :: starep -> Code dynrep
  _asSta :: Code dynrep -> starep

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
                             , _ensureN :: !(forall a. Int -> rep -> (rep -> Code a) -> Code a -> Code a)      -- ^ Ensure that n characters exist
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
                  (_ensureN ?ops)
                  uncons

{- INSTANCES -}
-- InputPrep Instances
instance InputPrep String where
  _prepare qinput k =
    k (InputOps (\pocs k -> staOffWith pocs $ \po qcs -> [|| let c:cs' = $$qcs in $$(k [||c||] (StaOW (intAdd po 1) [||cs'||])) ||])
                (\pocs good bad -> staOffWith pocs $ \po qcs -> [||
                      case $$qcs of
                        c : cs' -> $$(good [||c||] (StaOW (intAdd po 1) [||cs'||]))
                        []     -> $$bad
                    ||])
                (\n pocs good bad -> staOffWith pocs $ \qo qcs -> let (qo', qcs') = offWithShiftRight [||drop||] qo qcs (n - 1) in [||
                      case $$qcs' of
                        [] -> $$bad
                        cs -> $$(good (StaOW qo' [||cs||]))
                    ||])
                False)
      (StaOW (_asSta [||0#||]) qinput)

instance InputPrep ByteString where
  _prepare qinput k = [||
      let PS (ForeignPtr addr# final) (I# off#) (I# size#) = $$qinput
          next i# =
            case readWord8OffAddr# (addr# `plusAddr#` i#) 0# realWorld# of
              (# s', x #) -> case touch# final s' of
                !_ -> chr# (word2Int# (word8ToWord# x))
      in $$(k (InputOps (\qi k -> [|| let !c# = next $$(dynOffset qi) in $$(k [||C# c#||] (intAdd qi 1)) ||])
                        (\qi k _ -> [|| let !c# = next $$(dynOffset qi) in $$(k [||C# c#||] (intAdd qi 1)) ||]) -- always guarded by fastEnsureN
                        (\n qi k -> intLess (dynOffset (intAdd qi (n - 1))) [||size#||] (k qi))
                        True)
              (_asSta [||off#||]))
    ||]

instance InputPrep Text where
  _prepare qinput k =
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
                (\(I# n) pt good bad -> staText pt $ \StaText{..} -> [|| -- could be improved, I guess?
                    case $$(textShiftRight origText (n -# 1#)) of
                      Text _ _ 0                -> $$bad
                      t@(Text _ off unconsumed) -> $$(good (StaT $ StaText [||t||] arrText [||off||] [||unconsumed||]))
                  ||])
                False)
      (DynT qinput)

--instance InputPrep String where _prepare input = _prepare @(UArray Int Char) [||listArray (0, length $$input-1) $$input||]
instance InputPrep (UArray Int Char) where
  _prepare qinput k = [||
      let !(UArray _ _ (I# size#) input#) = $$qinput
      in $$(k (InputOps (\qi k -> k [||C# (indexWideCharArray# input# $$(dynOffset qi))||] (intAdd qi 1))
                        (\qi k _ -> k [||C# (indexWideCharArray# input# $$(dynOffset qi))||] (intAdd qi 1)) -- always guarded by fastEnsureN
                        (\n qi k -> intLess (dynOffset (intAdd qi (n - 1))) [||size#||] (k qi))
                        True)
              (_asSta [||0#||]))
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
                        (\(I# n) qi good bad -> [||
                            case $$(byteStringShiftRight qi (n -# 1#)) of
                              (# _, _, _, _, 0#, _ #) -> $$bad
                              bs                      -> $$(good [||bs||])
                          ||])
                        False)
              [||initial||])
    ||]

instance InputPrep Stream where
  _prepare qinput k =
    k (InputOps (\pocs k -> staOffWith pocs $ \po qcs -> [|| let c :> cs' = $$qcs in $$(k [||c||] (StaOW (intAdd po 1) [||cs'||])) ||])
                (\pocs k _ -> staOffWith pocs $ \po qcs -> [|| let c :> cs' = $$qcs in $$(k [||c||] (StaOW (intAdd po 1) [||cs'||])) ||])
                (\n pocs good _ -> staOffWith pocs $ \qo qcs -> good (uncurry StaOW $ offWithShiftRight [||dropStream||] qo qcs (n - 1)))
                True)
      (StaOW (_asSta [||0#||]) qinput)


instance InputPrep Text16 where _prepare qinput = _prepare @Text [|| let Text16 t = $$qinput in t ||]
instance InputPrep CharList where _prepare qinput = _prepare @String [|| let CharList cs = $$qinput in cs ||]

-- PositionOps Instances
instance PositionOps PartialStaOffset where same po (StaO qo' n) = intSame (dynOffset (intAdd po (negate n))) qo'
instance PositionOps (PartialStaOffWith ts) where
  same pocs1 pocs2 = staOffWith pocs1 $ \po _ -> staOffWith pocs2 $ \po' _ -> same po po'
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
instance DynOps_ Int# PartialStaOffset where
  _asDyn = dynOffset
  _asSta = flip StaO 0

instance DynOps_ (# Int#, ts #) (PartialStaOffWith ts) where
  _asDyn (StaOW qo qcs) = [||(# $$(dynOffset qo), $$qcs #)||]
  _asDyn (DynOW qocs) = qocs
  _asSta = DynOW

instance DynOps_ Text PartialStaText where
  _asDyn (StaT t) = origText t
  _asDyn (DynT t) = t
  _asSta = DynT

instance DynOps_ UnpackedLazyByteString (Code UnpackedLazyByteString) where
  _asDyn = id
  _asSta = id

-- LogOps Instances
instance LogOps PartialStaOffset where
  shiftLeft po n k = k (intSubNonNeg po n)
  shiftRight po n k = k (intAdd po n)
  offToInt pi = [||I# $$(dynOffset pi)||]

instance LogOps (PartialStaOffWith String) where
  shiftLeft pocs _ k = k pocs
  shiftRight pocs n k = staOffWith pocs $ \qo qcs -> k (uncurry StaOW $ offWithShiftRight [||drop||] qo qcs n)
  offToInt pocs = staOffWith pocs $ \qo _ -> [||I# $$(dynOffset qo)||]

instance LogOps (PartialStaOffWith Stream) where
  shiftLeft pocs _ k = k pocs
  shiftRight pocs n k = staOffWith pocs $ \qo qcs -> k (uncurry StaOW $ offWithShiftRight [||dropStream||] qo qcs n)
  offToInt pocs = staOffWith pocs $ \qo _ -> [||I# $$(dynOffset qo)||]

instance LogOps PartialStaText where
  shiftLeft pt (I# qi#) k = staText pt $ \StaText{..} -> k (DynT (textShiftLeft origText qi#))
  shiftRight pt (I# n#) k = staText pt $ \StaText{..} -> k (DynT (textShiftRight origText n#))
  offToInt = offsetText

instance LogOps (Code UnpackedLazyByteString) where
  shiftLeft qo# (I# qi#) k = k (byteStringShiftLeft qo# qi#)
  shiftRight qo# (I# qi#) k = k (byteStringShiftRight qo# qi#)
  offToInt qo# = [||case $$(qo#) of (# i#, _, _, _, _, _ #) -> I# i# ||]
