{-# OPTIONS_HADDOCK show-extensions #-}
{-# OPTIONS_GHC -Wno-deprecations #-} --FIXME: remove when Text16 is removed
{-# LANGUAGE CPP,
             MagicHash,
             TypeFamilies,
             UnboxedTuples,
             StandaloneKindSignatures #-}
{-|
Module      : Parsley.Internal.Backend.Machine.InputRep
Description : Internal representations of input and miscellaneous operations.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the translation from user input type to the
underlying parsley representation of it, as well as some miscellaneous
functions for working with specific types of input (these do not appear
in the rest of the machinery, but in "Parsley.Internal.Backend.Machine.InputOps"
and potentially the generated code).

@since 1.0.0.0
-}
module Parsley.Internal.Backend.Machine.InputRep (
    -- * Representation Type-Families
    Rep, RepKind,
    -- * @Int#@ Operations
    intSame, intLess, intLess', intAdd, min#, max#,
    -- * @Offwith@ Operations
    OffWith, offWith, offWithSame, offWithShiftRight,
    --OffWithStreamAnd(..),
    -- * @LazyByteString@ Operations
    UnpackedLazyByteString, emptyUnpackedLazyByteString,
    -- * @Stream@ Operations
    dropStream,
    -- * @Text@ Operations
    offsetText,
    -- * Crucial Exposed Functions
    {- |
    These functions must be exposed, since they can appear
    in the generated code.
    -}
    textShiftRight, textShiftLeft, {-textEnsureN,-} textNonEmpty,
    byteStringShiftRight, byteStringShiftLeft, byteStringMore, byteStringNext, --byteStringEnsureN,
    -- * Re-exports
    module Parsley.Internal.Core.InputTypes
  ) where

import Data.Array.Unboxed                (UArray)
import Data.ByteString.Internal          (ByteString(..))
import Data.Kind                         (Type)
import Data.Text.Internal                (Text(..))
import Data.Text.Unsafe                  (iter_, reverseIter_)
import GHC.Exts                          (Int(..), Char(..), TYPE, RuntimeRep(..), (==#), (<#), (+#), (-#), isTrue#)
#if __GLASGOW_HASKELL__ > 900
import GHC.Exts                          (LiftedRep)
#endif
import GHC.ForeignPtr                    (ForeignPtr(..), ForeignPtrContents)
import GHC.Prim                          (Int#, Addr#, nullAddr#, readWord8OffAddr#, word2Int#, chr#, touch#, realWorld#)
#if __GLASGOW_HASKELL__ > 900
import GHC.Prim                          (word8ToWord#)
#else
import GHC.Prim                          (Word#)
#endif
import Parsley.Internal.Common.Utils     (Code)
import Parsley.Internal.Core.InputTypes  (Text16(..), CharList(..), Stream(..))

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString(..))

#if __GLASGOW_HASKELL__ <= 900
{-# INLINE word8ToWord# #-}
word8ToWord# :: Word# -> Word#
word8ToWord# x = x
#endif

{- Representation Types -}
{-|
This allows types like @String@ and @Stream@ to be manipulated
more efficiently by packaging them along with an offset which can
be used for quicker comparisons.

@since 1.0.0.0
-}
type OffWith ts = (# Int#, ts #)

{-|
This type unpacks /lazy/ `Lazy.ByteString`s for efficiency.

@since 1.0.0.0
-}
type UnpackedLazyByteString = (#
    Int#,
    Addr#,
    ForeignPtrContents,
    Int#,
    Int#,
    Lazy.ByteString
  #)

{-|
Initialises an `OffWith` type, with a starting offset of @0@.

@since 1.0.0.0
-}
offWith :: Code ts -> Code (OffWith ts)
offWith qts = [||(# 0#, $$qts #)||]

{-|
Initialises an `UnpackedLazyByteString` with a specified offset.
This offset varies as each lazy chunk is consumed.

@since 1.0.0.0
-}
emptyUnpackedLazyByteString :: Code Int# -> Code UnpackedLazyByteString
emptyUnpackedLazyByteString qi# = [|| (# $$(qi#), nullAddr#, error "nullForeignPtr", 0#, 0#, Lazy.Empty #) ||]

{- Representation Mappings -}
-- NOTE: When a new input type is added here, it needs an Input instance in Parsley.Backend.Machine
{-|
The representation type of an input `Rep`, does not have to be a lifted type. To match a
representation of an input with the correct kind, this type family must be used.

@since 1.0.0.0
-}
type RepKind :: Type -> RuntimeRep
type family RepKind input where
  RepKind [Char] = IntRep
  RepKind (UArray Int Char) = IntRep
  RepKind Text16 = LiftedRep
  RepKind ByteString = IntRep
  RepKind Text = LiftedRep
  RepKind Lazy.ByteString = 'TupleRep '[IntRep, AddrRep, LiftedRep, IntRep, IntRep, LiftedRep]
  RepKind CharList = 'TupleRep '[IntRep, LiftedRep]
  RepKind Stream = 'TupleRep '[IntRep, LiftedRep]

{-|
This type family relates a user input type with the underlying parsley
representation, which is significantly more efficient to work with.
Most parts of the machine work with `Rep`.

@since 1.0.0.0
-}
type Rep :: forall (rep :: Type) -> TYPE (RepKind rep)
type family Rep input where
  Rep [Char] = Int#
  Rep (UArray Int Char) = Int#
  Rep Text16 = Text
  Rep ByteString = Int#
  Rep Text = Text
  Rep Lazy.ByteString = UnpackedLazyByteString
  Rep CharList = (# Int#, String #)
  Rep Stream = (# Int#, Stream #)

{- Generic Representation Operations -}
{-|
Verifies that two `Int#`s are equal.

@since 1.0.0.0
-}
intSame :: Code Int# -> Code Int# -> Code Bool
intSame qi# qj# = [||isTrue# ($$(qi#) ==# $$(qj#))||]

{-|
Is the first argument is less than the second?

@since 1.0.0.0
-}
intLess :: Code Int# -> Code Int# -> Code Bool
intLess qi# qj# = [||isTrue# ($$(qi#) <# $$(qj#))||]

intLess' :: Code Int# -> Code Int# -> (Code Int# -> Code a) -> Code a -> Code a
intLess' qi# qj# yes no = [||
    case $$(qi#) <# $$(qj#) of
      1# -> $$(yes qi#)
      0# -> $$no
  ||]

intAdd :: Code Int# -> Int# -> Code Int#
intAdd qx 0# = qx
intAdd qx qn = [||$$qx +# qn||]

{-|
Extracts the offset from `Text`.

@since 1.0.0.0
-}
offsetText :: Code Text -> Code Int
offsetText qt = [||case $$qt of Text _ off _ -> off||]

{-|
Compares the bundled offsets of two `OffWith`s are equal: does not
need to inspect the corresponding input.

@since 1.0.0.0
-}
offWithSame :: Code (OffWith ts) -> Code (OffWith ts) -> Code Bool
offWithSame qi# qj# = [||
    case $$(qi#) of
      (# i#, _ #) -> case $$(qj#) of
        (# j#, _ #) -> $$(intSame [||i#||] [||j#||])
  ||]

{-|
Shifts an `OffWith` to the right, taking care to also drop tokens from the
companion input.

@since 1.0.0.0
-}
offWithShiftRight :: Code (Int -> ts -> ts) -- ^ A @drop@ function for underlying input.
                  -> Code (OffWith ts)      -- ^ The `OffWith` to shift.
                  -> Int#                   -- ^ How much to shift by.
                  -> Code (OffWith ts)
offWithShiftRight drop qo# qi# = [||
    case $$(qo#) of (# o#, ts #) -> (# o# +# qi#, $$drop (I# qi#) ts #)
  ||]

{-|
Drops tokens off of a `Stream`.

@since 1.0.0.0
-}
dropStream :: Int -> Stream -> Stream
dropStream 0 cs = cs
dropStream n (_ :> cs) = dropStream (n-1) cs

{-|
Drops tokens off of `Text`.

@since 1.0.0.0
-}
{-# INLINABLE textShiftRight #-}
textShiftRight :: Text -> Int# -> Text
textShiftRight (Text arr off unconsumed) !i = go i arr off unconsumed
  where
    go 0# !arr !off !unconsumed = Text arr off unconsumed
    go n !arr !off !unconsumed
      | unconsumed > 0 = let !d = iter_ (Text arr off unconsumed) 0
                         in go (n -# 1#) arr (off + d) (unconsumed - d)
      | otherwise = Text arr off unconsumed

{-# INLINABLE textNonEmpty #-}
textNonEmpty :: Text -> Bool
textNonEmpty (Text _ _ 0) = False
textNonEmpty _            = True

{-|
Rewinds input consumption on `Text` where the input is still available (i.e. in the same chunk).

@since 1.0.0.0
-}
textShiftLeft :: Text -> Int# -> Text
textShiftLeft (Text arr off unconsumed) i = go i off unconsumed
  where
    go 0# off' unconsumed' = Text arr off' unconsumed'
    go n off' unconsumed'
      | off' > 0 = let !d = reverseIter_ (Text arr off' unconsumed') 0 in go (n -# 1#) (off' + d) (unconsumed' - d)
      | otherwise = Text arr off' unconsumed'

{-# INLINE emptyUnpackedLazyByteString' #-}
emptyUnpackedLazyByteString' :: Int# -> UnpackedLazyByteString
emptyUnpackedLazyByteString' i# = (# i#, nullAddr#, error "nullForeignPtr", 0#, 0#, Lazy.Empty #)

{-# INLINABLE byteStringNext #-}
byteStringNext :: UnpackedLazyByteString -> (# Char, UnpackedLazyByteString #)
byteStringNext (# i#, addr#, final, off#, size#, cs #) =
  case readWord8OffAddr# addr# off# realWorld# of
    (# s', x #) -> case touch# final s' of
      !_ -> (# C# (chr# (word2Int# (word8ToWord# x))),
          if I# size# /= 1 then (# i# +# 1#, addr#, final, off# +# 1#, size# -# 1#, cs #)
          else case cs of
            Lazy.Chunk (PS (ForeignPtr addr'# final') (I# off'#) (I# size'#)) cs' ->
              (# i# +# 1#, addr'#, final', off'#, size'#, cs' #)
            Lazy.Empty -> emptyUnpackedLazyByteString' (i# +# 1#)
        #)

{-# INLINE byteStringMore #-}
byteStringMore :: UnpackedLazyByteString -> Bool
byteStringMore (# _, _, _, _, 0#, _ #) = False
byteStringMore (# _, _, _, _, _, _ #) = True

{-|
Drops tokens off of a lazy `Lazy.ByteString`.

@since 1.0.0.0
-}
{-# INLINABLE byteStringShiftRight #-}
byteStringShiftRight :: UnpackedLazyByteString -> Int# -> UnpackedLazyByteString
byteStringShiftRight (# i#, addr#, final, off#, size#, cs #) j#
  | isTrue# (j# <# size#)  = (# i# +# j#, addr#, final, off# +# j#, size# -# j#, cs #)
  | otherwise = case cs of
    Lazy.Chunk (PS (ForeignPtr addr'# final') (I# off'#) (I# size'#)) cs' -> byteStringShiftRight (# i# +# size#, addr'#, final', off'#, size'#, cs' #) (j# -# size#)
    Lazy.Empty -> emptyUnpackedLazyByteString' (i# +# size#)

{-|
Rewinds input consumption on a lazy `Lazy.ByteString` if input is still available (within the same chunk).

@since 1.0.0.0
-}
{-# INLINABLE byteStringShiftLeft #-}
byteStringShiftLeft :: UnpackedLazyByteString -> Int# -> UnpackedLazyByteString
byteStringShiftLeft (# i#, addr#, final, off#, size#, cs #) j# =
  let d# = min# off# j#
  in (# i# -# d#, addr#, final, off# -# d#, size# +# d#, cs #)

{-|
Finds the minimum of two `Int#` values.

@since 1.0.0.0
-}
{-# INLINABLE min# #-}
min# :: Int# -> Int# -> Int#
min# i# j# = case i# <# j# of
  0# -> j#
  _  -> i#

{-|
Finds the maximum of two `Int#` values.

@since 1.0.0.0
-}
{-# INLINABLE max# #-}
max# :: Int# -> Int# -> Int#
max# i# j# = case i# <# j# of
  0# -> i#
  _  -> j#
