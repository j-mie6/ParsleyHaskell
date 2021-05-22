{-# LANGUAGE MagicHash,
             TypeFamilies,
             UnboxedTuples,
             StandaloneKindSignatures #-}
module Parsley.Internal.Backend.Machine.InputRep (
    Rep, RepKind,
    intSame, intLess, min#, max#,
    OffWith, offWith, offWithSame, offWithShiftRight,
    --OffWithStreamAnd(..),
    UnpackedLazyByteString, emptyUnpackedLazyByteString,
    Stream, dropStream,
    offsetText,
    representationTypes,
    -- These must be exposed
    textShiftRight, textShiftLeft,
    byteStringShiftRight, byteStringShiftLeft
  ) where

import Data.Array.Unboxed                (UArray)
import Data.ByteString.Internal          (ByteString(..))
import Data.Kind                         (Type)
import Data.Text.Internal                (Text(..))
import Data.Text.Unsafe                  (iter_, reverseIter_)
import GHC.Exts                          (Int(..), TYPE, RuntimeRep(..), (==#), (<#), (+#), (-#), isTrue#)
import GHC.ForeignPtr                    (ForeignPtr(..), ForeignPtrContents)
import GHC.Prim                          (Int#, Addr#, nullAddr#)
import Parsley.Internal.Common.Utils     (Code)
import Parsley.Internal.Core.InputTypes  (Text16, CharList, Stream(..))

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString(..))
import qualified Language.Haskell.TH           as TH   (Q, Type)

{- Representation Types -}
type OffWith ts = (# Int#, ts #)
--data OffWithStreamAnd ts = OffWithStreamAnd {-# UNPACK #-} !Int !Stream ts
type UnpackedLazyByteString = (#
    Int#,
    Addr#,
    ForeignPtrContents,
    Int#,
    Int#,
    Lazy.ByteString
  #)

representationTypes :: [TH.Q TH.Type]
representationTypes = [[t|[Char]|], [t|UArray Int Char|], [t|Text16|], [t|ByteString|], [t|CharList|], [t|Stream|], [t|Lazy.ByteString|], [t|Text|]]

offWith :: Code ts -> Code (OffWith ts)
offWith qts = [||(# 0#, $$qts #)||]

emptyUnpackedLazyByteString :: Code Int# -> Code UnpackedLazyByteString
emptyUnpackedLazyByteString qi# = [|| (# $$(qi#), nullAddr#, error "nullForeignPtr", 0#, 0#, Lazy.Empty #) ||]

{- Representation Mappings -}
-- When a new input type is added here, it needs an Input instance in Parsley.Backend.Machine
type RepKind :: Type -> RuntimeRep
type family RepKind input where
  RepKind [Char] = IntRep
  RepKind (UArray Int Char) = IntRep
  RepKind Text16 = IntRep
  RepKind ByteString = IntRep
  RepKind Text = LiftedRep
  RepKind Lazy.ByteString = 'TupleRep '[IntRep, AddrRep, LiftedRep, IntRep, IntRep, LiftedRep]
  RepKind CharList = 'TupleRep '[IntRep, LiftedRep]
  RepKind Stream = 'TupleRep '[IntRep, LiftedRep]
  --RepKind (OffWithStreamAnd _) = 'TupleRep '[IntRep, LiftedRep, LiftedRep] --REMOVE
  --RepKind (Text, Stream) = 'TupleRep '[LiftedRep, LiftedRep] --REMOVE

type Rep :: forall (rep :: Type) -> TYPE (RepKind rep)
type family Rep input where
  Rep [Char] = Int#
  Rep (UArray Int Char) = Int#
  Rep Text16 = Int#
  Rep ByteString = Int#
  Rep Text = Text
  Rep Lazy.ByteString = UnpackedLazyByteString
  Rep CharList = (# Int#, String #)
  Rep Stream = (# Int#, Stream #)
  --Rep (OffWithStreamAnd ts) = (# Int#, Stream, ts #)
  --Rep (Text, Stream) = (# Text, Stream #)

{- Generic Representation Operations -}
intSame :: Code Int# -> Code Int# -> Code Bool
intSame qi# qj# = [||isTrue# ($$(qi#) ==# $$(qj#))||]

intLess :: Code Int# -> Code Int# -> Code Bool
intLess qi# qj# = [||isTrue# ($$(qi#) <# $$(qj#))||]

offsetText :: Code Text -> Code Int
offsetText qt = [||case $$qt of Text _ off _ -> off||]

offWithSame :: Code (# Int#, ts #) -> Code (# Int#, ts #) -> Code Bool
offWithSame qi# qj# = [||
    case $$(qi#) of
      (# i#, _ #) -> case $$(qj#) of
        (# j#, _ #) -> $$(intSame [||i#||] [||j#||])
  ||]

offWithShiftRight :: Code (Int -> ts -> ts) -> Code (# Int#, ts #) -> Code Int# -> Code (# Int#, ts #)
offWithShiftRight drop qo# qi# = [||
    case $$(qo#) of (# o#, ts #) -> (# (o# +# $$(qi#)), ($$drop (I# $$(qi#)) ts) #)
  ||]

{-offWithStreamAnd :: ts -> OffWithStreamAnd ts
offWithStreamAnd ts = OffWithStreamAnd 0 nomore ts

offWithStreamAndToInt :: OffWithStreamAnd ts -> Int
offWithStreamAndToInt (OffWithStreamAnd i _ _) = i-}

dropStream :: Int -> Stream -> Stream
dropStream 0 cs = cs
dropStream n (_ :> cs) = dropStream (n-1) cs

textShiftRight :: Text -> Int -> Text
textShiftRight (Text arr off unconsumed) i = go i off unconsumed
  where
    go 0 off' unconsumed' = Text arr off' unconsumed'
    go n off' unconsumed'
      | unconsumed' > 0 = let !d = iter_ (Text arr off' unconsumed') 0
                          in go (n-1) (off'+d) (unconsumed'-d)
      | otherwise = Text arr off' unconsumed'

textShiftLeft :: Text -> Int -> Text
textShiftLeft (Text arr off unconsumed) i = go i off unconsumed
  where
    go 0 off' unconsumed' = Text arr off' unconsumed'
    go n off' unconsumed'
      | off' > 0 = let !d = reverseIter_ (Text arr off' unconsumed') 0 in go (n-1) (off'+d) (unconsumed'-d)
      | otherwise = Text arr off' unconsumed'

{-# INLINE emptyUnpackedLazyByteString' #-}
emptyUnpackedLazyByteString' :: Int# -> UnpackedLazyByteString
emptyUnpackedLazyByteString' i# = (# i#, nullAddr#, error "nullForeignPtr", 0#, 0#, Lazy.Empty #)

byteStringShiftRight :: UnpackedLazyByteString -> Int# -> UnpackedLazyByteString
byteStringShiftRight (# i#, addr#, final, off#, size#, cs #) j#
  | isTrue# (j# <# size#)  = (# i# +# j#, addr#, final, off# +# j#, size# -# j#, cs #)
  | otherwise = case cs of
    Lazy.Chunk (PS (ForeignPtr addr'# final') (I# off'#) (I# size'#)) cs' -> byteStringShiftRight (# i# +# size#, addr'#, final', off'#, size'#, cs' #) (j# -# size#)
    Lazy.Empty -> emptyUnpackedLazyByteString' (i# +# size#)

byteStringShiftLeft :: UnpackedLazyByteString -> Int# -> UnpackedLazyByteString
byteStringShiftLeft (# i#, addr#, final, off#, size#, cs #) j# =
  let d# = min# off# j#
  in (# i# -# d#, addr#, final, off# -# d#, size# +# d#, cs #)

min# :: Int# -> Int# -> Int#
min# i# j# = case i# <# j# of
  0# -> j#
  _  -> i#

max# :: Int# -> Int# -> Int#
max# i# j# = case i# <# j# of
  0# -> i#
  _  -> j#