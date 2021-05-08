{-# LANGUAGE MagicHash,
             TypeFamilies,
             TypeFamilyDependencies,
             UnboxedTuples,
             StandaloneKindSignatures #-}
module Parsley.Internal.Backend.Machine.InputRep (
    Unboxed, Rep,
    intSame, intLess, min#, max#,
    OffWith(..), offWith, offWithSame, offWithShiftRight,
    OffWithStreamAnd(..),
    UnpackedLazyByteString(..), UnboxedUnpackedLazyByteString, emptyUnpackedLazyByteString,
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
data OffWith ts = OffWith {-# UNPACK #-} !Int ts
data OffWithStreamAnd ts = OffWithStreamAnd {-# UNPACK #-} !Int !Stream ts
data UnpackedLazyByteString = UnpackedLazyByteString
  {-# UNPACK #-} !Int
  !Addr#
  ForeignPtrContents
  {-# UNPACK #-} !Int
  {-# UNPACK #-} !Int
  Lazy.ByteString

representationTypes :: [TH.Q TH.Type]
representationTypes = [[t|Int|], [t|OffWith [Char]|], [t|OffWith Stream|], [t|UnpackedLazyByteString|], [t|Text|]]

offWith :: Code ts -> Code (Unboxed (OffWith ts))
offWith qts = [||(# 0#, $$qts #)||]

type UnboxedUnpackedLazyByteString = (# Int#, Addr#, ForeignPtrContents, Int#, Int#, Lazy.ByteString #)

emptyUnpackedLazyByteString :: Code Int# -> Code (Unboxed UnpackedLazyByteString)
emptyUnpackedLazyByteString qi# = [|| (# $$(qi#), nullAddr#, error "nullForeignPtr", 0#, 0#, Lazy.Empty #) ||]

{- Representation Mappings -}
-- When a new input type is added here, it needs an Input instance in Parsley.Backend.Machine
type family Rep input where
  Rep [Char] = Int
  Rep (UArray Int Char) = Int
  Rep Text16 = Int
  Rep ByteString = Int
  Rep CharList = OffWith String
  Rep Text = Text
  --Rep CacheText = (Text, Stream)
  Rep Lazy.ByteString = UnpackedLazyByteString
  --Rep Lazy.ByteString = OffWith Lazy.ByteString
  Rep Stream = OffWith Stream

type RepKind :: Type -> RuntimeRep
type family RepKind rep where
  RepKind Int = IntRep
  RepKind Text = LiftedRep
  RepKind UnpackedLazyByteString = 'TupleRep '[IntRep, AddrRep, LiftedRep, IntRep, IntRep, LiftedRep]
  RepKind (OffWith _) = 'TupleRep '[IntRep, LiftedRep]
  RepKind (OffWithStreamAnd _) = 'TupleRep '[IntRep, LiftedRep, LiftedRep]
  RepKind (Text, Stream) = 'TupleRep '[LiftedRep, LiftedRep]

type Unboxed :: forall (rep :: Type) -> TYPE (RepKind rep)
type family Unboxed rep = urep | urep -> rep where
  Unboxed Int = Int#
  Unboxed Text = Text
  Unboxed UnpackedLazyByteString = UnboxedUnpackedLazyByteString
  Unboxed (OffWith ts) = (# Int#, ts #)
  Unboxed (OffWithStreamAnd ts) = (# Int#, Stream, ts #)
  Unboxed (Text, Stream) = (# Text, Stream #)

{- Generic Representation Operations -}
--offWithSame :: Code (OffWith ts -> OffWith ts -> Bool)
--offWithSame = [||\(OffWith i _) (OffWith j _) -> i == j||]

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

offWithStreamAndBox :: (# Int#, Stream, ts #) -> OffWithStreamAnd ts
offWithStreamAndBox (# i#, ss, ts #) = OffWithStreamAnd (I# i#) ss ts

offWithStreamAndUnbox :: OffWithStreamAnd ts -> (# Int#, Stream, ts #)
offWithStreamAndUnbox (OffWithStreamAnd (I# i#) ss ts) = (# i#, ss, ts #)

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
emptyUnpackedLazyByteString' :: Int# -> UnboxedUnpackedLazyByteString
emptyUnpackedLazyByteString' i# = (# i#, nullAddr#, error "nullForeignPtr", 0#, 0#, Lazy.Empty #)

byteStringShiftRight :: UnboxedUnpackedLazyByteString -> Int# -> UnboxedUnpackedLazyByteString
byteStringShiftRight (# i#, addr#, final, off#, size#, cs #) j#
  | isTrue# (j# <# size#)  = (# i# +# j#, addr#, final, off# +# j#, size# -# j#, cs #)
  | otherwise = case cs of
    Lazy.Chunk (PS (ForeignPtr addr'# final') (I# off'#) (I# size'#)) cs' -> byteStringShiftRight (# i# +# size#, addr'#, final', off'#, size'#, cs' #) (j# -# size#)
    Lazy.Empty -> emptyUnpackedLazyByteString' (i# +# size#)

byteStringShiftLeft :: UnboxedUnpackedLazyByteString -> Int# -> UnboxedUnpackedLazyByteString
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