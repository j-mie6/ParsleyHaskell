{-# LANGUAGE MagicHash,
             TypeFamilies,
             TypeFamilyDependencies,
             UnboxedTuples #-}
module Parsley.Internal.Backend.Machine.InputRep (
    Unboxed, Rep,
    OffWith(..), offWith, offWithSame, offWithShiftRight,
    OffWithStreamAnd(..),
    UnpackedLazyByteString(..), emptyUnpackedLazyByteString,
    Stream, dropStream,
    representationTypes,
    -- These must be exposed
    textShiftRight, textShiftLeft,
    byteStringShiftRight, byteStringShiftLeft
  ) where

import Data.Array.Unboxed                (UArray)
import Data.ByteString.Internal          (ByteString(..))
import Data.Text.Internal                (Text(..))
import Data.Text.Unsafe                  (iter_, reverseIter_)
import GHC.Exts                          (TYPE, RuntimeRep(..))
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

offWith :: Code (ts -> OffWith ts)
offWith = [||OffWith 0||]

{-# INLINE emptyUnpackedLazyByteString #-}
emptyUnpackedLazyByteString :: Int -> UnpackedLazyByteString
emptyUnpackedLazyByteString i = UnpackedLazyByteString i nullAddr# (error "nullForeignPtr") 0 0 Lazy.Empty

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

type family RepKind rep where
  RepKind Int = IntRep
  RepKind Text = LiftedRep
  RepKind UnpackedLazyByteString = 'TupleRep '[IntRep, AddrRep, LiftedRep, IntRep, IntRep, LiftedRep]
  RepKind (OffWith _) = 'TupleRep '[IntRep, LiftedRep]
  RepKind (OffWithStreamAnd _) = 'TupleRep '[IntRep, LiftedRep, LiftedRep]
  RepKind (Text, Stream) = 'TupleRep '[LiftedRep, LiftedRep]

type family Unboxed rep = (urep :: TYPE (RepKind rep)) | urep -> rep where
  Unboxed Int = Int#
  Unboxed Text = Text
  Unboxed UnpackedLazyByteString = (# Int#, Addr#, ForeignPtrContents, Int#, Int#, Lazy.ByteString #)
  Unboxed (OffWith ts) = (# Int#, ts #)
  Unboxed (OffWithStreamAnd ts) = (# Int#, Stream, ts #)
  Unboxed (Text, Stream) = (# Text, Stream #)

{- Generic Representation Operations -}
offWithSame :: Code (OffWith ts -> OffWith ts -> Bool)
offWithSame = [||\(OffWith i _) (OffWith j _) -> i == j||]

offWithShiftRight :: Code (Int -> ts -> ts) -> Code (OffWith ts -> Int -> OffWith ts)
offWithShiftRight drop = [||\(OffWith o ts) i -> OffWith (o + i) ($$drop i ts)||]

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

byteStringShiftRight :: UnpackedLazyByteString -> Int -> UnpackedLazyByteString
byteStringShiftRight !(UnpackedLazyByteString i addr# final off size cs) j
  | j < size  = UnpackedLazyByteString (i + j) addr# final (off + j) (size - j) cs
  | otherwise = case cs of
    Lazy.Chunk (PS (ForeignPtr addr'# final') off' size') cs' -> byteStringShiftRight (UnpackedLazyByteString (i + size) addr'# final' off' size' cs') (j - size)
    Lazy.Empty -> emptyUnpackedLazyByteString (i + size)

byteStringShiftLeft :: UnpackedLazyByteString -> Int -> UnpackedLazyByteString
byteStringShiftLeft (UnpackedLazyByteString i addr# final off size cs) j =
  let d = min off j
  in UnpackedLazyByteString (i - d) addr# final (off - d) (size + d) cs