{-# LANGUAGE BangPatterns,
             MagicHash,
             UnboxedTuples,
             TemplateHaskell,
             FlexibleInstances,
             TypeApplications,
             MultiParamTypeClasses,
             TypeFamilies,
             PolyKinds,
             DataKinds,
             FunctionalDependencies,
             TypeFamilyDependencies #-}
module Input where

import Utils                    (Code)
import Data.Array.Base          (UArray(..), listArray)
import GHC.Prim                 (Int#, Addr#, ByteArray#, nullAddr#, indexWideCharArray#, indexWord16Array#, readWord8OffAddr#, word2Int#, chr#, touch#, realWorld#, plusAddr#, (+#))
import GHC.Exts                 (Int(..), Char(..), TYPE, RuntimeRep(..))
import Data.Text.Array          (aBA, empty)
import Data.Text.Internal       (Text(..))
import Data.Text.Unsafe         (iter, Iter(..), iter_, reverseIter_)
import Data.ByteString.Internal (ByteString(..))
import GHC.ForeignPtr           (ForeignPtr(..), ForeignPtrContents)
import Control.Monad.ST         (ST)
import Data.STRef               (STRef, newSTRef, readSTRef, writeSTRef)
import Data.STRef.Unboxed       (STRefU, newSTRefU, readSTRefU, writeSTRefU)
import qualified Data.Text                     as Text (length, index)
import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString(..))
--import Language.Haskell.TH      (Q, Type)

data PreparedInput r s rep (urep :: TYPE r) = PreparedInput {-next-}       (rep -> (# Char, rep #))
                                                            {-more-}       (rep -> Bool)
                                                            {-same-}       (rep -> rep -> Bool)
                                                            {-init-}       rep
                                                            {-box-}        (urep -> rep)
                                                            {-unbox-}      (rep -> urep)
                                                            {-newCRef-}    (rep -> ST s (STRefU s Int))
                                                            {-readCRef-}   (STRefU s Int -> ST s rep)
                                                            {-writeCRef-}  (STRefU s Int -> rep -> ST s ())
                                                            {-shiftLeft-}  (rep -> Int -> rep)
                                                            {-shiftRight-} (rep -> Int -> rep)
                                                            {-offToInt-}   (rep -> Int)
newtype Text16 = Text16 Text
newtype CacheText = CacheText Text
newtype CharList = CharList String
data Stream = {-# UNPACK #-} !Char :> Stream

nomore :: Stream
nomore = '\0' :> nomore

{-inputTypes :: [Q Type]
inputTypes = [[t|Int|], [t|OffWith s|], [t|Text|]]-}

data OffWith s = OffWith {-# UNPACK #-} !Int s

offWith :: s -> OffWith s
offWith s = OffWith 0 s

offWithBox :: (# Int#, s #) -> OffWith s
offWithBox (# i#, s #) = OffWith (I# i#) s

offWithUnbox :: OffWith s -> (# Int#, s #)
offWithUnbox (OffWith (I# i#) s) = (# i#, s #)

offWithSame :: OffWith s -> OffWith s -> Bool
offWithSame (OffWith i _) (OffWith j _) = i == j

offWithToInt :: OffWith s -> Int
offWithToInt (OffWith i _) = i

data OffWithStreamAnd s = OffWithStreamAnd {-# UNPACK #-} !Int !Stream s

offWithStreamAnd :: s -> OffWithStreamAnd s
offWithStreamAnd s = OffWithStreamAnd 0 nomore s

offWithStreamAndBox :: (# Int#, Stream, s #) -> OffWithStreamAnd s
offWithStreamAndBox (# i#, ss, s #) = OffWithStreamAnd (I# i#) ss s

offWithStreamAndUnbox :: OffWithStreamAnd s -> (# Int#, Stream, s #)
offWithStreamAndUnbox (OffWithStreamAnd (I# i#) ss s) = (# i#, ss, s #)

offWithStreamAndToInt :: OffWithStreamAnd s -> Int
offWithStreamAndToInt (OffWithStreamAnd i _ _) = i

data UnpackedLazyByteString = UnpackedLazyByteString
  {-# UNPACK #-} !Int
  !Addr#
  ForeignPtrContents
  {-# UNPACK #-} !Int
  {-# UNPACK #-} !Int
  Lazy.ByteString

{-# INLINE emptyUnpackedLazyByteString #-}
emptyUnpackedLazyByteString :: Int -> UnpackedLazyByteString
emptyUnpackedLazyByteString i = UnpackedLazyByteString i nullAddr# (error "nullForeignPtr") 0 0 Lazy.Empty

type family Rep rep where
  Rep Int = IntRep
  Rep Text = LiftedRep
  Rep UnpackedLazyByteString = 'TupleRep '[IntRep, AddrRep, LiftedRep, IntRep, IntRep, LiftedRep]
  Rep (OffWith s) = 'TupleRep '[IntRep, LiftedRep]
  Rep (OffWithStreamAnd s) = 'TupleRep '[IntRep, LiftedRep, LiftedRep]
  Rep (Text, Stream) = 'TupleRep '[LiftedRep, LiftedRep]

type family Unboxed rep = (urep :: TYPE (Rep rep)) | urep -> rep where
  Unboxed Int = Int#
  Unboxed Text = Text
  Unboxed UnpackedLazyByteString = (# Int#, Addr#, ForeignPtrContents, Int#, Int#, Lazy.ByteString #)
  Unboxed (OffWith s) = (# Int#, s #)
  Unboxed (OffWithStreamAnd s) = (# Int#, Stream, s #)
  Unboxed (Text, Stream) = (# Text, Stream #)

class Input input rep | input -> rep where
  prepare :: Code input -> Code (PreparedInput (Rep rep) s rep (Unboxed rep))

instance Input [Char] Int where
  prepare input = prepare @(UArray Int Char) [||listArray (0, length $$input-1) $$input||]

instance Input (UArray Int Char) Int where
  prepare qinput = [||
      let UArray _ _ size input# = $$qinput
          next i@(I# i#) = (# C# (indexWideCharArray# input# i#), I# (i# +# 1#) #)
          o << i = max (o - i) 0
      in PreparedInput next (< size) (==) 0 (\i# -> I# i#) (\(I# i#) -> i#) newSTRefU readSTRefU writeSTRefU (<<) (+) id
    ||]

instance Input Text16 Int where
  prepare qinput = [||
      let Text16 (Text arr off size) = $$qinput
          arr# = aBA arr
          next i@(I# i#) = (# C# (chr# (word2Int# (indexWord16Array# arr# i#))), I# (i# +# 1#) #)
          o << i = max (o - i) 0
      in PreparedInput next (< size) (==) off (\i# -> I# i#) (\(I# i#) -> i#) newSTRefU readSTRefU writeSTRefU (<<) (+) id
    ||]

instance Input ByteString Int where
  prepare qinput = [||
      let PS (ForeignPtr addr# final) off size = $$qinput
          next i@(I# i#) =
            case readWord8OffAddr# (addr# `plusAddr#` i#) 0# realWorld# of
              (# s', x #) -> case touch# final s' of
                _ -> (# C# (chr# (word2Int# x)), i + 1 #)
          o << i = max (o - i) 0
      in PreparedInput next (< size) (==) off (\i# -> I# i#) (\(I# i#) -> i#) newSTRefU readSTRefU writeSTRefU (<<) (+) id
    ||]

instance Input CharList (OffWith String) where
  prepare qinput = [||
      let CharList input = $$qinput
          next (OffWith i (c:cs)) = (# c, OffWith (i+1) cs #)
          size = length input
          more (OffWith i _) = i < size
          --more (OffWith _ []) = False
          --more _              = True
          OffWith o cs >> i = OffWith (o + i) (drop i cs)
          newCRef (OffWith i _) = newSTRefU i
          readCRef ref = fmap (\i -> OffWith i []) (readSTRefU ref)
          writeCRef ref (OffWith i _) = writeSTRefU ref i
      in PreparedInput next more offWithSame (offWith input) offWithBox offWithUnbox newCRef readCRef writeCRef const (>>) offWithToInt
    ||]

instance Input Text Text where
  prepare qinput = [||
      let input = $$qinput
          next t@(Text arr off unconsumed) = let !(Iter c d) = iter t 0 in (# c, Text arr (off+d) (unconsumed-d) #)
          more (Text _ _ unconsumed) = unconsumed > 0
          same (Text _ i _) (Text _ j _) = i == j
          (Text arr off unconsumed) << i = go i off unconsumed
            where
              go 0 off' unconsumed' = Text arr off' unconsumed'
              go n off' unconsumed'
                | off' > 0 = let !d = reverseIter_ (Text arr off' unconsumed') 0 in go (n-1) (off'+d) (unconsumed'-d)
                | otherwise = Text arr off' unconsumed'
          (Text arr off unconsumed) >> i = go i off unconsumed
            where
              go 0 off' unconsumed' = Text arr off' unconsumed'
              go n off' unconsumed'
                | unconsumed' > 0 = let !d = iter_ (Text arr off' unconsumed') 0 in go (n-1) (off'+d) (unconsumed'-d)
                | otherwise = Text arr off' unconsumed'
          toInt (Text arr off unconsumed) = div off 2
          newCRef (Text _ i _) = newSTRefU i
          readCRef ref = fmap (\i -> Text empty i 0) (readSTRefU ref)
          writeCRef ref (Text _ i _) = writeSTRefU ref i
      in PreparedInput next more same input id id newCRef readCRef writeCRef (<<) (>>) toInt
    ||]

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
    ||]-}

instance Input Lazy.ByteString UnpackedLazyByteString where
  prepare qinput = [||
      let input = $$qinput
          next (UnpackedLazyByteString i addr# final off@(I# off#) size cs) =
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
          same (UnpackedLazyByteString i _ _ _ _ _) (UnpackedLazyByteString j _ _ _ _ _) = i == j
          UnpackedLazyByteString i addr# final off size cs << j =
            let d = min off j
            in UnpackedLazyByteString (i - d) addr# final (off - d) (size + d) cs
          (!(UnpackedLazyByteString i addr# final off size cs)) >> j
            | j < size  = UnpackedLazyByteString (i + j) addr# final (off + j) (size - j) cs
            | otherwise = case cs of
              Lazy.Chunk (PS (ForeignPtr addr'# final') off' size') cs' -> UnpackedLazyByteString (i + size) addr'# final' off' size' cs' >> (j - size)
              Lazy.Empty -> emptyUnpackedLazyByteString (i + size)
          initial = case input of
            Lazy.Chunk (PS (ForeignPtr addr# final) off size) cs -> UnpackedLazyByteString 0 addr# final off size cs
            Lazy.Empty -> emptyUnpackedLazyByteString 0
          box !(# i#, addr#, final, off#, size#, cs #) = UnpackedLazyByteString (I# i#) addr# final (I# off#) (I# size#) cs
          unbox (UnpackedLazyByteString (I# i#) addr# final (I# off#) (I# size#) cs) = (# i#, addr#, final, off#, size#, cs #)
          newCRef o = newSTRefU (toInt o)
          readCRef ref = fmap emptyUnpackedLazyByteString (readSTRefU ref)
          writeCRef ref o = writeSTRefU ref (toInt o)
          toInt (UnpackedLazyByteString i _ _ _ _ _) = i
      in PreparedInput next more same initial box unbox newCRef readCRef writeCRef (<<) (>>) toInt
    ||]

{-instance Input Lazy.ByteString (OffWith Lazy.ByteString) where
  prepare qinput = [||
      let input = $$qinput
          next (OffWith i (Lazy.Chunk (PS ptr@(ForeignPtr addr# final) off@(I# off#) size) cs)) =
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
          newCRef (OffWith i _) = newSTRefU i
          readCRef ref = fmap (\i -> OffWith i Lazy.Empty) (readSTRefU ref)
          writeCRef ref (OffWith i _) = writeSTRefU ref i
      in PreparedInput next more offWithSame (offWith input) offWithBox offWithUnbox newCRef readCRef writeCRef (<<) (>>) offWithToInt
    ||]-}

instance Input Stream (OffWith Stream) where
  prepare qinput = [||
      let input = $$qinput
          next (OffWith o (c :> cs)) = (# c, OffWith (o + 1) cs #)
          (OffWith o cs) >> i = OffWith (o + i) (sdrop i cs)
            where
              sdrop 0 cs = cs
              sdrop n (_ :> cs) = sdrop (n-1) cs
          newCRef (OffWith i _) = newSTRefU i
          readCRef ref = fmap (\i -> OffWith i nomore) (readSTRefU ref)
          writeCRef ref (OffWith i _) = writeSTRefU ref i
      in PreparedInput next (const True) offWithSame (offWith input) offWithBox offWithUnbox newCRef readCRef writeCRef const (>>) offWithToInt
    ||]