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
             FunctionalDependencies #-}
module Input where

import Utils                    (TExpQ)
import Data.Array.Base          (UArray(..), listArray)
import GHC.Prim                 (Int#, ByteArray#, indexWideCharArray#, indexWord16Array#, readWord8OffAddr#, word2Int#, chr#, touch#, realWorld#)
import GHC.Exts                 (Int(..), Char(..), TYPE, RuntimeRep(..))
import Data.Text.Array          (aBA)
import Data.Text.Internal       (Text(..))
import Data.Text.Unsafe         (iter, Iter(..), iter_, reverseIter_)
import Data.ByteString.Internal (ByteString(..))
import GHC.ForeignPtr           (ForeignPtr(..))
import Control.Monad.ST         (ST)
import Data.STRef               (STRef, newSTRef, readSTRef, writeSTRef)
import Data.STRef.Unboxed       (STRefU, newSTRefU, readSTRefU, writeSTRefU)
import qualified Data.Text as Text (length, index)
--import Language.Haskell.TH      (Q, Type)

data PreparedInput r s rep (urep :: TYPE r) = PreparedInput {-next-}       (rep -> (# Char, rep #))
                                                            {-more-}       (rep -> Bool)
                                                            {-same-}       (rep -> rep -> Bool)
                                                            {-init-}       rep 
                                                            {-box-}        (urep -> rep)
                                                            {-unbox-}      (rep -> urep)
                                                            {-newCRef-}    (rep -> ST s (CRef s rep))
                                                            {-readCRef-}   (CRef s rep -> ST s rep)
                                                            {-writeCRef-}  (CRef s rep -> rep -> ST s ())
                                                            {-shiftLeft-}  (rep -> Int -> rep)
                                                            {-shiftRight-} (rep -> Int -> rep)
                                                            {-offToInt-}   (rep -> Int)
newtype Text16 = Text16 Text
newtype CharList = CharList String
data OffString = OffString {-# UNPACK #-} !Int String
data Chars = More {-# UNPACK #-} !Char Chars | Empty
data Stream = {-# UNPACK #-} !Char :> Stream 
data OffStream = OffStream {-# UNPACK #-} !Int Stream

nomore :: Stream
nomore = '\0' :> nomore

{-inputTypes :: [Q Type]
inputTypes = [[t|Int|], [t|OffString|], [t|Text|], [t|OffStream|]]-}

type family Rep rep where
  Rep Int = IntRep
  Rep OffString = 'TupleRep '[IntRep, LiftedRep]
  Rep Text = LiftedRep
  Rep OffStream = LiftedRep

type family CRef s rep where
  CRef s Int = STRefU s Int
  CRef s OffString = STRef s OffString
  CRef s Text = STRef s Text
  CRef s OffStream = STRef s OffStream

class Input input rep | input -> rep where
  type Unboxed rep :: TYPE (Rep rep)
  prepare :: TExpQ input -> TExpQ (PreparedInput (Rep rep) s rep (Unboxed rep))

instance Input [Char] Int where 
  type Unboxed Int = Int#
  prepare input = prepare @(UArray Int Char) [||listArray (0, length $$input-1) $$input||]

instance Input (UArray Int Char) Int where 
  type Unboxed Int = Int#
  prepare qinput = [||
      let UArray _ _ size input# = $$qinput
          next i@(I# i#) = (# C# (indexWideCharArray# input# i#), i + 1 #)
          o << i = max (o - i) 0
      in PreparedInput next (< size) (==) 0 (\i# -> I# i#) (\(I# i#) -> i#) newSTRefU readSTRefU writeSTRefU (<<) (+) id
    ||]

instance Input Text16 Int where
  type Unboxed Int = Int#
  prepare qinput = [||
      let Text16 (Text arr off size) = $$qinput
          arr# = aBA arr
          next i@(I# i#) = (# C# (chr# (word2Int# (indexWord16Array# arr# i#))), i + 1 #)
          o << i = max (o - i) 0
      in PreparedInput next (< size) (==) off (\i# -> I# i#) (\(I# i#) -> i#) newSTRefU readSTRefU writeSTRefU (<<) (+) id
    ||]

instance Input ByteString Int where
  type Unboxed Int = Int#
  prepare qinput = [||
      let PS (ForeignPtr addr# final) off size = $$qinput
          next i@(I# i#) = 
            case readWord8OffAddr# addr# i# realWorld# of
              (# s', x #) -> case touch# final s' of 
                _ -> (# C# (chr# (word2Int# x)), i + 1 #)
          o << i = max (o - i) 0
      in PreparedInput next (< size) (==) off (\i# -> I# i#) (\(I# i#) -> i#) newSTRefU readSTRefU writeSTRefU (<<) (+) id
    ||]

instance Input CharList OffString where
  type Unboxed OffString = (# Int#, String #)
  prepare qinput = [||
      let CharList input = $$qinput
          size = length input
          next (OffString i (c:cs)) = (# c, OffString (i+1) cs #)
          more (OffString i _) = i < size
          same (OffString i _) (OffString j _) = i == j
          box (# i, cs #) = OffString (I# i) cs
          unbox (OffString (I# i) cs) = (# i, cs #)
          OffString o cs >> i = OffString (o + i) (drop i cs)
          toInt (OffString i _) = i
      in PreparedInput next more same (OffString 0 input) box unbox newSTRef readSTRef writeSTRef const (>>) toInt
    ||]

instance Input Text Text where
  type Unboxed Text = Text
  prepare qinput = [||
      let input = $$qinput
          next t@(Text arr off unconsumed) = let !(Iter c d) = iter t 0 in (# c, Text arr (off+d) (unconsumed-d) #)
          more (Text _ _ unconsumed) = unconsumed > 0
          same (Text _ i _) (Text _ j _) = i == j
          -- Using these for fix length look-ahead is really inefficient, we could package up a Chars along with it?
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
      in PreparedInput next more same input id id newSTRef readSTRef writeSTRef (<<) (>>) toInt
    ||]

instance Input Stream OffStream where
  type Unboxed OffStream = OffStream
  prepare qinput = [||
      let input = $$qinput
          next (OffStream o (c :> cs)) = (# c, OffStream (o + 1) cs #)
          same (OffStream i _) (OffStream j _) = i == j
          (OffStream o cs) >> i = OffStream (o + i) (sdrop i cs)
            where 
              sdrop 0 cs = cs
              sdrop n (_ :> cs) = sdrop (n-1) cs
          toInt (OffStream o _) = o
      in PreparedInput next (const True) same (OffStream 0 input) id id newSTRef readSTRef writeSTRef const (>>) toInt
    ||]