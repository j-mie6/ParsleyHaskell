{-# LANGUAGE BangPatterns,
             MagicHash,
             UnboxedTuples,
             TemplateHaskell,
             FlexibleInstances,
             TypeApplications,
             MultiParamTypeClasses,
             TypeFamilies,
             PolyKinds,
             DataKinds #-}
module Input where

import Utils                    (TExpQ)
import Data.Array.Base          (UArray(..), listArray)
import GHC.Prim                 (Int#, ByteArray#, indexWideCharArray#, indexWord16Array#, readWord8OffAddr#, word2Int#, chr#, touch#, realWorld#)
import GHC.Exts                 (Int(..), Char(..), TYPE, RuntimeRep(..))
import Data.Text.Array          (aBA)
import Data.Text.Internal       (Text(..))
import Data.ByteString.Internal (ByteString(..))
import GHC.ForeignPtr           (ForeignPtr(..))
import qualified Data.Text as Text (length, index)

data PreparedInput k rep (urep :: TYPE k) = PreparedInput (rep -> (# Char, rep #)) (rep -> Bool) (rep -> rep -> Bool) rep (urep -> rep) (rep -> urep)
newtype Text16                            = Text16 Text

data OffString = OffString !Int !String

type family Rep rep where
  Rep Int = IntRep
  Rep OffString = LiftedRep

class Input s (rep :: *) where
  type Unboxed rep :: TYPE (Rep rep)
  prepare :: TExpQ s -> TExpQ (PreparedInput (Rep rep) rep (Unboxed rep))

instance Input [Char] Int where 
  type Unboxed Int = Int#
  prepare input = prepare @(UArray Int Char) [||listArray (0, length $$input-1) $$input||]

instance Input (UArray Int Char) Int where 
  type Unboxed Int = Int#
  prepare qinput = [||
      let UArray _ _ size input# = $$qinput
          next i@(I# i#) = (# C# (indexWideCharArray# input# i#), i + 1 #)
      in PreparedInput next (< size) (==) 0 (\i# -> I# i#) (\(I# i#) -> i#)
    ||]

instance Input Text16 Int where 
  type Unboxed Int = Int#
  prepare qinput = [||
      let Text16 (Text arr off size) = $$qinput
          arr# = aBA arr
          next i@(I# i#) = (# C# (chr# (word2Int# (indexWord16Array# arr# i#))), i + 1 #)
      in PreparedInput next (< size) (==) off (\i# -> I# i#) (\(I# i#) -> i#)
    ||]

-- I'd *strongly* advise against using this, parsing complexity is O(n^2) for this variant
instance Input Text Int where
  type Unboxed Int = Int#
  prepare qinput = [||
      let input = $$qinput
          size = Text.length input
          next i = (# Text.index input i, i + 1 #)
      in PreparedInput next (< size) (==) 0 (\i# -> I# i#) (\(I# i#) -> i#)
    ||]

instance Input ByteString Int where
  type Unboxed Int = Int#
  prepare qinput = [||
      let PS (ForeignPtr addr# final) off size = $$qinput
          next i@(I# i#) = 
            case readWord8OffAddr# addr# i# realWorld# of
              (# s', x #) -> case touch# final s' of 
                _ -> (# C# (chr# (word2Int# x)), i + 1 #)
      in PreparedInput next (< size) (==) off (\i# -> I# i#) (\(I# i#) -> i#)
    ||]