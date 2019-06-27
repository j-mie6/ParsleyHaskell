{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             BangPatterns,
             MagicHash,
             UnboxedTuples,
             TemplateHaskell,
             FlexibleInstances,
             TypeApplications #-}
module MachineOps where

import Utils              (TExpQ)
import GHC.ST             (ST(..))
import Data.STRef         (STRef, writeSTRef, readSTRef, newSTRef)
import Data.Array.Base    (STUArray(..), UArray(..), unsafeRead, unsafeWrite, MArray, getNumElements, listArray)
import GHC.Prim           (Int#, Char#, ByteArray#, indexWideCharArray#, indexWord16Array#, readWord8OffAddr#, word2Int#, chr#, touch#, realWorld#)
import GHC.Exts           (Int(..), Char(..), (-#), (+#), (*#))
import Data.Text.Internal (Text(..))
import Data.Text.Array    (aBA)
import Data.ByteString.Internal (ByteString(..))
import GHC.ForeignPtr     (ForeignPtr(..))
import Safe.Coerce        (coerce)
import qualified Data.ByteString.Char8 as BS (pack)
import qualified Data.Text as Text (pack)


data SList a = !a ::: SList a | SNil
data IList = ICons {-# UNPACK #-} !Int IList | INil
data HList xs where
  HNil :: HList '[]
  HCons :: !a -> HList as -> HList (a ': as)

newtype H s a = H (SList (O# -> C -> ST s (Maybe a)))
type X = HList
type C = IList
type O = Int
type O# = Int#
{- A key property of the pure semantics of the machine states that
    at the end of the execution of a machine, all the stacks shall
    be empty. This also holds true of any recursive machines, for
    obvious reasons. In the concrete machine, however, it is not
    entirely necessary for this invariant to be obeyed: indeed the
    stacks that would have otherwise been passed to the continuation
    in the pure semantics were available to the caller in the
    concrete machine. As such, continuations are only required to
    demand the values of X and o, with all other values closed over
    during suspension. -}
type K s xs a = X xs -> O# -> ST s (Maybe a)
data PreparedInput = PreparedInput (Int -> Char) Int
data InputOps = InputOps {charAt :: TExpQ (Int -> Char), size :: TExpQ Int}

class Input s where prepare :: TExpQ s -> TExpQ PreparedInput
instance Input [Char] where prepare input = prepare @(UArray Int Char) [||listArray (0, length $$input-1) $$input||]
instance Input Text where 
  prepare qinput = [||
      let Text arr (I# off#) size = $$qinput
          arr# = aBA arr
          charAt (I# i#) = C# (chr# (word2Int# (indexWord16Array# arr# (i#{- +# off#-}))))
      in PreparedInput charAt size
    ||]
instance Input (UArray Int Char) where 
  prepare qinput = [||
      let UArray _ _ size input# = $$qinput
          charAt (I# i#) = C# (indexWideCharArray# input# i#)
      in PreparedInput charAt size
    ||]
instance Input ByteString where
  prepare qinput = [||
      let PS (ForeignPtr addr# final) (I# off#) size = $$qinput
          charAt (I# i#) = 
            case readWord8OffAddr# addr# ({-off# +# -}i#) realWorld# of
              (# s', x #) -> case touch# final s' of 
                _ -> C# (chr# (word2Int# x))
      in PreparedInput charAt size
    ||]

type QH s a = TExpQ (H s a)
type QX xs = TExpQ (X xs)
type QK s ks a = TExpQ (K s ks a)
type QC = TExpQ IList
type QO = TExpQ O
type QST s a = TExpQ (ST s a)

makeX :: ST s (X '[])
makeX = return $! HNil
{-# INLINE pushX #-}
pushX :: a -> X xs -> X (a ': xs)
pushX !x xs = HCons x xs
{-# INLINE popX #-}
popX :: X (a ': xs) -> (# a, X xs #)
popX (HCons x xs) = (# x, xs #)
{-# INLINE popX_ #-}
popX_ :: X (a ': xs) -> X xs
popX_ (HCons x xs) = xs
{-# INLINE pokeX #-}
pokeX :: a -> X (a ': xs) -> X (a ': xs)
pokeX y (HCons x xs) = HCons y xs
{-# INLINE modX #-}
modX :: (a -> b) -> X (a ': xs) -> X (b ': xs)
modX f (HCons x xs) = HCons (f $! x) xs
{-# INLINE peekX #-}
peekX :: X (a ': xs) -> a
peekX (HCons x xs) = x

makeK :: ST s (K s '[] a)
makeK = return $! noreturn
noreturn :: X xs -> O# -> ST s (Maybe a)
noreturn xs o# = error "Machine is only permitted return-by-failure"

makeH :: ST s (H s a)
makeH = return $! H SNil
pushH :: (O# -> C -> ST s (Maybe a)) -> H s a -> H s a
pushH !h (H hs) = H (h:::hs)
{-# INLINE popH_ #-}
popH_ :: H s a -> H s a
popH_ (H (_:::hs)) = H hs

makeC :: ST s C
makeC = return $! INil
{-# INLINE pushC #-}
pushC :: O -> C -> C
pushC = ICons
{-# INLINE popC #-}
popC :: C -> (# O, C #)
popC (ICons o cs) = (# o, cs #)
{-# INLINE popC_ #-}
popC_ :: C -> C
popC_ (ICons _ cs) = cs
pokeC :: O -> C -> C
pokeC !o (ICons _ cs) = ICons o cs

{-# INLINE newΣ #-}
newΣ :: x -> ST s (STRef s x)
newΣ x = newSTRef x
{-# INLINE writeΣ #-}
writeΣ :: STRef s x -> x -> ST s ()
writeΣ ref x = writeSTRef ref x
{-# INLINE readΣ #-}
readΣ :: STRef s x -> ST s x
readΣ ref = readSTRef ref
{-# INLINE modifyΣ #-}
modifyΣ :: STRef s x -> (x -> x) -> ST s ()
modifyΣ σ f =
  do !x <- readΣ σ
     writeΣ σ (f $! x)

setupHandler :: QH s a -> QC -> QO -> TExpQ (H s a -> O# -> C -> ST s (Maybe a)) ->
                                      (QH s a -> QC -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandler hs cs !o !h !k = k [|| pushH (\(!o#) (!cs) -> $$h $$hs o# cs) $$hs ||] [|| pushC $$o $$cs ||]

{-# INLINE raise #-}
raise :: H s a -> C -> O -> ST s (Maybe a)
raise (H SNil) cs !o          = return Nothing
raise (H (h:::_)) cs !(I# o#) = h o# cs

nextSafe :: Bool -> InputOps -> QO -> TExpQ (Char -> Bool) -> (QO -> TExpQ Char -> QST s (Maybe a)) -> QST s (Maybe a) -> QST s (Maybe a)
nextSafe True input o p good bad = [|| let !c = $$(charAt input) $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else $$bad ||]
nextSafe False input o p good bad = [||
    let bad' = $$bad in
      if  $$(size input) > $$o then let !c = $$(charAt input) $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else bad'
      else bad'
  ||]
