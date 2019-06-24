{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE TemplateHaskell #-}
module MachineOps where

import Utils           (TExpQ)
import GHC.ST          (ST(..))
import Data.STRef      (STRef, writeSTRef, readSTRef, newSTRef)
import Data.Array.Base (STUArray(..), UArray(..), newArray_, unsafeRead, unsafeWrite, MArray, getNumElements)
import GHC.Prim        (Int#, Char#, newByteArray#, indexWideCharArray#)
import GHC.Exts        (Int(..), Char(..), (-#), (+#), (*#))

data SList a = !a ::: !(SList a) | SNil
data IList = ICons {-# UNPACK #-} !Int !IList | INil
data HList xs where
  HNil :: HList '[]
  HCons :: !a -> !(HList as) -> HList (a ': as)
data K s ks a where
  KNil :: K s '[] a
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
  KCons :: !(X xs -> O# -> ST s (Maybe a)) -> !(K s ks a) -> K s (xs ': ks) a

newtype H s a = H (SList (O# -> H s a -> C -> ST s (Maybe a)))
type X = HList
type C = IList
type O = Int
type O# = Int#
data Input = Input {charAt :: TExpQ (Int -> Char), size :: TExpQ Int, substr :: TExpQ (Int -> Int -> UArray Int Char)}

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
pushX = HCons
{-# INLINE popX #-}
popX :: X (a ': xs) -> (# a, X xs #)
popX !(HCons x xs) = (# x, xs #)
{-# INLINE popX_ #-}
popX_ :: X (a ': xs) -> X xs
popX_ !(HCons x xs) = xs
{-# INLINE pokeX #-}
pokeX :: a -> X (a ': xs) -> X (a ': xs)
pokeX y !(HCons x xs) = HCons y xs
{-# INLINE modX #-}
modX :: (a -> b) -> X (a ': xs) -> X (b ': xs)
modX f !(HCons x xs) = HCons (f x) xs
{-# INLINE peekX #-}
peekX :: X (a ': xs) -> a
peekX !(HCons x xs) = x

makeK :: ST s (K s '[] a)
makeK = return $! KNil
{-# INLINE pushK #-}
pushK :: (X xs -> O# -> ST s (Maybe a)) -> K s ks a -> K s (xs ': ks) a
pushK = KCons
{-# INLINE popK #-}
popK :: K s (xs ': ks) a -> (# (X xs -> O# -> ST s (Maybe a)), K s ks a #)
popK !(KCons k ks) = (# k, ks #)
{-# INLINE peekK #-}
peekK :: K s (xs ': ks) a -> (X xs -> O# -> ST s (Maybe a))
peekK !(KCons k ks) = k
noreturn :: X xs -> O# -> ST s (Maybe a)
noreturn xs o# = error "Machine is only permitted return-by-failure"

makeH :: ST s (H s a)
makeH = return $! (H SNil)
pushH :: (O# -> H s a -> C -> ST s (Maybe a)) -> H s a -> H s a
pushH !h !(H hs) = H (h:::hs)
{-# INLINE popH_ #-}
popH_ :: H s a -> H s a
popH_ !(H (_:::hs)) = H hs

makeC :: ST s C
makeC = return $! INil
{-# INLINE pushC #-}
pushC :: O -> C -> C
pushC = ICons
{-# INLINE popC #-}
popC :: C -> (# O, C #)
popC !(ICons o cs) = (# o, cs #)
{-# INLINE popC_ #-}
popC_ :: C -> C
popC_ !(ICons _ cs) = cs
pokeC :: O -> C -> C
pokeC o !(ICons _ cs) = ICons o cs

newΣ :: x -> ST s (STRef s x)
newΣ = newSTRef

writeΣ :: STRef s x -> x -> ST s ()
writeΣ = writeSTRef

readΣ :: STRef s x -> ST s x
readΣ = readSTRef

modifyΣ :: STRef s x -> (x -> x) -> ST s ()
modifyΣ σ f =
  do x <- readSTRef σ
     writeSTRef σ (f $! x)

setupHandler :: QH s a -> QC -> QO -> TExpQ (O# -> H s a -> C -> ST s (Maybe a)) ->
                                      (QH s a -> QC -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandler !hs !cs !o !h !k = k [|| pushH $$h $$hs ||][|| pushC $$o $$cs ||]

{-# INLINE raise #-}
raise :: H s a -> C -> O -> ST s (Maybe a)
raise (H SNil) !_ !_             = return Nothing
raise (H (h:::hs')) !cs !(I# o#) = h o# (H hs') cs

nextSafe :: Bool -> Input -> QO -> TExpQ (Char -> Bool) -> (QO -> TExpQ Char -> QST s (Maybe a)) -> QST s (Maybe a) -> QST s (Maybe a)
nextSafe True input o p good bad = [|| let !c = $$(charAt input) $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else $$bad ||]
nextSafe False input o p good bad = [||
    let bad' = $$bad in
      if  $$(size input) > $$o then let !c = $$(charAt input) $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else bad'
      else bad'
  ||]