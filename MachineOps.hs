{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
module MachineOps where

import Utils           (TExpQ)
import GHC.ST          (ST(..))
import Data.STRef      (STRef, writeSTRef, readSTRef, newSTRef)
import Data.Array.Base (STUArray(..), UArray(..), newArray_, unsafeRead, unsafeWrite, MArray, getNumElements)
import GHC.Prim        (Int#, Char#, newByteArray#, indexWideCharArray#)
import GHC.Exts        (Int(..), Char(..), (-#), (+#), (*#))

data SList a = !a ::: !(SList a) | SNil
data HList xs where
  HNil :: HList '[]
  HCons :: a -> !(HList as) -> HList (a ': as)
data K s ks a where
  KNil :: K s '[] a
  KCons :: !(X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)) -> !(K s ks a) -> K s (xs ': ks) a

newtype H s a = H (SList (O# -> H s a -> CIdx# -> C s -> D# -> ST s (Handled s a)))
type X = HList
type CIdx = Int
type CIdx# = Int#
type C s = STUArray s Int Int
type O = Int
type O# = Int#
type D = Int
type D# = Int#
data Input = Input {charAt :: TExpQ (Int -> Char), size :: TExpQ Int, substr :: TExpQ (Int -> Int -> UArray Int Char)}
data Σ s = Σ { save :: QST s (), restore :: QST s (), rollback :: TExpQ (D -> ST s ()) }

type QH s a = TExpQ (H s a)
type QX xs = TExpQ (X xs)
type QK s ks a = TExpQ (K s ks a)
type QCIdx = TExpQ CIdx
type QC s = TExpQ (C s)
type QO = TExpQ O
type QD = TExpQ D
type QST s a = TExpQ (ST s a)

double :: STUArray s Int Int -> ST s (STUArray s Int Int)
double !arr =
  do !sz <- getNumElements arr
     resize arr sz (sz * 2)

resize :: STUArray s Int Int -> Int -> Int -> ST s (STUArray s Int Int)
resize arr old (I# new) =
  do !arr' <- ST (\s -> case newByteArray# (new *# 8#) s of (# s', arr'# #) -> (# s', STUArray 0 ((I# new)-1) (I# new) arr'# #))
     let copy !from !to !n = do !x <- unsafeRead from n
                                unsafeWrite to n x
                                if n == 0 then return $! ()
                                else copy from to $! (n-1)
                             in copy arr arr' $! (old-1)
     return $! arr'

makeX :: ST s (X '[])
makeX = return $! HNil
{-# INLINE pushX #-}
pushX :: a -> X xs -> X (a ': xs)
pushX = HCons
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
modX f (HCons x xs) = HCons (f x) xs
{-# INLINE peekX #-}
peekX :: X (a ': xs) -> a
peekX (HCons x xs) = x

makeK :: ST s (K s '[] a)
makeK = return $! KNil
{-# INLINE pushK #-}
pushK :: (X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)) -> K s ks a -> K s (xs ': ks) a
pushK = KCons
{-# INLINE popK #-}
popK :: K s (xs ': ks) a -> (#(X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)), K s ks a #)
popK (KCons k ks) = (# k, ks #)

makeH :: ST s (H s a)
makeH = return $! (H SNil)
pushH :: (O# -> H s a -> CIdx# -> C s -> D# -> ST s (Handled s a)) -> H s a -> H s a
pushH !h !(H hs) = H (h:::hs)
{-# INLINE popH_ #-}
popH_ :: H s a -> H s a
popH_ !(H (_:::hs)) = H hs

makeC :: ST s (CIdx, C s)
makeC = do cs <- newArray_ (0, 3)
           return $! (-1, cs)
{-# INLINE pushC #-}
pushC :: O -> CIdx -> C s -> ST s (CIdx, C s)
pushC c i !cs = let !j = i + 1 in
  do sz <- getNumElements cs
     if j == sz then do !cs' <- double cs
                        unsafeWrite cs' j c
                        return $! (j, cs')
     else do unsafeWrite cs j c; return $! (j, cs)
popC :: CIdx -> C s -> ST s (O, CIdx)
popC !i !cs = do !c <- unsafeRead cs i; return $! (c, i - 1)
{-# INLINE popC_ #-}
popC_ :: CIdx -> CIdx
popC_ !i = i - 1
pokeC :: O -> CIdx -> C s -> ST s ()
pokeC !c !i !cs = unsafeWrite cs i c

modifyΣ :: STRef s (SList a) -> (a -> a) -> ST s ()
modifyΣ σ f =
  do (x:::xs) <- readSTRef σ
     writeSTRef σ ((f $! x) ::: xs)

writeΣ :: STRef s (SList a) -> a -> ST s ()
writeΣ σ = modifyΣ σ . const

readΣ :: STRef s (SList a) -> ST s a
readΣ σ =
  do (x:::_) <- readSTRef σ
     return $! x

pokeΣ :: STRef s (SList a) -> a -> ST s a
pokeΣ σ y =
  do (x:::xs) <- readSTRef σ
     writeSTRef σ (y:::xs)
     return $! x

newtype Handled s a = Handled {runHandler :: ST s (Maybe a)}
handled :: ST s (Maybe a) -> ST s (Handled s a)
handled = return . Handled

{-# INLINE setupHandler #-}
setupHandler :: QH s a -> QCIdx -> QC s -> QO -> TExpQ (O# -> H s a -> CIdx# -> C s -> D# -> ST s (Handled s a)) ->
                                                 (QH s a -> QCIdx -> QC s -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandler !hs !cidx !cs !o !h !k = [||
  do !(cidx', cs') <- pushC $$o $$cidx $$cs
     $$(k [|| pushH $$h $$hs ||] [|| cidx' ||] [|| cs' ||])
  ||]

{-# INLINE raise #-}
raise :: H s a -> CIdx -> C s -> O -> D -> ST s (Handled s a)
raise (H SNil) !_ !_ !_ !_                            = handled (return Nothing)
raise (H (h:::hs')) !(I# cidx#) !cs !(I# o#) !(I# d#) = h o# (H hs') cidx# cs d#

{-# INLINE recover #-}
recover :: Σ s -> QD -> QST s (Maybe a) -> QST s (Handled s a)
recover σs d k = [||
  do $$(rollback σs) $$d
     handled $$k
  ||]

nextSafe :: Bool -> Input -> QO -> TExpQ (Char -> Bool) -> (QO -> TExpQ Char -> QST s (Maybe a)) -> QST s (Maybe a) -> QST s (Maybe a)
nextSafe True input o p good bad = [|| let !c = $$(charAt input) $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else $$bad ||]
nextSafe False input o p good bad = [||
    let bad' = $$bad in
      if  $$(size input) > $$o then let !c = $$(charAt input) $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else bad'
      else bad'
  ||]