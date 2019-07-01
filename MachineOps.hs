{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             BangPatterns,
             MagicHash,
             UnboxedTuples,
             TemplateHaskell #-}
module MachineOps where

import Utils              (TExpQ)
import Control.Monad.ST   (ST)
import Data.STRef         (STRef, writeSTRef, readSTRef, newSTRef)
import GHC.Prim           (Int#)
import GHC.Exts           (Int(..))
import Safe.Coerce        (coerce)

data SList a = !a ::: SList a | SNil
data HList xs where
  HNil :: HList '[]
  HCons :: !a -> HList as -> HList (a ': as)

newtype H s a = H (SList (O# -> ST s (Maybe a)))
type X = HList
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
data InputOps = InputOps { _more  :: TExpQ (Int -> Bool)
                         , _next  :: TExpQ (Int -> (# Char, Int #))
                         , _same  :: TExpQ (Int -> Int -> Bool)
                         , _box   :: TExpQ (Int# -> Int)
                         , _unbox :: TExpQ (Int -> Int#) }

type QH s a = TExpQ (H s a)
type QX xs = TExpQ (X xs)
type QK s ks a = TExpQ (K s ks a)
type QO o = TExpQ O
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
pushH :: (O# -> ST s (Maybe a)) -> H s a -> H s a
pushH !h (H hs) = H (h:::hs)
{-# INLINE popH_ #-}
popH_ :: H s a -> H s a
popH_ (H (_:::hs)) = H hs
{-# INLINE pokeH #-}
pokeH :: (O# -> ST s (Maybe a)) -> H s a -> H s a
pokeH !h (H (_:::hs)) = H (h:::hs)

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

setupHandler :: QH s a -> QO o -> TExpQ (H s a -> O# -> O# -> ST s (Maybe a)) ->
                                 (QH s a -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandler hs !o !h !k = k [|| let I# c# = $$o in pushH (\(!o#) -> $$h $$hs o# c#) $$hs ||]

{-# INLINE raise #-}
raise :: H s a -> O -> ST s (Maybe a)
raise (H SNil) !o          = return Nothing
raise (H (h:::_)) !(I# o#) = h o#

nextSafe :: Bool -> InputOps -> QO o -> TExpQ (Char -> Bool) -> (QO o -> TExpQ Char -> QST s (Maybe a)) -> QST s (Maybe a) -> QST s (Maybe a)
nextSafe True input o p good bad = [|| let !(# c, o' #) = $$(_next input) $$o in if $$p c then $$(good [|| o' ||] [|| c ||]) else $$bad ||]
nextSafe False input o p good bad = [||
    let bad' = $$bad in
      if  $$(_more input) $$o then let !(# c, o' #) = $$(_next input) $$o in if $$p c then $$(good [|| o' ||] [|| c ||]) else bad'
      else bad'
  ||]