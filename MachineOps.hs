{-# LANGUAGE GADTs,
             DataKinds,
             KindSignatures,
             PolyKinds,
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
import GHC.Exts           (Int(..), TYPE)
import Safe.Coerce        (coerce)
import Input              (CRef)

data SList a = !a ::: SList a | SNil
data HList xs where
  HNil :: HList '[]
  HCons :: !a -> HList as -> HList (a ': as)

newtype H s o a = H (SList (O# -> ST s (Maybe a)))
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
type K k s (o# :: TYPE k) xs a = X xs -> O# -> ST s (Maybe a)
data InputOps s o = InputOps { _more      :: TExpQ (O -> Bool)
                             , _next      :: TExpQ (O -> (# Char, O #))
                             , _same      :: TExpQ (O -> O -> Bool)
                             , _box       :: TExpQ (O# -> O)
                             , _unbox     :: TExpQ (O -> O#)
                             , _newCRef   :: TExpQ (O -> ST s (CRef s O))
                             , _readCRef  :: TExpQ (CRef s O -> ST s O)
                             , _writeCRef :: TExpQ (CRef s O -> O -> ST s ()) }

type QH s o a = TExpQ (H s o a)
type QX xs = TExpQ (X xs)
type QK k s (o# :: TYPE k) ks a = TExpQ (K k s o# ks a)
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

makeK :: ST s (K k s o '[] a)
makeK = return $! noreturn
noreturn :: K k s o xs a
noreturn xs = error "Machine is only permitted return-by-failure"

makeH :: ST s (H s o a)
makeH = return $! H SNil
pushH :: (O# -> ST s (Maybe a)) -> H s o a -> H s o a
pushH !h (H hs) = H (h:::hs)
{-# INLINE popH_ #-}
popH_ :: H s o a -> H s o a
popH_ (H (_:::hs)) = H hs

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

setupHandler :: QH s o a -> QO o -> TExpQ (H s o a -> O# -> O# -> ST s (Maybe a)) ->
                                    (QH s o a -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandler hs !o !h !k = k [|| let I# c# = $$o in pushH (\(!o#) -> $$h $$hs o# c#) $$hs ||]

{-# INLINE raise #-}
raise :: H s o a -> O -> ST s (Maybe a)
raise (H SNil) !o          = return Nothing
raise (H (h:::_)) !(I# o#) = h o#

nextSafe :: Bool -> InputOps s o -> QO o -> TExpQ (Char -> Bool) -> (QO o -> TExpQ Char -> QST s (Maybe a)) -> QST s (Maybe a) -> QST s (Maybe a)
nextSafe True input o p good bad = [|| let !(# c, o' #) = $$(_next input) $$o in if $$p c then $$(good [|| o' ||] [|| c ||]) else $$bad ||]
nextSafe False input o p good bad = [||
    let bad' = $$bad in
      if  $$(_more input) $$o then let !(# c, o' #) = $$(_next input) $$o in if $$p c then $$(good [|| o' ||] [|| c ||]) else bad'
      else bad'
  ||]