{-# LANGUAGE GADTs,
             DataKinds,
             KindSignatures,
             PolyKinds,
             TypeOperators,
             BangPatterns,
             MagicHash,
             TemplateHaskell,
             TypeSynonymInstances,
             CPP,
             ImplicitParams,
             ScopedTypeVariables,
             FlexibleInstances,
             AllowAmbiguousTypes,
             TypeApplications,
             ConstrainedClassMethods #-}
module MachineOps where

import Utils              (Code)
import Indexed            (Nat(..))
import Control.Monad.ST   (ST)
import Data.STRef         (STRef, writeSTRef, readSTRef, newSTRef)
import Data.STRef.Unboxed (STRefU)
import GHC.Exts           (TYPE)
import Safe.Coerce        (coerce)
import Input              (BoxOps(..), InputOps, next, Unboxed, OffWith, UnpackedLazyByteString, Stream{-, representationTypes-})
import Data.Text          (Text)
import Data.Void          (Void)

#define inputInstances(derivation) \
derivation(Int)                    \
derivation((OffWith [Char]))       \
derivation((OffWith Stream))       \
derivation(UnpackedLazyByteString) \
derivation(Text)

data QList xs where
  QNil :: QList '[]
  QCons :: Code x -> QList xs -> QList (x ': xs)

data Vec n a where
  VNil :: Vec Zero a
  VCons :: a -> Vec n a -> Vec (Succ n) a

type H s o a = Unboxed o -> ST s (Maybe a)
type Cont s o a x = x -> Unboxed o -> ST s (Maybe a)

type SubRoutine s o a x = Cont s o a x -> Unboxed o -> H s o a -> ST s (Maybe a)
newtype QSubRoutine s o a x = QSubRoutine (Code (SubRoutine s o a x))
newtype QJoin s o a x = QJoin (Code (Cont s o a x))

tailQ :: QList (x ': xs) -> QList xs
tailQ (QCons x xs) = xs

headQ :: QList (x ': xs) -> Code x
headQ (QCons x xs) = x

raise :: forall o n s a. Vec (Succ n) (Code (H s o a)) -> Code (H s o a)
raise (VCons h _) = h

setupHandler :: Vec n (Code (H s o a)) -> Code o
             -> (Code o -> Code (H s o a))
             -> (Vec (Succ n) (Code (H s o a)) -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))
setupHandler hs o h k = [||
    let handler = $$(h o)
    in $$(k (VCons [||handler||] hs))
  ||]

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

class ReturnOps o where
  halt :: Code (Cont s o a a)
  noreturn :: Code (Cont s o a Void)

#define deriveReturnOps(_o)                                       \
instance ReturnOps _o where                                       \
{                                                                 \
  halt = [||\x o# -> return $! Just x||];                         \
  noreturn = [||\x o# -> error "Return is not permitted here"||]; \
};
inputInstances(deriveReturnOps)

class HandlerOps o where
  buildHandler :: BoxOps o => (Code o -> Code o -> Code (ST s (Maybe a))) -> Code o -> Code (H s o a)
  fatal :: Code (H s o a)

#define deriveHandlerOps(_o)                                \
instance HandlerOps _o where                                \
{                                                           \
  buildHandler h c = [||\o# -> $$(h c [||$$box o#||])||];   \
  fatal = [||\(!o#) -> return Nothing :: ST s (Maybe a)||]; \
};
inputInstances(deriveHandlerOps) -- \c -> [||\o# -> $$(mh (γ {xs = QCons c (xs γ), o = [||$$box o#||]}))||]

-- RIP Dream :(
{-$(let derive _o = [d|
        instance HandlerOps _o where
          fatal = [||\(!o#) -> return Nothing :: ST s (Maybe a)||]
        |] in traverse derive representationTypes)-}

callWithContinuation :: BoxOps o => QSubRoutine s o a x -> Code (Cont s o a x) -> Code o -> Vec (Succ n) (Code (H s o a)) -> Code (ST s (Maybe a))
callWithContinuation (QSubRoutine sub) ret o (VCons h _) = [||$$sub $$ret ($$unbox $$o) $! $$h||]

sat :: (?ops :: InputOps o) => Code o -> Code (Char -> Bool) -> (Code o -> Code Char -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a)) -> Code (ST s (Maybe a))
sat o p good bad = next o $ \qc qo' -> [||
    if $$p $$qc then $$(good qo' qc)
                else $$bad
  ||]