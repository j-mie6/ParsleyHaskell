{-# LANGUAGE GADTs,
             DataKinds,
             KindSignatures,
             PolyKinds,
             TypeOperators,
             BangPatterns,
             MagicHash,
             TemplateHaskell,
             TypeSynonymInstances,
             RankNTypes,
             CPP,
             ImplicitParams,
             ScopedTypeVariables,
             FlexibleInstances,
             AllowAmbiguousTypes,
             TypeApplications #-}
module MachineOps where

import Utils              (Code)
import Indexed            (Nat(..))
import Control.Monad.ST   (ST)
import Data.STRef         (STRef, writeSTRef, readSTRef, newSTRef)
import Data.STRef.Unboxed (STRefU)
import GHC.Exts           (TYPE)
import Safe.Coerce        (coerce)
import Input              (BoxOps(unbox), InputOps, next, Unboxed, OffWith, UnpackedLazyByteString, Stream{-, representationTypes-})
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

type AbsExec s o a x = (x -> Unboxed o -> ST s (Maybe a)) -> Unboxed o -> H s o a -> ST s (Maybe a)
newtype QAbsExec s o a x = QAbsExec (Code (AbsExec s o a x))
newtype QJoin s o a x = QJoin (Code (x -> Unboxed  o -> ST s (Maybe a)))

tailQ :: QList (x ': xs) -> QList xs
tailQ (QCons x xs) = xs

headQ :: QList (x ': xs) -> Code x
headQ (QCons x xs) = x

raise :: forall o n s a. Vec (Succ n) (Code (H s o a)) -> Code (H s o a)
raise (VCons h _) = h

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
  halt :: Code (a -> Unboxed o -> ST s (Maybe a))
  noreturn :: Code (r -> Unboxed o -> ST s (Maybe a))

#define deriveReturnOps(_o)                                       \
instance ReturnOps _o where                                       \
{                                                                 \
  halt = [||\x o# -> return $! Just x||];                         \
  noreturn = [||\x o# -> error "Return is not permitted here"||]; \
};
inputInstances(deriveReturnOps)

class BoxOps o => FailureOps o where
  setupHandler :: Vec n (Code (H s o a)) -> Code o
               -> (Code o -> Code (H s o a))
               -> (Vec (Succ n) (Code (H s o a)) -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))
  fatal :: Code (H s o a)

#define deriveFailureOps(_o)                                \
instance FailureOps _o where                                \
{                                                           \
  setupHandler hs o h k = [||                               \
    let handler ((!o#) :: Unboxed _o) = $$(h o) o#          \
    in $$(k (VCons [||handler||] hs)) ||];                  \
  fatal = [||\(!o#) -> return Nothing :: ST s (Maybe a)||]; \
};
inputInstances(deriveFailureOps)

-- RIP Dream :(
{-$(let derive _o = [d|
        instance FailureOps _o where
          setupHandler hs o h k = [||
              let handler ((!o#) :: Unboxed _o) = $$(h o) o#
              in $$(k (VCons [||handler||] hs))
            ||]
          fatal = [||\(!o#) -> return Nothing :: ST s (Maybe a)||]
        |] in traverse derive representationTypes)-}

runConcrete :: BoxOps o => Vec (Succ n) (Code (H s o a)) -> Code (AbsExec s o a x) -> Code (x -> Unboxed o -> ST s (Maybe a)) -> Code o -> Code (ST s (Maybe a))
runConcrete (VCons h _) m ret o = [||$$m $$ret ($$unbox $$o) $! $$h||]

sat :: (?ops :: InputOps o) => Code o -> Code (Char -> Bool) -> (Code o -> Code Char -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a)) -> Code (ST s (Maybe a))
sat o p good bad = next o $ \qc qo' -> [||
    if $$p $$qc then $$(good qo' qc)
                else $$bad
  ||]