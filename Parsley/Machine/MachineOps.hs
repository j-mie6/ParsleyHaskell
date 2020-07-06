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
module Parsley.Machine.MachineOps where

import Parsley.Common.Utils   (Code)
import Parsley.Common.Indexed (Nat(..))
import Control.Monad.ST       (ST)
import Data.STRef             (STRef, writeSTRef, readSTRef, newSTRef)
import Data.STRef.Unboxed     (STRefU)
import GHC.Exts               (TYPE)
import Parsley.Machine.Input  (BoxOps(..), InputOps, next, Unboxed, OffWith, UnpackedLazyByteString, Stream{-, representationTypes-})
import Data.Text              (Text)
import Data.Void              (Void)

#define inputInstances(derivation) \
derivation(Int)                    \
derivation((OffWith [Char]))       \
derivation((OffWith Stream))       \
derivation(UnpackedLazyByteString) \
derivation(Text)

data OpStack xs where
  Empty :: OpStack '[]
  Op :: Code x -> OpStack xs -> OpStack (x ': xs)

data Vec n a where
  VNil :: Vec Zero a
  VCons :: a -> Vec n a -> Vec (Succ n) a

type HandlerStack n s o a = Vec n (Code (Handler s o a))

type Handler s o a = Unboxed o -> ST s (Maybe a)
type Cont s o a x = x -> Unboxed o -> ST s (Maybe a)

type SubRoutine s o a x = Cont s o a x -> Unboxed o -> Handler s o a -> ST s (Maybe a)
newtype QSubRoutine s o a x = QSubRoutine { unwrapSub :: Code (SubRoutine s o a x) }
newtype QJoin s o a x = QJoin { unwrapJoin :: Code (Cont s o a x) }

raise :: forall o n s a. Vec (Succ n) (Code (Handler s o a)) -> Code (Handler s o a)
raise (VCons h _) = h

setupHandler :: HandlerStack n s o a -> Code o
             -> (Code o -> Code (Handler s o a))
             -> (Vec (Succ n) (Code (Handler s o a)) -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))
setupHandler hs input h k = [||
    let handler = $$(h input)
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
  buildHandler :: BoxOps o => (Code o -> Code o -> Code (ST s (Maybe a))) -> Code o -> Code (Handler s o a)
  fatal :: Code (Handler s o a)

#define deriveHandlerOps(_o)                                \
instance HandlerOps _o where                                \
{                                                           \
  buildHandler h c = [||\o# -> $$(h c [||$$box o#||])||];   \
  fatal = [||\(!o#) -> return Nothing :: ST s (Maybe a)||]; \
};
inputInstances(deriveHandlerOps)

-- RIP Dream :(
{-$(let derive _o = [d|
        instance HandlerOps _o where
          fatal = [||\(!o#) -> return Nothing :: ST s (Maybe a)||]
        |] in traverse derive representationTypes)-}

callWithContinuation :: BoxOps o => Code (SubRoutine s o a x) -> Code (Cont s o a x) -> Code o -> Vec (Succ n) (Code (Handler s o a)) -> Code (ST s (Maybe a))
callWithContinuation sub ret input (VCons h _) = [||$$sub $$ret ($$unbox $$input) $! $$h||]

sat :: (?ops :: InputOps o) => Code o -> Code (Char -> Bool) -> ( Code Char -> Code o -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a)) -> Code (ST s (Maybe a))
sat input p good bad = next input $ \qc qinput' -> [||
    if $$p $$qc then $$(good qc qinput')
                else $$bad
  ||]