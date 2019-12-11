{-# LANGUAGE GADTs,
             DataKinds,
             KindSignatures,
             PolyKinds,
             TypeOperators,
             BangPatterns,
             MagicHash,
             UnboxedTuples,
             TemplateHaskell,
             TypeSynonymInstances,
             RankNTypes,
             CPP,
             ImplicitParams,
             ScopedTypeVariables,
             FlexibleInstances #-}
module MachineOps where

import Utils              (Code)
import Control.Monad.ST   (ST)
import Data.STRef         (STRef, writeSTRef, readSTRef, newSTRef)
import Data.STRef.Unboxed (STRefU)
import GHC.Exts           (TYPE, type (~~))
import Safe.Coerce        (coerce)
import Input              (Rep, Unboxed, OffWith, UnpackedLazyByteString, Stream)
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

type H s o a = Unboxed o -> ST s (Maybe a)
data InputOps s o = InputOps { _more       :: Code (o -> Bool)
                             , _next       :: Code (o -> (# Char, o #))
                             , _same       :: Code (o -> o -> Bool)
                             , _box        :: Code (Unboxed o -> o)
                             , _unbox      :: Code (o -> Unboxed o)
                             , _newCRef    :: Code (o -> ST s (STRefU s Int))
                             , _readCRef   :: Code (STRefU s Int -> ST s o)
                             , _writeCRef  :: Code (STRefU s Int -> o -> ST s ())
                             , _shiftLeft  :: Code (o -> Int -> o)
                             , _shiftRight :: Code (o -> Int -> o)
                             , _offToInt   :: Code (o -> Int) }

more       :: (?ops :: InputOps s o) => Code (o -> Bool)
more       = _more       ?ops
next       :: (?ops :: InputOps s o) => Code (o -> (# Char, o #))
next       = _next       ?ops
same       :: (?ops :: InputOps s o) => Code (o -> o -> Bool)
same       = _same       ?ops
unbox      :: (?ops :: InputOps s o) => Code (o -> Unboxed o)
unbox      = _unbox      ?ops
box        :: (?ops :: InputOps s o) => Code (Unboxed o -> o)
box        = _box        ?ops
newCRef    :: (?ops :: InputOps s o) => Code (o -> ST s (STRefU s Int))
newCRef    = _newCRef    ?ops
readCRef   :: (?ops :: InputOps s o) => Code (STRefU s Int -> ST s o) 
readCRef   = _readCRef   ?ops
writeCRef  :: (?ops :: InputOps s o) => Code (STRefU s Int -> o -> ST s ())
writeCRef  = _writeCRef  ?ops
shiftLeft  :: (?ops :: InputOps s o) => Code (o -> Int -> o)
shiftLeft  = _shiftLeft  ?ops
shiftRight :: (?ops :: InputOps s o) => Code (o -> Int -> o)
shiftRight = _shiftRight ?ops
offToInt   :: (?ops :: InputOps s o) => Code (o -> Int)
offToInt   = _offToInt   ?ops

type AbsExec s o a x = (x -> Unboxed o -> ST s (Maybe a)) -> Unboxed o -> (Unboxed o -> ST s (Maybe a)) -> ST s (Maybe a)
newtype QAbsExec s o a x = QAbsExec (Code (AbsExec s o a x))
newtype QJoin s o a x = QJoin (Code (x -> Unboxed o -> ST s (Maybe a)))

tailQ :: QList (x ': xs) -> QList xs
tailQ (QCons x xs) = xs

headQ :: QList (x ': xs) -> Code x
headQ (QCons x xs) = x

noreturn :: forall s r x (o# :: TYPE r) a. x -> o# -> ST s (Maybe a)
noreturn x = error "Machine is only permitted return-by-failure"

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

{-setupHandler :: (?ops :: InputOps s o, FailureOps o) => [Code (H s o a)] -> Code o
             -> (Code (H s o a) -> Code o -> Code (Unboxed o -> ST s (Maybe a)))
             -> ([Code (H s o a)] -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))
setupHandler hs o h k = [|| let handler = $$(h (raise hs) o) in $$(k ([||handler||]:hs)) ||]-}
--setupHandler hs o h k = k ((h (raise hs) o):hs)

class FailureOps o where
  setupHandler :: (?ops :: InputOps s o) => [Code (H s o a)] -> Code o
               -> (Code (H s o a) -> Code o -> Code (Unboxed o -> ST s (Maybe a)))
               -> ([Code (H s o a)] -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))
  raise :: (?ops :: InputOps s o) => [Code (H s o a)] -> Code (Unboxed o -> ST s (Maybe a))

#define deriveFailureOps(_o)                                   \
instance FailureOps _o where                                   \
{                                                              \
  setupHandler [] o h k = k [h (raise []) o];                  \
  setupHandler hs o h k = [||                                  \
    let handler ((!o#) :: Unboxed _o) = $$(h (raise hs) o) o#  \
    in $$(k ([||handler||]:hs)) ||];                           \
  raise [] = [||\(!o#) -> return Nothing :: ST s (Maybe a)||]; \
  raise (h:_) = h;                                             \
};
inputInstances(deriveFailureOps)

-- RIP Dream :(
{-$(let derive _o = [d| 
        instance FailureOps _o where
          setupHandler ops hs !o !h !k = k [|| pushH (\(!o#) -> $$h $$hs o# ($$(_unbox ops) $$o)) $$hs ||]
          raise ops = [||\(H hs) (!o) -> case hs of 
              SNil -> return Nothing
              h:::_ -> h ($$(_unbox ops) o)
            ||]
        |] in traverse derive inputTypes)-}

runConcrete :: (?ops :: InputOps s o, FailureOps o) => [Code (H s o a)] -> Code (AbsExec s o a x) -> Code (x -> Unboxed o -> ST s (Maybe a)) -> Code o -> Code (ST s (Maybe a))
runConcrete hs m ret o = [||$$m $$ret ($$unbox $$o) $! $$(raise hs)||]

nextSafe :: (?ops :: InputOps s o) => Bool -> Code o -> Code (Char -> Bool) -> (Code o -> Code Char -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a)) -> Code (ST s (Maybe a))
nextSafe True o p good bad = [|| let !(# c, o' #) = $$next $$o in if $$p c then $$(good [|| o' ||] [|| c ||]) else $$bad ||]
nextSafe False o p good bad = [||
    let bad' = $$bad in
      if  $$more $$o then let !(# c, o' #) = $$next $$o in if $$p c then $$(good [|| o' ||] [|| c ||]) else bad'
      else bad'
  ||]