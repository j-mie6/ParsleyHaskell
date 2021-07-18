{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
{-# LANGUAGE AllowAmbiguousTypes,
             CPP,
             MagicHash #-}
module Parsley.Internal.Backend.Machine.BindingOps (module Parsley.Internal.Backend.Machine.BindingOps) where

import Control.Monad.ST                                (ST)
import Data.Array.Unboxed                              (UArray)
import Data.ByteString.Internal                        (ByteString)
import Data.Text                                       (Text)
import Parsley.Internal.Backend.Machine.InputRep       (Rep)
import Parsley.Internal.Backend.Machine.Types.Base     (Handler#)
import Parsley.Internal.Backend.Machine.Types.Dynamics (DynSubRoutine, DynCont, DynHandler)
import Parsley.Internal.Backend.Machine.Types.Statics  (StaCont#, StaHandler, StaHandler#, staHandler# )
import Parsley.Internal.Common.Utils                   (Code)
import Parsley.Internal.Core.InputTypes                (Text16, CharList, Stream)

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString)

#define inputInstances(derivation) \
derivation([Char])                 \
derivation((UArray Int Char))      \
derivation(Text16)                 \
derivation(ByteString)             \
derivation(CharList)               \
derivation(Stream)                 \
derivation(Lazy.ByteString)        \
derivation(Text)

class HandlerOps o where
  bindHandler# :: StaHandler s o a -> (DynHandler s o a -> Code b) -> Code b

#define deriveHandlerOps(_o)                                \
instance HandlerOps _o where                                \
{                                                           \
  bindHandler# h k = [||                                    \
    let handler (o# :: Rep _o) = $$(staHandler# h [||o#||]) \
    in $$(k [||handler||])                                  \
  ||];                                                      \
};
inputInstances(deriveHandlerOps)

class JoinBuilder o where
  setupJoinPoint# :: StaCont# s o a x -> (DynCont s o a x -> Code b) -> Code b

#define deriveJoinBuilder(_o)                                                             \
instance JoinBuilder _o where                                                             \
{                                                                                         \
  setupJoinPoint# binding k =                                                             \
    [|| let join x !(o# :: Rep _o) = $$(binding [||x||] [||o#||]) in $$(k [||join||]) ||] \
};
inputInstances(deriveJoinBuilder)

class RecBuilder o where
  bindIterHandler# :: (Code (Rep o) -> StaHandler# s o a)
                   -> (Code (Rep o -> Handler# s o a) -> Code b)
                   -> Code b
  buildIter# :: Code (Rep o)
             -> (Code (Rep o -> ST s (Maybe a)) -> Code (Rep o) -> Code (ST s (Maybe a)))
             -> Code (ST s (Maybe a))
  buildRec#  :: (DynSubRoutine s o a x -> DynCont s o a x -> Code (Rep o) -> DynHandler s o a -> Code (ST s (Maybe a)))
             -> DynSubRoutine s o a x

#define deriveRecBuilder(_o)                                                                           \
instance RecBuilder _o where                                                                           \
{                                                                                                      \
  bindIterHandler# h k = [||                                                                           \
      let handler (c# :: Rep _o) (o# :: Rep _o) = $$(h [||c#||] [||o#||]) in $$(k [||handler||])       \
    ||];                                                                                               \
  buildIter# o l = [||                                                                                 \
      let loop !(o# :: Rep _o) = $$(l [||loop||] [||o#||])                                             \
      in loop $$o                                                                                      \
    ||];                                                                                               \
  buildRec# binding =                                                                                  \
    {- The idea here is to try and reduce the number of times registers have to be passed around -}    \
    [|| let self ret !(o# :: Rep _o) h = $$(binding [||self||] [||ret||] [||o#||] [||h||]) in self ||] \
};
inputInstances(deriveRecBuilder)

{- Marshalling Operations -}
class MarshalOps o where
  dynHandler# :: StaHandler# s o a -> DynHandler s o a
  dynCont# :: StaCont# s o a x -> DynCont s o a x

#define deriveMarshalOps(_o)                                          \
instance MarshalOps _o where                                          \
{                                                                     \
  dynHandler# sh = [||\ !(o# :: Rep _o) -> $$(sh [||o#||]) ||];       \
  dynCont# sk = [||\ x (o# :: Rep _o) -> $$(sk [||x||] [||o#||]) ||]; \
};
inputInstances(deriveMarshalOps)