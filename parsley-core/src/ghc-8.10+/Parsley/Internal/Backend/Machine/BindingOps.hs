{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
{-# LANGUAGE AllowAmbiguousTypes,
             CPP,
             MagicHash #-}
{-|
Module      : Parsley.Internal.Backend.Machine.BindingOps
Description : Various functions that handle levity-polymorphic code bindings
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the parts of the code-base that deal with levity-polymorphic code.

For performance, and to help GHC optimise, parsley takes an aggressive stance with unboxing
and representing input using unlifted types. This means that the code generator is levity 
polymorphic. While the generated code itself is not polymorphic, to respect the soundness
of GHC, any code that is generated which explicitly creates an unlifted value is kept in
type-class methods and instantiated for every input type. All of these classes are found
here.

@since 1.4.0.0
-}
module Parsley.Internal.Backend.Machine.BindingOps (module Parsley.Internal.Backend.Machine.BindingOps) where

import Control.Monad.ST                                (ST)
import Data.Array.Unboxed                              (UArray)
import Data.ByteString.Internal                        (ByteString)
import Data.Text                                       (Text)
import Parsley.Internal.Backend.Machine.InputRep       (Rep)
import Parsley.Internal.Backend.Machine.Types.Base     (Handler#)
import Parsley.Internal.Backend.Machine.Types.Dynamics (DynSubroutine, DynCont, DynHandler)
import Parsley.Internal.Backend.Machine.Types.Statics  (StaCont#, StaHandler#)
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

{-|
Used to generate a binding for a handler.

@since 1.4.0.0
-}
class HandlerOps o where
  {-|
  Generate a let-bound handler and provide it to another continuation.

  @since 1.4.0.0
  -}
  bindHandler# :: StaHandler# s o a            -- ^ Static handler to bind
               -> (DynHandler s o a -> Code b) -- ^ The continuation that expects the bound handler
               -> Code b

#define deriveHandlerOps(_o)                    \
instance HandlerOps _o where                    \
{                                               \
  bindHandler# h k = [||                        \
    let handler (o# :: Rep _o) = $$(h [||o#||]) \
    in $$(k [||handler||])                      \
  ||];                                          \
};
inputInstances(deriveHandlerOps)

{-|
Generates join-point bindings.

@since 1.4.0.0
-}
class JoinBuilder o where
  {-| 
  Generate a let-bound join point and provide it to another continuation.

  @since 1.4.0.0
  -}
  setupJoinPoint# :: StaCont# s o a x            -- ^ The join point to bind.
                  -> (DynCont s o a x -> Code b) -- ^ The continuation that expects the bound join point
                  -> Code b

#define deriveJoinBuilder(_o)                                                             \
instance JoinBuilder _o where                                                             \
{                                                                                         \
  setupJoinPoint# binding k =                                                             \
    [|| let join x !(o# :: Rep _o) = $$(binding [||x||] [||o#||]) in $$(k [||join||]) ||] \
};
inputInstances(deriveJoinBuilder)

{-|
Various functions for creating bindings for recursive parsers.

@since 1.4.0.0
-}
class RecBuilder o where
  {-|
  Create a binder for specialist iterating handlers: these have two arguments,
  one for the current captured offset and then the second for the offset at
  point of failure.

  @since 1.4.0.0
  -}
  bindIterHandler# :: (Code (Rep o) -> StaHandler# s o a)        -- ^ The iter handler to bind
                   -> (Code (Rep o -> Handler# s o a) -> Code b) -- ^ The continuation that accepts the bound handler
                   -> Code b

  {-|
  Creates a binding for a tail-recursive loop.

  @since 1.4.0.0
  -}
  bindIter# :: Code (Rep o)                                                -- ^ Initial offset for the loop.
            -> (DynHandler s o a -> Code (Rep o) -> Code (ST s (Maybe a))) -- ^ The code for the loop given handler and offset.
            -> Code (ST s (Maybe a))                                       -- ^ Code of the executing loop.

  {-|
  Creates a binding for a regular let-bound parser.

  @since 1.4.0.0
  -}
  bindRec#  :: (DynSubroutine s o a x -> DynCont s o a x -> Code (Rep o) -> DynHandler s o a -> Code (ST s (Maybe a))) -- ^ Code for the binding, accepting itself as an argument.
            -> DynSubroutine s o a x                                                                                   -- ^ The code that represents this binding's name.

#define deriveRecBuilder(_o)                                                                           \
instance RecBuilder _o where                                                                           \
{                                                                                                      \
  bindIterHandler# h k = [||                                                                           \
      let handler (c# :: Rep _o) (o# :: Rep _o) = $$(h [||c#||] [||o#||]) in $$(k [||handler||])       \
    ||];                                                                                               \
  bindIter# o l = [||                                                                                  \
      let loop !(o# :: Rep _o) = $$(l [||loop||] [||o#||])                                             \
      in loop $$o                                                                                      \
    ||];                                                                                               \
  bindRec# binding =                                                                                   \
    {- The idea here is to try and reduce the number of times registers have to be passed around -}    \
    [|| let self ret !(o# :: Rep _o) h = $$(binding [||self||] [||ret||] [||o#||] [||h||]) in self ||] \
};
inputInstances(deriveRecBuilder)

{- Marshalling Operations -}
{-|
These operations are responsible for materialising the static handlers
and continuations into dynamic forms that can be passed into other bindings
at runtime.

@since 1.4.0.0
-}
class MarshalOps o where
  {-|
  Converts a static handler into a dynamic one (represented as a lambda)

  @since 1.4.0.0
  -}
  dynHandler# :: StaHandler# s o a -> DynHandler s o a

  {-|
  Converts a static continuation into a dynamic one (represented as a lambda)

  @since 1.4.0.0
  -}
  dynCont# :: StaCont# s o a x -> DynCont s o a x

#define deriveMarshalOps(_o)                                          \
instance MarshalOps _o where                                          \
{                                                                     \
  dynHandler# sh = [||\ !(o# :: Rep _o) -> $$(sh [||o#||]) ||];       \
  dynCont# sk = [||\ x (o# :: Rep _o) -> $$(sk [||x||] [||o#||]) ||]; \
};
inputInstances(deriveMarshalOps)