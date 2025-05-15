{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
{-# OPTIONS_GHC -Wno-deprecations #-} --FIXME: remove when Text16 is removed
{-# LANGUAGE AllowAmbiguousTypes,
             CPP,
             MagicHash,
             TypeApplications,
             ScopedTypeVariables,
             FunctionalDependencies,
             TypeFamilies,
             InstanceSigs,
             UnboxedTuples #-}
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

import Control.Monad.ST                                 (ST)
import Data.Array.Unboxed                               (UArray)
import Data.ByteString.Internal                         (ByteString)
import Data.Text                                        (Text)
import Data.Kind                                        (Type)
import Data.Proxy                                       (Proxy)
import Language.Haskell.TH                              (newName, Q, unsafeCodeCoerce, Pat (..), Name, unTypeCode)
import Language.Haskell.TH.Syntax                       (Exp(..), Dec(FunD), Clause (..), Body (..))
import Parsley.Internal.Backend.Machine.InputRep        (DynRep)
import Parsley.Internal.Backend.Machine.Types.Base      (Handler#, Pos)
import Parsley.Internal.Backend.Machine.Types.Dynamics  (DynCont, DynHandler, DynFunc)
import Parsley.Internal.Backend.Machine.Types.Input     (Input#(..))
import Parsley.Internal.Backend.Machine.Types.Statics   (StaCont#, StaHandler#, StaSubroutine#, StaRegisterStack#, toDynRegStack)
import Parsley.Internal.Backend.Machine.Types.Registers (RegBindNames (..), Regs (..), RegTHNames(..))
import Parsley.Internal.Common.Utils                    (Code)
import Parsley.Internal.Core.InputTypes                 (Text16, CharList, Stream)
import Parsley.Internal.Common.THUtils                  (eta)

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString)

#define inputInstances(derivation) \
derivation(String)                 \
derivation((UArray Int Char))      \
derivation(Text16)                 \
derivation(ByteString)             \
derivation(CharList)               \
derivation(Stream)                 \
derivation(Lazy.ByteString)        \
derivation(Text)


-- Helpers

supplyRegs :: forall rs s o a. RegBindNames rs -> Code (LoopRoutine rs s o a) -> Code (LoopRoutine '[] s o a)
supplyRegs NoName l                = l
supplyRegs (RegName _ name rest) l = supplyRegs  @_ @_ @o rest [|| $$l $$name ||]

-- Generate new names for register binds
nameRegs :: forall rs. RegBindNames rs -> Q (RegTHNames rs)
nameRegs NoName             = pure NoTHName 
nameRegs (RegName s _ rest) = do 
  rest' <- nameRegs rest 
  regname <- newName "r"
  return (RegTHName s regname rest')

-- Same as `nameRegs` but for unbound registers
nameRegs' :: forall rs. Regs rs -> Q (RegTHNames rs)
nameRegs' NoRegs = pure NoTHName 
nameRegs' (Regs s rest) = do
  rest' <- nameRegs' rest 
  regname <- newName "r"
  return (RegTHName s regname rest')

convertNamesToCode :: forall rs. RegTHNames rs -> RegBindNames rs 
convertNamesToCode NoTHName                = NoName
convertNamesToCode (RegTHName r name rest) = RegName r (unsafeCodeCoerce (return (VarE name))) (convertNamesToCode rest )

extractNameFromPat :: Pat -> Name
extractNameFromPat (SigP (VarP name) _ )         = name
extractNameFromPat (SigP (BangP (VarP name)) _ ) = name
extractNameFromPat (VarP name)                   = name
extractNameFromPat (BangP (VarP name))           = name
extractNameFromPat _ = error "Could not extract name from Pat!" -- TODO: better error??

namesToArgList :: forall rs. RegTHNames rs -> [Pat] -> [Pat]
namesToArgList NoTHName tail                = tail
namesToArgList (RegTHName _ name rest) tail = VarP name:namesToArgList rest tail 

feedRegNames :: forall rs x. RegBindNames rs -> StaRegisterStack# rs x -> Code x
feedRegNames NoName k              = k 
feedRegNames (RegName _ name rs) k = feedRegNames rs (k name) 


{-|
Used to generate a binding for a handler.

@since 1.4.0.0
-}
class HandlerOps o where
  {-|
  Generate a let-bound handler and provide it to another continuation.

  @since 1.4.0.0
  -}
  bindHandler# :: (RegBindNames hs -> StaHandler# '[] s o a) -- ^ Static handler to bind, waiting to capture the register binds
               -> Regs hs                                    -- ^ Registers required by handler, and which to bind in handler definition.
               -> (DynHandler hs s o a -> Code b)            -- ^ The continuation that expects the bound handler
               -> Code b

-- Function to create the bind for in `HandlerOps`

createHandlerDef :: forall hs s o a b. (RegBindNames hs -> StaHandler# '[] s o a) -> Regs hs -> Q Pat -> (DynHandler hs s o a -> Code b) -> Code b
createHandlerDef hbody regs qoff k = unsafeCodeCoerce $ do 
        handlerName <- newName "handler"
        regNames <- nameRegs' regs
        pos <- [p| (pos :: Pos) |]
        off <- qoff
        let makebind = do
                        let posE = pure $ VarE $ extractNameFromPat pos
                        let offE = pure $ VarE $ extractNameFromPat off
                        body <- unTypeCode $ hbody (convertNamesToCode regNames) (Input# (unsafeCodeCoerce offE) (unsafeCodeCoerce posE))
                        return $ FunD handlerName [Clause (namesToArgList regNames [pos, off]) (NormalB body) [] ]
        k' <- unTypeCode $ k (unsafeCodeCoerce $ return (VarE handlerName))
        bind <- makebind
        return (LetE [bind] k')

#define deriveHandlerOps(_o)                                                                \
instance HandlerOps _o where                                                                \
{                                                                                           \
  bindHandler# h freeRegs = createHandlerDef @_ @_ @_o h freeRegs [p| (!o# :: DynRep _o) |] \
};
inputInstances(deriveHandlerOps);


createRegStackDecl :: forall rs x. Regs rs -> StaRegisterStack# rs x -> Q Exp
createRegStackDecl regs k = do; boundRegsNames <- nameRegs' regs; unTypeCode $ feedRegNames @rs @x (convertNamesToCode boundRegsNames) k

createJoinPointDef :: forall rs s o a x b. StaCont# rs s o a x -> Regs rs -> Q Pat -> (DynCont rs s o a x -> Code b) -> Code b
createJoinPointDef jbody regs qoff k = unsafeCodeCoerce $ do 
        joinName <- newName "join"
        xName <- newName "x"
        regNames <- nameRegs' regs
        pos <- [p| (pos :: Pos) |]
        off <- qoff
        let makebind = do
                        let posE = unsafeCodeCoerce $ pure $ VarE $ extractNameFromPat pos
                        let offE = unsafeCodeCoerce $ pure $ VarE $ extractNameFromPat off
                        let xE   = unsafeCodeCoerce $ pure $ VarE xName
                        body <- unTypeCode $ feedRegNames @rs @(ST s (Maybe a)) (convertNamesToCode regNames) (jbody xE (Input# offE posE)) 
                        return $ FunD joinName [Clause ([VarP xName, pos, off] ++ namesToArgList regNames []) (NormalB body) [] ]
        k' <- unTypeCode $ k (unsafeCodeCoerce $ return (VarE joinName))
        bind <- makebind
        return (LetE [bind] k')

{-|
Generates join-point bindings.

@since 1.4.0.0
-}
class JoinBuilder o where
  {-|
  Generate a let-bound join point and provide it to another continuation.

  @since 1.4.0.0
  -}
  setupJoinPoint# :: forall rs s a x b. Proxy s -> Proxy a -> Proxy x -> StaCont# rs s o a x -- ^ The join point to bind.
                  -> Regs rs                                                                 -- ^ Registers join point expects.
                  -> (DynCont rs s o a x -> Code b)                                          -- ^ The continuation that expects the bound join point
                  -> Code b

#define deriveJoinBuilder(_o)                                                                                     \
instance JoinBuilder _o where                                                                                     \
{                                                                                                                 \
  setupJoinPoint# :: forall rs s a x b. Proxy s -> Proxy a -> Proxy x -> StaCont# rs s _o a x                     \
                  -> Regs rs                                                                                      \
                  -> (DynCont rs s _o a x -> Code b)                                                              \
                  -> Code b;                                                                                      \
  setupJoinPoint# _ _ _ binding regs = createJoinPointDef @rs @s @_o @a @x binding regs [p| (!o# :: DynRep _o) |] \
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
  bindIterHandler# :: (RegBindNames hs -> (Input# o -> Input# o -> Code (ST s (Maybe a)))) -- ^ The iter handler to bind
                   -> Regs hs
                   -> (Code (Pos -> DynRep o -> Handler# hs s o a) -> Code b) -- ^ The continuation that accepts the bound handler
                   -> Code b

  {-|
  Generalisation of `bindIter#` for when we have bound liquid registers.

  @since 1.4.0.0
  -}
  bindIter# :: Input# o                                                                  -- ^ Initial offset for the loop.
            -> RegBindNames rs
            -> (Code (LoopRoutine rs s o a) -> RegBindNames rs -> Input# o -> Code (ST s (Maybe a))) 
            -- ^ The code for the loop given self-call and offset. 
            -> Code (ST s (Maybe a))                                                           -- ^ Code of the executing loop.

  {-|
  Creates a binding for a regular let-bound parser.

  @since 1.4.0.0
  -}
  bindRec# :: forall rs hs ys s a x. DynFunc rs hs ys s o a x -- ^ Name of parser given at the top level
            -> Regs rs -> Proxy hs -> Proxy ys -- ^ Registers (and witnesses)
            -> (RegBindNames rs -> StaSubroutine# '[] hs ys s o a x )-- ^ Code for the binding, accepting itself as an argument.
            -> Q Dec  -- ^ The code that represents this binding's name.

-- Functions to create the bindings in `RecBuilder`

{-|
Type family to capture the arity of a loop body which might have multiple
liquid registers passed through it.
-}
type family LoopRoutine (xs :: [Type]) s o a where 
  LoopRoutine '[] s o a = Pos -> DynRep o -> ST s (Maybe a)
  LoopRoutine (x:xs) s o a = x -> LoopRoutine xs s o a  


createIterHandlerDef :: forall hs s o a b. (RegBindNames hs -> (Input# o -> Input# o -> Code (ST s (Maybe a)))) -> Regs hs -> Q Pat -> Q Pat -> (Code (Pos -> DynRep o -> Handler# hs s o a) -> Code b) -> Code b
createIterHandlerDef hbody regs qcoff qoff k = unsafeCodeCoerce $ do 
        handlerName <- newName "handler"
        regNames <- nameRegs' regs
        posc <- [p| (posc :: Pos) |]
        offc <- qcoff
        pos <- [p| (pos :: Pos) |]
        off <- qoff
        let makebind = do
                        let posE = pure $ VarE $ extractNameFromPat pos
                        let offE = pure $ VarE $ extractNameFromPat off
                        let poscE = pure $ VarE $ extractNameFromPat posc
                        let offcE = pure $ VarE $ extractNameFromPat offc
                        body <- unTypeCode $ hbody (convertNamesToCode regNames) (Input# (unsafeCodeCoerce offcE) (unsafeCodeCoerce poscE)) (Input# (unsafeCodeCoerce offE) (unsafeCodeCoerce posE))
                        return $ FunD handlerName [Clause ([posc, offc] ++ namesToArgList regNames [pos, off]) (NormalB body) [] ]
        k' <- unTypeCode $ k (unsafeCodeCoerce $ return (VarE handlerName))
        bind <- makebind
        return (LetE [bind] k')

createLoopDef :: forall rs s o a b. Input# o -> RegBindNames rs -> Q Pat -> (Code (LoopRoutine rs s o a) -> RegBindNames rs -> Input# o -> Code (ST s (Maybe a))) -> Code b
createLoopDef initialOffset regs qoff l = unsafeCodeCoerce $ do 
        joinName <- newName "loop"
        regNames <- nameRegs regs
        pos <- [p| (pos :: Pos) |]
        off <- qoff
        let makebind = do
                        let posE = pure $ VarE $ extractNameFromPat pos
                        let offE = pure $ VarE $ extractNameFromPat off
                        let body = l (unsafeCodeCoerce $ pure $ VarE joinName) (convertNamesToCode regNames) (Input# (unsafeCodeCoerce offE) (unsafeCodeCoerce posE))
                        body' <- unTypeCode body
                        return $ FunD joinName [Clause (namesToArgList regNames [pos, off]) (NormalB body') [] ]
        k' <- unTypeCode [|| $$(supplyRegs @_ @_ @o regs (unsafeCodeCoerce $ return (VarE joinName))) $$(pos# initialOffset) $$(off# initialOffset) ||]
        bind <- makebind
        return (LetE [bind] k')

createRecDef :: forall rs hs ys s o a x. DynFunc rs hs ys s o a x -> Regs rs -> (RegBindNames rs -> StaSubroutine# '[] hs ys s o a x) -> Q Pat -> Q Dec 
createRecDef name regs body qoff = do 
  recE <- unTypeCode name
  regNames <- nameRegs' regs
  -- fixed arguments
  ret <- [p| ret |]
  h   <- [p| h |]
  pos <- [p| (pos :: Pos) |]
  off <- qoff
  let retE = unsafeCodeCoerce $ pure $ VarE $ extractNameFromPat ret 
  let hE   = unsafeCodeCoerce $ pure $ VarE $ extractNameFromPat h
  let posE = unsafeCodeCoerce $ pure $ VarE $ extractNameFromPat pos
  let offE = unsafeCodeCoerce $ pure $ VarE $ extractNameFromPat off
  let recName = extractNameFromExpr recE
  body' <- unTypeCode $ body (convertNamesToCode regNames) retE hE (Input# offE posE)
  return $ FunD recName [Clause (namesToArgList regNames [ret, h, pos, off]) (NormalB body') []]
  where 
    extractNameFromExpr (VarE name) = name 
    extractNameFromExpr _ = error "could not extract name from expr!"

#define deriveRecBuilder(_o)                                                                                                                                            \
instance RecBuilder _o where                                                                                                                                            \
{                                                                                                                                                                       \
  bindIterHandler# h freeRegs = createIterHandlerDef h freeRegs [p| (c# :: DynRep _o) |] [p| (!o# :: DynRep _o) |];                                                     \
  bindIter# inp regs = createLoopDef inp regs [p| (!o# :: DynRep _o) |];                                                                                                \
  bindRec# :: forall rs hs ys s a x. DynFunc rs hs ys s _o a x  -> Regs rs -> Proxy hs -> Proxy ys -> (RegBindNames rs -> StaSubroutine# '[] hs ys s _o a x ) -> Q Dec; \
  bindRec# name regs _ _ binding = createRecDef @rs @hs @ys name regs binding [p| (!o# :: DynRep _o) |]                                                                 \
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
  dynHandler# :: forall hs s a. Proxy s -> Proxy a -> Regs hs -> StaHandler# hs s o a  -> DynHandler hs s o a

  {-|
  Converts a static continuation into a dynamic one (represented as a lambda)

  @since 1.4.0.0
  -}
  dynCont# :: forall rs s a x. Proxy s -> Proxy a -> Proxy x -> Regs rs -> StaCont# rs s o a x -> DynCont rs s o a x

#define deriveMarshalOps(_o)                                                                                                                                           \
instance MarshalOps _o where                                                                                                                                           \
{                                                                                                                                                                      \
  dynHandler# :: forall hs s a. Proxy s -> Proxy a -> Regs hs  -> StaHandler# hs s _o a -> DynHandler hs s _o a;                                                       \
  dynHandler# _ _ NoRegs        sh = eta [||\ (pos :: Pos) (o# :: DynRep _o) -> $$(sh (Input# [||o#||] [||pos||])) ||];                                                \
  dynHandler# ps pa (Regs _ rs) sh = [|| \r -> $$(dynHandler# @_o @_ @s @a ps pa rs (sh [||r||]) ) ||];                                                                \
  dynCont# :: forall rs s a x. Proxy s -> Proxy a -> Proxy x -> Regs rs -> StaCont# rs s _o a x -> DynCont rs s _o a x;                                                \
  dynCont# _ _ _ regs sk = eta [|| \x (pos :: Pos) (o# :: DynRep _o) -> $$(eta $ toDynRegStack @_ @(ST s (Maybe a)) regs $ sk [||x||] (Input# [||o#||] [||pos||])) ||] \
};
inputInstances(deriveMarshalOps);