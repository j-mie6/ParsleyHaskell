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

import Control.Monad.ST                                (ST)
import Data.Array.Unboxed                              (UArray)
import Data.ByteString.Internal                        (ByteString)
import Data.Text                                       (Text)
import Parsley.Internal.Backend.Machine.InputRep       (DynRep)
import Parsley.Internal.Backend.Machine.Types.Base     (Handler#, Pos)
import Parsley.Internal.Backend.Machine.Types.Statics  (toDynRegStack)
import Parsley.Internal.Backend.Machine.Types.Dynamics (DynSubroutine, DynCont, DynHandler, DynRegisterStack)
import Parsley.Internal.Backend.Machine.Types.Input    (Input#(..))
import Parsley.Internal.Backend.Machine.Types.Statics  (StaCont#, StaHandler#, StaSubroutine#, StaRegisterStack#)
import Parsley.Internal.Common.Utils                   (Code)
import Parsley.Internal.Core.InputTypes                (Text16, CharList, Stream)

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString)
import Data.Kind (Type)
import Parsley.Internal.Backend.Machine.Identifiers (ΣVar)
import Language.Haskell.TH (newName, Q, unsafeCodeCoerce, Pat (..))
import Language.Haskell.TH.Syntax (Exp(..), Dec(FunD), mkName, Clause (..), Body (..), Pat (BangP))
import Language.Haskell.TH (unTypeCode, runQ)
import Data.Type.Equality ((:~:))
import Data.Data ((:~:)(..))
import Type.Reflection (eqTypeRep, typeRep, type (:~~:) (HRefl))
import Parsley.Internal.Backend.Machine.Types.Registers (RegBindNames (..), Regs (..), RegTHNames(..))
import Unsafe.Coerce (unsafeCoerce)
import Data.Proxy (Proxy)
import Parsley.Internal.Common.THUtils (eta)

#define inputInstances(derivation) \
derivation(String)                 \
derivation((UArray Int Char))      \
derivation(Text16)                 \
derivation(ByteString)             \
derivation(CharList)               \
derivation(Stream)                 \
derivation(Lazy.ByteString)        \
derivation(Text)

#define inputInstancesWithName(derivation)   \
derivation(String, String);                  \
derivation(UArray, (UArray Int Char));       \
derivation(Text16, Text16);                  \
derivation(ByteString, ByteString);          \
derivation(CharList, CharList);              \
derivation(Stream, Stream);                  \
derivation(LazyByteString, Lazy.ByteString); \
derivation(Text, Text);

{-|
Used to generate a binding for a handler.

@since 1.4.0.0
-}
class HandlerOps o where
  {-|
  Generate a let-bound handler and provide it to another continuation.

  @since 1.4.0.0
  -}
  -- TODO: we could get rid of the names -> handler continuation and let it just be StaHandler#. The power of hindsight, i guess...
  bindHandler# :: (RegBindNames hs -> StaHandler# '[] s o a) -- ^ Static handler to bind, waiting to capture the register binds
               -> Regs hs                                    -- ^ Registers required by handler, and which to bind in handler definition.
               -> (DynHandler hs s o a -> Code b)            -- ^ The continuation that expects the bound handler
               -> Code b


-- Some cpphs magic to propagate _o type to the lowest level
#define regHandlerWrapperName(_name) wrapHandlerRegs/**/_name

-- Binding ops for binding n-ary handlers
#define defHandlerRegWrapper(_name, _o) \
regHandlerWrapperName(_name) :: (RegBindNames hs -> StaHandler# '[] s _o a) -> (forall rs. RegTHNames rs  -> (RegBindNames hs -> Q Exp));\
regHandlerWrapperName(_name) h NoTHName                = \regs -> unTypeCode [|| \(pos :: Pos) !(o# :: DynRep _o) -> $$(h regs (Input# [||o#||] [||pos||])) ||];\
regHandlerWrapperName(_name) h (RegTHName _ name rest) = \regs -> do; func <- regHandlerWrapperName(_name) h rest regs; return (LamE [VarP name] func); 

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
  where
    extractNameFromPat (SigP (VarP name) _ ) = name
    extractNameFromPat (SigP (BangP (VarP name)) _ ) = name
    extractNameFromPat _ = undefined -- TODO: better error??

#define deriveHandlerOps(_name, _o)                                                \
instance HandlerOps _o where                                                       \
{                                                                                  \
  bindHandler# h freeRegs k = createHandlerDef @_ @_ @_o h freeRegs ([p| (!o# :: DynRep _o) |]) k\
};

defHandlerRegWrapper(String, String);                 
defHandlerRegWrapper(UArray, (UArray Int Char));      
defHandlerRegWrapper(Text16, Text16);                   
defHandlerRegWrapper(ByteString, ByteString);         
defHandlerRegWrapper(CharList, CharList);             
defHandlerRegWrapper(Stream, Stream);                 
defHandlerRegWrapper(LazyByteString, Lazy.ByteString);
defHandlerRegWrapper(Text, Text);
inputInstancesWithName(deriveHandlerOps);

-- main entry point to bind something that takes in `Regs rs`, actually
createDeclWithRegs :: forall rs. (forall rs'. RegTHNames rs' -> (RegBindNames rs -> Q Exp)) -> Regs rs -> Q Exp
createDeclWithRegs regWrapper regs = do; boundRegsNames <- nameRegs' regs; regWrapper boundRegsNames (convertNamesToCode boundRegsNames)

feedRegNames :: forall rs x. RegBindNames rs -> StaRegisterStack# rs x -> Code x
feedRegNames NoName k = k 
feedRegNames (RegName _ name rs) k = feedRegNames rs (k name) 
-- regWrapperName(_name) loop l (RegTHName _ name rest) = \regs -> do; func <- regWrapperName(_name) loop l rest regs; return (LamE [VarP name] func); \

foo :: forall rs x. Regs rs -> StaRegisterStack# rs x -> DynRegisterStack rs x
foo NoRegs f = f 
foo (Regs _ rs) f = [||\r -> $$(foo @_ @x rs (f [|| r ||])) ||]

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
                        let posE = pure $ VarE $ extractNameFromPat pos
                        let offE = pure $ VarE $ extractNameFromPat off
                        let xE = pure $ VarE xName
                        body <- unTypeCode $ feedRegNames @rs @(ST s (Maybe a)) (convertNamesToCode regNames) 
                                          (jbody (unsafeCodeCoerce xE) (Input# (unsafeCodeCoerce offE) (unsafeCodeCoerce posE))) 
                        return $ FunD joinName [Clause ([VarP xName, pos, off] ++ namesToArgList regNames []) (NormalB body) [] ]
        k' <- unTypeCode $ k (unsafeCodeCoerce $ return (VarE joinName))
        bind <- makebind
        return (LetE [bind] k')
  where
    extractNameFromPat (SigP (VarP name) _ ) = name
    extractNameFromPat (SigP (BangP (VarP name)) _ ) = name
    extractNameFromPat _ = undefined -- TODO: better error??

{-|
Generates join-point bindings.

@since 1.4.0.0
-}
class JoinBuilder o where
  {-|
  Generate a let-bound join point and provide it to another continuation.

  @since 1.4.0.0
  -}
  setupJoinPoint# :: forall rs s a x b. Proxy s -> Proxy a -> Proxy x -> StaCont# rs s o a x            -- ^ The join point to bind.
                  -> Regs rs                        -- ^ Registers join point expects.
                  -> (DynCont rs s o a x -> Code b) -- ^ The continuation that expects the bound join point
                  -> Code b

#define deriveJoinBuilder(_o)                                     \
instance JoinBuilder _o where                                     \
{                                                                 \
  setupJoinPoint# :: forall rs s a x b. Proxy s -> Proxy a -> Proxy x -> StaCont# rs s _o a x     \
                  -> Regs rs                        \
                  -> (DynCont rs s _o a x -> Code b)  \
                  -> Code b;\
  setupJoinPoint# _ _ _ binding regs = createJoinPointDef @rs @s @_o @a @x binding regs [p| (!o# :: DynRep _o) |]  \
};
inputInstances(deriveJoinBuilder)

{-  [|| let join x (pos :: Pos)  =              \
              $$(foo @rs @(ST s (Maybe a)) regs (binding [||x||] (Input# [||o#||] [||pos||])))     \-}
{-|
Type family to capture the arity of a loop body which might have multiple
liquid registers passed through it.
-}
type family LiquidLoopRoutine (xs :: [Type]) s o a where 
  LiquidLoopRoutine '[] s o a = Pos -> DynRep o -> ST s (Maybe a)
  LiquidLoopRoutine (x:xs) s o a = x -> LiquidLoopRoutine xs s o a  

type family StaLiquidLoopRoutine (xs :: [Type]) s o a where 
  StaLiquidLoopRoutine '[] s o a = Code Pos -> Code (DynRep o) -> Code (ST s (Maybe a))
  StaLiquidLoopRoutine (x:xs) s o a = Code x -> StaLiquidLoopRoutine xs s o a  


{-| 
Existentially qualified input registers of `LiquidLoopRoutine`.
-}
data QLiquidLoopRoutine s o a = forall xs. QLiquidLoopRoutine !(StaLiquidLoopRoutine xs s o a) !(RegBindNames xs)

noName :: RegBindNames '[]
noName = NoName 

regName :: ΣVar x -> Code x -> (RegBindNames xs -> RegBindNames (x:xs))
regName = RegName 


qLiquidLoopRoutine :: forall s o a rs. Code (LiquidLoopRoutine rs s o a) -> RegBindNames rs -> QLiquidLoopRoutine s o a
qLiquidLoopRoutine loop frees = QLiquidLoopRoutine (stat frees loop) frees 
  where 
    stat :: forall rs. RegBindNames rs -> Code (LiquidLoopRoutine rs s o a) -> StaLiquidLoopRoutine rs s o a
    stat NoName loop = \pos o -> [|| $$loop $$pos $$o ||]
    stat (RegName _ _ ws) loop = \r -> stat ws [|| $$loop $$r ||] 

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
  Creates a binding for a tail-recursive loop.

  @since 1.4.0.0
  -}
  bindIter# :: Input# o                                                                        -- ^ Initial offset for the loop.
            -> (Code (Pos -> DynRep o -> ST s (Maybe a)) -> Input# o -> Code (ST s (Maybe a))) -- ^ The code for the loop given self-call and offset.
            -> Code (ST s (Maybe a))                                                           -- ^ Code of the executing loop.

  {-|
  Generalisation of `bindIter#` for when we have bound liquid registers.

  @since 1.4.0.0
  -}
  bindLiquidIter# :: Input# o                                                                  -- ^ Initial offset for the loop.
            -> RegBindNames rs
            -> (Code (LiquidLoopRoutine rs s o a) -> RegBindNames rs -> Input# o -> Code (ST s (Maybe a))) 
            -- ^ The code for the loop given self-call and offset. 
            -> Code (ST s (Maybe a))                                                           -- ^ Code of the executing loop.

  {-|
  Creates a binding for a regular let-bound parser.

  @since 1.4.0.0
  -}
  bindRec# ::  StaSubroutine# '[] hs ys s o a x -- ^ Code for the binding, accepting itself as an argument.
            -> DynSubroutine '[] hs ys s o a x                                       -- ^ The code that represents this binding's name.

-- NOTE: Everything below is awful, cpphs is awful, I'm awful. Blame TTH and cpphs not working together so well.

supplyRegs :: forall rs s o a. RegBindNames rs -> Code (LiquidLoopRoutine rs s o a) -> Code (LiquidLoopRoutine '[] s o a)
supplyRegs NoName l = l 
supplyRegs (RegName _ name rest) l = supplyRegs  @_ @_ @o rest [|| $$l $$name ||]

-- Generate new names for register binds
nameRegs :: forall rs. RegBindNames rs -> Q (RegTHNames rs)
nameRegs NoName = pure NoTHName 
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
convertNamesToCode NoTHName = NoName
convertNamesToCode (RegTHName r name rest) = let rest' = convertNamesToCode rest 
                                              in RegName r (unsafeCodeCoerce (return (VarE name))) rest'

namesToArgList :: forall rs. RegTHNames rs -> [Pat] -> [Pat]
namesToArgList NoTHName tail                = tail
namesToArgList (RegTHName _ name rest) tail = VarP name:namesToArgList rest tail 

createLoopDecl :: forall rs. (forall rs'. RegTHNames rs' -> (RegBindNames rs -> Q Exp)) -> RegBindNames rs -> Q Exp
createLoopDecl regWrapper regs = do; boundRegsNames <- nameRegs regs; regWrapper boundRegsNames (convertNamesToCode boundRegsNames)

#define regWrapperName(_name) wrapRegs/**/_name

#define defRegWrapper(_name, _o) \
regWrapperName(_name) :: Code (LiquidLoopRoutine rs s _o a) -> (Code (LiquidLoopRoutine rs s _o a) -> RegBindNames rs -> Input# _o -> Code (ST s (Maybe a))) -> (forall rs'. RegTHNames rs' -> (RegBindNames rs -> Q Exp));\
regWrapperName(_name) loop l NoTHName = \regs -> unTypeCode [|| \(pos :: Pos) !(o# :: DynRep _o) -> $$(l loop regs (Input# [||o#||] [||pos||])) ||];\
regWrapperName(_name) loop l (RegTHName _ name rest) = \regs -> do; func <- regWrapperName(_name) loop l rest regs; return (LamE [VarP name] func); \



#define deriveRecBuilder(_name, _o)                                                                 \
instance RecBuilder _o where                                                                        \
{                                                                                                   \
  bindIterHandler# h freeRegs k = [||                                                                        \
      let handler (posc :: Pos) (c# :: DynRep _o) = $$(unsafeCodeCoerce $ createDeclWithRegs (regHandlerWrapperName(_name) (\bregs -> h bregs (Input# [||c#||] [||posc||])) ) freeRegs) \
        in $$(k [||handler||])                                                         \
    ||]; \
  bindIter# inp l = [||                                                                             \
      let loop (pos :: Pos) !(o# :: DynRep _o) = $$(l [||loop||] (Input# [||o#||] [||pos||]))       \
      in loop $$(pos# inp) $$(off# inp)                                                             \
    ||];                                                                                            \
  bindLiquidIter# inp regs l = [||                                                                  \
      let loop = $$(unsafeCodeCoerce $ createLoopDecl (regWrapperName(_name) [||loop||] l) regs)    \
      in $$(supplyRegs @_ @_ @_o regs [||loop||]) $$(pos# inp) $$(off# inp)                         \
    ||];                                                                                            \
  bindRec# binding =                                                                                \
    {- The idea here is to try and reduce the number of times registers have to be passed around -} \
    [|| let self ret h (pos :: Pos) !(o# :: DynRep _o) =                                            \
              $$(binding [||ret||] [||h||] (Input# [||o#||] [||pos||])) in self ||]      \
};
inputInstancesWithName(deriveRecBuilder)
--deriveRecBuilder(String,String)
defRegWrapper(String, String);                 
defRegWrapper(UArray, (UArray Int Char));      
defRegWrapper(Text16, Text16);                   
defRegWrapper(ByteString, ByteString);         
defRegWrapper(CharList, CharList);             
defRegWrapper(Stream, Stream);                 
defRegWrapper(LazyByteString, Lazy.ByteString);
defRegWrapper(Text, Text);
                                                                                                                                           

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

#define deriveMarshalOps(_o)                                                                                        \
instance MarshalOps _o where                                                                                        \
{                                                                                                                   \
  dynHandler# :: forall hs s a. Proxy s -> Proxy a -> Regs hs  -> StaHandler# hs s _o a -> DynHandler hs s _o a;    \
  dynHandler# _ _ NoRegs        sh = [||\ (pos :: Pos) (o# :: DynRep _o) -> $$(sh (Input# [||o#||] [||pos||])) ||]; \
  dynHandler# ps pa (Regs _ rs) sh = [|| \r -> $$(dynHandler# @_o @_ @s @a ps pa rs (sh [||r||]) ) ||];             \
  dynCont# :: forall rs s a x. Proxy s -> Proxy a -> Proxy x -> Regs rs -> StaCont# rs s _o a x -> DynCont rs s _o a x; \
  dynCont# _ _ _ regs sk = eta [|| \x (pos :: Pos) (o# :: DynRep _o) -> $$(eta $ toDynRegStack @_ @(ST s (Maybe a)) regs $ sk [||x||] (Input# [||o#||] [||pos||])) ||];            \
};
inputInstances(deriveMarshalOps);