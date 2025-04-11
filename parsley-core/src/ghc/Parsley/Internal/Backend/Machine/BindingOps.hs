{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
{-# OPTIONS_GHC -Wno-deprecations #-} --FIXME: remove when Text16 is removed
{-# LANGUAGE AllowAmbiguousTypes,
             CPP,
             MagicHash,
             TypeApplications,
             MultiParamTypeClasses,
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
import Parsley.Internal.Backend.Machine.Types.Dynamics (DynSubroutine, DynCont, DynHandler)
import Parsley.Internal.Backend.Machine.Types.Input    (Input#(..))
import Parsley.Internal.Backend.Machine.Types.Statics  (StaCont#, StaHandler#, StaSubroutine#)
import Parsley.Internal.Common.Utils                   (Code)
import Parsley.Internal.Core.InputTypes                (Text16, CharList, Stream)

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString)
import Data.Kind (Type)
import Parsley.Internal.Backend.Machine.Identifiers (ΣVar)
import Language.Haskell.TH (newName, Name, Q, unsafeCodeCoerce, Pat (VarP))
import Language.Haskell.TH.Syntax (Exp(..), Dec(FunD), mkName)
import Language.Haskell.TH (unTypeCode, runQ)
import Data.Type.Equality ((:~:))
import Data.Data ((:~:)(..))
import Type.Reflection (eqTypeRep, typeRep, type (:~~:) (HRefl))

#define inputInstances(derivation) \
derivation(String)                 \
derivation((UArray Int Char))      \
derivation(Text16)                 \
derivation(ByteString)             \
derivation(CharList)               \
derivation(Stream)                 \
derivation(Lazy.ByteString)        \
derivation(Text)

#define inputInstancesWithName(derivation)  \
derivation(String, String);                  \
derivation(UArray, (UArray Int Char));       \
derivation(Text16, Text16);                    \
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
  bindHandler# :: StaHandler# s o a            -- ^ Static handler to bind
               -> (DynHandler s o a -> Code b) -- ^ The continuation that expects the bound handler
               -> Code b

#define deriveHandlerOps(_o)                                                       \
instance HandlerOps _o where                                                       \
{                                                                                  \
  bindHandler# h k = [||                                                           \
    let handler (pos :: Pos) (o# :: DynRep _o) = $$(h (Input# [||o#||] [||pos||])) \
    in $$(k [||handler||])                                                         \
  ||];                                                                             \
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

#define deriveJoinBuilder(_o)                                                         \
instance JoinBuilder _o where                                                         \
{                                                                                     \
  setupJoinPoint# binding k =                                                         \
    [|| let join x (pos :: Pos) !(o# :: DynRep _o) =                                  \
              $$(binding [||x||] (Input# [||o#||] [||pos||])) in $$(k [||join||]) ||] \
};
inputInstances(deriveJoinBuilder)

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
data QLiquidLoopRoutine s o a = forall xs. QLiquidLoopRoutine !(StaLiquidLoopRoutine xs s o a) !(RegNames xs)

data RegNames (rs :: [Type]) where 
  NoName :: RegNames '[]
  RegName :: ΣVar x -> Code x -> RegNames xs -> RegNames (x:xs)

noName :: RegNames '[]
noName = NoName 

regName :: ΣVar x -> Code x -> (RegNames xs -> RegNames (x:xs))
regName = RegName 

data RegTHNames (rs :: [Type]) where 
  NoTHName :: RegTHNames '[]
  RegTHName :: ΣVar x -> Name -> RegTHNames xs -> RegTHNames (x:xs)


qLiquidLoopRoutine :: forall s o a rs. Code (LiquidLoopRoutine rs s o a) -> RegNames rs -> QLiquidLoopRoutine s o a
qLiquidLoopRoutine loop frees = QLiquidLoopRoutine (stat frees loop) frees 
  where 
    stat :: forall rs. RegNames rs -> Code (LiquidLoopRoutine rs s o a) -> StaLiquidLoopRoutine rs s o a
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
  bindIterHandler# :: (Input# o -> StaHandler# s o a)                      -- ^ The iter handler to bind
                   -> (Code (Pos -> DynRep o -> Handler# s o a) -> Code b) -- ^ The continuation that accepts the bound handler
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
            -> RegNames rs
            -> (Code (LiquidLoopRoutine rs s o a) -> RegNames rs -> Input# o -> Code (ST s (Maybe a))) 
            -- ^ The code for the loop given self-call and offset. 
            -> Code (ST s (Maybe a))                                                           -- ^ Code of the executing loop.

  {-|
  Creates a binding for a regular let-bound parser.

  @since 1.4.0.0
  -}
  bindRec#  :: (DynSubroutine '[] s o a x -> StaSubroutine# '[] s o a x) -- ^ Code for the binding, accepting itself as an argument.
            -> DynSubroutine '[] s o a x                             -- ^ The code that represents this binding's name.

{-
class LastOneMatches (x :: Type) (ys :: [Type])
instance LastOneMatches x '[x]
instance LastOneMatches x xs => LastOneMatches x (y:xs)

class DeleteLastOne (xs :: [Type]) (xs' :: [Type])
instance DeleteLastOne '[x] '[]
instance DeleteLastOne xs xs' => DeleteLastOne (x:xs) (x:xs')

class Mirror (xs :: [Type]) (ys :: [Type]) 
instance Mirror '[] '[]
--instance (xs ~ (x:xs'), LastOneMatches x ys, DeleteLastOne ys ys', Mirror xs' ys') => Mirror xs ys

type family Append (xs :: [Type]) (ys :: [Type]) :: [Type] where
  Append '[] ys = ys
  Append (x ': xs) ys = x ': Append xs ys

class AppendsTo (xs :: [Type]) (ys :: [Type]) (zs :: [Type])

instance AppendsTo '[] ys ys
instance AppendsTo ys '[] ys
instance AppendsTo xs ys zs => AppendsTo (x:xs) ys (x:zs)

hAppend :: RegNames xs -> RegNames ys -> RegNames (Append xs ys)
hAppend NoName ys = ys
hAppend (RegName s x xs) ys = RegName s x (hAppend xs ys)

appendEmpty :: RegNames xs -> Append xs '[] :~: xs
appendEmpty NoName = Refl 
appendEmpty (RegName _ _ xs) = case appendEmpty xs of Refl -> Refl 

regListEq :: RegNames xs -> RegNames ys -> Maybe (xs :~: ys) 
regListEq NoName NoName = Just Refl
regListEq (RegName (_ :: x) _ xs) (RegName (_ :: y) _ ys) =  
  case eqTypeRep (typeRep @x) (typeRep @y) of
    Just HRefl ->
      case regListEq xs ys of
        Just Refl -> Just Refl
        Nothing -> Nothing
    Nothing -> Nothing 
regListEq _ _ = Nothing

createLoopDecl' :: forall rs s o a.
             RegNames rs -- ^ Registers that the loop continuation expects.
          -> Code (LiquidLoopRoutine rs s o a) -- ^ name of loop
          -> (Code (LiquidLoopRoutine rs s o a) -> RegNames rs -> Input# o -> Code (ST s (Maybe a))) 
          -- ^ machine of the body of the loop
          -> Code (LiquidLoopRoutine rs s o a)
createLoopDecl' regs loop l = impl NoName regs -- [|| case appendRightId @rs of Refl -> $$(impl NoName regs) ||]
  where 
    foo = impl NoName regs
    impl :: forall xs ys. RegNames ys -> RegNames xs -> Code (LiquidLoopRoutine xs s o a)
    impl regs NoName = [|| \(pos :: Pos) !(o# :: DynRep o) -> $$(l loop regs (Input# [||o#||] [||pos||])) ||]
      where
        regsFinal = case appendEmpty regs of Refl -> regs 
    impl regs (RegName s x ws) = [|| \r -> $$(impl foo ws) ||]
      where 
        foo = hAppend regs (RegName s x NoName)
-}
{-
 creator (l loop boundRegs) 
  where
    (boundRegs, creator) = runQ $ createLambda regs
    createLambda :: forall rs. RegNames rs -> Q (RegNames rs, (Input# o -> Code (ST s (Maybe a))) -> Code (LiquidLoopRoutine rs s o a))
    createLambda NoName = pure (NoName, \l -> [|| \(pos :: Pos) !(o# :: DynRep o) -> $$(l (Input# [||o#||] [||pos||])) ||])
    createLambda (RegName s _ rest) = do 
        x <- createLambda rest
        regName <- newName "r"
        let regs = RegName s (unsafeCodeCoerce (return (VarE regName))) rest'
        let body = \l -> (LamE [VarP regName] (func l))
        return (regs, body)
    {-
    foo NoName = [||\(pos :: Pos) !(o# :: DynRep o) -> $$(l [||loop||] regs (Input# [||o#||] [||pos||]))||]
    foo (RegName _ _ _) = \regs -> [||\(pos :: Pos) !(o# :: DynRep o) -> $$(l [||loop||] regs (Input# [||o#||] [||pos||]))||]
    -}
-}


-- NOTE: Everything below is awful, cpphs is awful, I'm awful. Blame TTH and cpphs not working together so well.

supplyRegs :: forall rs s o a. RegNames rs -> Code (LiquidLoopRoutine rs s o a) -> Code (LiquidLoopRoutine '[] s o a)
supplyRegs NoName l = l 
supplyRegs (RegName _ name rest) l = supplyRegs  @_ @_ @o rest [|| $$l $$name ||]

nameRegs :: forall rs. RegNames rs -> Q (RegTHNames rs)
nameRegs NoName = pure NoTHName 
nameRegs (RegName s _ rest) = do 
  rest' <- nameRegs rest 
  regname <- newName "r"
  return (RegTHName s regname rest')

convertNamesToCode :: forall rs. RegTHNames rs -> RegNames rs 
convertNamesToCode NoTHName = NoName
convertNamesToCode (RegTHName r name rest) = let rest' = convertNamesToCode rest 
                                              in RegName r (unsafeCodeCoerce (return (VarE name))) rest'

createLoopDecl :: forall rs. (forall rs'. RegTHNames rs' -> (RegNames rs -> Q Exp)) -> RegNames rs -> Q Exp
createLoopDecl regWrapper regs = do; boundRegsNames <- nameRegs regs; regWrapper boundRegsNames (convertNamesToCode boundRegsNames)

{- 
wrapRegsTest :: Code (LiquidLoopRoutine rs s String a) -> (Code (LiquidLoopRoutine rs s String a) -> RegNames rs -> Input# String -> Code (ST s (Maybe a))) -> (forall rs'. RegTHNames rs' -> (RegNames rs -> Q Exp))
wrapRegsTest loop l NoTHName = \regs -> unTypeCode [|| let thing (pos :: Pos) !(o# :: DynRep String) = $$(l loop regs (Input# [||o#||] [||pos||])) in thing ||]
wrapRegsTest loop l (RegTHName _ name rest) = \regs -> do; func <- wrapRegsTest loop l rest regs; return (LamE [VarP name] func)
-}

#define regWrapperName(_name) wrapRegs/**/_name

#define defRegWrapper(_name, _o) \
regWrapperName(_name) :: Code (LiquidLoopRoutine rs s _o a) -> (Code (LiquidLoopRoutine rs s _o a) -> RegNames rs -> Input# _o -> Code (ST s (Maybe a))) -> (forall rs'. RegTHNames rs' -> (RegNames rs -> Q Exp));\
regWrapperName(_name) loop l NoTHName = \regs -> unTypeCode [|| \(pos :: Pos) !(o# :: DynRep _o) -> $$(l loop regs (Input# [||o#||] [||pos||])) ||];\
regWrapperName(_name) loop l (RegTHName _ name rest) = \regs -> do; func <- regWrapperName(_name) loop l rest regs; return (LamE [VarP name] func); \
 
#define deriveRecBuilder(_name, _o)                                                                 \
instance RecBuilder _o where                                                                        \
{                                                                                                   \
  bindIterHandler# h k = [||                                                                        \
      let handler (posc :: Pos) (c# :: DynRep _o) (poso :: Pos) (o# :: DynRep _o) =                 \
            $$(h (Input# [||c#||] [||posc||]) (Input# [||o#||] [||poso||])) in $$(k [||handler||])  \
    ||];                                                                                            \
  bindIter# inp l = [||                                                                   \
      let loop (pos :: Pos) !(o# :: DynRep _o) = $$(l [||loop||] (Input# [||o#||] [||pos||]))       \
      in loop $$(pos# inp) $$(off# inp)                                                             \
    ||];                                                                                            \
  bindLiquidIter# inp regs l = [||                                                                  \
      let loop = $$(unsafeCodeCoerce $ createLoopDecl (regWrapperName(_name) [||loop||] l) regs)      \
      in $$(supplyRegs @_ @_ @_o regs [||loop||]) $$(pos# inp) $$(off# inp)                                   \
    ||];       \
  bindRec# binding =                                                                                \
    {- The idea here is to try and reduce the number of times registers have to be passed around -} \
    [|| let self ret h (pos :: Pos) !(o# :: DynRep _o) =                                            \
              $$(binding [||self||] [||ret||] [||h||] (Input# [||o#||] [||pos||])) in self ||]      \
};
inputInstancesWithName(deriveRecBuilder)
defRegWrapper(String, String);                 
defRegWrapper(UArray, (UArray Int Char));      
defRegWrapper(Text16, Text16);                   
defRegWrapper(ByteString, ByteString);         
defRegWrapper(CharList, CharList);             
defRegWrapper(Stream, Stream);                 
defRegWrapper(LazyByteString, Lazy.ByteString);
defRegWrapper(Text, Text);

--defRegWrapper(String, String)

--bindIterHandler# :: (Input# String -> StaHandler# s String a)
-- -> (Code (Pos -> DynRep String -> Handler# s String a) -> Code b)
-- -> Code b
                                                                                                                                                                                                              

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

#define deriveMarshalOps(_o)                                                                             \
instance MarshalOps _o where                                                                             \
{                                                                                                        \
  dynHandler# sh = [||\ (pos :: Pos) (o# :: DynRep _o) -> $$(sh (Input# [||o#||] [||pos||])) ||];        \
  dynCont# sk = [||\ x (pos :: Pos) (o# :: DynRep _o) -> $$(sk [||x||] (Input# [||o#||] [||pos||])) ||]; \
};
inputInstances(deriveMarshalOps)
