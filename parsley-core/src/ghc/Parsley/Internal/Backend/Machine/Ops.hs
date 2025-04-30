{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
{-# OPTIONS_HADDOCK show-extensions #-}
{-# LANGUAGE AllowAmbiguousTypes,
             ConstrainedClassMethods,
             ConstraintKinds,
             ImplicitParams,
             MagicHash,
             NamedFieldPuns,
             PatternSynonyms,
             RecordWildCards,
             TypeApplications,
             ScopedTypeVariables,
             UnboxedTuples #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Ops
Description : Higher-level operations used by evaluation.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains all the relevant operations for the evaluation
of a machine. These are used by "Parsley.Internal.Backend.Machine.Eval"
to provide the various instruction interpretations.

@since 1.0.0.0
-}
module Parsley.Internal.Backend.Machine.Ops (
    -- * Core Machine Operations
    dup, returnST,
    -- ** Abstracted Input Operations
    sat, emitLengthCheck, fetch,
    -- ** Register Operations
    newΣ, writeΣ, readΣ, solidifyΣ,
    -- ** Handler Operations
    -- *** Basic handlers and operations
    fatal, raise,
    -- *** Handler preparation
    buildHandler, buildYesHandler, buildIterYesHandler,
    -- *** Handler binding
    bindAlwaysHandler, bindSameHandler,
    -- ** Continuation Operations
    -- *** Basic continuations and operations
    halt, noreturn,
    resume, callWithContinuation, callCC,
    -- *** Continuation preparation
    suspend,
    -- ** Join Point Operations
    setupJoinPoint,
    -- ** Iteration Operations
    bindIterAlways', -- TODO: rename to remove aposth
    bindIterSame',   -- TODO: ^
    -- ** Recursion Operations
    buildRec,
    -- ** Marshalling Operations
    dynHandler, dynCont,
    -- ** Log Operations
    logHandler, preludeString,
    -- ** Convenience Types
    Ops, LogHandler, StaHandlerBuilder, StaYesHandler,
    -- * Re-exports from "Parsley.Internal.Backend.Machine.InputOps"
    HandlerOps, JoinBuilder, RecBuilder, PositionOps, MarshalOps, LogOps
  ) where

import Control.Monad                                              (liftM2)
import Control.Monad.Reader                                       (ask, local)
import Control.Monad.ST                                           (ST)
import Data.List                                                  (mapAccumL)
import Data.STRef                                                 (writeSTRef, readSTRef, newSTRef)
import Data.Void                                                  (Void)
import Debug.Trace                                                (trace)
import Parsley.Internal.Backend.Machine.BindingOps
import Parsley.Internal.Backend.Machine.Defunc                    (Defunc(INPUT), genDefunc, _if, pattern FREEVAR)
import Parsley.Internal.Backend.Machine.Identifiers               (MVar, ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.InputOps                  (PositionOps(..), LogOps(..), InputOps, DynOps, next, uncons, check, asDyn, asSta)
import Parsley.Internal.Backend.Machine.InputRep                  (StaRep, DynRep)
import Parsley.Internal.Backend.Machine.Instructions              (Access(..))
import Parsley.Internal.Backend.Machine.LetBindings               (Metadata(failureInputCharacteristic, successInputCharacteristic))
import Parsley.Internal.Backend.Machine.Types                     (MachineMonad, Machine(..), run)
import Parsley.Internal.Backend.Machine.Types.Registers           (Regs(..), RegBindNames (..), RegTHNames (..), fromRegs, debugRegsList)
import Parsley.Internal.Backend.Machine.Types.Context
import Parsley.Internal.Backend.Machine.Types.Dynamics            (DynFunc, DynCont, DynHandler, DynRegisterStack, DynSubroutine)
import Parsley.Internal.Backend.Machine.Types.Input               (Input(..), Input#(..), toInput, fromInput, chooseInput)
import Parsley.Internal.Backend.Machine.Types.Input.Offset        (moveOne)
import Parsley.Internal.Backend.Machine.Types.InputCharacteristic (InputCharacteristic)
import Parsley.Internal.Backend.Machine.Types.State               (Γ(..), OpStack(..))
import Parsley.Internal.Backend.Machine.Types.Statics
import Parsley.Internal.Common                                    (One, Code, Vec(..), Nat(..))
import Parsley.Internal.Common.THUtils                            (eta, unTypeCode, unsafeCodeCoerce)
import System.Console.Pretty                                      (color, Color(Green, White, Red, Blue))

import Parsley.Internal.Backend.Machine.Types.Input.Offset as Offset (Offset(..), updateDeepestKnown)
import qualified Parsley.Internal.Opt   as Opt
import Parsley.Internal.Backend.Machine.Types.Base (Handler#, Pos, RegisterStack#)
import Data.Data (Proxy(..), (:~:) (..))
import Parsley.Internal.Core.Identifiers (ΣVar(..))
import Unsafe.Coerce (unsafeCoerce)
import Language.Haskell.TH (Exp(LamE), Pat (VarP))
import Language.Haskell.TH.Syntax (Q)
import qualified Data.Set as Set
import Parsley.Internal.Backend.Machine.Identifiers (SomeΣVar(..))

{- General Operations -}
{-|
Creates a let-binding that allows the same value to be
used multiple times without re-computation.

@since 1.0.0.0
-}
dup :: (?flags :: Opt.Flags) => Defunc x -> (Defunc x -> Code r) -> Code r
dup (FREEVAR x) k = k (FREEVAR x)
dup (INPUT o) k = k (INPUT o)
dup x k = [|| let !dupx = $$(genDefunc x) in $$(k (FREEVAR [||dupx||])) ||]

{-|
This is just plain ol' `return`. It is given a concrete
type here so that "Ambiuous Type Error" is avoided in the
generated code.

@since 1.0.0.0
-}
{-# INLINE returnST #-}
returnST :: forall s a. a -> ST s a
returnST = return @(ST s)

{- Abstracted Input Operations -}
{-|
Given a predicate, a continuation that accepts an updated state `Γ`,
code to execute on failure, and a state @γ@, tries to read a character
from the input within @γ@, executing the failure code if it does not
exist or does not match.

@since 2.1.0.0
-}
sat :: (?flags :: Opt.Flags)
    => (Defunc Char -> Defunc Bool)                        -- ^ Predicate to test the character with.
    -> Code Char                                           -- ^ The character to test against.
    -> (Defunc Char -> Code b)                             -- ^ Code to execute on success.
    -> Code b                                              -- ^ Code to execute on failure.
    -> Code b
sat p c good bad = let v = FREEVAR c in _if (p v) (good v) bad

{-|
Consumes the next character and adjusts the offset to match.

@since 1.8.0.0
-}
fetch :: (?ops :: InputOps (StaRep o))
      => Offset o -> (Code Char -> Offset o -> Code b) -> Code b
fetch input k = next (offset input) $ \c offset' -> k c (moveOne input offset')

{-|
Emits a length check for a number of characters \(n\) in the most efficient
way it can. It takes two continuations a @good@ and a @bad@: the @good@ is used
when the \(n\) characters are available and the @bad@ when they are not.

@since 2.3.0.0
-}
emitLengthCheck :: (?ops :: InputOps (StaRep o))
                => Int                                             -- ^ The number of required characters \(n\).
                -> Int                                             -- ^ The number of characters to prefetch \(m\).
                -> Maybe (Code Char -> Code a -> Code a)           -- ^ An optional check for the head character.
                -> (Offset o -> [(Code Char, Offset o)] -> Code a) -- ^ The good continuation if \(n\) characters are available.
                -> Code a                                          -- ^ The bad continuation if the characters are unavailable.
                -> Offset o                                        -- ^ The input to test on.
                -> (Offset o -> StaRep o)
                -> Code a
emitLengthCheck n m headCheck good bad input sel = check n m (sel input) headCheck good' bad
  where good' deepestKnown = let input' = updateDeepestKnown deepestKnown input in good input' . feed input'
        feed input' = snd . mapAccumL (\off (c, rep) -> let off' = moveOne off rep in (off', (c, off'))) input'

{- Register Operations -}
{-|
Depending on the access type either generates the code for a new register and
registers it with the `Ctx`, or generates a binding with `dup` and registers
that in the `Ctx` cache.

@since 1.0.0.0
-}
newΣ :: (?flags :: Opt.Flags) => forall x s o a r. ΣVar x -> Access -> Defunc x -> (Ctx s o a -> Code (ST s r)) -> Ctx s o a -> Code (ST s r)
newΣ σ Bound x k ctx =  dup x $ \dupx -> [||
    let bref = $$(genDefunc dupx)
      in $$(k (insertNewΣ σ Nothing (Just [|| bref ||]) dupx ctx))
  ||]
newΣ σ Soft x k ctx = dup x $ \dupx -> k (insertNewΣ σ Nothing Nothing dupx ctx)
newΣ σ Hard x k ctx = dup x $ \dupx -> [||
    do ref <- newSTRef $$(genDefunc dupx)
       $$(k (insertNewΣ σ (Just [||ref||]) Nothing dupx ctx))
  ||]

{-|
Depending on the access type, either generates the code for a write to a register
(and caching that result) or updates the cache with the register's new value.

@since 1.0.0.0
-}
writeΣ :: (?flags :: Opt.Flags) => ΣVar x -> Access -> Defunc x -> (Ctx s o a -> Code (ST s r)) -> Ctx s o a -> Code (ST s r)
writeΣ σ Bound x k ctx = dup x $ \dupx -> [||
    let bref = $$(genDefunc dupx)
      in $$(k (bindΣ σ [|| bref ||] $ cacheΣ σ dupx ctx))
    ||]
writeΣ σ Soft x k ctx = dup x $ \dupx -> k (cacheΣ σ dupx ctx)
writeΣ σ Hard x k ctx = let ref = concreteΣ σ ctx in dup x $ \dupx -> [||
    do writeSTRef $$ref $$(genDefunc dupx)
       $$(k (cacheΣ σ dupx ctx))
  ||]

{-|
Depending on the access type, either generates a read from a register or fetches
the value from the cache and feeds it to a continuation.

@since 1.0.0.0
-}
readΣ :: (?flags :: Opt.Flags) => ΣVar x -> Access -> (Defunc x -> Ctx s o a -> Code (ST s r)) -> Ctx s o a -> Code (ST s r)
readΣ σ Bound k ctx = let bref = boundΣ σ ctx in [||
       $$(let fv = FREEVAR bref in k fv (cacheΣ σ fv ctx))
  ||]
readΣ σ Soft k ctx = k (cachedΣ σ ctx) ctx
readΣ σ Hard k ctx = let ref = concreteΣ σ ctx in [||
    do x <- readSTRef $$ref
       $$(let fv = FREEVAR [||x||] in k fv (cacheΣ σ fv ctx))
  ||]


{-| 
Reads the `ctx` cache and writes this to the concrete `STRef`. Also removes any bindings associated
with a register from `ctx` using `unbindΣ`.
-}
solidifyΣ :: (?flags :: Opt.Flags) => ΣVar x -> (Ctx s o a -> Code (ST s r))-> Ctx s o a -> Code (ST s r)
solidifyΣ σ k ctx = writeΣ σ Hard (cachedΣ σ ctx) k (unbindΣ σ ctx)

{- Handler Operations -}
-- Basic handlers and operations
{-|
This is the root-most handler, when it is executed the parser fails immediately
by returning @Nothing@.

@since 1.2.0.0
-}
fatal :: QAugmentedStaHandler s o a
fatal = QAugmentedStaHandler (augmentHandlerSta Nothing (const [|| returnST Nothing ||])) NoRegs


{-|
Fails by evaluating the next handler with the current input. Makes
use of `staHandlerEval` to make use of static information available
about the state of the input (since 1.4.0.0).

@since 1.0.0.0
-}
raise :: (DynOps o, ?flags :: Opt.Flags) => Ctx s o a -> Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))
raise ctx γ = let VCons h _ = handlers γ in case h of (QAugmentedStaHandler h regs) -> staHandlerEval h (gatherBinds regs ctx) (input γ)


{-|
Finds the current bound names of given registers from a given context
-}
gatherBinds :: forall rs s o a. Regs rs -> Ctx s o a -> RegBindNames rs
gatherBinds NoRegs _ = NoName
gatherBinds (Regs σ rs) ctx = RegName σ (boundΣ σ ctx ) (gatherBinds rs ctx)

{-|
Feed a `RegBindNames` list to a register stack.
-}
feedBinds :: forall rs x. RegBindNames rs -> StaRegisterStack# rs x -> Code x
feedBinds NoName f             = f
feedBinds (RegName _ name rs) f = feedBinds rs (f name)

{-|
Modify a context by accepting a list of new bind names for the registers. 
-}
bindRegsToCtx :: forall rs s o a x. Regs rs -> Ctx s o a -> (Ctx s o a -> Code x) -> StaRegisterStack# rs x
bindRegsToCtx NoRegs ctx k = k ctx
bindRegsToCtx (Regs σ rs) ctx k = \r -> bindRegsToCtx rs (bindΣ σ r ctx) k 


-- Handler preparation
{-|
Converts a partially evaluated parser into a handler: this is done by
completing the evaluation in the context of a future offset, and taking
a captured offset and pushing it to the stack. Returns a `StaHandlerBuilder`,
which takes the captured offset as the first argument.

@since 1.2.0.0
-}
buildHandler :: forall hs xs n r s o a. DynOps o
             => Γ s o xs n r a                                  -- ^ State to execute the handler with.
             -> Ctx s o a                                       -- ^ Context under which to run the handler.
             -> Machine s o (o:xs) n r a                        -- ^ Code generation for handler
             -> Regs hs                                         -- ^ Registers handler requires.
             -> Word                                            -- ^ The unique identifier for the offset on failure.
             -> StaHandlerBuilder hs s o a
buildHandler γ ctx h regs u c = fromStaHandler# $ acceptNames regs ctx
  where
    acceptNames :: forall hs. Regs hs -> Ctx s o a -> StaHandler# hs s o a
    acceptNames NoRegs ctx = \inp -> run h γ {operands = Op (INPUT c) (operands γ), input = toInput u inp} ctx
    acceptNames (Regs σ rs) ctx = \regName -> acceptNames rs (bindΣ σ regName ctx)

{-
  fromStaHandler# $ lambdafy regs h
  where 
    lambdafy :: forall hs. Regs hs -> (Γ s o (o : xs) n r a -> Code (ST s (Maybe a))) -> StaHandler# hs s o a 
    lambdafy NoRegs h = \inp -> h (γ {operands = Op (INPUT c) (operands γ), input = toInput u inp})
    lambdafy (Regs _ rs) h = \r -> lambdafy rs h
-}
{-|
Converts a partially evaluated parser into a "yes" handler: this means that
the handler /always/ knows that the inputs are equal, so does not require
both a captured and a current offset. Otherwise, is similar to `buildHandler`.

@since 2.1.0.0
-}
buildYesHandler ::forall s o n r a xs hs. Γ s o xs n r a
                -> Ctx s o a                             -- ^ Context under which to run the handler.
                -> Machine s o xs n r a                  -- ^ Code generation for handler.
                -> Regs hs                               -- ^ Registers handler needs.
                -> StaYesHandler hs s o a
buildYesHandler γ ctx h regs inp = acceptNames regs ctx
  where
    acceptNames :: forall hs. Regs hs -> Ctx s o a -> StaSameHandler hs s a
    acceptNames NoRegs ctx = run h γ {input = inp} ctx
    acceptNames (Regs σ rs) ctx = \regName -> acceptNames rs (bindΣ σ regName ctx)

{-|
Converts a partially evaluated parser into a "yes" handler: this means that
the handler /always/ knows that the inputs are equal, so does not require
both a captured and a current offset. Otherwise, is similar to `buildHandler`.

@since 2.1.0.0
-}
buildIterYesHandler :: forall xs hs s o n r a. DynOps o
                    => Γ s o xs n r a
                    -> Ctx s o a                             -- ^ Context under which to run the handler.
                    -> Machine s o xs n r a                  -- ^ Code generation for handler.
                    -> Regs hs                               -- ^ Registers handler needs.
                    -> Word
                    -> StaHandler hs s o a
buildIterYesHandler γ ctx h regs u = fromStaHandler# (peel regs $ buildYesHandler γ ctx h regs . toInput u)
  where
    peel :: forall hs. Regs hs -> (Input# o -> StaSameHandler hs s a) -> StaHandler# hs s o a
    peel NoRegs      h = h
    peel (Regs _ rs) h = \r -> peel rs (\inp -> h inp r)

-- Handler binding
{-|
Wraps around `bindHandler#` to create a binding for "always" handlers, which always
perform the same action regardless of if the captured and current offsets match or
not.

@since 1.4.0.0
-}
bindAlwaysHandler :: forall s o xs hs n r a b. HandlerOps o
                  => Γ s o xs n r a                    -- ^ The state from which to capture the offset.
                  -> Bool                              -- ^ Whether or not a binding is required
                  -> StaHandlerBuilder hs s o a        -- ^ The handler waiting to receive the captured offset and be bound.
                  -> Regs hs
                  -> (Γ s o xs (Succ n) r a -> Code b) -- ^ The parser to receive the binding.
                  -> Code b
bindAlwaysHandler γ needed h regs k = bindHandlerInline# needed (staHandler# (h (input γ))) regs $
  \qh -> k (γ {handlers = VCons (QAugmentedStaHandler (augmentHandler (Just (input γ)) qh) regs) (handlers γ)})

{-|
Wraps around `bindHandler#` to create /three/ bindings for a handler that acts
differently depending on whether inputs match or not. The three bindings are
for the case where they are the same, the case where they differ, and the case
where they are unknown (which is defined in terms of the previous two).

@since 2.1.0.0
-}
bindSameHandler :: forall s o xs hs n r a b. (HandlerOps o, PositionOps (StaRep o), DynOps o)
                => Γ s o xs n r a                    -- ^ The state from which to capture the offset.
                -> Bool                              -- ^ Is a binding required for the matching handler?
                -> StaYesHandler hs s o a            -- ^ The handler that handles matching input.
                -> Bool                              -- ^ Is a binding required for the mismatched handler?
                -> StaHandlerBuilder hs s o a        -- ^ The handler that handles mismatched input.
                -> Regs hs                           -- ^ Registers required by handler 
                -- TODO: maybe two sets of regs?
                -> (Γ s o xs (Succ n) r a -> Code b) -- ^ The parser to receive the composite handler.
                -> Code b
bindSameHandler γ yesNeeded yes noNeeded no regs k =
  bindYesInline# @hs @s @a yesNeeded (yes (input γ)) regs $ \qyes ->
    bindHandlerInline# noNeeded (staHandler# $ no (input γ)) regs $ \qno ->
        let handler = mkHandlerJoin regs qyes (staHandler# qno)
        in bindHandlerInline# @o True handler regs $ \qhandler ->
          k (γ {handlers = VCons (QAugmentedStaHandler (augmentHandlerFull (input γ) qhandler qyes qno) regs) (handlers γ)})
  where
    mkHandlerJoin :: forall hs. Regs hs -> StaSameHandler hs s a -> StaHandler# hs s o a -> StaHandler# hs s o a
    mkHandlerJoin NoRegs      qyes qno = \inp -> [||if $$(same (offset (off (input γ))) (asSta @o (off# inp))) then $$qyes else $$(qno inp)||]
    mkHandlerJoin (Regs _ rs) qyes qno = \r -> mkHandlerJoin rs (qyes r) (qno r)

{-|
Feed register binds to a `StaHandler#` from a `RegBindNames`
-}
feedHandlerBoundRegs :: forall hs s o a. RegBindNames hs -> StaHandler# hs s o a -> StaHandler# '[] s o a
feedHandlerBoundRegs NoName h = h
feedHandlerBoundRegs (RegName _ name rs) h = feedHandlerBoundRegs rs (h name)

feedSameHandlerBoundRegs :: forall hs s o a. RegBindNames hs -> StaSameHandler hs s a -> StaSameHandler '[] s a
feedSameHandlerBoundRegs NoName h = h
feedSameHandlerBoundRegs (RegName _ name rs) h = feedSameHandlerBoundRegs rs (h name)


{- Continuation Operations -}
-- Basic continuations and operations
{-|
The root-most return continuation, this is used when the top-level
parser returns: it returns the result with @Just@ and terminates
the entire parser.

@since 1.2.0.0
-}
halt :: StaCont '[] s o a a
halt = mkStaCont $ \x _ -> [||returnST (Just $$x)||]

{-|
This continuation is used for binding that never return, which is
enforced by the `Void` in the type. This signifies that a binding
may only exit on failure, which is the case with iterating parsers.

@since 1.2.0.0
-}
noreturn :: forall s o a. StaCont '[] s o a Void
noreturn = mkStaCont $ error "Return is not permitted here"

{-|
Executes a given continuation (which may be a return continuation or a
join point) taking the required components from the state `Γ`.

@since 1.2.0.0
-}
resume :: (DynOps o, ?flags :: Opt.Flags) => StaCont rs s o a x -> Ctx s o a -> Regs rs -> Γ s o (x : xs) n r a -> Code (ST s (Maybe a))
resume k ctx regs γ = let Op x _ = operands γ in feedBinds (gatherBinds regs ctx) $ staCont# k (genDefunc x) (fromInput (input γ))

{-|
A form of @callCC@, this calls a subroutine with a given return continuation
passed to it. This may be the current continuation, but also may just be a
previous return continuation in the case of a tail call.

@since 1.8.0.0
-}
callWithContinuation :: (MarshalOps o, DynOps o)
                     => Ctx s o a
                     -> StaSubroutine '[] hs ys s o a x           -- ^ The subroutine @sub@ that will be called.
                     -> Regs hs                                   -- ^ Witnesses for handler's registers.
                     -> StaCont ys s o a x                        -- ^ The return continuation for the subroutine.
                     -> Regs ys                                   -- ^ Witnesses for return cont.'s registers.
                     -> Input o                                   -- ^ The input to feed to @sub@.
                     -> Vec (Succ n) (QAugmentedStaHandler s o a) -- ^ The stack from which to obtain the handler to pass to @sub@.
                     -> Code (ST s (Maybe a))
callWithContinuation ctx sub hregs ret retregs input (VCons h _) = case h of
  QAugmentedStaHandler h regs ->
    staSubroutine# sub (dynCont retregs ret) (fitHandler ctx hregs (dynHandler h regs (failureInputCharacteristic (meta sub))) regs) (fromInput input)
  where
    eqReg :: ΣVar a -> ΣVar b -> Maybe (a :~: b)
    eqReg (ΣVar σa) (ΣVar σb) = if σa == σb then unsafeCoerce (Just Refl) else Nothing
    eqRegs :: forall hs rs. Regs hs -> Regs rs -> Maybe (hs :~: rs)
    eqRegs NoRegs NoRegs = Just Refl
    eqRegs (Regs σ1 xs) (Regs σ2 ys) = do
      Refl <- eqRegs xs ys
      Refl <- eqReg σ1 σ2
      return Refl
    eqRegs _ _ = Nothing

    -- Take a handler with input regs hs, transform this into a handler with inputs hs' such that all necessary 
    -- registers from hs' are piped and others are gathered from the given callsite context (i.e. they have not changed in the call)
    fitHandler :: forall hs hs' s o a. Ctx s o a -> Regs hs' -> DynHandler hs s o a -> Regs hs -> DynHandler hs' s o a
    fitHandler ctx regs dh hregs  = provide @hs' @hs regs ctx dh hregs  
      where
        -- Find intersection
        hregsSet = fromRegs hregs 
        regsSet = fromRegs regs
        sharedRegs = hregsSet `Set.intersection` regsSet

        provide :: forall rs' rs. Regs rs' -> Ctx s o a -> DynHandler rs s o a -> Regs rs -> DynHandler rs' s o a
        provide NoRegs ctx dh rs = supplyAllFromContext ctx dh rs
        provide (Regs σ rs') ctx dh rs = if Set.member (SomeΣVar σ) sharedRegs
                                         then [|| \hr -> $$(provide rs' (bindΣ σ [|| hr ||] ctx )  dh rs) ||] -- Supply
                                         else [|| \_ -> $$(provide rs' ctx dh rs) ||] -- Ignore
        

        supplyAllFromContext :: forall rs. Ctx s o a -> DynHandler rs s o a -> Regs rs -> DynHandler '[] s o a
        supplyAllFromContext ctx dh NoRegs = dh 
        supplyAllFromContext ctx dh (Regs σ rs) = supplyAllFromContext ctx [|| $$dh $$(boundΣ σ ctx) ||] rs


-- Continuation preparation
{-|
Converts a partial parser into a return continuation in a manner similar
to `buildHandler`.

@since 1.8.0.0
-}
suspend :: forall ys s o a x xs n r. (?flags :: Opt.Flags)
        => Ctx s o a                                       -- ^ Context that will be modified with return registers
        -> Machine s o (x : xs) n r a                      -- ^ Machine that is to meant be run.
        -> Regs ys                                         -- ^ Return continuation registers.
        -> Γ s o xs n r a                                  -- ^ The state to execute the continuation with.
        -> (Input# o -> Input o)                           -- ^ Function used to generate the offset
        -> StaCont ys s o a x
suspend ctx m regs γ off = mkStaCont $ \x o# -> bindRegsToCtx @ys regs ctx (run m (γ {operands = Op (FREEVAR x) (operands γ), input = off o#}))

{-|
Combines `suspend` and `callWithContinuation`, simultaneously performing
an optimisation on the offset if the subroutine has known input characteristics.

@since 1.5.0.0
-}
callCC :: forall xs hs ys s o n r a x. (MarshalOps o, DynOps o, ?flags :: Opt.Flags)
       => Word                                                   --
       -> StaSubroutine '[] hs ys s o a x                        -- ^ The subroutine @sub@ that will be called.
       -> Regs hs
       -> Regs ys
       -> Machine s o (x : xs) (Succ n) r a                      -- ^ The return continuation to generate.
       -> Ctx s o a                                              -- ^ Context of the callsite
       -> Γ s o xs (Succ n) r a                                  --
       -> Code (ST s (Maybe a))
callCC u sub hregs rregs m ctx γ = callWithContinuation ctx sub hregs (suspend ctx m rregs γ (chooseInput (successInputCharacteristic (meta sub)) u inp)) rregs inp (handlers γ)
  where
    inp :: Input o
    inp = input γ

{- Join Point Operations -}
{-|
Wraps around `setupJoinPoint#` to make a join point and register it
into the `Ctx`.

@since 1.4.0.0
-}
setupJoinPoint :: forall rs s o xs n r a x. (JoinBuilder o, DynOps o, ?flags :: Opt.Flags)
               => ΦVar x                     -- ^ The name of the binding.
               -> Regs rs
               -> Machine s o (x : xs) n r a -- ^ The definition of the binding.
               -> Machine s o xs n r a       -- ^ The scope within which the binding is valid.
               -> MachineMonad s o xs n r a
setupJoinPoint φ regs (Machine k) mx = freshUnique $ \u -> ask >>= (\ctx ->
  return $ \γ -> setupJoinPoint# @o (Proxy @s) (Proxy @a) (Proxy @x)
    (\qx inp -> bindRegsToCtx regs ctx (run (Machine $ local voidCoins k) (γ {operands = Op (FREEVAR qx) (operands γ), input = toInput u inp}))) regs
    (\qjoin -> run mx γ (insertΦ φ (mkStaContDyn qjoin regs) regs ctx)))


{- Iteration Operations -}
{-|
Uses `bindIterHandler#` and `bindIter#` to create an iterated parser
from its loop body and return continuation. The exit of a loop is done
using failure, and this failure does not discriminate whether or not
the loop consumed input in its final iteration.

@since 1.8.0.0
-}
bindIterAlways' :: forall s o a rs hs. (RecBuilder o, DynOps o, ?flags :: Opt.Flags)
               => Ctx s o a                  -- ^ The context to keep the binding
               -> MVar Void                  -- ^ The name of the binding.
               -> Regs rs                    -- ^ Registers present in the loop body.
               -> Machine s o '[] One Void a -- ^ The body of the loop.
               -> Bool                       -- ^ Does loop exit require a binding?
               -> StaHandlerBuilder hs s o a -- ^ What to do after the loop exits (by failing)
               -> Regs hs
               -> Input o                    -- ^ The initial offset to provide to the loop
               -> Word                       -- ^ The unique name for captured offset /and/ iteration offset
               -> Code (ST s (Maybe a))
bindIterAlways' ctx μ regs l needed h hregs inp u =
   bindIterHandlerInline# @o @s @a @_ @hs needed (staHandler# . h . toInput u) hregs $ \qhandler ->
      bindLiquidIter# @o (fromInput inp) (gatherBinds regs ctx) $ \qloop loopBoundRegs inp# ->
        updateBinds loopBoundRegs ctx $ \ctx ->
          -- First populate the context with the new binds for names
          let inp = toInput u inp#
          in run l (Γ Empty (QStaCont noreturn NoRegs) inp (VCons (QAugmentedStaHandler (augmentHandler (Just inp) (qhandler inp#)) hregs) VNil))
                  (voidCoins (insertSub μ (mkStaSubroutine $ lambdafy regs qloop) regs hregs NoRegs ctx))
  where
    lambdafy :: forall rs. Regs rs -> Code (LiquidLoopRoutine rs s o a) -> StaSubroutine# rs hs '[] s o a Void
    lambdafy NoRegs qloop  = \_ _ inp -> [|| $$qloop $$(pos# inp) $$(off# inp) ||]
    lambdafy (Regs σ rs) qloop = \r -> lambdafy rs [|| $$qloop $$r ||]
    -- \_ _ inp -> [|| $$qloop $$(pos# inp) $$(off# inp) ||]
    --liquefyΣ :: (?flags :: Opt.Flags) => ΣVar x -> (Ctx s o a -> Code (ST s r))-> Ctx s o a -> Code (ST s r)

updateBinds :: forall s o a rs r. RegBindNames rs -> Ctx s o a -> (Ctx s o a -> Code (ST s r)) -> Code (ST s r)
updateBinds NoName ctx k = k ctx
updateBinds (RegName σ bind rs) ctx k = updateBinds rs (bindΣ σ bind ctx) k

{-|
Similar to `bindIterAlways`, but builds a handler that performs in
the same way as `bindSameHandler`.

@since 2.1.0.0
-}
bindIterSame' :: forall s o a rs hs. (RecBuilder o, HandlerOps o, PositionOps (StaRep o), DynOps o, ?flags :: Opt.Flags)
             => Ctx s o a                  -- ^ The context to store the binding in.
             -> MVar Void                  -- ^ The name of the binding.
             -> Regs rs                    -- ^ Registers present in the loop body.
             -> Machine s o '[] One Void a -- ^ The loop body.
             -> Bool                       -- ^ Is a binding required for the matching handler?
             -> StaHandler hs s o a        -- ^ The handler when input is the same.
             -> Bool                       -- ^ Is a binding required for the differing handler?
             -> StaHandlerBuilder hs s o a -- ^ The handler when input differs.
             -> Regs hs
             -> Input o                    -- ^ The initial offset of the loop.
             -> Word                       -- ^ The unique name of the captured offsets /and/ the iteration offset.
             -> Code (ST s (Maybe a))
bindIterSame' ctx μ regs l neededYes yes neededNo no hregs inp u =
  bindHandlerInline# @o @s @a neededYes (staHandler# yes) hregs $ \qyes ->
    bindIterHandlerInline# @o @s @a neededNo (staHandler# . no . toInput u) hregs $ \qno -> -- 
      let handler (inpc :: Input# o) = makeHandlerJoin inpc hregs qyes qno
      in bindIterHandlerInline# @o True handler hregs $ \qhandler ->
          bindLiquidIter# @o (fromInput inp) (gatherBinds regs ctx) $ \qloop loopBoundRegs inp# ->
              updateBinds loopBoundRegs ctx $ \ctx ->
                let off = toInput u inp#
                in run l (Γ Empty (QStaCont noreturn NoRegs) off (VCons (QAugmentedStaHandler (augmentHandlerFull off (qhandler inp#) (moveInputInside hregs (staHandler# qyes) inp#) (qno inp#)) hregs) VNil))
                          (voidCoins (insertSub μ (mkStaSubroutine $ lambdafy regs qloop) regs hregs NoRegs ctx))
  where
    lambdafy :: forall rs. Regs rs -> Code (LiquidLoopRoutine rs s o a) -> StaSubroutine# rs hs '[] s o a Void
    lambdafy NoRegs qloop  = \_ _ inp -> [|| $$qloop $$(pos# inp) $$(off# inp) ||]
    lambdafy (Regs σ rs) qloop = \r -> lambdafy rs [|| $$qloop $$r ||]

    moveInputInside :: forall hs. Regs hs -> StaHandler# hs s o a -> Input# o -> StaSameHandler hs s a
    moveInputInside NoRegs sh inp = sh inp
    moveInputInside (Regs _ rs) sh inp = \r -> moveInputInside rs (sh r) inp

    makeHandlerJoin :: forall hs. Input# o -> Regs hs -> StaHandler hs s o a -> (Input# o -> StaHandler hs s o a) -> StaHandler# hs s o a
    makeHandlerJoin inpc NoRegs      qyes qno = \(inpo :: Input# o) -> [||if $$(same (asSta @o (off# inpc)) (asSta @o (off# inpo))) then $$(staHandler# qyes inpc) else $$(staHandler# (qno inpc) inpo)||]
    makeHandlerJoin inpc (Regs _ rs) qyes qno = \r -> makeHandlerJoin inpc rs (applyR qyes r) (\inp -> applyR (qno inp) r)
      where
        applyR :: forall h hs. StaHandler (h:hs) s o a -> Code h -> StaHandler hs s o a
        applyR h r = StaHandler{ staHandler# = staHandler# h r, dynOrigin = (\d -> [|| $$d $$r||]) <$> dynOrigin h}

{- Recursion Operations -}
{-|
Wraps around `bindRec#` to produce a recursive parser binding. This function
also provides all the free-registers which are closed over by the binding.
This eliminates recursive calls from having to pass all of the same registers
each time round.

@since 1.5.0.0
-}
buildRec :: forall rs hs ys s o a r. (RecBuilder o, DynOps o)
         => MVar r                   -- ^ The name of the binding.
         -> DynFunc rs hs ys s o a r -- ^ Top level bound name for parser.
         -> Regs rs                 -- ^ The registers required by the binding.
         -> Regs hs                 -- ^ The registers required by the dynamic handler.
         -> Regs ys                 -- ^ The registers required by the return continuation.
         -> Ctx s o a               -- ^ The context to re-insert the register-less binding
         -> Machine s o '[] One r a -- ^ The body of the binding.
         -> Metadata                -- ^ The metadata associated with the binding
         -> DynFunc rs hs ys s o a r
buildRec μ func rs hs rregs ctx k meta =
  takeFreeRegisters @rs @hs @ys @s @o @a @r rs hs rregs ctx $ \ctx -> 
      bindRec# @o @hs @ys $ \qret (qh :: DynHandler hs s o a) inp -> 
      run k (Γ Empty (QStaCont (mkStaContDyn qret rregs) rregs) (toInput 0 inp) (VCons (QAugmentedStaHandler (augmentHandlerDyn @hs Nothing qh hs) hs) VNil))
            (insertSub @rs @hs @ys μ (mkStaSubroutineMeta @_ @hs meta (feedBinds' rs func)) rs hs rregs (nextUnique ctx))
  where
    feedBinds' :: forall rs. Regs rs -> DynFunc rs hs ys s o a r -> StaSubroutine# rs hs ys s o a r 
    feedBinds' NoRegs func = \k h inp -> [|| $$func $$k $$h $$(pos# inp) $$(off# inp) ||]
    feedBinds' (Regs _ rs) func = \r -> feedBinds' rs [|| $$func $$r ||]

{- Binding Operations -}
bindHandlerInline# :: forall o s a b hs. HandlerOps o
                   => Bool
                   -> StaHandler# hs s o a
                   -> Regs hs
                   -> (StaHandler hs s o a -> Code b)
                   -> Code b
bindHandlerInline# True  h regs k = bindHandler# @o (\bregs -> feedHandlerBoundRegs @hs @s @o @a bregs h) regs (k . fromDynHandler @hs @s @o @a regs)
bindHandlerInline# False h _ k = k (fromStaHandler# h)

bindYesInline# :: forall hs s a b. Bool -> StaSameHandler hs s a -> Regs hs -> (StaSameHandler hs s a -> Code b) -> Code b
bindYesInline# True v regs k = [|| let yesSame = $$(unsafeCodeCoerce $ createDeclWithRegs yesWrapper regs) in $$(k $ mkSta regs [||yesSame||]) ||] -- TODO: semi-urgent do the bind of `yesSame
  where
    yesWrapper :: forall rs. RegTHNames rs -> RegBindNames hs -> Q Exp
    yesWrapper NoTHName = \bregs -> unTypeCode $ feedSameHandlerBoundRegs @hs @s @_ @a bregs v
    yesWrapper (RegTHName _ name rest) = \bregs -> do ; func <- yesWrapper rest bregs; return (LamE [VarP name] func)
    mkSta :: forall rs. Regs rs -> DynRegisterStack rs (ST s (Maybe a)) -> StaSameHandler rs s a
    mkSta NoRegs dh = dh
    mkSta (Regs _ rs) dh = \r -> mkSta rs [||$$dh $$r ||]
bindYesInline# False v _ k = k v

bindIterHandlerInline# :: forall o s a b hs. RecBuilder o
                       => Bool
                       -> (Input# o -> StaHandler# hs s o a)
                       -> Regs hs
                       -> ((Input# o -> StaHandler hs s o a) -> Code b)
                       -> Code b
bindIterHandlerInline# True h regs k =
  bindIterHandler# @o (\bregs inp -> feedHandlerBoundRegs @hs @s @o @a bregs $ h inp) regs $ \qh ->
    k (\inp -> fromDynHandler @hs @s @o @a regs [||$$qh $$(pos# inp) $$(off# inp)||])
bindIterHandlerInline# False h _ k = k (fromStaHandler# . h)

{- Marshalling Operations -}
{-|
Wraps around `dynHandler#`, but ensures that if the `StaHandler`
originated from a `DynHandler` itself, that no work is performed.

Takes in an `InputCharacteristic`, which is used to refine the
handler given knowledge about how it might be used.

@since 1.5.0.0
-}
dynHandler :: forall hs s o a. MarshalOps o => AugmentedStaHandler hs s o a -> Regs hs -> InputCharacteristic -> DynHandler hs s o a
dynHandler h regs = staHandlerCharacteristicDyn regs h (eta . dynHandler# @o (Proxy @s) (Proxy @a) regs)

{-|
Wraps around `dynCont#`, but ensures that if the `StaCont`
originated from a `DynCont` itself, that no work is performed.

@since 1.4.0.0
-}
dynCont :: forall rs s o a x. MarshalOps o => Regs rs -> StaCont rs s o a x -> DynCont rs s o a x
dynCont regs (StaCont sk Nothing) = eta (dynCont# @o (Proxy @s) (Proxy @a) (Proxy @x) regs sk)
dynCont _ (StaCont _ (Just dk))   = dk

{- Log Operations =-}
{-|
The specialised handler for the @debug@ combinator. It will fail again after
having printed the debug information.

@since 1.2.0.0
-}
logHandler :: (?ops :: InputOps (StaRep o), LogHandler o, ?flags :: Opt.Flags) => String -> Ctx s o a -> Γ s o xs (Succ n) ks a -> Word -> StaHandlerBuilder '[] s o a
logHandler name ctx γ u _ = let VCons qh _ = handlers γ in case qh of
      QAugmentedStaHandler h regs -> fromStaHandler# $ \inp# -> let inp = toInput u inp# in [||
                                trace $$(preludeString name '<' (γ {input = inp}) ctx (color Red " Fail")) $$(staHandlerEval h (gatherBinds regs ctx) inp)
                              ||]

{-|
Used for the debug instructions and handler, produces the debugging information
string.

@since 1.2.0.0
-}
preludeString :: forall s o xs n r a. (?ops :: InputOps (StaRep o), LogHandler o)
              => String         -- ^ The name as per the debug combinator
              -> Char           -- ^ Either @<@ or @>@ depending on whether we are entering or leaving.
              -> Γ s o xs n r a
              -> Ctx s o a
              -> String         -- ^ String that represents the current status
              -> Code String
preludeString name dir γ ctx ends =
  shiftLeft offset 5 $ \start ->
    shiftRight offset 5 $ \end ->
      let indent          = replicate (debugLevel ctx * 2) ' '
          inputTrace      = [|| let replace '\n' = color Green "↙"
                                    replace ' '  = color White "·"
                                    replace c    = return c
                                    go i# = $$(uncons (asSta @o [||i#||]) (\qc qi' -> [||
                                        if $$(same (asSta @o [||i#||]) end) then []
                                        else replace $$qc ++ go $$(asDyn @o qi') ||])
                                      [||color Red "•"||])
                                in go $$(asDyn @o start) ||]
          prelude         = [|| concat [indent, dir : name, dir : " (", show $$(offToInt offset), "): "] ||]
          caretSpace      = [|| replicate (length $$prelude + $$(offToInt offset) - $$(offToInt start)) ' ' ||]
      in [|| concat [$$prelude, $$inputTrace, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    offset = Offset.offset (off (input γ))


{- Convenience Types -}
{-|
A convience bundle of all of the type class constraints.

@since 1.0.0.0
-}
type Ops o =
  ( HandlerOps o
  , JoinBuilder o
  , RecBuilder o
  , PositionOps (StaRep o)
  , MarshalOps o
  , LogOps (StaRep o)
  , DynOps o
  )

{-|
The constraints needed to build a `logHandler`.

@since 1.0.0.0
-}
type LogHandler o = (PositionOps (StaRep o), LogOps (StaRep o), DynOps o)

{-|
A `StaHandler` that has not yet captured its offset.

@since 1.2.0.0
-}
type StaHandlerBuilder hs s o a = Input o -> StaHandler hs s o a

{-|
A "yes-handler" that has not yet captured its offset

@since 2.1.0.0
-}
-- TODO: look into making this n-ary over free registers
type StaYesHandler hs s o a = Input o -> StaSameHandler hs s a
