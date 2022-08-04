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
    newΣ, writeΣ, readΣ,
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
    bindIterAlways,
    bindIterSame,
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
import Data.STRef                                                 (writeSTRef, readSTRef, newSTRef)
import Data.Void                                                  (Void)
import Debug.Trace                                                (trace)
import GHC.Exts                                                   (Int(..), (-#))
import Language.Haskell.TH.Syntax                                 (liftTyped)
import Parsley.Internal.Backend.Machine.BindingOps
import Parsley.Internal.Backend.Machine.Defunc                    (Defunc(INPUT), genDefunc, _if, pattern FREEVAR)
import Parsley.Internal.Backend.Machine.Identifiers               (MVar, ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.InputOps                  (PositionOps(..), LogOps(..), InputOps, next, more)
import Parsley.Internal.Backend.Machine.InputRep                  (Rep)
import Parsley.Internal.Backend.Machine.Instructions              (Access(..))
import Parsley.Internal.Backend.Machine.LetBindings               (Regs(..), Metadata(failureInputCharacteristic, successInputCharacteristic))
import Parsley.Internal.Backend.Machine.THUtils                   (eta)
import Parsley.Internal.Backend.Machine.Types                     (MachineMonad, Machine(..), run)
import Parsley.Internal.Backend.Machine.Types.Context
import Parsley.Internal.Backend.Machine.Types.Dynamics            (DynFunc, DynCont, DynHandler)
import Parsley.Internal.Backend.Machine.Types.Input               (Input(..), Input#(..), toInput, fromInput, consume, chooseInput)
import Parsley.Internal.Backend.Machine.Types.InputCharacteristic (InputCharacteristic)
import Parsley.Internal.Backend.Machine.Types.State               (Γ(..), OpStack(..))
import Parsley.Internal.Backend.Machine.Types.Statics
import Parsley.Internal.Common                                    (One, Code, Vec(..), Nat(..))
import Parsley.Internal.Core.Result                               (Result(..))
import System.Console.Pretty                                      (color, Color(Green, White, Red, Blue))

import Parsley.Internal.Backend.Machine.Types.Input.Offset as Offset (Offset(..))

{- General Operations -}
{-|
Creates a let-binding that allows the same value to be
used multiple times without re-computation.

@since 1.0.0.0
-}
dup :: Defunc x -> (Defunc x -> Code r) -> Code r
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
sat :: (Defunc Char -> Defunc Bool)                        -- ^ Predicate to test the character with.
    -> Code Char                                           -- ^ The character to test against.
    -> (Defunc Char -> Code b)                             -- ^ Code to execute on success.
    -> Code b                                              -- ^ Code to execute on failure.
    -> Code b
sat p c good bad = let v = FREEVAR c in _if (p v) (good v) bad

{-|
Consumes the next character and adjusts the offset to match.

@since 1.8.0.0
-}
fetch :: (?ops :: InputOps (Rep o))
      => Input o -> (Code Char -> Input o -> Code b) -> Code b
fetch input k = next (offset (off input)) $ \c offset' -> k c (consume offset' input)

{-|
Emits a length check for a number of characters \(n\) in the most efficient
way it can. It takes two continuations a @good@ and a @bad@: the @good@ is used
when the \(n\) characters are available and the @bad@ when they are not.

@since 1.4.0.0
-}
emitLengthCheck :: (?ops :: InputOps (Rep o), PositionOps (Rep o))
                => Int      -- ^ The number of required characters \(n\).
                -> Code a   -- ^ The good continuation if \(n\) characters are available.
                -> Code a   -- ^ The bad continuation if the characters are unavailable.
                -> Offset o -- ^ The input to test on.
                -> Code a
emitLengthCheck 0 good _ _   = good
emitLengthCheck 1 good bad input = [|| if $$(more (offset input)) then $$good else $$bad ||]
emitLengthCheck (I# n) good bad input = [||
  if $$(more (shiftRight (offset input) (liftTyped (n -# 1#)))) then $$good
  else $$bad ||]

{- Register Operations -}
{-|
Depending on the access type either generates the code for a new register and
registers it with the `Ctx`, or generates a binding with `dup` and registers
that in the `Ctx` cache.

@since 1.0.0.0
-}
newΣ :: ΣVar x -> Access -> Defunc x -> (Ctx s o a -> Code (ST s r)) -> Ctx s o a -> Code (ST s r)
newΣ σ Soft x k ctx = dup x $ \dupx -> k (insertNewΣ σ Nothing dupx ctx)
newΣ σ Hard x k ctx = dup x $ \dupx -> [||
    do ref <- newSTRef $$(genDefunc dupx)
       $$(k (insertNewΣ σ (Just [||ref||]) dupx ctx))
  ||]

{-|
Depending on the access type, either generates the code for a write to a register
(and caching that result) or updates the cache with the register's new value.

@since 1.0.0.0
-}
writeΣ :: ΣVar x -> Access -> Defunc x -> (Ctx s o a -> Code (ST s r)) -> Ctx s o a -> Code (ST s r)
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
readΣ :: ΣVar x -> Access -> (Defunc x -> Ctx s o a -> Code (ST s r)) -> Ctx s o a -> Code (ST s r)
readΣ σ Soft k ctx = k (cachedΣ σ ctx) ctx
readΣ σ Hard k ctx = let ref = concreteΣ σ ctx in [||
    do x <- readSTRef $$ref
       $$(let fv = FREEVAR [||x||] in k fv (cacheΣ σ fv ctx))
  ||]

{- Handler Operations -}
-- Basic handlers and operations
{-|
This is the root-most handler, when it is executed the parser fails immediately
by returning @Nothing@.

@since 1.2.0.0
-}
fatal :: AugmentedStaHandler s o a
fatal = augmentHandlerSta Nothing (const [|| returnST (Failure ()) ||])

{-|
Fails by evaluating the next handler with the current input. Makes
use of `staHandlerEval` to make use of static information available
about the state of the input (since 1.4.0.0).

@since 1.0.0.0
-}
raise :: Γ s o xs (Succ n) r a -> Code (ST s (Result () a))
raise γ = let VCons h _ = handlers γ in staHandlerEval h (input γ)

-- Handler preparation
{-|
Converts a partially evaluated parser into a handler: this is done by
completing the evaluation in the context of a future offset, and taking
a captured offset and pushing it to the stack. Returns a `StaHandlerBuilder`,
which takes the captured offset as the first argument.

@since 1.2.0.0
-}
buildHandler :: Γ s o xs n r a                                  -- ^ State to execute the handler with.
             -> (Γ s o (o : xs) n r a -> Code (ST s (Result () a))) -- ^ Partial parser accepting the modified state.
             -> Word                                            -- ^ The unique identifier for the offset on failure.
             -> StaHandlerBuilder s o a
buildHandler γ h u c = fromStaHandler# $ \inp -> h (γ {operands = Op (INPUT c) (operands γ), input = toInput u inp})

{-|
Converts a partially evaluated parser into a "yes" handler: this means that
the handler /always/ knows that the inputs are equal, so does not require
both a captured and a current offset. Otherwise, is similar to `buildHandler`.

@since 2.1.0.0
-}
buildYesHandler :: Γ s o xs n r a
                -> (Γ s o xs n r a -> Code (ST s (Result () a)))
                -> StaYesHandler s o a
buildYesHandler γ h inp = h (γ {input = inp})

{-|
Converts a partially evaluated parser into a "yes" handler: this means that
the handler /always/ knows that the inputs are equal, so does not require
both a captured and a current offset. Otherwise, is similar to `buildHandler`.

@since 2.1.0.0
-}
buildIterYesHandler :: Γ s o xs n r a
                    -> (Γ s o xs n r a -> Code (ST s (Result () a)))
                    -> Word
                    -> StaHandler s o a
buildIterYesHandler γ h u = fromStaHandler# (buildYesHandler γ h . toInput u)

-- Handler binding
{-|
Wraps around `bindHandler#` to create a binding for "always" handlers, which always
perform the same action regardless of if the captured and current offsets match or
not.

@since 1.4.0.0
-}
bindAlwaysHandler :: forall s o xs n r a b. HandlerOps o
                  => Γ s o xs n r a                    -- ^ The state from which to capture the offset.
                  -> Bool                              -- ^ Whether or not a binding is required
                  -> StaHandlerBuilder s o a           -- ^ The handler waiting to receive the captured offset and be bound.
                  -> (Γ s o xs (Succ n) r a -> Code b) -- ^ The parser to receive the binding.
                  -> Code b
bindAlwaysHandler γ needed h k = bindHandlerInline# needed (staHandler# (h (input γ))) $ \qh ->
  k (γ {handlers = VCons (augmentHandler (Just (input γ)) qh) (handlers γ)})

{-|
Wraps around `bindHandler#` to create /three/ bindings for a handler that acts
differently depending on whether inputs match or not. The three bindings are
for the case where they are the same, the case where they differ, and the case
where they are unknown (which is defined in terms of the previous two).

@since 2.1.0.0
-}
bindSameHandler :: forall s o xs n r a b. (HandlerOps o, PositionOps (Rep o))
                => Γ s o xs n r a                    -- ^ The state from which to capture the offset.
                -> Bool                              -- ^ Is a binding required for the matching handler?
                -> StaYesHandler s o a               -- ^ The handler that handles matching input.
                -> Bool                              -- ^ Is a binding required for the mismatched handler?
                -> StaHandlerBuilder s o a           -- ^ The handler that handles mismatched input.
                -> (Γ s o xs (Succ n) r a -> Code b) -- ^ The parser to receive the composite handler.
                -> Code b
bindSameHandler γ yesNeeded yes noNeeded no k =
  bindYesInline# yesNeeded (yes (input γ)) $ \qyes ->
    bindHandlerInline# noNeeded (staHandler# (no (input γ))) $ \qno ->
      let handler inp = [||if $$(same (offset (off (input γ))) (off# inp)) then $$qyes else $$(staHandler# qno inp)||]
      in bindHandlerInline# @o True handler $ \qhandler ->
          k (γ {handlers = VCons (augmentHandlerFull (input γ) qhandler qyes qno) (handlers γ)})

{- Continuation Operations -}
-- Basic continuations and operations
{-|
The root-most return continuation, this is used when the top-level
parser returns: it returns the result with @Just@ and terminates
the entire parser.

@since 1.2.0.0
-}
halt :: StaCont s o a a
halt = mkStaCont $ \x _ -> [||returnST (Success $$x)||]

{-|
This continuation is used for binding that never return, which is
enforced by the `Void` in the type. This signifies that a binding
may only exit on failure, which is the case with iterating parsers.

@since 1.2.0.0
-}
noreturn :: StaCont s o a Void
noreturn = mkStaCont $ \_ _ -> [||error "Return is not permitted here"||]

{-|
Executes a given continuation (which may be a return continuation or a
join point) taking the required components from the state `Γ`.

@since 1.2.0.0
-}
resume :: StaCont s o a x -> Γ s o (x : xs) n r a -> Code (ST s (Result () a))
resume k γ = let Op x _ = operands γ in staCont# k (genDefunc x) (fromInput (input γ))

{-|
A form of @callCC@, this calls a subroutine with a given return continuation
passed to it. This may be the current continuation, but also may just be a
previous return continuation in the case of a tail call.

@since 1.8.0.0
-}
callWithContinuation :: MarshalOps o
                     => StaSubroutine s o a x           -- ^ The subroutine @sub@ that will be called.
                     -> StaCont s o a x                 -- ^ The return continuation for the subroutine.
                     -> Input o                         -- ^ The input to feed to @sub@.
                     -> Vec (Succ n) (AugmentedStaHandler s o a) -- ^ The stack from which to obtain the handler to pass to @sub@.
                     -> Code (ST s (Result () a))
callWithContinuation sub ret input (VCons h _) = staSubroutine# sub (dynCont ret) (dynHandler h (failureInputCharacteristic (meta sub))) (fromInput input)

-- Continuation preparation
{-|
Converts a partial parser into a return continuation in a manner similar
to `buildHandler`.

@since 1.8.0.0
-}
suspend :: (Γ s o (x : xs) n r a -> Code (ST s (Result () a))) -- ^ The partial parser to turn into a return continuation.
        -> Γ s o xs n r a                                  -- ^ The state to execute the continuation with.
        -> (Input# o -> Input o)                           -- ^ Function used to generate the offset
        -> StaCont s o a x
suspend m γ off = mkStaCont $ \x o# -> m (γ {operands = Op (FREEVAR x) (operands γ), input = off o#})

{-|
Combines `suspend` and `callWithContinuation`, simultaneously performing
an optimisation on the offset if the subroutine has known input characteristics.

@since 1.5.0.0
-}
callCC :: forall s o xs n r a x. MarshalOps o
       => Word                                                   --
       -> StaSubroutine s o a x                                  -- ^ The subroutine @sub@ that will be called.
       -> (Γ s o (x : xs) (Succ n) r a -> Code (ST s (Result () a))) -- ^ The return continuation to generate
       -> Γ s o xs (Succ n) r a                                  --
       -> Code (ST s (Result () a))
callCC u sub k γ = callWithContinuation sub (suspend k γ (chooseInput (successInputCharacteristic (meta sub)) u inp)) inp (handlers γ)
  where
    inp :: Input o
    inp = input γ

{- Join Point Operations -}
{-|
Wraps around `setupJoinPoint#` to make a join point and register it
into the `Ctx`.

@since 1.4.0.0
-}
setupJoinPoint :: forall s o xs n r a x. JoinBuilder o
               => ΦVar x                     -- ^ The name of the binding.
               -> Machine s o a (x : xs) n r -- ^ The definition of the binding.
               -> Machine s o a xs n r       -- ^ The scope within which the binding is valid.
               -> MachineMonad s o a xs n r
setupJoinPoint φ (Machine k) mx = freshUnique $ \u ->
    liftM2 (\mk ctx γ ->
      setupJoinPoint# @o
        (\qx inp -> mk (γ {operands = Op (FREEVAR qx) (operands γ), input = toInput u inp}))
        (\qjoin -> run mx γ (insertΦ φ (mkStaContDyn qjoin) ctx)))
      (local voidCoins k) ask

{- Iteration Operations -}
{-|
Uses `bindIterHandler#` and `bindIter#` to create an iterated parser
from its loop body and return continuation. The exit of a loop is done
using failure, and this failure does not discriminate whether or not
the loop consumed input in its final iteration.

@since 1.8.0.0
-}
bindIterAlways :: forall s o a. RecBuilder o
               => Ctx s o a                  -- ^ The context to keep the binding
               -> MVar Void                  -- ^ The name of the binding.
               -> Machine s o a '[] One Void -- ^ The body of the loop.
               -> Bool                       -- ^ Does loop exit require a binding?
               -> StaHandlerBuilder s o a    -- ^ What to do after the loop exits (by failing)
               -> Input o                    -- ^ The initial offset to provide to the loop
               -> Word                       -- ^ The unique name for captured offset /and/ iteration offset
               -> Code (ST s (Result () a))
bindIterAlways ctx μ l needed h inp u =
  bindIterHandlerInline# @o needed (staHandler# . h . toInput u) $ \qhandler ->
    bindIter# @o (fromInput inp) $ \qloop inp# ->
      let inp = toInput u inp#
      in run l (Γ Empty noreturn inp (VCons (augmentHandler (Just inp) (qhandler inp#)) VNil))
               (voidCoins (insertSub μ (mkStaSubroutine $ \_ _ inp -> [|| $$qloop $$(pos# inp) $$(off# inp) ||]) ctx))

{-|
Similar to `bindIterAlways`, but builds a handler that performs in
the same way as `bindSameHandler`.

@since 2.1.0.0
-}
bindIterSame :: forall s o a. (RecBuilder o, HandlerOps o, PositionOps (Rep o))
             => Ctx s o a                  -- ^ The context to store the binding in.
             -> MVar Void                  -- ^ The name of the binding.
             -> Machine s o a '[] One Void -- ^ The loop body.
             -> Bool                       -- ^ Is a binding required for the matching handler?
             -> StaHandler s o a           -- ^ The handler when input is the same.
             -> Bool                       -- ^ Is a binding required for the differing handler?
             -> StaHandlerBuilder s o a    -- ^ The handler when input differs.
             -> Input o                    -- ^ The initial offset of the loop.
             -> Word                       -- ^ The unique name of the captured offsets /and/ the iteration offset.
             -> Code (ST s (Result () a))
bindIterSame ctx μ l neededYes yes neededNo no inp u =
  bindHandlerInline# @o neededYes (staHandler# yes) $ \qyes ->
    bindIterHandlerInline# neededNo (staHandler# . no . toInput u) $ \qno ->
      let handler inpc inpo = [||if $$(same (off# inpc) (off# inpo)) then $$(staHandler# qyes inpc) else $$(staHandler# (qno inpc) inpo)||]
      in bindIterHandlerInline# @o True handler $ \qhandler ->
        bindIter# @o (fromInput inp) $ \qloop inp# ->
          let off = toInput u inp#
          in run l (Γ Empty noreturn off (VCons (augmentHandlerFull off (qhandler inp#) (staHandler# qyes inp#) (qno inp#)) VNil))
                   (voidCoins (insertSub μ (mkStaSubroutine $ \_ _ inp -> [|| $$qloop $$(pos# inp) $$(off# inp) ||]) ctx))

{- Recursion Operations -}
{-|
Wraps around `bindRec#` to produce a recursive parser binding. This function
also provides all the free-registers which are closed over by the binding.
This eliminates recursive calls from having to pass all of the same registers
each time round.

@since 1.5.0.0
-}
buildRec :: forall rs s o a r. RecBuilder o
         => MVar r                  -- ^ The name of the binding.
         -> Regs rs                 -- ^ The registered required by the binding.
         -> Ctx s o a               -- ^ The context to re-insert the register-less binding
         -> Machine s o a '[] One r -- ^ The body of the binding.
         -> Metadata                -- ^ The metadata associated with the binding
         -> DynFunc rs s o a r
buildRec μ rs ctx k meta =
  takeFreeRegisters rs ctx $ \ctx ->
    bindRec# @o $ \qself qret qh inp ->
      run k (Γ Empty (mkStaContDyn qret) (toInput 0 inp) (VCons (augmentHandlerDyn Nothing qh) VNil))
            (insertSub μ (mkStaSubroutineMeta meta $ \k h inp -> [|| $$qself $$k $$h $$(pos# inp) $$(off# inp) ||]) (nextUnique ctx))

{- Binding Operations -}
bindHandlerInline# :: forall o s a b. HandlerOps o
                   => Bool
                   -> StaHandler# s o a
                   -> (StaHandler s o a -> Code b)
                   -> Code b
bindHandlerInline# True  h k = bindHandler# @o h (k . fromDynHandler)
bindHandlerInline# False h k = k (fromStaHandler# h)

bindYesInline# :: Bool -> Code a -> (Code a -> Code b) -> Code b
bindYesInline# True  v k = [|| let yesSame = $$v in $$(k [||yesSame||]) ||]
bindYesInline# False v k = k v

bindIterHandlerInline# :: forall o s a b. RecBuilder o
                       => Bool
                       -> (Input# o -> StaHandler# s o a)
                       -> ((Input# o -> StaHandler s o a) -> Code b)
                       -> Code b
bindIterHandlerInline# True  h k = bindIterHandler# @o h $ \qh -> k (\inp -> fromDynHandler [||$$qh $$(pos# inp) $$(off# inp)||])
bindIterHandlerInline# False h k = k (fromStaHandler# . h)

{- Marshalling Operations -}
{-|
Wraps around `dynHandler#`, but ensures that if the `StaHandler`
originated from a `DynHandler` itself, that no work is performed.

Takes in an `InputCharacteristic`, which is used to refine the
handler given knowledge about how it might be used.

@since 1.5.0.0
-}
dynHandler :: forall s o a. MarshalOps o => AugmentedStaHandler s o a -> InputCharacteristic -> DynHandler s o a
dynHandler h = staHandlerCharacteristicDyn h (eta . dynHandler# @o)

{-|
Wraps around `dynCont#`, but ensures that if the `StaCont`
originated from a `DynCont` itself, that no work is performed.

@since 1.4.0.0
-}
dynCont :: forall s o a x. MarshalOps o => StaCont s o a x -> DynCont s o a x
dynCont (StaCont sk Nothing)  = eta (dynCont# @o sk)
dynCont (StaCont _ (Just dk)) = dk

{- Log Operations =-}
{-|
The specialised handler for the @debug@ combinator. It will fail again after
having printed the debug information.

@since 1.2.0.0
-}
logHandler :: (?ops :: InputOps (Rep o), LogHandler o) => String -> Ctx s o a -> Γ s o xs (Succ n) ks a -> Word -> StaHandlerBuilder s o a
logHandler name ctx γ u _ = let VCons h _ = handlers γ in fromStaHandler# $ \inp# -> let inp = toInput u inp# in [||
    trace $$(preludeString name '<' (γ {input = inp}) ctx (color Red " Fail")) $$(staHandlerEval h inp)
  ||]

{-|
Used for the debug instructions and handler, produces the debugging information
string.

@since 1.2.0.0
-}
preludeString :: forall s o xs n r a. (?ops :: InputOps (Rep o), LogHandler o)
              => String         -- ^ The name as per the debug combinator
              -> Char           -- ^ Either @<@ or @>@ depending on whether we are entering or leaving.
              -> Γ s o xs n r a
              -> Ctx s o a
              -> String         -- ^ String that represents the current status
              -> Code String
preludeString name dir γ ctx ends = [|| concat [$$prelude, $$eof, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    offset          = Offset.offset (off (input γ))
    indent          = replicate (debugLevel ctx * 2) ' '
    start           = shiftLeft offset [||5#||]
    end             = shiftRight offset [||5#||]
    inputTrace      = [|| let replace '\n' = color Green "↙"
                              replace ' '  = color White "·"
                              replace c    = return c
                              go i#
                                | $$(same [||i#||] end) || not $$(more [||i#||]) = []
                                | otherwise = $$(next [||i#||] (\qc qi' -> [||replace $$qc ++ go $$qi'||]))
                          in go $$start ||]
    eof             = [|| if $$(more end) then $$inputTrace else $$inputTrace ++ color Red "•" ||]
    prelude         = [|| concat [indent, dir : name, dir : " (", show $$(offToInt offset), "): "] ||]
    caretSpace      = [|| replicate (length $$prelude + $$(offToInt offset) - $$(offToInt start)) ' ' ||]

{- Convenience Types -}
{-|
A convience bundle of all of the type class constraints.

@since 1.0.0.0
-}
type Ops o =
  ( HandlerOps o
  , JoinBuilder o
  , RecBuilder o
  , PositionOps (Rep o)
  , MarshalOps o
  , LogOps (Rep o)
  )

{-|
The constraints needed to build a `logHandler`.

@since 1.0.0.0
-}
type LogHandler o = (PositionOps (Rep o), LogOps (Rep o))

{-|
A `StaHandler` that has not yet captured its offset.

@since 1.2.0.0
-}
type StaHandlerBuilder s o a = Input o -> StaHandler s o a

{-|
A "yes-handler" that has not yet captured its offset

@since 2.1.0.0
-}
type StaYesHandler s o a = Input o -> Code (ST s (Result () a))
