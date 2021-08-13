{-# LANGUAGE OverloadedStrings,
             PatternSynonyms,
             DerivingStrategies #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Instructions
Description : Core instructions that make up a low-level parser.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This contains the instructions and satelite datatypes for representing
parsers at the lowest CPS-form level. These are indexed by multiple types,
which are documented in the source (if not on Haddock!).

@since 1.0.0.0
-}
module Parsley.Internal.Backend.Machine.Instructions (
    -- * Main Instructions
    Instr(..),
    -- * Auxilliary Types
    Handler(..),
    Access(..),
    MetaInstr(..),
    -- * Smart Instructions
    _App, _Fmap, _Modify, _Make, _Put, _Get,
    -- * Smart Meta-Instructions
    addCoins, refundCoins, drainCoins, giveBursary, prefetchChar, blockCoins
  ) where

import Data.Kind                                    (Type)
import Data.Void                                    (Void)
import Parsley.Internal.Backend.Machine.Identifiers (MVar, ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.Types.Coins (Coins(Coins))
import Parsley.Internal.Common                      (IFunctor4, Fix4(In4), Const4(..), imap4, cata4, Nat(..), One, intercalateDiff)

import Parsley.Internal.Backend.Machine.Defunc as Machine (Defunc, user)
import Parsley.Internal.Core.Defunc            as Core    (Defunc(ID), pattern FLIP_H)

{-|
This represents the instructions of the machine, in CPS form as an indexed functor.

When an instruction has a `Succ` in the type, it indicates that it is capable of failing.

@since 1.4.0.0
-}
data Instr (o :: Type)                                  -- The FIXED input type
           (k :: [Type] -> Nat -> Type -> Type -> Type) -- The FIXED continuation parameter
           (xs :: [Type])                               -- The VARIABLE type defining the required types on the stack on entry
           (n :: Nat)                                   -- The VARIABLE type defining how many handlers are required on entry
           (r :: Type)                                  -- The VARIABLE intermediate type defining what value this parser immediately produces
           (a :: Type)                                  -- The (technically VARIABLE) type specifying the final result of the parser
  where
  {-| This instruction returns from either calls or the entire parser at the top-level.

  @since 1.0.0.0 -}
  Ret       :: Instr o k '[x] n x a {- ^ -}
  {-| Pushes a value onto the stack, which is required by the continuation parameter.

  @since 1.0.0.0 -}
  Push      :: Machine.Defunc x {- ^ Value to push. -} -> k (x : xs) n r a {- ^ Machine requiring value. -} -> Instr o k xs n r a
  {-| Removes a value from the stack, so it is the correct shape for the continuation parameter.

  @since 1.0.0.0 -}
  Pop       :: k xs n r a {- ^ -} -> Instr o k (x : xs) n r a
  {-| Applies a function to the top two elements of the stack, converting them to something else and pushing it back on.

  @since 1.0.0.0 -}
  Lift2     :: Machine.Defunc (x -> y -> z) {- ^ Function to apply. -}
            -> k (z : xs) n r a             {- ^ Machine requiring new value. -}
            -> Instr o k (y : x : xs) n r a
  {-| Reads a character so long as it matches a given predicate. If it does not, or no input is available, this instruction fails.

  @since 1.0.0.0 -}
  Sat       :: Machine.Defunc (Char -> Bool) {- ^ Predicate to apply. -}
            -> k (Char : xs) (Succ n) r a    {- ^ Machine requiring read character. -}
            -> Instr o k xs (Succ n) r a
  {-| Calls another let-bound parser.

  @since 1.0.0.0 -}
  Call      :: MVar x                  {- ^ The binding to invoke. -}
            -> k (x : xs) (Succ n) r a {- ^ Continuation to do after the call. -}
            -> Instr o k xs (Succ n) r a
  {-| Jumps to another let-bound parser tail-recursively.

  @since 1.0.0.0 -}
  Jump      :: MVar x {- ^ The binding to jump to. -} -> Instr o k '[] (Succ n) x a
  {-| Fails unconditionally.

  @since 1.0.0.0 -}
  Empt      :: Instr o k xs (Succ n) r a {- ^ -}
  {-| Discards a failure handler, so that it is no longer in scope.

  @since 1.0.0.0 -}
  Commit    :: k xs n r a {- ^ Next machine, which will /not/ require the discarded handler. -} -> Instr o k xs (Succ n) r a
  {-| Registers a handler to deal with possible failure in the given machine.

  @since 1.4.0.0 -}
  Catch     :: k xs (Succ n) r a          {- ^ Machine where failure is handled by the handler. -}
            -> Handler o k (o : xs) n r a {- ^ The handler to register. -}
            -> Instr o k xs n r a
  {-| Pushes the current input offset onto the stack.

  @since 1.0.0.0 -}
  Tell      :: k (o : xs) n r a {- ^ The machine that accepts the input. -} -> Instr o k xs n r a
  {-| Pops the input offset off of the stack and makes that the current input offset.

  @since 1.0.0.0 -}
  Seek      :: k xs n r a {- ^ Machine to continue with new input. -} -> Instr o k (o : xs) n r a
  {-| Picks one of two continuations based on whether a `Left` or `Right` is on the stack.

  @since 1.0.0.0 -}
  Case      :: k (x : xs) n r a {- ^ Machine to execute if `Left` on stack. -}
            -> k (y : xs) n r a {- ^ Machine to execute if `Right` on stack. -}
            -> Instr o k (Either x y : xs) n r a
  {-| Given a collection of predicates and machines, this instruction will execute the first machine
      for which the corresponding predicate returns true for the value on the top of the stack.

  @since 1.0.0.0 -}
  Choices   :: [Machine.Defunc (x -> Bool)] {- ^ A list of predicates to try. -}
            -> [k xs n r a]                 {- ^ A corresponding list of machines. -}
            -> k xs n r a                   {- ^ A default machine to execute if no predicates match. -}
            -> Instr o k (x : xs) n r a
  {-| Sets up an iteration, where the second argument is executed repeatedly until it fails, which is
      handled by the given handler. The use of `Void` indicates that `Ret` is illegal within the loop.

  @since 1.0.0.0 -}
  Iter      :: MVar Void                  {- ^ The name of the binding. -}
            -> k '[] One Void a           {- ^ The body of the loop: it cannot return "normally". -}
            -> Handler o k (o : xs) n r a {- ^ The handler for the loop's exit. -}
            -> Instr o k xs n r a
  {-| Jumps to a given join point.

  @since 1.0.0.0 -}
  Join      :: ΦVar x {- ^ The join point to jump to. -} -> Instr o k (x : xs) n r a
  {-| Sets up a new join point binding.

  @since 1.0.0.0 -}
  MkJoin    :: ΦVar x           {- ^ The name of the binding that can be referred to later. -}
            -> k (x : xs) n r a {- ^ The body of the join point binding. -}
            -> k xs n r a       {- ^ The scope within which the binding is valid.  -}
            -> Instr o k xs n r a
  {-| Swaps the top two elements on the stack

  @since 1.0.0.0 -}
  Swap      :: k (x : y : xs) n r a {- ^ The machine that requires the reversed stack. -} -> Instr o k (y : x : xs) n r a
  {-| Duplicates the top value on the stack. May produce a let-binding.

  @since 1.0.0.0 -}
  Dup       :: k (x : x : xs) n r a {- ^ Machine that requires doubled element. -} -> Instr o k (x : xs) n r a
  {-| Initialises a new register for use within the continuation. Initial value is on the stack.

  @since 1.0.0.0 -}
  Make      :: ΣVar x     {- ^ The name of the new register. -}
            -> Access     {- ^ Whether or not the register is "concrete". -}
            -> k xs n r a {- ^ The scope within which the register is accessible. -}
            -> Instr o k (x : xs) n r a
  {-| Pushes the value contained within a register onto the stack.

  @since 1.0.0.0 -}
  Get       :: ΣVar x           {- ^ Name of the register to read. -}
            -> Access           {- ^ Whether or not the value is cached. -}
            -> k (x : xs) n r a {- ^ The machine that requires the value. -}
            -> Instr o k xs n r a
  {-| Places the value on the top of the stack into a given register.

  @since 1.0.0.0 -}
  Put       :: ΣVar x     {- ^ Name of the register to update. -}
            -> Access     {- ^ Whether or not the value needs to be stored in a concrete register. -}
            -> k xs n r a
            -> Instr o k (x : xs) n r a
  {-| Begins a debugging scope, the inner scope requires /two/ handlers,
      the first is the log handler itself, and then the second is the
      "real" fail handler for when the log handler is executed.

  @since 1.0.0.0 -}
  LogEnter  :: String                   {- ^ The message to be printed. -}
            -> k xs (Succ (Succ n)) r a {- ^ The machine to be debugged. -}
            -> Instr o k xs (Succ n) r a
  {-| Ends the log scope after a succesful execution.

  @since 1.0.0.0 -}
  LogExit   :: String     {- ^ The message to be printed. -}
            -> k xs n r a {- ^ The machine that follows. -}
            -> Instr o k xs n r a
  {-| Executes a meta-instruction, which is interacting with
      implementation specific static information.

  @since 1.0.0.0 -}
  MetaInstr :: MetaInstr n {- ^ A meta-instruction to perform. -}
            -> k xs n r a  {- ^ The machine that follows. -}
            -> Instr o k xs n r a

{-|
There are two types of organic handlers within parsley, which are
captured by this type, which is also an IFunctor and wraps around
`Instr`.

@since 1.4.0.0
-}
data Handler (o :: Type) (k :: [Type] -> Nat -> Type -> Type -> Type) (xs :: [Type]) (n :: Nat) (r :: Type) (a :: Type) where
  {-| These handlers have two distinct behaviours depending on whether the
      captured offset matches the current offset or not.

  @since 1.4.0.0 -}
  Same :: Bool             -- ^ Whether the input matches handler should generate a binding
       -> k xs n r a       -- ^ Execute when the input matches, notice that the captured offset is discarded since it is equal to the current.
       -> Bool             -- ^ Whether the input does not match handler should generate a binding
       -> k (o : xs) n r a -- ^ Execute when the input does not match, the resulting behaviour could use the captured or current input.
       -> Handler o k (o : xs) n r a
  {-| These handlers are unconditional on the input, and will always do the same
      thing regardless of the input provided.

  @since 1.7.0.0 -}
  Always :: Bool             -- ^ Whether the handler should generate a binding
         -> k (o : xs) n r a -- ^ The handler
         -> Handler o k (o : xs) n r a

{-|
This determines whether or not an interaction with an register should be materialised
in the generated code or not.

@since 1.0.0.0
-}
data Access = Hard -- ^ Register exists at runtime and this interaction will use it.
            | Soft -- ^ Register may not exist, and the interaction should be with cache regardless.
            deriving stock Show

{-|
These are meta-instructions, which interact with static information to direct the
code-generation process. They are not formally part of parsley's semantics and can
be omitted from an implementation without consequence.

@since 1.0.0.0
-}
data MetaInstr (n :: Nat) where
  {-| Adds coins to the piggy-bank system (see "Parsley.Internal.Backend.Machine.Types.Context" for more information).
      If there are coins already available, add a piggy-bank, otherwise generate a length check and add the coins.

      A handler is required, in case the length check fails.

  @since 1.5.0.0 -}
  AddCoins    :: Coins -> MetaInstr (Succ n)
  {-| Refunds to the piggy-bank system (see "Parsley.Internal.Backend.Machine.Types.Context" for more information).
      This always happens for free, and is added straight to the coins.

  @since 1.5.0.0 -}
  RefundCoins :: Coins -> MetaInstr n
  {-| Remove coins from piggy-bank system (see "Parsley.Internal.Backend.Machine.Types.Context" for more information)
      This is used to pay for more expensive calls to bindings with known required input.

      A handler is required, as there may not be enough coins to pay the cost and a length check causes a failure.

  @since 1.5.0.0 -}
  DrainCoins  :: Coins -> MetaInstr (Succ n)
  {-| Refunds to the piggy-bank system (see "Parsley.Internal.Backend.Machine.Types.Context" for more information).
      This always happens for free, and is added straight to the coins. Unlike `RefundCoins` this cannot reclaim
      input, nor is is subtractive in the analysis.

  @since 1.5.0.0 -}
  GiveBursary :: Coins -> MetaInstr n
  {-| Fetches a character to read in advance. This is used to factor out a common token from alternatives.
      The boolean argument represents whether or not the read is covered by a factored length check, or
      requires its own.

  @since 1.5.0.0 -}
  PrefetchChar :: Bool -> MetaInstr (Succ n)
  {-|
  True meta instruction: does /nothing/ except for reset coin count during coin analysis.

  @since 1.6.0.0
  -}
  BlockCoins :: MetaInstr n

mkCoin :: (Coins -> MetaInstr n) -> Coins -> Fix4 (Instr o) xs n r a -> Fix4 (Instr o) xs n r a
mkCoin _    (Coins 0 0) = id
mkCoin meta n           = In4 . MetaInstr (meta n)

{-|
Smart-constuctor around `AddCoins`.

@since 1.5.0.0
-}
addCoins :: Coins -> Fix4 (Instr o) xs (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a
addCoins (Coins 1 1) = id
addCoins coins       = mkCoin AddCoins coins

{-|
Smart-constuctor around `RefundCoins`.

@since 1.5.0.0
-}
refundCoins :: Coins -> Fix4 (Instr o) xs n r a -> Fix4 (Instr o) xs n r a
refundCoins = mkCoin RefundCoins

{-|
Smart-constuctor around `DrainCoins`.

@since 1.5.0.0
-}
drainCoins :: Coins -> Fix4 (Instr o) xs (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a
drainCoins = mkCoin DrainCoins

{-|
Smart-constuctor around `RefundCoins`.

@since 1.5.0.0
-}
giveBursary :: Coins -> Fix4 (Instr o) xs n r a -> Fix4 (Instr o) xs n r a
giveBursary = mkCoin GiveBursary

{-|
Smart-constructor around `PrefetchChar`.

@since 1.5.0.0
-}
prefetchChar :: Bool -> Fix4 (Instr o) xs (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a
prefetchChar check = In4 . MetaInstr (PrefetchChar check)

{-|
Smart-constructor around `PrefetchChar`.

@since 1.6.0.0
-}
blockCoins :: Fix4 (Instr o) xs (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a
blockCoins = In4 . MetaInstr BlockCoins

{-|
Applies a value on the top of the stack to a function on the second-most top of the stack.

@since 1.0.0.0
-}
_App :: Fix4 (Instr o) (y : xs) n r a -> Instr o (Fix4 (Instr o)) (x : (x -> y) : xs) n r a
_App = Lift2 (user ID)

{-|
Adjusts the value on the top of the stack with the given function.

@since 1.0.0.0
-}
_Fmap :: Machine.Defunc (x -> y) -> Fix4 (Instr o) (y : xs) n r a -> Instr o (Fix4 (Instr o)) (x : xs) n r a
_Fmap f k = Push f (In4 (Lift2 (user (FLIP_H ID)) k))

{-|
Updates the value in a given register using the function on the top of the stack.

@since 1.0.0.0
-}
_Modify :: ΣVar x -> Fix4 (Instr o) xs n r a -> Instr o (Fix4 (Instr o)) ((x -> x) : xs) n r a
_Modify σ  = _Get σ . In4 . _App . In4 . _Put σ

{-|
Smart-instruction for `Make` that uses a `Hard` access.

@since 1.0.0.0
-}
_Make :: ΣVar x -> k xs n r a -> Instr o k (x : xs) n r a
_Make σ = Make σ Hard

{-|
Smart-instruction for `Put` that uses a `Hard` access.

@since 1.0.0.0
-}
_Put :: ΣVar x -> k xs n r a -> Instr o k (x : xs) n r a
_Put σ = Put σ Hard

{-|
Smart-instruction for `Get` that uses a `Hard` access.

@since 1.0.0.0
-}
_Get :: ΣVar x -> k (x : xs) n r a -> Instr o k xs n r a
_Get σ = Get σ Hard

-- Instances
instance IFunctor4 (Instr o) where
  imap4 _ Ret                 = Ret
  imap4 f (Push x k)          = Push x (f k)
  imap4 f (Pop k)             = Pop (f k)
  imap4 f (Lift2 g k)         = Lift2 g (f k)
  imap4 f (Sat g k)           = Sat g (f k)
  imap4 f (Call μ k)          = Call μ (f k)
  imap4 _ (Jump μ)            = Jump μ
  imap4 _ Empt                = Empt
  imap4 f (Commit k)          = Commit (f k)
  imap4 f (Catch p h)         = Catch (f p) (imap4 f h)
  imap4 f (Tell k)            = Tell (f k)
  imap4 f (Seek k)            = Seek (f k)
  imap4 f (Case p q)          = Case (f p) (f q)
  imap4 f (Choices fs ks def) = Choices fs (map f ks) (f def)
  imap4 f (Iter μ l h)        = Iter μ (f l) (imap4 f h)
  imap4 _ (Join φ)            = Join φ
  imap4 f (MkJoin φ p k)      = MkJoin φ (f p) (f k)
  imap4 f (Swap k)            = Swap (f k)
  imap4 f (Dup k)             = Dup (f k)
  imap4 f (Make σ a k)        = Make σ a (f k)
  imap4 f (Get σ a k)         = Get σ a (f k)
  imap4 f (Put σ a k)         = Put σ a (f k)
  imap4 f (LogEnter name k)   = LogEnter name (f k)
  imap4 f (LogExit name k)    = LogExit name (f k)
  imap4 f (MetaInstr m k)     = MetaInstr m (f k)

instance IFunctor4 (Handler o) where
  imap4 f (Same gyes yes gno no) = Same gyes (f yes) gno (f no)
  imap4 f (Always gk k)          = Always gk (f k)

instance Show (Fix4 (Instr o) xs n r a) where
  show = ($ "") . getConst4 . cata4 (Const4 . alg)
    where
      alg :: forall xs n r a. Instr o (Const4 (String -> String)) xs n r a -> String -> String
      alg Ret                      = "Ret"
      alg (Call μ k)               = "(Call " . shows μ . " " . getConst4 k . ")"
      alg (Jump μ)                 = "(Jump " . shows μ . ")"
      alg (Push x k)               = "(Push " . shows x . " " . getConst4 k . ")"
      alg (Pop k)                  = "(Pop " . getConst4 k . ")"
      alg (Lift2 f k)              = "(Lift2 " . shows f . " " . getConst4 k . ")"
      alg (Sat f k)                = "(Sat " . shows f . " " . getConst4 k . ")"
      alg Empt                     = "Empt"
      alg (Commit k)               = "(Commit " . getConst4 k . ")"
      alg (Catch p h)              = "(Catch " . getConst4 p . " " . shows h . ")"
      alg (Tell k)                 = "(Tell " . getConst4 k . ")"
      alg (Seek k)                 = "(Seek " . getConst4 k . ")"
      alg (Case p q)               = "(Case " . getConst4 p . " " . getConst4 q . ")"
      alg (Choices fs ks def)      = "(Choices " . shows fs . " [" . intercalateDiff ", " (map getConst4 ks) . "] " . getConst4 def . ")"
      alg (Iter μ l h)             = "{Iter " . shows μ . " " . getConst4 l . " " . shows h . "}"
      alg (Join φ)                 = shows φ
      alg (MkJoin φ p k)           = "(let " . shows φ . " = " . getConst4 p . " in " . getConst4 k . ")"
      alg (Swap k)                 = "(Swap " . getConst4 k . ")"
      alg (Dup k)                  = "(Dup " . getConst4 k . ")"
      alg (Make σ a k)             = "(Make " . shows σ . " " . shows a . " " . getConst4 k . ")"
      alg (Get σ a k)              = "(Get " . shows σ . " " . shows a . " " . getConst4 k . ")"
      alg (Put σ a k)              = "(Put " . shows σ . " " . shows a . " " . getConst4 k . ")"
      alg (LogEnter _ k)           = getConst4 k
      alg (LogExit _ k)            = getConst4 k
      alg (MetaInstr BlockCoins k) = getConst4 k
      alg (MetaInstr m k)          = "[" . shows m . "] " . getConst4 k

instance Show (Handler o (Const4 (String -> String)) (o : xs) n r a) where
  show (Same _ yes _ no) = "(Dup (Tell (Lift2 same (If " (getConst4 yes (" " (getConst4 no "))))")))
  show (Always _ k)      = getConst4 k ""

instance Show (MetaInstr n) where
  show (AddCoins n)     = "Add " ++ show n ++ " coins"
  show (RefundCoins n)  = "Refund " ++ show n ++ " coins"
  show (DrainCoins n)   = "Using " ++ show n ++ " coins"
  show (GiveBursary n)  = "Bursary of " ++ show n ++ " coins"
  show (PrefetchChar b) = "Prefetch character " ++ (if b then "with" else "without") ++ " length-check"
  show BlockCoins       = ""
