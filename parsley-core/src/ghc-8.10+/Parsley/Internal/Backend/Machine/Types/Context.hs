{-# LANGUAGE DeriveAnyClass,
             MagicHash,
             DerivingStrategies,
             UnboxedTuples,
             PatternSynonyms #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Types.Context
Description : Fully static context required to generate a parser
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the compile-time state of a parser, which is
used to aid code generation.

@since 1.4.0.0
-}
module Parsley.Internal.Backend.Machine.Types.Context (
    -- * Core Data-types
    Ctx,
    QJoin,
    emptyCtx,

    -- * Subroutines
    -- $sub-doc
    insertSub, askSub,

    -- * Join Points
    -- $join-doc
    insertΦ, askΦ,

    -- * Registers
    -- $reg-doc

    -- ** Putters
    insertNewΣ, cacheΣ,
    -- ** Getters
    concreteΣ, cachedΣ,
    takeFreeRegisters,

    -- * Debug Level Tracking
    -- $debug-doc
    debugUp, debugDown, debugLevel,

    -- * Unique Offsets
    -- $offset-doc
    freshUnique, nextUnique,

    -- * Token Credit System (Piggy-banks)
    -- $piggy-doc

    -- ** Modifiers
    storePiggy, breakPiggy, spendCoin, giveCoins, refundCoins, voidCoins,
    -- ** Getters
    coins, hasCoin, isBankrupt, canAfford,
    -- ** Input Reclamation
    addChar, readChar
  ) where

import Control.Exception                               (Exception, throw)
import Control.Monad                                   (liftM2, (<=<))
import Control.Monad.Reader                            (asks, local, MonadReader)
import Data.STRef                                      (STRef)
import Data.Dependent.Map                              (DMap)
import Data.Maybe                                      (fromMaybe)
import Parsley.Internal.Backend.Machine.Defunc         (Defunc)
import Parsley.Internal.Backend.Machine.Identifiers    (MVar(..), ΣVar(..), ΦVar, IMVar, IΣVar)
import Parsley.Internal.Backend.Machine.LetBindings    (Regs(..))
import Parsley.Internal.Backend.Machine.Types.Coins    (Coins, willConsume, canReclaim)
import Parsley.Internal.Backend.Machine.Types.Dynamics (DynFunc, DynSubroutine)
import Parsley.Internal.Backend.Machine.Types.Input    (Input)
import Parsley.Internal.Backend.Machine.Types.Statics  (QSubroutine(..), StaFunc, StaSubroutine, StaCont)
import Parsley.Internal.Common                         (Queue, enqueue, dequeue, poke, Code, RewindQueue)
import Parsley.Internal.Core.CharPred                  (CharPred, pattern Item, andPred)

import qualified Data.Dependent.Map                           as DMap  ((!), insert, empty, lookup)
import qualified Parsley.Internal.Common.QueueLike            as Queue (empty, null)
import qualified Parsley.Internal.Common.RewindQueue          as Queue (rewind)

-- Core Data-types
{-|
The `Ctx` stores information that aids or facilitates the generation of parser code,
but its components are fully static and do not materialise as runtime values, but
may form part of the generated code.

@since 1.0.0.0
-}
data Ctx s o a = Ctx { μs         :: !(DMap MVar (QSubroutine s o a))              -- ^ Map of subroutine bindings.
                     , φs         :: !(DMap ΦVar (QJoin s o a))                    -- ^ Map of join point bindings.
                     , σs         :: !(DMap ΣVar (Reg s))                          -- ^ Map of available registers.
                     , debugLevel :: {-# UNPACK #-} !Int                           -- ^ Approximate depth of debug combinator.
                     , coins      :: {-# UNPACK #-} !Int                           -- ^ Number of tokens free to consume without length check.
                     , offsetUniq :: {-# UNPACK #-} !Word                          -- ^ Next unique offset identifier.
                     , piggies    :: !(Queue Coins)                                -- ^ Queue of future length check credit.
                     , knownChars :: !(RewindQueue (Code Char, CharPred, Input o)) -- ^ Characters that can be reclaimed on backtrack.
                     }

{-|
`QJoin` represents Φ-nodes in the generated parser, and is represented
as a `Parsley.Internal.Backend.Machine.Types.Statics.StaCont`.

@since 1.0.0.0
-}
newtype QJoin s o a x = QJoin { unwrapJoin :: StaCont s o a x }

{-|
Creates an empty `Ctx` populated with a map of the top-level (recursive)
bindings: information about their required free-registers is included.

@since 1.0.0.0
-}
emptyCtx :: DMap MVar (QSubroutine s o a) -> Ctx s o a
emptyCtx μs = Ctx μs DMap.empty DMap.empty 0 0 0 Queue.empty Queue.empty

-- Subroutines
{- $sub-doc
Subroutines are the representations of let-bindings or recursive parsers
in the original user program. They are factored out to prevent code-explosion.

The names of these bindings are helpfully stored within the `Ctx` and can be
accessed statically. While the initial context is always populated with the
top-level recursive bindings, additional bindings can be added "dynamically"
during evaluation, for instance iterative bindings and recursive bindings that
capture their free-registers.
-}
{-|
Registers a new subroutine into the context, which will be available
according to "local" @Reader@ semantics.

@since 1.2.0.0
-}
insertSub :: MVar x                -- ^ The name of the binding.
          -> StaSubroutine s o a x -- ^ The binding to register.
          -> Ctx s o a             -- ^ The current context.
          -> Ctx s o a             -- ^ The new context.
insertSub μ q ctx = ctx {μs = DMap.insert μ (QSubroutine q NoRegs) (μs ctx)}

{-|
Fetches a binding from the context according to its name (See `Parsley.Internal.Core.Identifiers.MVar`).
In the (hopefully impossible!) event that it is not found in the map, will throw a @MissingDependency@
exception. If this binding had free registers, these are generously provided by the `Ctx`.

@since 1.2.0.0
-}
askSub :: MonadReader (Ctx s o a) m => MVar x -> m (StaSubroutine s o a x)
askSub μ =
  do QSubroutine sub rs <- askSubUnbound μ
     asks (provideFreeRegisters sub rs)

askSubUnbound :: MonadReader (Ctx s o a) m => MVar x -> m (QSubroutine s o a x)
askSubUnbound μ = asks (fromMaybe (throw (missingDependency μ)) . DMap.lookup μ . μs)

-- Join Points
{- $join-doc
Similar to the subroutines, join points (or Φ-nodes) are used by the parsley engine
to factor out common branches of code. When generated, access to these bindings is
available via the `Ctx`.
-}
{-|
Registers a new binding into the `Ctx` so that it can be retrieved later. Binding
expires according to "local" @Reader@ semantics.

@since 1.0.0.0
-}
insertΦ :: ΦVar x          -- ^ The name of the new binding.
        -> StaCont s o a x -- ^ The binding to add.
        -> Ctx s o a       -- ^ The old context.
        -> Ctx s o a       -- ^ The new context.
insertΦ φ qjoin ctx = ctx {φs = DMap.insert φ (QJoin qjoin) (φs ctx)}

{-|
Fetches a binding from the `Ctx`.

@since 1.2.0.0
-}
askΦ :: MonadReader (Ctx s o a) m => ΦVar x -> m (StaCont s o a x)
askΦ φ = asks (unwrapJoin . (DMap.! φ) . φs)

-- Registers
{- $reg-doc
Registers are used within parsley to persist state across different parts of a parser.
Across recursion and call-boundaries, these materialise as @STRef@s. These are stored
in the `Ctx` and can be looked up when required.

However, parsley does not mandate that registers /must/ exist in this form. Registers
can be subject to caching, where a register's static "most-recently known" may be
stored within the `Ctx` in addition to the "true" binding. This can, in effect, mean
that registers do not exist at runtime. Both forms of register data can be extracted,
however exceptions will guard against mis-management.
-}
data Reg s x = Reg { getReg    :: Maybe (Code (STRef s x)) -- ^ The "true" register
                   , getCached :: Maybe (Defunc x) }       -- ^ The "most-recently known" value

{-|
Registers a recently created register into the `Ctx`. This must be provided with
the original value in the register, which is injected into the cache.

@since 1.0.0.0
-}
insertNewΣ :: ΣVar x                   -- ^ The name of the register.
           -> Maybe (Code (STRef s x)) -- ^ The runtime representation, if available.
           -> Defunc x                 -- ^ The initial value stored into the register.
           -> Ctx s o a                -- ^ The old context.
           -> Ctx s o a                -- ^ The new context.
insertNewΣ σ qref x ctx = ctx {σs = DMap.insert σ (Reg qref (Just x)) (σs ctx)}

{-|
Updated the "last-known value" of a register in the cache.

@since 1.0.0.0
-}
cacheΣ :: ΣVar x -> Defunc x -> Ctx s o a -> Ctx s o a
cacheΣ σ x ctx = case DMap.lookup σ (σs ctx) of
  Just (Reg ref _) -> ctx {σs = DMap.insert σ (Reg ref (Just x)) (σs ctx)}
  Nothing          -> throw (outOfScopeRegister σ)

{-|
Fetches a known to be concrete register (i.e. one that must be materialised
at runtime as an @STRef@). If this register does not exist, this throws an
@IntangibleRegister@ exception.

@since 1.0.0.0
-}
concreteΣ :: ΣVar x -> Ctx s o a -> Code (STRef s x)
concreteΣ σ = fromMaybe (throw (intangibleRegister σ)) . (getReg <=< DMap.lookup σ . σs)

{-|
Fetches the cached "last-known value" of a register. If the cache is unaware of
this value, a @RegisterFault@ exception is thrown.

@since 1.0.0.0
-}
cachedΣ :: ΣVar x -> Ctx s o a -> Defunc x
cachedΣ σ = fromMaybe (throw (registerFault σ)) . (getCached <=< (DMap.lookup σ . σs))

{-|
When a binding is generated, it needs to generate function arguments for each of the
free registers it requires. This is performed by this function, which also adds each
of these freshly bound registers into the `Ctx`. Has the effect of converting a
`Parsley.Internal.Backend.Machine.Types.Dynamics.DynSubroutine` into a
`Parsley.Internal.Backend.Machine.Types.Dynamics.DynFunc`.

@since 1.2.0.0
-}
-- This needs to return a DynFunc: it is fed back to shared territory
takeFreeRegisters :: Regs rs                              -- ^ The free registers demanded by the binding.
                  -> Ctx s o a                            -- ^ The old context.
                  -> (Ctx s o a -> DynSubroutine s o a x) -- ^ Given the new context, function that produces the subroutine.
                  -> DynFunc rs s o a x                   -- ^ The newly produced dynamic function.
takeFreeRegisters NoRegs ctx body = body ctx
takeFreeRegisters (FreeReg σ σs) ctx body = [||\(!reg) -> $$(takeFreeRegisters σs (insertScopedΣ σ [||reg||] ctx) body)||]

insertScopedΣ :: ΣVar x -> Code (STRef s x) -> Ctx s o a -> Ctx s o a
insertScopedΣ σ qref ctx = ctx {σs = DMap.insert σ (Reg (Just qref) Nothing) (σs ctx)}

-- This needs to take a StaFunc, it is fed back via `askSub`
provideFreeRegisters :: StaFunc rs s o a x -> Regs rs -> Ctx s o a -> StaSubroutine s o a x
provideFreeRegisters sub NoRegs _ = sub
provideFreeRegisters f (FreeReg σ σs) ctx = provideFreeRegisters (f (concreteΣ σ ctx)) σs ctx

-- Debug Level Tracking
{- $debug-doc
The debug combinator generates runtime diagnostic information. To make this more ergonomic,
it would be nice to indent nested debug info. To do this perfectly, a debug level that controls
indentation would need to be added to `Parsley.Internal.Backend.Machine.Types.State.Γ`. This
is problematic since, without a lot of work and complexity, it would introduce a runtime penalty
for not just debug parsers, but all other parsers too. As a compromise, the debug level is stored
purely statically in the `Ctx`: the consequence is that the indentation level resets across a
call-boundary.
-}
{-|
Increase the debug level for the forseeable static future.

@since 1.0.0.0
-}
debugUp :: Ctx s o a -> Ctx s o a
debugUp ctx = ctx {debugLevel = debugLevel ctx + 1}

{-|
Decrease the debug level for the forseeable static future.

@since 1.0.0.0
-}
debugDown :: Ctx s o a -> Ctx s o a
debugDown ctx = ctx {debugLevel = debugLevel ctx - 1}

-- Unique Offsets
{- $offset-doc
The `Parsley.Internal.Backend.Machine.Types.Offset.Offset` type refines dynamic offsets
with statically known properties such as input consumed and the source of the offset.
These sources are unique and must be generated statically, with "local" @Reader@ semantics.
This means that the `Ctx` lends itself nicely to managing the pool of fresh offset names.
-}
{-|
Advances the unique identifier stored in the `Ctx`. This is used to /skip/ a given name.

@since 1.4.0.0
-}
nextUnique :: Ctx s o a -> Ctx s o a
nextUnique ctx = ctx {offsetUniq = offsetUniq ctx + 1}

{-|
Generate a fresh name that is valid for the scope of the provided continuation.

@since 1.4.0.0
-}
freshUnique :: MonadReader (Ctx s o a) m => (Word -> m b) -> m b
freshUnique f =
  do unique <- asks offsetUniq
     local nextUnique (f unique)

-- Token Credit System (Piggy-banks)
{- $piggy-doc
Parsley has analysis in place to factor out length checks when it is statically known that
/n/ tokens must be consumed in order for a parser to succeed. Part of this analysis is the
cut analysis performed in the frontend, and then the coins analysis in the backend during
code generation. The meta instructions that reference "coins" interact with a system during
interpretation called the "Piggy-bank" system: this is all stored and accessed via the `Ctx`.

The system works like this:

* The `Ctx` stores two components: some coins and some piggybanks.
* When there are coins present in the `Ctx`, these can be "spent" to read a token without
  emitting a length check for it (the guarantee is that a length check was generated to
  get hold of those coins).
* When the coins run out a piggy-bank can be broken to get more coins: this should generate
  a length check for value of the coins in the bank
* When all the piggy-banks are exhausted, a length check must be generated for each
  token that is consumed.
* When adding coins into the system, if the `Ctx` is bankrupt, then the coins are added
  immediately along with a length check, otherwise a piggy-bank is added.

These are the basic principles behind this system, and it works effectively. There are some
extra edge-case operations that are described in their corresponding documentation. The
reason why piggy-banks are stored in the context and /not/ consumed immediately to add to
the coin count is so that length checks are delayed to the last possible moment: you should
have used all of your current allocation before asking for more!

In addition to this above system, Parsley stores previously read characters in a rewind queue:
this means that when backtracking is performed (i.e. when looking ahead) the characters can be
statically rewound and made available for free.
-}
{-|
Place a piggy-bank into the reserve, delaying the corresponding length check until it is
broken.

@since 1.5.0.0
-}
storePiggy :: Coins -> Ctx s o a -> Ctx s o a
storePiggy coins ctx = ctx {piggies = enqueue coins (piggies ctx)}

{-|
Break the next piggy-bank in the queue, and fill the coins in return.

__Note__: This should generate a length check when used!

@since 1.0.0.0
-}
breakPiggy :: Ctx s o a -> Ctx s o a
breakPiggy ctx = let (coins, piggies') = dequeue (piggies ctx) in ctx {coins = willConsume coins, piggies = piggies'}

{-|
Does the context have coins available?

@since 1.0.0.0
-}
hasCoin :: Ctx s o a -> Bool
hasCoin = canAfford 1

{-|
Is it the case that there are no coins /and/ no piggy-banks remaining?

@since 1.0.0.0
-}
isBankrupt :: Ctx s o a -> Bool
isBankrupt = liftM2 (&&) (not . hasCoin) (Queue.null . piggies)

{-|
Spend a single coin, used when a token is consumed.

@since 1.0.0.0
-}
spendCoin :: Ctx s o a -> Ctx s o a
spendCoin ctx = ctx {coins = coins ctx - 1}

{-|
Adds coins into the current supply.

@since 1.5.0.0
-}
giveCoins :: Coins -> Ctx s o a -> Ctx s o a
giveCoins c ctx = ctx {coins = coins ctx + willConsume c}

{-|
Adds coins into the current supply.

@since 1.5.0.0
-}
refundCoins :: Coins -> Ctx s o a -> Ctx s o a
refundCoins c ctx =
  giveCoins c ctx { knownChars = Queue.rewind (canReclaim c) (knownChars ctx) }

{-|
Removes all coins and piggy-banks, such that @isBankrupt == True@.

@since 1.0.0.0
-}
voidCoins :: Ctx s o a -> Ctx s o a
voidCoins ctx = ctx {coins = 0, piggies = Queue.empty, knownChars = Queue.empty}

{-|
Asks if the current coin total can afford a charge of \(n\) characters.

This is used by `Parsley.Internal.Backend.Instructions.DrainCoins`, which will have to emit a full length check
of size \(n\) if this quota cannot be reached.

@since 1.5.0.0
-}
canAfford :: Int -> Ctx s o a -> Bool
canAfford n = (>= n) . coins

{-|
Caches a known character and the next offset into the context so that it
can be retrieved later.

@since 1.5.0.0
-}
addChar :: Code Char -> Input o -> Ctx s o a -> Ctx s o a
addChar c o ctx = ctx { knownChars = enqueue (c, Item, o) (knownChars ctx) }

{-|
Reads a character from the context's retrieval queue if one exists.
If not, reads a character from another given source (and adds it to the
rewind buffer).

@since 2.1.0.0
-}
readChar :: Ctx s o a                                                             -- ^ The original context.
         -> CharPred                                                              -- ^ The predicate that this character will be tested against
         -> ((Code Char -> Input o -> Code b) -> Code b)                          -- ^ The fallback source of input.
         -> (Code Char -> CharPred -> CharPred -> Input o -> Ctx s o a -> Code b) -- ^ The continuation that needs the read characters and updated context.
         -> Code b
readChar ctx pred fallback k
  | reclaimable = unsafeReadChar ctx k
  | otherwise   = fallback $ \c o -> unsafeReadChar (addChar c o ctx) k
  where
    reclaimable = not (Queue.null (knownChars ctx))
    unsafeReadChar ctx k = let -- combine the old information with the new information, refining the predicate
                               -- This works for notFollowedBy at the /moment/ because the predicate does not cross the handler boundary...
                               -- Perhaps any that cross handler boundaries should be complemented if that ever happens.
                               -- FIXME: why does this poke and dequeue, why not just dequeue and then process?
                               updateChar (c, p, o) = (c, andPred p pred, o)
                               ((_, pOld, _), q) = poke updateChar (knownChars ctx)
                               ((c, p, o), q') = dequeue q
                           in k c pOld p o (ctx { knownChars = q' })

-- Exceptions
newtype MissingDependency = MissingDependency IMVar deriving anyclass Exception
newtype OutOfScopeRegister = OutOfScopeRegister IΣVar deriving anyclass Exception
newtype IntangibleRegister = IntangibleRegister IΣVar deriving anyclass Exception
newtype RegisterFault = RegisterFault IΣVar deriving anyclass Exception

missingDependency :: MVar x -> MissingDependency
missingDependency (MVar v) = MissingDependency v
outOfScopeRegister :: ΣVar x -> OutOfScopeRegister
outOfScopeRegister (ΣVar σ) = OutOfScopeRegister σ
intangibleRegister :: ΣVar x -> IntangibleRegister
intangibleRegister (ΣVar σ) = IntangibleRegister σ
registerFault :: ΣVar x -> RegisterFault
registerFault (ΣVar σ) = RegisterFault σ

instance Show MissingDependency where show (MissingDependency μ) = "Dependency μ" ++ show μ ++ " has not been compiled"
instance Show OutOfScopeRegister where show (OutOfScopeRegister σ) = "Register r" ++ show σ ++ " is out of scope"
instance Show IntangibleRegister where show (IntangibleRegister σ) = "Register r" ++ show σ ++ " is intangible in this scope"
instance Show RegisterFault where show (RegisterFault σ) = "Attempting to access register r" ++ show σ ++ " from cache has failed"
