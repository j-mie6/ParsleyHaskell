{-# LANGUAGE DeriveAnyClass,
             MagicHash,
             DerivingStrategies #-}
module Parsley.Internal.Backend.Machine.Types.Context (
    Ctx,
    QJoin(..),
    emptyCtx,
    insertSub, insertΦ, insertNewΣ, cacheΣ, concreteΣ, cachedΣ,
    takeFreeRegisters,
    askSub, askΦ,
    debugUp, debugDown, debugLevel,
    storePiggy, breakPiggy, spendCoin, giveCoins, voidCoins, coins,
    freshUnique, nextUnique,
    hasCoin, isBankrupt, liquidate
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
import Parsley.Internal.Backend.Machine.Types.Dynamics (DynFunc, DynSubRoutine)
import Parsley.Internal.Backend.Machine.Types.Statics  (QSubRoutine(..), StaFunc, StaSubRoutine, StaCont)
import Parsley.Internal.Common                         (Queue, enqueue, dequeue, Code)

import qualified Data.Dependent.Map as DMap             ((!), insert, empty, lookup)
import qualified Parsley.Internal.Common.Queue as Queue (empty, null, foldr)

newtype QJoin s o a x = QJoin { unwrapJoin :: StaCont s o a x }

data Reg s x = Reg { getReg    :: Maybe (Code (STRef s x))
                   , getCached :: Maybe (Defunc x) }

data Ctx s o a = Ctx { μs         :: DMap MVar (QSubRoutine s o a)
                     , φs         :: DMap ΦVar (QJoin s o a)
                     , σs         :: DMap ΣVar (Reg s)
                     , debugLevel :: Int
                     , coins      :: Int
                     , offsetUniq :: Word
                     , piggies    :: Queue Int }

emptyCtx :: DMap MVar (QSubRoutine s o a) -> Ctx s o a
emptyCtx μs = Ctx μs DMap.empty DMap.empty 0 0 0 Queue.empty

insertSub :: MVar x -> StaSubRoutine s o a x -> Ctx s o a -> Ctx s o a
insertSub μ q ctx = ctx {μs = DMap.insert μ (QSubRoutine q NoRegs) (μs ctx)}

insertΦ :: ΦVar x -> StaCont s o a x -> Ctx s o a -> Ctx s o a
insertΦ φ qjoin ctx = ctx {φs = DMap.insert φ (QJoin qjoin) (φs ctx)}

insertNewΣ :: ΣVar x -> Maybe (Code (STRef s x)) -> Defunc x -> Ctx s o a -> Ctx s o a
insertNewΣ σ qref x ctx = ctx {σs = DMap.insert σ (Reg qref (Just x)) (σs ctx)}

insertScopedΣ :: ΣVar x -> Code (STRef s x) -> Ctx s o a -> Ctx s o a
insertScopedΣ σ qref ctx = ctx {σs = DMap.insert σ (Reg (Just qref) Nothing) (σs ctx)}

cacheΣ :: ΣVar x -> Defunc x -> Ctx s o a -> Ctx s o a
cacheΣ σ x ctx = case DMap.lookup σ (σs ctx) of
  Just (Reg ref _) -> ctx {σs = DMap.insert σ (Reg ref (Just x)) (σs ctx)}
  Nothing          -> throw (outOfScopeRegister σ)

concreteΣ :: ΣVar x -> Ctx s o a -> Code (STRef s x)
concreteΣ σ = fromMaybe (throw (intangibleRegister σ)) . (getReg <=< DMap.lookup σ . σs)

cachedΣ :: ΣVar x -> Ctx s o a -> Defunc x
cachedΣ σ = fromMaybe (throw (registerFault σ)) . (getCached <=< (DMap.lookup σ . σs))

askSub :: MonadReader (Ctx s o a) m => MVar x -> m (StaSubRoutine s o a x)
askSub μ =
  do QSubRoutine sub rs <- askSubUnbound μ
     asks (provideFreeRegisters sub rs)

askSubUnbound :: MonadReader (Ctx s o a) m => MVar x -> m (QSubRoutine s o a x)
askSubUnbound μ = asks (fromMaybe (throw (missingDependency μ)) . DMap.lookup μ . μs)

-- This needs to return a DynFunc: it is fed back to shared territory
takeFreeRegisters :: Regs rs -> Ctx s o a -> (Ctx s o a -> DynSubRoutine s o a x) -> DynFunc rs s o a x
takeFreeRegisters NoRegs ctx body = body ctx
takeFreeRegisters (FreeReg σ σs) ctx body = [||\(!reg) -> $$(takeFreeRegisters σs (insertScopedΣ σ [||reg||] ctx) body)||]

-- This needs to take a StaFunc
provideFreeRegisters :: StaFunc rs s o a x -> Regs rs -> Ctx s o a -> StaSubRoutine s o a x
provideFreeRegisters sub NoRegs _ = sub
provideFreeRegisters f (FreeReg σ σs) ctx = provideFreeRegisters (f (concreteΣ σ ctx)) σs ctx

askΦ :: MonadReader (Ctx s o a) m => ΦVar x -> m (StaCont s o a x)
askΦ φ = asks (unwrapJoin . (DMap.! φ) . φs)

debugUp :: Ctx s o a -> Ctx s o a
debugUp ctx = ctx {debugLevel = debugLevel ctx + 1}

debugDown :: Ctx s o a -> Ctx s o a
debugDown ctx = ctx {debugLevel = debugLevel ctx - 1}

-- Piggy bank functions
storePiggy :: Int -> Ctx s o a -> Ctx s o a
storePiggy coins ctx = ctx {piggies = enqueue coins (piggies ctx)}

breakPiggy :: Ctx s o a -> Ctx s o a
breakPiggy ctx = let (coins, piggies') = dequeue (piggies ctx) in ctx {coins = coins, piggies = piggies'}

hasCoin :: Ctx s o a -> Bool
hasCoin = (> 0) . coins

isBankrupt :: Ctx s o a -> Bool
isBankrupt = liftM2 (&&) (not . hasCoin) (Queue.null . piggies)

spendCoin :: Ctx s o a -> Ctx s o a
spendCoin ctx = ctx {coins = coins ctx - 1}

nextUnique :: Ctx s o a -> Ctx s o a
nextUnique ctx = ctx {offsetUniq = offsetUniq ctx + 1}

freshUnique :: MonadReader (Ctx s o a) m => (Word -> m b) -> m b
freshUnique f =
  do unique <- asks offsetUniq
     local nextUnique (f unique)

giveCoins :: Int -> Ctx s o a -> Ctx s o a
giveCoins c ctx = ctx {coins = coins ctx + c}

voidCoins :: Ctx s o a -> Ctx s o a
voidCoins ctx = ctx {coins = 0, piggies = Queue.empty}

liquidate :: Ctx s o a -> Int
liquidate ctx = Queue.foldr (+) (coins ctx) (piggies ctx)

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