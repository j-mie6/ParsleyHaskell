{-# LANGUAGE DeriveAnyClass,
             ExistentialQuantification,
             TypeFamilies #-}
module Parsley.Backend.Machine.State (
    HandlerStack, Handler, Cont, SubRoutine, MachineMonad, Func,
    Γ(..), Ctx, OpStack(..),
    QSubRoutine(..), QJoin(..), Machine(..),
    run,
    emptyCtx,
    insertSub, insertΦ, insertNewΣ, insertScopedΣ, cacheΣ, concreteΣ, cachedΣ,
    askSub, askΦ,
    debugUp, debugDown, debugLevel,
    storePiggy, breakPiggy, spendCoin, giveCoins, voidCoins, coins,
    hasCoin, isBankrupt, liquidate
  ) where

import Control.Exception                   (Exception, throw)
import Control.Monad                       (liftM2)
import Control.Monad.Reader                (asks, MonadReader, Reader, runReader)
import Control.Monad.ST                    (ST)
import Data.STRef                          (STRef)
import Data.Dependent.Map                  (DMap)
import Data.Kind                           (Type)
import Data.Maybe                          (fromMaybe)
import Parsley.Backend.Machine.Identifiers (MVar(..), ΣVar(..), ΦVar, IMVar, IΣVar)
import Parsley.Backend.Machine.InputRep    (Unboxed)
import Parsley.Backend.Machine.LetBindings (Regs(..))
import Parsley.Common                      (Queue, enqueue, dequeue, Code, Vec)

import qualified Data.Dependent.Map as DMap    ((!), insert, empty, lookup)
import qualified Parsley.Common.Queue as Queue (empty, null, foldr)

type HandlerStack n s o r = Vec n (Code (Handler s o r))
type Handler s o r = Unboxed o -> ST s r
type Cont s o r x = x -> Unboxed o -> ST s r
type SubRoutine s o r x = Cont s o r x -> Unboxed o -> Handler s o r -> ST s r
type MachineMonad s o xs n x r = Reader (Ctx s o r) (Γ s o xs n x r -> Code (ST s r))

type family Func (rs :: [Type]) s o a x where
  Func '[] s o a x      = SubRoutine s o a x
  Func (r : rs) s o a x = STRef s r -> Func rs s o a x

data QSubRoutine s o r x = forall rs. QSubRoutine  (Code (Func rs s o r x)) (Regs rs)
newtype QJoin s o r x = QJoin { unwrapJoin :: Code (Cont s o r x) }
newtype Machine s o xs n r a = Machine { getMachine :: MachineMonad s o xs n r a }

run :: Machine s o xs n x r -> Γ s o xs n x r -> Ctx s o r -> Code (ST s r)
run = flip . runReader . getMachine

data OpStack xs where
  Empty :: OpStack '[]
  Op :: Code x -> OpStack xs -> OpStack (x ': xs)

data Reg s x = Reg { getReg    :: Maybe (Code (STRef s x))
                   , getCached :: Maybe (Code x) }

data Γ s o xs n x r = Γ { operands :: OpStack xs
                        , retCont  :: Code (Cont s o r x)
                        , input    :: Code o
                        , handlers :: HandlerStack n s o r }

data Ctx s o r = Ctx { μs         :: DMap MVar (QSubRoutine s o r)
                     , φs         :: DMap ΦVar (QJoin s o r)
                     , σs         :: DMap ΣVar (Reg s)
                     , debugLevel :: Int
                     , coins      :: Int
                     , piggies    :: Queue Int }

emptyCtx :: DMap MVar (QSubRoutine s o r) -> Ctx s o r
emptyCtx μs = Ctx μs DMap.empty DMap.empty 0 0 Queue.empty

insertSub :: MVar x -> Code (SubRoutine s o r x) -> Ctx s o r -> Ctx s o r
insertSub μ q ctx = ctx {μs = DMap.insert μ (QSubRoutine q NoRegs) (μs ctx)}

insertΦ :: ΦVar x -> Code (Cont s o r x) -> Ctx s o r -> Ctx s o r
insertΦ φ qjoin ctx = ctx {φs = DMap.insert φ (QJoin qjoin) (φs ctx)}

insertNewΣ :: ΣVar x -> Maybe (Code (STRef s x)) -> Code x -> Ctx s o r -> Ctx s o r
insertNewΣ σ qref qx ctx = ctx {σs = DMap.insert σ (Reg qref (Just qx)) (σs ctx)}

insertScopedΣ :: ΣVar x -> Code (STRef s x) -> Ctx s o r -> Ctx s o r
insertScopedΣ σ qref ctx = ctx {σs = DMap.insert σ (Reg (Just qref) Nothing) (σs ctx)}

cacheΣ :: ΣVar x -> Code x -> Ctx s o r -> Ctx s o r
cacheΣ σ qx ctx = case DMap.lookup σ (σs ctx) of
  Just (Reg ref _) -> ctx {σs = DMap.insert σ (Reg ref (Just qx)) (σs ctx)}
  Nothing          -> throw (outOfScopeRegister σ)

concreteΣ :: ΣVar x -> Ctx s o r -> Code (STRef s x)
concreteΣ σ = fromMaybe (throw (intangibleRegister σ)) . (>>= getReg) . DMap.lookup σ . σs

cachedΣ :: ΣVar x -> Ctx s o r -> Code x
cachedΣ σ = fromMaybe (throw (registerFault σ)) . (>>= getCached) . DMap.lookup σ . σs

askSub :: MonadReader (Ctx s o r) m => MVar x -> m (Code (SubRoutine s o r x))
askSub μ =
  do QSubRoutine sub rs <- askSubUnbound μ
     asks (provideFreeRegisters sub rs)

askSubUnbound :: MonadReader (Ctx s o r) m => MVar x -> m (QSubRoutine s o r x)
askSubUnbound μ = asks (fromMaybe (throw (missingDependency μ)) . DMap.lookup μ . μs)

provideFreeRegisters :: Code (Func rs s o r x) -> Regs rs -> Ctx s o r -> Code (SubRoutine s o r x)
provideFreeRegisters sub NoRegs _ = sub
provideFreeRegisters f (FreeReg σ σs) ctx = provideFreeRegisters [||$$f $$(concreteΣ σ ctx)||] σs ctx

askΦ :: MonadReader (Ctx s o r) m => ΦVar x -> m (Code (Cont s o r x))
askΦ φ = asks (unwrapJoin . (DMap.! φ) . φs)

debugUp :: Ctx s o r -> Ctx s o r
debugUp ctx = ctx {debugLevel = debugLevel ctx + 1}

debugDown :: Ctx s o r -> Ctx s o r
debugDown ctx = ctx {debugLevel = debugLevel ctx - 1}

-- Piggy bank functions
storePiggy :: Int -> Ctx s o r -> Ctx s o r
storePiggy coins ctx = ctx {piggies = enqueue coins (piggies ctx)}

breakPiggy :: Ctx s o r -> Ctx s o r
breakPiggy ctx = let (coins, piggies') = dequeue (piggies ctx) in ctx {coins = coins, piggies = piggies'}

hasCoin :: Ctx s o r -> Bool
hasCoin = (> 0) . coins

isBankrupt :: Ctx s o r -> Bool
isBankrupt = liftM2 (&&) (not . hasCoin) (Queue.null . piggies)

spendCoin :: Ctx s o r -> Ctx s o r
spendCoin ctx = ctx {coins = coins ctx - 1}

giveCoins :: Int -> Ctx s o r -> Ctx s o r
giveCoins c ctx = ctx {coins = coins ctx + c}

voidCoins :: Ctx s o r -> Ctx s o r
voidCoins ctx = ctx {coins = 0, piggies = Queue.empty}

liquidate :: Ctx s o r -> Int
liquidate ctx = Queue.foldr (+) (coins ctx) (piggies ctx)

newtype MissingDependency = MissingDependency IMVar deriving Exception
newtype OutOfScopeRegister = OutOfScopeRegister IΣVar deriving Exception
newtype IntangibleRegister = IntangibleRegister IΣVar deriving Exception
newtype RegisterFault = RegisterFault IΣVar deriving Exception

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