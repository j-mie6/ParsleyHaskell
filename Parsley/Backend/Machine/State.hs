{-# LANGUAGE DataKinds,
             TypeOperators,
             GADTs,
             FlexibleContexts #-}
module Parsley.Backend.Machine.State where

import Parsley.Backend.Machine.Identifiers
import Parsley.Backend.Machine.InputRep (Unboxed)
import Parsley.Common.Vec         (Vec)
import Parsley.Common.Utils       (Code)
import Control.Monad.ST           (ST)
import Control.Monad.Reader       (asks, MonadReader, Reader, runReader)
import Control.Exception          (Exception, throw)
import Data.STRef                 (STRef)
import Parsley.Common.Queue       (Queue, enqueue, dequeue)
import Data.Dependent.Map         (DMap)
import Control.Monad              (liftM2)
import qualified Data.Dependent.Map as DMap    ((!), insert, empty, lookup, map, toList, traverseWithKey)
import qualified Parsley.Common.Queue as Queue (empty, size, null, foldr)

data OpStack xs where
  Empty :: OpStack '[]
  Op :: Code x -> OpStack xs -> OpStack (x ': xs)

type HandlerStack n s o a = Vec n (Code (Handler s o a))

type Handler s o a = Unboxed o -> ST s (Maybe a)
type Cont s o a x = x -> Unboxed o -> ST s (Maybe a)

type SubRoutine s o a x = Cont s o a x -> Unboxed o -> Handler s o a -> ST s (Maybe a)
newtype QSubRoutine s o a x = QSubRoutine { unwrapSub :: Code (SubRoutine s o a x) }
newtype QJoin s o a x = QJoin { unwrapJoin :: Code (Cont s o a x) }

type MachineMonad s o xs n r a = Reader (Ctx s o a) (Γ s o xs n r a -> Code (ST s (Maybe a)))
newtype Machine s o xs n r a = Machine { getMachine :: MachineMonad s o xs n r a }

run :: Machine s o xs n r a -> Γ s o xs n r a -> Ctx s o a -> Code (ST s (Maybe a))
run = flip . runReader . getMachine

data Γ s o xs n r a = Γ { operands :: OpStack xs
                        , retCont  :: Code (Cont s o a r)
                        , input    :: Code o
                        , handlers :: HandlerStack n s o a }

type Reg = STRef
newtype QReg s x = QReg { unwrapReg :: Code (Reg s x) }
data Ctx s o a = Ctx { μs         :: DMap MVar (QSubRoutine s o a)
                     , φs         :: DMap ΦVar (QJoin s o a)
                     , σs         :: DMap ΣVar (QReg s)
                     , debugLevel :: Int
                     , coins      :: Int
                     , piggies    :: Queue Int }

emptyCtx :: Ctx s o a
emptyCtx = Ctx DMap.empty DMap.empty DMap.empty 0 0 Queue.empty

insertSub :: MVar x -> Code (SubRoutine s o a x) -> Ctx s o a -> Ctx s o a
insertSub μ q ctx = ctx {μs = DMap.insert μ (QSubRoutine q) (μs ctx)}

insertΦ :: ΦVar x -> Code (Cont s o a x) -> Ctx s o a -> Ctx s o a
insertΦ φ qjoin ctx = ctx {φs = DMap.insert φ (QJoin qjoin) (φs ctx)}

insertΣ :: ΣVar x -> Code (Reg s x) -> Ctx s o a -> Ctx s o a
insertΣ σ qref ctx = ctx {σs = DMap.insert σ (QReg qref) (σs ctx)}

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

giveCoins :: Int -> Ctx s o a -> Ctx s o a
giveCoins c ctx = ctx {coins = coins ctx + c}

voidCoins :: Ctx s o a -> Ctx s o a
voidCoins ctx = ctx {coins = 0, piggies = Queue.empty}

liquidate :: Ctx s o a -> Int
liquidate ctx = Queue.foldr (+) (coins ctx) (piggies ctx)

newtype MissingDependency = MissingDependency IMVar
newtype OutOfScopeRegister = OutOfScopeRegister IΣVar

missingDependency :: MVar x -> MissingDependency
missingDependency (MVar v) = MissingDependency v
dependencyOf :: MissingDependency -> MVar x
dependencyOf (MissingDependency v) = MVar v
outOfScopeRegister :: ΣVar x -> OutOfScopeRegister
outOfScopeRegister (ΣVar σ) = OutOfScopeRegister σ

askSub :: MonadReader (Ctx s o a) m => MVar x -> m (Code (SubRoutine s o a x))
askSub μ = do
  sub <- asks (fmap unwrapSub . DMap.lookup μ . μs)
  maybe (throw (missingDependency μ)) return sub

askΣ :: MonadReader (Ctx s o a) m => ΣVar x -> m (Code (Reg s x))
askΣ σ = do
  reg <- asks (fmap unwrapReg . DMap.lookup σ . σs)
  maybe (throw (outOfScopeRegister σ)) return reg

askΦ :: MonadReader (Ctx s o a) m => ΦVar x -> m (Code (Cont s o a x))
askΦ φ = asks (unwrapJoin . (DMap.! φ) . φs)

instance Show MissingDependency where show (MissingDependency μ) = "Dependency μ" ++ show μ ++ " has not been compiled"
instance Exception MissingDependency

instance Show OutOfScopeRegister where show (OutOfScopeRegister σ) = "Register r" ++ show σ ++ " is out of scope"
instance Exception OutOfScopeRegister