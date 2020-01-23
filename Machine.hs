{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             RankNTypes,
             BangPatterns,
             FlexibleInstances,
             MagicHash,
             UnboxedTuples,
             TemplateHaskell,
             PolyKinds,
             ScopedTypeVariables,
             FlexibleContexts,
             RecordWildCards,
             ConstraintKinds,
             CPP,
             ImplicitParams,
             TypeFamilies,
             TypeApplications,
             ViewPatterns,
             MultiWayIf #-}
module Machine where

import MachineOps
import MachineAST
import Input                      (PreparedInput(..), Rep, Unboxed, OffWith, UnpackedLazyByteString, Stream)
import Indexed                    (Free3, Void3, absurd, fold3)
import Utils                      (WQ(..), code, (>*<), Code)
import Defunc                     (Defunc, genDefunc2, genDefunc)
import Control.Monad              (forM, join, liftM2)
import Control.Monad.ST           (ST)
import Control.Monad.Reader       (ask, asks, local, Reader, runReader, MonadReader)
import Control.Exception          (Exception, throw)
import Data.STRef                 (STRef)
import Data.STRef.Unboxed         (STRefU)
import Queue                      (Queue, enqueue, dequeue)
import Data.Map.Strict            (Map)
import Data.Dependent.Map         (DMap, DSum(..))
import Data.GADT.Compare          (GCompare)
import Debug.Trace                (trace)
import System.Console.Pretty      (color, Color(Green, White, Red, Blue))
import Data.Text                  (Text)
import Data.Functor.Const         (Const(..), getConst)
import Language.Haskell.TH        (runQ, Q, newName, Name)
import Language.Haskell.TH.Syntax (unTypeQ, unsafeTExpCoerce, Exp(VarE, LetE), Dec(FunD), Clause(Clause), Body(NormalB))
import qualified Data.Map.Strict    as Map  ((!), insert, empty)
import qualified Data.Dependent.Map as DMap ((!), insert, empty, lookup, map, toList, traverseWithKey)
import qualified Queue                      (empty, size, null)

#define inputInstances(derivation) \
derivation(Int)                    \
derivation((OffWith [Char]))       \
derivation((OffWith Stream))       \
derivation(UnpackedLazyByteString) \
derivation(Text)

{- A key property of the pure semantics of the machine states that
    at the end of the execution of a machine, all the stacks shall
    be empty. This also holds true of any recursive machines, for
    obvious reasons. In the concrete machine, however, it is not
    entirely necessary for this invariant to be obeyed: indeed the
    stacks that would have otherwise been passed to the continuation
    in the pure semantics were available to the caller in the
    concrete machine. As such, continuations are only required to
    demand the values of X and o, with all other values closed over
    during suspension. -}
data Γ s o xs r a = Γ { xs    :: QList xs
                      , ret   :: Code (r -> Unboxed o -> ST s (Maybe a))
                      , o     :: Code o
                      , hs    :: [Code (Unboxed o -> ST s (Maybe a))] }

newtype QSTRef s x = QSTRef (Code (STRef s x))
newtype QORef s = QORef (Code (STRefU s Int))
data Ctx s o a = Ctx { μs         :: DMap MVar (QAbsExec s o a)
                     , φs         :: DMap ΦVar (QJoin s o a)
                     , σs         :: DMap ΣVar (QSTRef s)
                     , stcs       :: Map IΣVar (QORef s)
                     , constCount :: Int
                     , debugLevel :: Int
                     , coins      :: Int
                     , piggies    :: Queue Int }
emptyCtx :: Ctx s o a
emptyCtx = Ctx DMap.empty DMap.empty DMap.empty Map.empty 0 0 0 Queue.empty

insertM :: MVar x -> Code (AbsExec s o a x) -> Ctx s o a -> Ctx s o a
insertM μ q ctx = ctx {μs = DMap.insert μ (QAbsExec q) (μs ctx)}

insertΦ :: ΦVar x -> Code (x -> Unboxed o -> ST s (Maybe a)) -> Ctx s o a -> Ctx s o a
insertΦ φ qjoin ctx = ctx {φs = DMap.insert φ (QJoin qjoin) (φs ctx)}

insertΣ :: ΣVar x -> Code (STRef s x) -> Ctx s o a -> Ctx s o a
insertΣ σ qref ctx = ctx {σs = DMap.insert σ (QSTRef qref) (σs ctx)}

insertSTC :: ΣVar x -> Code (STRefU s Int) -> Ctx s o a -> Ctx s o a
insertSTC (ΣVar v) qref ctx = ctx {stcs = Map.insert v (QORef qref) (stcs ctx)}

addConstCount :: Int -> Ctx s o a -> Ctx s o a
addConstCount x ctx = ctx {constCount = constCount ctx + x}

skipBounds :: Ctx s o a -> Bool
skipBounds ctx = constCount ctx > 0

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
spendCoin ctx@(coins -> 0) = spendCoin (breakPiggy ctx)
spendCoin ctx              = ctx {coins = coins ctx - 1}

giveCoins :: Int -> Ctx s o a -> Ctx s o a
giveCoins c ctx = ctx {coins = coins ctx + c}

newtype MissingDependency = MissingDependency IMVar
newtype OutOfScopeRegister = OutOfScopeRegister IΣVar
type ExecMonad s o xs r a = Reader (Ctx s o a) (Γ s o xs r a -> Code (ST s (Maybe a)))
newtype Exec s o xs r a = Exec { unExec :: ExecMonad s o xs r a }
run :: Exec s o xs r a -> Γ s o xs r a -> Ctx s o a -> Code (ST s (Maybe a))
run (Exec m) γ ctx = runReader m ctx γ

type Ops o = (Handlers o, KOps o, FailureOps o, JoinBuilder o, FailureOps o, RecBuilder o)
type Handlers o = (HardForkHandler o, SoftForkHandler o, AttemptHandler o, ChainHandler o, LogHandler o)
class FailureOps o => HardForkHandler o where
  hardForkHandler :: (?ops :: InputOps s o) => (Γ s o xs ks a -> Code (ST s (Maybe a))) -> Γ s o xs ks a -> Code (H s o a) -> Code o -> Code (Unboxed o -> ST s (Maybe a))
class FailureOps o => SoftForkHandler o where
  softForkHandler :: (?ops :: InputOps s o) => (Γ s o xs ks a -> Code (ST s (Maybe a))) -> Γ s o xs ks a -> Code (H s o a) -> Code o -> Code (Unboxed o -> ST s (Maybe a))
class FailureOps o => AttemptHandler o where
  attemptHandler :: (?ops :: InputOps s o) => Code (H s o a) -> Code o -> Code (Unboxed o -> ST s (Maybe a))
class FailureOps o => ChainHandler o where
  chainHandler :: (?ops :: InputOps s o) => (Γ s o xs ks a -> Code (ST s (Maybe a))) -> Code (STRefU s Int)
               -> Γ s o xs ks a -> Code (H s o a) -> Code o -> Code (Unboxed o -> ST s (Maybe a))
class FailureOps o => LogHandler o where
  logHandler :: (?ops :: InputOps s o) => String -> Ctx s o a -> Γ s o xs ks a -> Code (H s o a) -> Code o -> Code (Unboxed o -> ST s (Maybe a))

exec :: Ops o => Code (PreparedInput (Rep o) s o (Unboxed o)) -> (Machine o a, DMap MVar (LetBinding o a)) -> Code (ST s (Maybe a))
exec input (Machine !m, ms) = trace ("EXECUTING: " ++ show m) [||
  do let !(PreparedInput next more same offset box unbox newCRef readCRef writeCRef shiftLeft shiftRight toInt) = $$input
     $$(let ?ops = InputOps [||more||] [||next||] [||same||] [||box||] [||unbox||] [||newCRef||] [||readCRef||] [||writeCRef||] [||shiftLeft||] [||shiftRight||] [||toInt||] 
        in scopeBindings ms
             nameLet
             QAbsExec
             (\(LetBinding k) names -> buildRec (emptyCtx {μs = names}) (readyExec k))
             (\names -> run (readyExec m) (Γ QNil [||noreturn||] [||offset||] []) (emptyCtx {μs = names})))
  ||]

missingDependency :: MVar x -> MissingDependency
missingDependency (MVar v) = MissingDependency v
dependencyOf :: MissingDependency -> MVar x
dependencyOf (MissingDependency v) = MVar v
outOfScopeRegister :: ΣVar x -> OutOfScopeRegister
outOfScopeRegister (ΣVar σ) = OutOfScopeRegister σ

nameLet :: LetBinding o a x -> String
nameLet _ = "rec"

scopeBindings :: GCompare key => DMap key named
                              -> (forall a. named a -> String)
                              -> (forall x. Code ((x -> y) -> z) -> q x)
                              -> (forall x. named x -> DMap key q -> Code ((x -> y) -> z))
                              -> (DMap key q -> Code a)
                              -> Code a
scopeBindings bindings nameOf wrap letBuilder scoped = unsafeTExpCoerce $
  do names <- makeNames bindings
     LetE <$> generateBindings names bindings <*> unTypeQ (scoped (package names))
  where
    package = DMap.map (wrap . unsafeTExpCoerce . return . VarE . getConst)
    makeNames = DMap.traverseWithKey (\_ v -> Const <$> newName (nameOf v))
    generateBindings names = traverse makeDecl . DMap.toList
      where
        makeDecl (k :=> v) = 
          do let Const name = names DMap.! k
             body <- unTypeQ (letBuilder v (package names))
             return (FunD name [Clause [] (NormalB body) []])

readyExec :: (?ops :: InputOps s o, Ops o) => Free3 (M o) Void3 xs r a -> Exec s o xs r a
readyExec = fold3 absurd (Exec . alg)
  where
    alg :: (?ops :: InputOps s o, Ops o) => M o (Exec s o) xs r a -> ExecMonad s o xs r a
    alg Halt                   = execHalt
    alg Ret                    = execRet
    alg (Call μ k)             = execCall μ k
    alg (Jump μ)               = execJump μ
    alg (Push x k)             = execPush x k
    alg (Pop k)                = execPop k
    alg (Lift2 f k)            = execLift2 f k
    alg (Sat p k)              = execSat p k
    alg Empt                   = execEmpt
    alg (Commit exit k)        = execCommit exit k
    alg (HardFork p q φ)       = execHardFork p q φ
    alg (SoftFork n p q φ)     = execSoftFork n p q φ
    alg (Join φ)               = execJoin φ
    alg (Attempt n k)          = execAttempt n k
    alg (Tell k)               = execTell k
    alg (Seek k)               = execSeek k
    alg (Case p q  φ)          = execCase p q  φ
    alg (Choices fs ks def  φ) = execChoices fs ks def  φ
    alg (ChainIter σ μ)        = execChainIter σ μ
    alg (ChainInit σ l μ k)    = execChainInit σ l μ k
    alg (Swap k)               = execSwap k
    alg (Make σ k)             = execMake σ k
    alg (Get σ k)              = execGet σ k
    alg (Put σ k)              = execPut σ k
    alg (LogEnter name k)      = execLogEnter name k
    alg (LogExit name k)       = execLogExit name k
    alg (MetaM m k)            = execMeta m k

execHalt :: ExecMonad s o '[a] r a
execHalt = return $! \γ -> [|| return $! Just $! $$(headQ (xs γ)) ||]

execRet :: (?ops :: InputOps s o, KOps o) => ExecMonad s o (x ': xs) x a
execRet = return $! resume

execCall :: (?ops :: InputOps s o, FailureOps o, KOps o) => MVar x -> Exec s o (x ': xs) r a -> ExecMonad s o xs r a
execCall μ (Exec k) =
  do !(QAbsExec m) <- askM μ
     mk <- k
     return $ \γ@Γ{..} -> runConcrete hs m (suspend mk γ) o

execJump :: (?ops :: InputOps s o, FailureOps o) => MVar x -> ExecMonad s o '[] x a
execJump μ =
  do !(QAbsExec m) <- askM μ
     return $! \γ@Γ{..} -> runConcrete hs m ret o

execPush :: WQ x -> Exec s o (x ': xs) r a -> ExecMonad s o xs r a
execPush x (Exec k) = fmap (\m γ -> m (γ {xs = QCons (_code x) (xs γ)})) k

execPop :: Exec s o xs r a -> ExecMonad s o (x ': xs) r a
execPop (Exec k) = fmap (\m γ -> m (γ {xs = tailQ (xs γ)})) k

execLift2 :: Defunc (x -> y -> z) -> Exec s o (z ': xs) r a -> ExecMonad s o (y ': x ': xs) r a
execLift2 f (Exec k) = fmap (\m γ -> m (γ {xs = let QCons y (QCons x xs') = xs γ in QCons (genDefunc2 f x y) xs'})) k

execSat :: (?ops :: InputOps s o, FailureOps o) => WQ (Char -> Bool) -> Exec s o (Char ': xs) r a -> ExecMonad s o xs r a
execSat p (Exec k) =
  do mk <- k
     skip <- asks skipBounds
     return $! emitLengthCheck (if skip then Nothing else Just 1) mk
  where
    readChar bad k γ@Γ{..} = sat o (_code p) (\o c -> k (γ {xs = QCons c xs, o = o})) bad
    newCode = do
      bankrupt <- asks isBankrupt
      hasChange <- asks hasCoin
      if | bankrupt -> emitLengthCheck (Just 1) <$> k
         | hasChange -> emitLengthCheck Nothing <$> local spendCoin k
         | otherwise -> local breakPiggy (emitLengthCheck . Just <$> asks coins <*> local spendCoin k)
    emitLengthCheck Nothing mk γ = readChar (raiseΓ γ) mk γ
    emitLengthCheck (Just n) mk γ = [|| let bad' = $$(raiseΓ γ) in $$(generateCheck n (readChar [||bad'||] mk γ) [||bad'||] γ)||]

execEmpt :: (?ops :: InputOps s o, FailureOps o) => ExecMonad s o xs r a
execEmpt = return $! raiseΓ

execCommit :: Bool -> Exec s o xs r a -> ExecMonad s o xs r a
execCommit exit (Exec k) = local (\ctx -> if exit then addConstCount (-1) ctx else ctx)
                                 (fmap (\m γ -> m (γ {hs = tail (hs γ)})) k)

execHardFork :: (?ops :: InputOps s o, HardForkHandler o, JoinBuilder o) => Exec s o xs r a -> Exec s o xs r a -> Maybe (ΦDecl (Exec s o) x xs r a) -> ExecMonad s o xs r a
execHardFork (Exec p) (Exec q) decl = setupJoinPoint decl id $
  do mp <- p
     mq <- q
     return $! \γ -> setupHandlerΓ γ (hardForkHandler mq γ) mp

#define deriveHardForkHandler(_o)         \
instance HardForkHandler _o where         \
{                                         \
  hardForkHandler mq γ h c = [||\(!o#) -> \
      if $$same $$c ($$box o#) then       \
        $$(mq (γ {o = [||$$box o#||]}))   \
      else $$h o#                         \
    ||]                                   \
};
inputInstances(deriveHardForkHandler)

execSoftFork :: (?ops :: InputOps s o, SoftForkHandler o, JoinBuilder o) => Maybe Int -> Exec s o xs r a -> Exec s o xs r a -> Maybe (ΦDecl (Exec s o) x xs r a) -> ExecMonad s o xs r a
execSoftFork constantInput (Exec p) (Exec q) decl = setupJoinPoint decl id $
  do mp <- inputSizeCheck constantInput p
     mq <- q
     return $! \γ -> setupHandlerΓ γ (softForkHandler mq γ) mp

#define deriveSoftForkHandler(_o) \
instance SoftForkHandler _o where { softForkHandler mq γ h c = [||\_ -> $$(mq (γ {o = c}))||] };
inputInstances(deriveSoftForkHandler)

execJoin :: (?ops :: InputOps s o) => ΦVar x -> ExecMonad s o (x ': xs) r a
execJoin φ =
  do QJoin k <- asks ((DMap.! φ) . φs)
     return $! \γ -> [|| $$k $$(headQ (xs γ)) ($$unbox $$(o γ)) ||]

execAttempt :: (?ops :: InputOps s o, AttemptHandler o) => Maybe Int -> Exec s o xs r a -> ExecMonad s o xs r a
execAttempt constantInput (Exec k) = do mk <- inputSizeCheck constantInput k; return $! \γ -> setupHandlerΓ γ attemptHandler mk

#define deriveAttemptHandler(_o) \
instance AttemptHandler _o where { attemptHandler h c = [||\_ -> $$h ($$unbox $$c)||] };
inputInstances(deriveAttemptHandler)

execTell :: Exec s o (o ': xs) r a -> ExecMonad s o xs r a
execTell (Exec k) = fmap (\mk γ -> mk (γ {xs = QCons (o γ) (xs γ)})) k

execSeek :: Exec s o xs r a -> ExecMonad s o (o ': xs) r a
execSeek (Exec k) = fmap (\mk γ -> let QCons o xs' = xs γ in mk (γ {xs = xs', o=o})) k

execCase :: (?ops :: InputOps s o, JoinBuilder o) => Exec s o (x ': xs) r a -> Exec s o (y ': xs) r a -> Maybe (ΦDecl (Exec s o) z xs r a) -> ExecMonad s o (Either x y ': xs) r a
execCase (Exec p) (Exec q) decl = setupJoinPoint decl tailQ $
  do mp <- p
     mq <- q
     return $! \γ ->
         let QCons e xs' = xs γ
         in [||case $$e of
           Left x -> $$(mp (γ {xs = QCons [||x||] xs'}))
           Right y  -> $$(mq (γ {xs = QCons [||y||] xs'}))||]

execChoices :: forall x y xs r a s o. (?ops :: InputOps s o, JoinBuilder o) => [WQ (x -> Bool)] -> [Exec s o xs r a] -> Exec s o xs r a -> Maybe (ΦDecl (Exec s o) y xs r a) -> ExecMonad s o (x ': xs) r a
execChoices fs ks (Exec def) decl = setupJoinPoint decl tailQ $
  do mdef <- def
     fmap (\mks γ -> let QCons x xs' = xs γ in go x fs mks mdef (γ {xs = xs'})) (forM ks (\(Exec k) -> k))
  where
    go :: Code x -> [WQ (x -> Bool)] -> [Γ s o xs r a -> Code (ST s (Maybe a))] -> (Γ s o xs r a -> Code (ST s (Maybe a))) -> Γ s o xs r a -> Code (ST s (Maybe a))
    go _ [] [] def γ = def γ
    go x (f:fs) (mk:mks) def γ = [||
        if $$(_code f) $$x then $$(mk γ)
        else $$(go x fs mks def γ)
      ||]

execChainIter :: (?ops :: InputOps s o, FailureOps o) => ΣVar x -> MVar x -> ExecMonad s o '[] x a
execChainIter σ μ =
  do !(QAbsExec l) <- askM μ
     !(QORef cref) <- askSTC σ
     return $! \γ@Γ{..} -> [||
       do $$writeCRef $$cref $$o
          $$(runConcrete hs l ret o)
       ||]

execChainInit :: (?ops :: InputOps s o, ChainHandler o, RecBuilder o) => ΣVar x -> Exec s o '[] x a -> MVar x -> Exec s o xs r a
              -> ExecMonad s o xs r a
execChainInit σ l μ (Exec k) =
  do mk <- k
     asks $! \ctx γ@(Γ xs ks o _) -> [||
        do cref <- $$newCRef $$o
           $$(setupHandlerΓ γ (chainHandler mk [||cref||] γ) (\γ' ->
              buildIter ctx μ σ l [||cref||] (hs γ') o))
      ||]

#define deriveChainHandler(_o)              \
instance ChainHandler _o where              \
{                                           \
  chainHandler mk cref γ h _ = [||\(!o#) -> \
      do                                    \
      {                                     \
        c <- $$readCRef $$cref;             \
        if $$same c ($$box o#) then         \
          $$(mk (γ {o = [|| $$box o# ||]})) \
        else $$h o#                         \
      } ||]                                 \
};
inputInstances(deriveChainHandler)

execSwap :: Exec s o (x ': y ': xs) r a -> ExecMonad s o (y ': x ': xs) r a
execSwap (Exec k) = fmap (\mk γ -> mk (γ {xs = let QCons y (QCons x xs') = xs γ in QCons x (QCons y xs')})) k

execMake :: ΣVar x -> Exec s o xs r a -> ExecMonad s o (x ': xs) r a
execMake σ k = asks $! \ctx γ -> let QCons x xs' = xs γ in [||
                  do ref <- newΣ $$x
                     $$(run k (γ {xs = xs'}) (insertΣ σ [||ref||] ctx))
                ||]

execGet :: ΣVar x -> Exec s o (x ': xs) r a -> ExecMonad s o xs r a
execGet σ (Exec k) =
  do !(QSTRef ref) <- askΣ σ
     mk <- k
     return $! \γ -> [||
       do x <- readΣ $$ref
          $$(mk (γ {xs = QCons [||x||] (xs γ)}))
       ||]

execPut :: ΣVar x -> Exec s o xs r a -> ExecMonad s o (x ': xs) r a
execPut σ (Exec k) =
  do !(QSTRef ref) <- askΣ σ
     mk <- k
     return $! \γ -> let QCons x xs' = xs γ in [||
       do writeΣ $$ref $$x
          $$(mk (γ {xs = xs'}))
       ||]

preludeString :: (?ops :: InputOps s o) => String -> Char -> Γ s o xs r a -> Ctx s o a -> String -> Code String
preludeString name dir γ ctx ends = [|| concat [$$prelude, $$eof, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    offset     = o γ
    indent     = replicate (debugLevel ctx * 2) ' '
    start      = [|| $$shiftLeft $$offset 5 ||]
    end        = [|| $$shiftRight $$offset 5 ||]
    inputTrace = [|| let replace '\n' = color Green "↙"
                         replace ' '  = color White "·"
                         replace c    = return c
                         go i
                           | $$same i $$end = []
                           | otherwise  = let (# c, i' #) = $$next i in replace c ++ go i'
                     in go $$start ||]
    eof        = [|| if $$more $$end then $$inputTrace else $$inputTrace ++ color Red "•" ||]
    prelude    = [|| concat [indent, dir : name, dir : " (", show ($$offToInt $$offset), "): "] ||]
    caretSpace = [|| replicate (length $$prelude + $$offToInt $$offset - $$offToInt $$start) ' ' ||]

execLogEnter :: (?ops :: InputOps s o, LogHandler o) => String -> Exec s o xs r a -> ExecMonad s o xs r a
execLogEnter name (Exec mk) =
  do k <- local debugUp mk
     asks $! \ctx γ ->
      (setupHandlerΓ γ (logHandler name ctx γ) (\γ' -> [|| trace $$(preludeString name '>' γ ctx "") $$(k γ')||]))

#define deriveLogHandler(_o)                                                                     \
instance LogHandler _o where                                                                     \
{                                                                                                \
  logHandler name ctx γ h _ = [||\(!o#) ->                                                       \
      trace $$(preludeString name '<' (γ {o = [||$$box o#||]}) ctx (color Red " Fail")) ($$h o#) \
    ||]                                                                                          \
};
inputInstances(deriveLogHandler)

execLogExit :: (?ops :: InputOps s o) => String -> Exec s o xs r a -> ExecMonad s o xs r a
execLogExit name (Exec mk) =
  do k <- local debugDown mk
     asks $! \ctx γ -> [|| trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(k γ) ||]

execMeta :: MetaM -> Exec s o xs r a -> ExecMonad s o xs r a
execMeta (AddCoins coins) (Exec k) =
  do coinsLeft <- asks hasCoin
     local (if coinsLeft then storePiggy coins else giveCoins coins) k
execMeta (RefundCoins coins) (Exec k) = local (giveCoins coins) k
--execMeta _ (Exec k) = k

setupHandlerΓ :: FailureOps o => Γ s o xs r a 
              -> (Code (H s o a) -> Code o -> Code (Unboxed o -> ST s (Maybe a)))
              -> (Γ s o xs r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))
setupHandlerΓ γ h k = setupHandler (hs γ) (o γ) h (\hs -> k (γ {hs = hs}))

raiseΓ :: forall s o xs r a. (?ops :: InputOps s o, FailureOps o) => Γ s o xs r a -> Code (ST s (Maybe a))
raiseΓ γ = [|| $$(raise @o (hs γ)) ($$unbox $$(o γ)) ||]

class RecBuilder o => JoinBuilder o where
  setupJoinPoint :: (?ops :: InputOps s o) => Maybe (ΦDecl (Exec s o) y ys r a)
                 -> (QList xs -> QList ys)
                 -> ExecMonad s o xs r a
                 -> ExecMonad s o xs r a

#define deriveJoinBuilder(_o)                                                               \
instance JoinBuilder _o where                                                               \
{                                                                                           \
  setupJoinPoint Nothing adapt mx = mx;                                                     \
  setupJoinPoint (Just (φ, (Exec k))) adapt mx =                                            \
    do                                                                                      \
    {                                                                                       \
      ctx <- ask;                                                                           \
      fmap (\mk γ -> [||                                                                    \
        let join x !o# = $$(mk (γ {xs = QCons [||x||] (adapt (xs γ)), o = [||$$box o#||]})) \
        in $$(run (Exec mx) γ (insertΦ φ [||join||] ctx))                                   \
      ||]) k                                                                                \
    }                                                                                       \
};
inputInstances(deriveJoinBuilder)

class RecBuilder o where
  buildIter :: (?ops :: InputOps s o) => Ctx s o a -> MVar x -> ΣVar x -> Exec s o '[] x a
            -> Code (STRefU s Int)
            -> [Code (H s o a)] -> Code o -> Code (ST s (Maybe a))
  buildRec  :: (?ops :: InputOps s o) => Ctx s o a
            -> Exec s o '[] r a
            -> Code ((r -> Unboxed o -> ST s (Maybe a)) -> Unboxed o 
                                                        -> (Unboxed o -> ST s (Maybe a)) 
                                                        -> ST s (Maybe a))

#define deriveRecBuilder(_o)                                                          \
instance RecBuilder _o where                                                          \
{                                                                                     \
  buildIter ctx μ σ l cref hs o = let bx = box in [||                                 \
      do                                                                              \
      {                                                                               \
        let {loop !o# =                                                               \
          $$(let ctx' = insertSTC σ cref (insertM μ [||\_ (!o#) _ -> loop o#||] ctx); \
                 γ = Γ QNil [||noreturn||] [||$$bx o#||] hs                           \
             in run l γ ctx')};                                                       \
        loop ($$unbox $$o)                                                            \
      } ||];                                                                          \
  buildRec ctx k = let bx = box in [|| \(!ret) (!o#) h ->                             \
    $$(run k (Γ QNil [||ret||] [||$$bx o#||] [[||h||]]) ctx) ||]                      \
};
inputInstances(deriveRecBuilder)

inputSizeCheck :: (?ops :: InputOps s o, FailureOps o) => Maybe Int -> ExecMonad s o xs r a -> ExecMonad s o xs r a
inputSizeCheck Nothing p = p
inputSizeCheck (Just n) p =
  do skip <- asks skipBounds
     mp <- local (addConstCount 1) p
     if skip then return $! mp
     else return $! \γ -> generateCheck n (mp γ) (raiseΓ γ) γ

generateCheck :: (?ops :: InputOps s o, FailureOps o) => Int -> Code (ST s (Maybe a)) -> Code (ST s (Maybe a)) -> Γ s o xs r a -> Code (ST s (Maybe a))
generateCheck 1 good bad γ = [|| if $$more $$(o γ) then $$good else $$bad ||]
generateCheck n good bad γ = [||
  if $$more ($$shiftRight $$(o γ) (n - 1)) then $$good
  else $$bad ||]

class KOps o where
  suspend :: (?ops :: InputOps s o) => (Γ s o (x ': xs) r a -> Code (ST s (Maybe a))) -> Γ s o xs r a -> Code (x -> Unboxed o -> ST s (Maybe a))
  resume :: (?ops :: InputOps s o) => Γ s o (x ': xs) x a -> Code (ST s (Maybe a))

#define deriveKOps(_o)                                                                         \
instance KOps _o where                                                                         \
{                                                                                              \
  suspend m γ = [|| \x (!o#) -> $$(m (γ {xs = QCons [||x||] (xs γ), o = [||$$box o#||]})) ||]; \
  resume γ = [|| $$(ret γ) $$(headQ (xs γ)) ($$unbox $$(o γ)) ||]                              \
};
inputInstances(deriveKOps)

askM :: MonadReader (Ctx s o a) m => MVar x -> m (QAbsExec s o a x)
askM μ = trace ("fetching " ++ show μ) $ do
  mexec <- asks (((DMap.lookup μ) . μs))
  case mexec of
    Just exec -> return $! exec
    Nothing   -> throw (missingDependency μ)

askΣ :: MonadReader (Ctx s o a) m => ΣVar x -> m (QSTRef s x)
askΣ σ = trace ("fetching " ++ show σ) $ do
  mref <- asks ((DMap.lookup σ) . σs)
  case mref of
    Just ref -> return $! ref
    Nothing  -> throw (outOfScopeRegister σ)

askΦ :: MonadReader (Ctx s o a) m => ΦVar x -> m (QJoin s o a x)
askΦ φ = trace ("fetching " ++ show φ) $ asks ((DMap.! φ) . φs)

askSTC :: MonadReader (Ctx s o a) m => ΣVar x -> m (QORef s)
askSTC (ΣVar v) = asks ((Map.! v) . stcs)

instance Show MissingDependency where show (MissingDependency (IMVar μ)) = "Dependency μ" ++ show μ ++ " has not been compiled"
instance Exception MissingDependency

instance Show OutOfScopeRegister where show (OutOfScopeRegister (IΣVar σ)) = "Register r" ++ show σ ++ " is out of scope"
instance Exception OutOfScopeRegister