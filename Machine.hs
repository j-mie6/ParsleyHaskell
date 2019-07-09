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
             KindSignatures,
             ScopedTypeVariables,
             GeneralizedNewtypeDeriving,
             FlexibleContexts,
             RecordWildCards,
             ConstraintKinds,
             CPP,
             ImplicitParams #-}
module Machine where

import MachineOps
import Input                 (PreparedInput(..), Rep, CRef, Unboxed, OffWith, UnpackedLazyByteString)
import Indexed               (IFunctor3, Free3(Op3), Void3, Const3(..), imap3, absurd, fold3)
import Utils                 (WQ(..), lift', (>*<), TExpQ)
import Data.Word             (Word64)
import Control.Monad         (forM)
import Control.Monad.ST      (ST)
import Control.Monad.Reader  (ask, asks, local, Reader, runReader, MonadReader)
import Data.STRef            (STRef)
import Data.Map.Strict       (Map)
import Data.Dependent.Map    (DMap)
import Data.GADT.Compare     (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))
import Safe.Coerce           (coerce)
import Debug.Trace           (trace)
import System.Console.Pretty (color, Color(Green, White, Red, Blue))
import Data.Text             (Text)
import Data.Void             (Void)
import qualified Data.Map.Strict    as Map  ((!), insert, empty)
import qualified Data.Dependent.Map as DMap ((!), insert, empty)

#define inputInstances(derivation) \
derivation(O)                      \
derivation((OffWith s))            \
derivation(UnpackedLazyByteString) \
derivation(Text)

newtype Machine o a = Machine { getMachine :: Free3 (M o) Void3 '[] Void a }
newtype ΣVar a = ΣVar IΣVar
newtype MVar a = MVar IMVar
newtype ΦVar a = ΦVar IΦVar
type ΦDecl k x xs r a = (ΦVar x, k (x ': xs) r a)
newtype LetBinding o a x = LetBinding (Free3 (M o) Void3 '[] x a)

instance Show (LetBinding o a x) where show (LetBinding m) = show m

data M o k xs r a where
  Halt      :: M o k '[a] Void a
  Ret       :: M o k '[x] x a
  Push      :: WQ x -> !(k (x ': xs) r a) -> M o k xs r a
  Pop       :: !(k xs r a) -> M o k (x ': xs) r a
  Lift2     :: !(WQ (x -> y -> z)) -> !(k (z ': xs) r a) -> M o k (y ': x ': xs) r a
  Sat       :: WQ (Char -> Bool) -> !(k (Char ': xs) r a) -> M o k xs r a
  Call      :: !(MVar x) -> !(k (x ': xs) r a) -> M o k xs r a
  Jump      :: !(MVar x) -> M o k xs x a
  Empt      :: M o k xs r a
  Commit    :: !Bool -> !(k xs r a) -> M o k xs r a
  HardFork  :: !(k xs r a) -> !(k xs r a) -> !(Maybe (ΦDecl k x xs r a)) -> M o k xs r a
  SoftFork  :: !(Maybe Int) -> !(k xs r a) -> !(k xs r a) -> !(Maybe (ΦDecl k x xs r a)) -> M o k xs r a
  Join      :: !(ΦVar x) -> M o k (x ': xs) r a
  Attempt   :: !(Maybe Int) -> !(k xs r a) -> M o k xs r a
  Tell      :: !(k (o ': xs) r a) -> M o k xs r a
  Seek      :: !(k xs r a) -> M o k (o ': xs) r a
  NegLook   :: !(k xs r a) -> !(k xs r a) -> M o k xs r a
  Case      :: !(k (x ': xs) r a) -> !(k (y ': xs) r a) -> M o k (Either x y ': xs) r a
  Choices   :: ![WQ (x -> Bool)] -> ![k xs r a] -> k xs r a -> M o k (x ': xs) r a
  ChainIter :: !(ΣVar x) -> !(MVar x) -> M o k ((x -> x) ': xs) x a
  ChainInit :: !(ΣVar x) -> !(k '[] x a) -> !(MVar x) -> !(k (x ': xs) r a) -> M o k (x ': xs) r a
  Swap      :: k (x ': y ': xs) r a -> M o k (y ': x ': xs) r a
  LogEnter  :: String -> !(k xs r a) -> M o k xs r a
  LogExit   :: String -> !(k xs r a) -> M o k xs r a

fmapInstr :: WQ (x -> y) -> Free3 (M o) f (y ': xs) r a -> Free3 (M o) f (x ': xs) r a
fmapInstr !f !m = Op3 (Push f (Op3 (Lift2 (lift' flip >*< lift' ($)) m)))

data Γ s o xs r a = Γ { xs    :: QList xs
                      , k     :: QK s o r a
                      , o     :: QO o
                      , hs    :: [QH s o a] }

newtype IMVar = IMVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype IΦVar = IΦVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype IΣVar = IΣVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype QSTRef s x = QSTRef (TExpQ (STRef s x))
newtype QCRef s x = QCRef (TExpQ (CRef s x))
data Ctx s o a = Ctx { μs         :: DMap MVar (QAbsExec s o a)
                     , φs         :: DMap ΦVar (QJoin (Rep o) s (Unboxed o) a)
                     , σs         :: DMap ΣVar (QSTRef s)
                     , stcs       :: Map IΣVar (QCRef s o)
                     , constCount :: Int
                     , debugLevel :: Int }

insertM :: MVar x -> TExpQ (AbsExec (Rep o) s (Unboxed o) a x) -> Ctx s o a -> Ctx s o a
insertM μ q ctx = ctx {μs = DMap.insert μ (QAbsExec q) (μs ctx)}

insertΦ :: ΦVar x -> TExpQ (x -> Unboxed o -> ST s (Maybe a)) -> Ctx s o a -> Ctx s o a
insertΦ φ qjoin ctx = ctx {φs = DMap.insert φ (QJoin qjoin) (φs ctx)}

insertΣ :: ΣVar x -> TExpQ (STRef s x) -> Ctx s o a -> Ctx s o a
insertΣ σ qref ctx = ctx {σs = DMap.insert σ (QSTRef qref) (σs ctx)}

insertSTC :: ΣVar x -> TExpQ (CRef s o) -> Ctx s o a -> Ctx s o a
insertSTC (ΣVar v) qref ctx = ctx {stcs = Map.insert v (QCRef qref) (stcs ctx)}

addConstCount :: Int -> Ctx s o a -> Ctx s o a
addConstCount x ctx = ctx {constCount = constCount ctx + x}

skipBounds :: Ctx s o a -> Bool
skipBounds ctx = constCount ctx > 0

debugUp :: Ctx s o a -> Ctx s o a
debugUp ctx = ctx {debugLevel = debugLevel ctx + 1}

debugDown :: Ctx s o a -> Ctx s o a
debugDown ctx = ctx {debugLevel = debugLevel ctx - 1}

newtype Exec s o xs r a = Exec (Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a)))
run :: Exec s o xs r a -> Γ s o xs r a -> Ctx s o a -> QST s (Maybe a)
run (Exec m) γ ctx = runReader m ctx γ

type Ops o = (Handlers o, KOps o, ConcreteExec o, JoinBuilder o, FailureOps o, RecBuilder o)
type Handlers o = (HardForkHandler o, SoftForkHandler o, AttemptHandler o, NegLookHandler o, ChainHandler o, LogHandler o)
class FailureOps o => HardForkHandler o where
  hardForkHandler :: (?ops :: InputOps s o) => (Γ s o xs ks a -> QST s (Maybe a)) -> Γ s o xs ks a -> TExpQ (H s o a -> Unboxed o -> Unboxed o -> ST s (Maybe a))
class FailureOps o => SoftForkHandler o where
  softForkHandler :: (?ops :: InputOps s o) => (Γ s o xs ks a -> QST s (Maybe a)) -> Γ s o xs ks a -> TExpQ (H s o a  -> Unboxed o -> Unboxed o -> ST s (Maybe a))
class FailureOps o => AttemptHandler o where
  attemptHandler :: (?ops :: InputOps s o) => TExpQ (H s o a  -> Unboxed o -> Unboxed o -> ST s (Maybe a))
class FailureOps o => NegLookHandler o where
  negLookHandler1 :: (?ops :: InputOps s o) => (Γ s o xs ks a -> QST s (Maybe a)) -> Γ s o xs ks a -> TExpQ (H s o a  -> Unboxed o -> Unboxed o -> ST s (Maybe a))
  negLookHandler2 :: (?ops :: InputOps s o) => TExpQ (H s o a  -> Unboxed o -> Unboxed o -> ST s (Maybe a))
class FailureOps o => ChainHandler o where
  chainHandler :: (?ops :: InputOps s o) => (Γ s o (x ': xs) ks a -> QST s (Maybe a)) -> TExpQ (STRef s x) -> TExpQ (CRef s o) 
               -> Γ s o (x ': xs) ks a -> TExpQ (H s o a  -> Unboxed o -> Unboxed o -> ST s (Maybe a))
class FailureOps o => LogHandler o where
  logHandler :: (?ops :: InputOps s o) => String -> Ctx s o a -> Γ s o xs ks a -> TExpQ (H s o a  -> Unboxed o -> Unboxed o -> ST s (Maybe a))

exec :: Ops o => TExpQ (PreparedInput (Rep o) s o (Unboxed o)) -> (Machine o a, DMap MVar (LetBinding o a), [IMVar]) -> QST s (Maybe a)
exec input (Machine !m, ms, topo) = trace ("EXECUTING: " ++ show m) [||
  do ks <- makeK
     let !(PreparedInput next more same offset box unbox newCRef readCRef writeCRef shiftLeft shiftRight toInt) = $$input
     $$(let ?ops = InputOps [||more||] [||next||] [||same||] [||box||] [||unbox||] [||newCRef||] [||readCRef||] [||writeCRef||] [||shiftLeft||] [||shiftRight||] [||toInt||]
        in readyCalls topo ms (readyExec m) 
             (Γ makeX [||ks||] [||offset||] makeH)
             (Ctx DMap.empty DMap.empty DMap.empty Map.empty 0 0))
  ||]

readyCalls :: (?ops :: InputOps s o, Ops o) => [IMVar] -> DMap MVar (LetBinding o a) -> Exec s o '[] Void a -> Γ s o '[] Void a -> Ctx s o a -> QST s (Maybe a)
readyCalls topo ms start γ = foldr readyFunc (run start γ) topo
  where
    readyFunc v rest (ctx :: Ctx s o a) = 
      let μ = MVar v
          LetBinding k = ms DMap.! μ
      in buildRec ctx μ (run (readyExec k)) rest

readyExec :: (?ops :: InputOps s o, Ops o) => Free3 (M o) Void3 xs r a -> Exec s o xs r a
readyExec = fold3 absurd (Exec . alg)
  where
    alg :: (?ops :: InputOps s o, Ops o) => M o (Exec s o) xs r a -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
    alg Halt                = execHalt
    alg Ret                 = execRet
    alg (Call μ k)          = execCall μ k
    alg (Jump μ)            = execJump μ
    alg (Push x k)          = execPush x k
    alg (Pop k)             = execPop k
    alg (Lift2 f k)         = execLift2 f k
    alg (Sat p k)           = execSat p k
    alg Empt                = execEmpt
    alg (Commit exit k)     = execCommit exit k
    alg (HardFork p q φ)    = execHardFork p q φ
    alg (SoftFork n p q φ)  = execSoftFork n p q φ
    alg (Join φ)            = execJoin φ
    alg (Attempt n k)       = execAttempt n k
    alg (Tell k)            = execTell k
    alg (NegLook m k)       = execNegLook m k
    alg (Seek k)            = execSeek k
    alg (Case p q)          = execCase p q
    alg (Choices fs ks def) = execChoices fs ks def
    alg (ChainIter σ μ)     = execChainIter σ μ
    alg (ChainInit σ l μ k) = execChainInit σ l μ k
    alg (Swap k)            = execSwap k
    alg (LogEnter name k)   = execLogEnter name k
    alg (LogExit name k)    = execLogExit name k

execHalt :: Reader (Ctx s o a) (Γ s o '[a] r a -> QST s (Maybe a))
execHalt = return $! \γ -> [|| return $! Just $! $$(peekX (xs γ)) ||]

execRet :: (?ops :: InputOps s o, KOps o) => Reader (Ctx s o a) (Γ s o (x ': xs) x a -> QST s (Maybe a))
execRet = return $! resume

execCall :: (?ops :: InputOps s o, ConcreteExec o, KOps o) => MVar x -> Exec s o (x ': xs) r a -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execCall μ (Exec k) =
  do !(QAbsExec m) <- askM μ
     mk <- k
     return $ \γ@Γ{..} -> [|| $$(runConcrete hs) $$m $$(suspend mk γ) $$o ||]

execJump :: (?ops :: InputOps s o, ConcreteExec o) => MVar x -> Reader (Ctx s o a) (Γ s o xs x a -> QST s (Maybe a))
execJump μ =
  do !(QAbsExec m) <- askM μ
     return $! \γ@Γ{..} -> [|| $$(runConcrete hs) $$m $$k $$o ||]

execPush :: WQ x -> Exec s o (x ': xs) r a -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execPush x (Exec k) = fmap (\m γ -> m (γ {xs = pushX (_code x) (xs γ)})) k

execPop :: Exec s o xs r a -> Reader (Ctx s o a) (Γ s o (x ': xs) r a -> QST s (Maybe a))
execPop (Exec k) = fmap (\m γ -> m (γ {xs = popX_ (xs γ)})) k

execLift2 :: WQ (x -> y -> z) -> Exec s o (z ': xs) r a -> Reader (Ctx s o a) (Γ s o (y ': x ': xs) r a -> QST s (Maybe a))
execLift2 f (Exec k) = fmap (\m γ -> m (γ {xs = let (# y, xs' #) = popX (xs γ); (# x, xs'' #) = popX xs' in pushX [||$$(_code f) $$x $$y||] xs''})) k

execSat :: (?ops :: InputOps s o, FailureOps o) => WQ (Char -> Bool) -> Exec s o (Char ': xs) r a -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execSat p (Exec k) =
  do mk <- k
     asks $! \ctx γ -> nextSafe (skipBounds ctx) (o γ) (_code p) (\o c -> mk (γ {xs = pushX c (xs γ), o = o})) (raiseΓ γ)

execEmpt :: (?ops :: InputOps s o, FailureOps o) => Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execEmpt = return $! raiseΓ

execCommit :: Bool -> Exec s o xs r a -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execCommit exit (Exec k) = local (\ctx -> if exit then addConstCount (-1) ctx else ctx)
                                 (fmap (\m γ -> m (γ {hs = popH_ (hs γ)})) k)

execHardFork :: (?ops :: InputOps s o, HardForkHandler o, JoinBuilder o) => Exec s o xs r a -> Exec s o xs r a -> Maybe (ΦDecl (Exec s o) x xs r a) -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execHardFork (Exec p) (Exec q) decl = setupJoinPoint decl $
  do mp <- p
     mq <- q
     return $! \γ -> setupHandlerΓ γ (hardForkHandler mq γ) mp

#define deriveHardForkHandler(_o)                                  \
instance HardForkHandler _o where                                  \
{                                                                  \
  hardForkHandler mq γ = [||\h (!o#) (!c#) ->                      \
      if $$same ($$box c#) ($$box o#) then                         \
        $$(mq (γ {o = [||$$box o#||], hs = pushH [||h||] (hs γ)})) \
      else h o#                                                    \
    ||]                                                            \
};
inputInstances(deriveHardForkHandler)

execSoftFork :: (?ops :: InputOps s o, SoftForkHandler o, JoinBuilder o) => Maybe Int -> Exec s o xs r a -> Exec s o xs r a -> Maybe (ΦDecl (Exec s o) x xs r a) -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execSoftFork constantInput (Exec p) (Exec q) decl = setupJoinPoint decl $
  do mp <- inputSizeCheck constantInput p
     mq <- q
     return $! \γ -> setupHandlerΓ γ (softForkHandler mq γ) mp

#define deriveSoftForkHandler(_o) \
instance SoftForkHandler _o where { softForkHandler mq γ = [||\h _ (!c#) -> $$(mq (γ {o = [||$$box c#||], hs = pushH [||h||] (hs γ)}))||] };
inputInstances(deriveSoftForkHandler)

execJoin :: (?ops :: InputOps s o) => ΦVar x -> Reader (Ctx s o a) (Γ s o (x ': xs) r a -> QST s (Maybe a))
execJoin φ = 
  do QJoin k <- asks ((DMap.! φ) . φs)
     return $! \γ -> [|| $$k $$(peekX (xs γ)) ($$unbox $$(o γ)) ||]

execAttempt :: (?ops :: InputOps s o, AttemptHandler o) => Maybe Int -> Exec s o xs r a -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execAttempt constantInput (Exec k) = do mk <- inputSizeCheck constantInput k; return $! \γ -> setupHandlerΓ γ attemptHandler mk

#define deriveAttemptHandler(_o) \
instance AttemptHandler _o where { attemptHandler = [||\h _ (!c#) -> h c#||] };
inputInstances(deriveAttemptHandler)

execTell :: Exec s o (o ': xs) r a -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execTell (Exec k) = fmap (\mk γ -> mk (γ {xs = pushX (o γ) (xs γ)})) k

execSeek :: Exec s o xs r a -> Reader (Ctx s o a) (Γ s o (o ': xs) r a -> QST s (Maybe a))
execSeek (Exec k) = fmap (\mk γ -> let (# o, xs' #) = popX (xs γ) in mk (γ {xs = xs', o=o})) k

execNegLook :: (?ops :: InputOps s o, NegLookHandler o) => Exec s o xs r a -> Exec s o xs r a -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execNegLook (Exec m) (Exec k) =
  do mm <- m
     mk <- k
     return $! \γ -> setupHandlerΓ γ negLookHandler2 (\γ' -> setupHandlerΓ γ' (negLookHandler1 mk γ) mm)

#define deriveNegLookHandler(_o)                                              \
instance NegLookHandler _o where                                              \
{                                                                             \
  negLookHandler1 mk γ = [||\_ _ (!c#) -> $$(mk (γ {o = [||$$box c#||]}))||]; \
  negLookHandler2 = [||\h _ (!c#) -> h c#||]                                  \
};
inputInstances(deriveNegLookHandler)

execCase :: Exec s o (x ': xs) r a -> Exec s o (y ': xs) r a -> Reader (Ctx s o a) (Γ s o (Either x y ': xs) r a -> QST s (Maybe a))
execCase (Exec p) (Exec q) =
  do mp <- p
     mq <- q
     return $! \γ ->
         let (# e, xs' #) = popX (xs γ)
         in [||case $$e of
           Left x -> $$(mp (γ {xs = pushX [||x||] xs'}))
           Right y  -> $$(mq (γ {xs = pushX [||y||] xs'}))||]

execChoices :: forall x xs r a s o. [WQ (x -> Bool)] -> [Exec s o xs r a] -> Exec s o xs r a -> Reader (Ctx s o a) (Γ s o (x ': xs) r a -> QST s (Maybe a))
execChoices fs ks (Exec def) = 
  do mdef <- def
     fmap (\mks γ -> let !(# x, xs' #) = popX (xs γ) in go x fs mks mdef (γ {xs = xs'})) (forM ks (\(Exec k) -> k))
  where
    go :: TExpQ x -> [WQ (x -> Bool)] -> [Γ s o xs r a -> QST s (Maybe a)] -> (Γ s o xs r a -> QST s (Maybe a)) -> Γ s o xs r a -> QST s (Maybe a)
    go _ [] [] def γ = def γ
    go x (f:fs) (mk:mks) def γ = [||
        if $$(_code f) $$x then $$(mk γ)
        else $$(go x fs mks def γ)
      ||]

execChainIter :: (?ops :: InputOps s o, ConcreteExec o) => ΣVar x -> MVar x -> Reader (Ctx s o a) (Γ s o ((x -> x) ': xs) x a -> QST s (Maybe a))
execChainIter σ μ =
  do !(QSTRef ref) <- askΣ σ
     !(QAbsExec l) <- askM μ
     !(QCRef cref) <- askSTC σ
     return $! \γ@Γ{..} -> [||
       do modifyΣ $$ref $$(peekX xs)
          $$writeCRef $$cref $$o
          $$(runConcrete hs) $$l $$k $$o
       ||]

execChainInit :: (?ops :: InputOps s o, ChainHandler o, RecBuilder o) => ΣVar x -> Exec s o '[] x a -> MVar x -> Exec s o (x ': xs) r a
              -> Reader (Ctx s o a) (Γ s o (x ': xs) r a -> QST s (Maybe a))
execChainInit σ l μ (Exec k) =
  do mk <- k
     asks $! \ctx γ@(Γ xs ks o _) -> [||
        do ref <- newΣ $$(peekX xs)
           cref <- $$newCRef $$o
           $$(setupHandlerΓ γ (chainHandler mk [||ref||] [||cref||] γ) (\γ' -> 
              buildIter ctx μ σ l [||ref||] [||cref||] (hs γ') o))
      ||]

#define deriveChainHandler(_o)                     \
instance ChainHandler _o where                     \
{                                                  \
  chainHandler mk ref cref γ = [||\h (!o#) _ ->    \
      do                                           \
      {                                            \
        c <- $$readCRef $$cref;                    \
        if $$same c ($$box o#) then                \
          do                                       \
          {                                        \
            y <- readΣ $$ref;                      \
            $$(mk (γ {xs = pokeX [||y||] (xs γ),   \
                      o = [|| $$box o# ||],        \
                      hs = pushH [||h||] (hs γ)})) \
          }                                        \
        else h o#                                  \
      } ||]                                        \
};
inputInstances(deriveChainHandler)

execSwap :: Exec s o (x ': y ': xs) r a -> Reader (Ctx s o a) (Γ s o (y ': x ': xs) r a -> QST s (Maybe a))
execSwap (Exec k) = fmap (\mk γ -> mk (γ {xs = let (# y, xs' #) = popX (xs γ); (# x, xs'' #) = popX xs' in pushX x (pushX y xs'')})) k

preludeString :: (?ops :: InputOps s o) => String -> Char -> Γ s o xs r a -> Ctx s o a -> String -> TExpQ String
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

execLogEnter :: (?ops :: InputOps s o, LogHandler o) => String -> Exec s o xs r a -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execLogEnter name k =
  do asks $! \ctx γ ->
      (setupHandlerΓ γ (logHandler name ctx γ) (\γ' -> [|| trace $$(preludeString name '>' γ ctx "") $$(run k γ' (debugUp ctx))||]))

#define deriveLogHandler(_o)                                                                   \
instance LogHandler _o where                                                                   \
{                                                                                              \
  logHandler name ctx γ = [||\h o# _ ->                                                        \
      trace $$(preludeString name '<' (γ {o = [||$$box o#||]}) ctx (color Red " Fail")) (h o#) \
    ||]                                                                                        \
};
inputInstances(deriveLogHandler)

execLogExit :: (?ops :: InputOps s o) => String -> Exec s o xs r a -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
execLogExit name k = asks $! \ctx γ -> [|| trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(run k γ (debugDown ctx)) ||]

setupHandlerΓ :: (?ops :: InputOps s o, FailureOps o) => Γ s o xs r a -> TExpQ (H s o a  -> Unboxed o -> Unboxed o -> ST s (Maybe a)) ->
                                                                               (Γ s o xs r a -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandlerΓ γ !h !k = setupHandler (hs γ) (o γ) h (\hs -> k (γ {hs = hs}))

class JoinBuilder o where
  setupJoinPoint :: (?ops :: InputOps s o) => Maybe (ΦDecl (Exec s o) x xs r a) 
                 -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a)) 
                 -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))

#define deriveJoinBuilder(_o)                                                      \
instance JoinBuilder _o where                                                      \
{                                                                                  \
  setupJoinPoint Nothing mx = mx;                                                  \
  setupJoinPoint (Just (φ, (Exec k))) mx =                                         \
    do                                                                             \
    {                                                                              \
      ctx <- ask;                                                                  \
      fmap (\mk γ -> [||                                                           \
        let join x !o# = $$(mk (γ {xs = pushX [||x||] (xs γ), o = [||$$box o#||]})) \
        in $$(run (Exec mx) γ (insertΦ φ [||join||] ctx))                          \
      ||]) k                                                                       \
    }                                                                              \
};
inputInstances(deriveJoinBuilder)

class RecBuilder o where
  buildIter :: (?ops :: InputOps s o) => Ctx s o a -> MVar x -> ΣVar x -> Exec s o '[] x a 
            -> TExpQ (STRef s x) -> TExpQ (CRef s o)
            -> [QH s o a]  -> QO o -> QST s (Maybe a)
  buildRec  :: (?ops :: InputOps s o) => Ctx s o a -> MVar x
            -> (Γ s o '[] x a -> Ctx s o a -> QST s (Maybe a)) 
            -> (Ctx s o a -> QST s (Maybe a)) 
            -> QST s (Maybe a)

#define deriveRecBuilder(_o)                                                                         \
instance RecBuilder _o where                                                                         \
{                                                                                                    \
  buildIter ctx μ σ l ref cref hs o = let bx = box in [||                                            \
      do                                                                                             \
      {                                                                                              \
        let {loop !o# =                                                                              \
          $$(run l (Γ QNil [||noreturn||] [||$$bx o#||] hs)                                          \
                   (insertSTC σ cref (insertM μ [||\_ (!o#) _ -> loop o#||] (insertΣ σ ref ctx))))}; \
        loop ($$unbox $$o)                                                                           \
      } ||];                                                                                         \
  buildRec ctx μ body k = let bx = box in [||                                                        \
      let recu !ks !o# h =                                                                           \
            $$(body (Γ QNil [||ks||] [||$$bx o#||] (pushH [||h||] makeH))                            \
                    (insertM μ [||recu||] ctx))                                                      \
      in $$(k (insertM μ [||recu||] ctx))                                                            \
    ||]                                                                                              \
};
inputInstances(deriveRecBuilder)

inputSizeCheck :: (?ops :: InputOps s o, FailureOps o) => Maybe Int -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a)) -> Reader (Ctx s o a) (Γ s o xs r a -> QST s (Maybe a))
inputSizeCheck Nothing p = p
inputSizeCheck (Just n) p =
  do skip <- asks skipBounds
     mp <- local (addConstCount 1) p
     if skip then return $! mp
     else if n == 1 then fmap (\ctx γ -> [|| if $$more $$(o γ) then $$(mp γ) else $$(raiseΓ γ) ||]) ask
     else fmap (\ctx γ -> [|| 
        if $$more ($$shiftRight $$(o γ) (n - 1)) then $$(mp γ)
        else $$(raiseΓ γ)
      ||]) ask

raiseΓ :: (?ops :: InputOps s o, FailureOps o) => Γ s o xs r a -> QST s (Maybe a)
raiseΓ γ = [|| $$(raise(hs γ)) $$(o γ) ||]

class KOps o where
  suspend :: (?ops :: InputOps s o) => (Γ s o (x ': xs) r a -> QST s (Maybe a)) -> Γ s o xs r a -> QK s o x a
  resume :: (?ops :: InputOps s o) => Γ s o (x ': xs) x a -> QST s (Maybe a)

#define deriveKOps(_o)                                                                         \
instance KOps _o where                                                                         \
{                                                                                              \
  suspend m γ = [|| \x (!o#) -> $$(m (γ {xs = pushX [||x||] (xs γ), o = [||$$box o#||]})) ||]; \
  resume γ = [|| $$(k γ) $$(peekX (xs γ)) ($$unbox $$(o γ)) ||]                                \
};
inputInstances(deriveKOps)

askM :: MonadReader (Ctx s o a) m => MVar x -> m (QAbsExec s o a x)
askM μ = {-trace ("fetching " ++ show μ) $ -}asks (((DMap.! μ) . μs))

askΣ :: MonadReader (Ctx s o a) m => ΣVar x -> m (QSTRef s x)
askΣ σ = {-trace ("fetching " ++ show σ) $ -}asks ((DMap.! σ) . σs)

askΦ :: MonadReader (Ctx s o a) m => ΦVar x -> m (QJoin (Rep o) s (Unboxed o) a x)
askΦ φ = {-trace ("fetching " ++ show φ) $ -}asks ((DMap.! φ) . φs)

askSTC :: MonadReader (Ctx s o a) m => ΣVar x -> m (QCRef s o)
askSTC (ΣVar v) = asks ((Map.! v) . stcs)

instance IFunctor3 (M o) where
  imap3 f Halt                           = Halt
  imap3 f Ret                            = Ret
  imap3 f (Push x k)                     = Push x (f k)
  imap3 f (Pop k)                        = Pop (f k)
  imap3 f (Lift2 g k)                    = Lift2 g (f k)
  imap3 f (Sat g k)                      = Sat g (f k)
  imap3 f (Call μ k)                     = Call μ (f k)
  imap3 f (Jump μ)                       = Jump μ
  imap3 f Empt                           = Empt
  imap3 f (Commit exit k)                = Commit exit (f k)
  imap3 f (SoftFork n p q (Just (φ, k))) = SoftFork n (f p) (f q) (Just (φ, f k))
  imap3 f (SoftFork n p q Nothing)       = SoftFork n (f p) (f q) Nothing
  imap3 f (HardFork p q (Just (φ, k)))   = HardFork (f p) (f q) (Just (φ, f k))
  imap3 f (HardFork p q Nothing)         = HardFork (f p) (f q) Nothing
  imap3 f (Join φ)                       = Join φ
  imap3 f (Attempt n k)                  = Attempt n (f k)
  imap3 f (Tell k)                       = Tell (f k)
  imap3 f (Seek k)                       = Seek (f k)
  imap3 f (NegLook m k)                  = NegLook (f m) (f k)
  imap3 f (Case p q)                     = Case (f p) (f q)
  imap3 f (Choices fs ks def)            = Choices fs (map f ks) (f def)
  imap3 f (ChainIter σ μ)                = ChainIter σ μ
  imap3 f (ChainInit σ l μ k)            = ChainInit σ (f l) μ (f k)
  imap3 f (Swap k)                       = Swap (f k)
  imap3 f (LogEnter name k)              = LogEnter name (f k)
  imap3 f (LogExit name k)               = LogExit name (f k)

instance Show (Machine o a) where show = show . getMachine
instance Show (Free3 (M o) f xs ks a) where
  show = getConst3 . fold3 (const (Const3 "")) (Const3 . alg) where
    alg :: forall i j k. M o (Const3 String) i j k -> String
    alg Halt                                  = "Halt"
    alg Ret                                   = "Ret"
    alg (Call μ k)                            = "(Call " ++ show μ ++ " " ++ getConst3 k ++ ")"
    alg (Jump μ)                              = "(Jump " ++ show μ ++ ")"
    alg (Push _ k)                            = "(Push x " ++ getConst3 k ++ ")"
    alg (Pop k)                               = "(Pop " ++ getConst3 k ++ ")"
    alg (Lift2 _ k)                           = "(Lift2 f " ++ getConst3 k ++ ")"
    alg (Sat _ k)                             = "(Sat f " ++ getConst3 k ++ ")"
    alg Empt                                  = "Empt"
    alg (Commit True k)                       = "(Commit end " ++ getConst3 k ++ ")"
    alg (Commit False k)                      = "(Commit " ++ getConst3 k ++ ")"
    alg (SoftFork Nothing p q Nothing)        = "(SoftFork " ++ getConst3 p ++ " " ++ getConst3 q ++ ")"
    alg (SoftFork (Just n) p q Nothing)       = "(SoftFork " ++ show n ++ " " ++ getConst3 p ++ " " ++ getConst3 q ++ ")"
    alg (SoftFork Nothing p q (Just (φ, k)))  = "(SoftFork " ++ getConst3 p ++ " " ++ getConst3 q ++ " (" ++ show φ ++ " = " ++ getConst3 k ++ "))"
    alg (SoftFork (Just n) p q (Just (φ, k))) = "(SoftFork " ++ show n ++ " " ++ getConst3 p ++ " " ++ getConst3 q ++ " (" ++ show φ ++ " = " ++ getConst3 k ++ "))"
    alg (HardFork p q Nothing)                = "(HardFork " ++ getConst3 p ++ " " ++ getConst3 q ++ ")"
    alg (HardFork p q (Just (φ, k)))          = "(HardFork " ++ getConst3 p ++ " " ++ getConst3 q ++ " (" ++ show φ ++ " = " ++ getConst3 k ++ "))"
    alg (Join φ)                              = show φ
    alg (Attempt Nothing k)                   = "(Try " ++ getConst3 k ++ ")"
    alg (Attempt (Just n) k)                  = "(Try " ++ show n ++ " " ++ getConst3 k ++ ")"
    alg (Tell k)                              = "(Tell " ++ getConst3 k ++ ")"
    alg (Seek k)                              = "(Seek " ++ getConst3 k ++ ")"
    alg (NegLook m k)                         = "(NegLook " ++ getConst3 m ++ " " ++ getConst3 k ++ ")"
    alg (Case m k)                            = "(Case " ++ getConst3 m ++ " " ++ getConst3 k ++ ")"
    alg (Choices _ ks def)                    = "(Choices " ++ show (map getConst3 ks) ++ " " ++ getConst3 def ++ ")"
    alg (ChainIter σ μ)                       = "(ChainIter " ++ show σ ++ " " ++ show μ ++ ")"
    alg (ChainInit σ m μ k)                   = "{ChainInit " ++ show σ ++ " " ++ show μ ++ " " ++ getConst3 m ++ " " ++ getConst3 k ++ "}"
    alg (Swap k)                              = "(Swap " ++ getConst3 k ++ ")"
    alg (LogEnter _ k)                        = getConst3 k
    alg (LogExit _ k)                         = getConst3 k

instance Show (MVar a) where show (MVar (IMVar μ)) = "μ" ++ show μ
instance Show (ΦVar a) where show (ΦVar (IΦVar φ)) = "φ" ++ show φ
instance Show (ΣVar a) where show (ΣVar (IΣVar σ)) = "σ" ++ show σ

instance GEq ΣVar where
  geq (ΣVar u) (ΣVar v)
    | u == v    = Just (coerce Refl)
    | otherwise = Nothing

instance GCompare ΣVar where
  gcompare (ΣVar u) (ΣVar v) = case compare u v of
    LT -> coerce GLT
    EQ -> coerce GEQ
    GT -> coerce GGT

instance GEq ΦVar where
  geq (ΦVar u) (ΦVar v)
    | u == v    = Just (coerce Refl)
    | otherwise = Nothing

instance GCompare ΦVar where
  gcompare (ΦVar u) (ΦVar v) = case compare u v of
    LT -> coerce GLT
    EQ -> coerce GEQ
    GT -> coerce GGT

instance GEq MVar where
  geq (MVar u) (MVar v)
    | u == v    = Just (coerce Refl)
    | otherwise = Nothing

instance GCompare MVar where
  gcompare (MVar u) (MVar v) = case compare u v of
    LT -> coerce GLT
    EQ -> coerce GEQ
    GT -> coerce GGT