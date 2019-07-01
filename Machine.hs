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
             ConstraintKinds #-}
module Machine where

import MachineOps
import Input                      (PreparedInput(..), Rep, CRef, Unboxed)
import Indexed                    (IFunctor3, Free3(Op3), Void3, Const3(..), imap3, absurd, fold3)
import Utils                      (WQ(..), lift', (>*<), TExpQ)
import Data.Word                  (Word64)
import Control.Monad              (forM)
import Control.Monad.ST           (ST)
import Control.Monad.Reader       (ask, asks, local, Reader, runReader, MonadReader)
import Data.STRef                 (STRef)
import Data.Map.Strict            (Map)
import Data.Dependent.Map         (DMap)
import Data.GADT.Compare          (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))
import Safe.Coerce                (coerce)
import Debug.Trace                (trace)
import System.Console.Pretty      (color, Color(Green, White, Red, Blue))
import qualified Data.Map.Strict    as Map  ((!), insert, empty)
import qualified Data.Dependent.Map as DMap ((!), insert, empty)

newtype Machine o a = Machine { getMachine :: Free3 (M o) Void3 '[] '[] a }
newtype ΣVar a = ΣVar IΣVar
newtype MVar a = MVar IMVar
newtype ΦVar a = ΦVar IΦVar
type ΦDecl k x xs ks a = (ΦVar x, k (x ': xs) ks a)
newtype LetBinding o a x = LetBinding (forall xs. Free3 (M o) Void3 xs (x ': xs) a)
letBind :: Free3 (M o) Void3 xs (x ': xs) a -> LetBinding o a x
letBind m = LetBinding (coerce m)

instance Show (LetBinding o a x) where show (LetBinding m) = show m

data M o k xs ks a where
  Halt      :: M o k '[a] '[] a
  Ret       :: M o k (x ': xs) (x ': xs) a
  Push      :: WQ x -> !(k (x ': xs) ks a) -> M o k xs ks a
  Pop       :: !(k xs ks a) -> M o k (x ': xs) ks a
  Lift2     :: !(WQ (x -> y -> z)) -> !(k (z ': xs) ks a) -> M o k (y ': x ': xs) ks a
  Sat       :: WQ (Char -> Bool) -> !(k (Char ': xs) ks a) -> M o k xs ks a
  Call      :: !(MVar x) -> !(k (x ': xs) ks a) -> M o k xs ks a
  Jump      :: !(MVar x) -> M o k xs (x ': xs) a
  Empt      :: M o k xs ks a
  Commit    :: !Bool -> !(k xs ks a) -> M o k xs ks a
  HardFork  :: !(k xs ks a) -> !(k xs ks a) -> !(Maybe (ΦDecl k x xs ks a)) -> M o k xs ks a
  SoftFork  :: !(Maybe Int) -> !(k xs ks a) -> !(k xs ks a) -> !(Maybe (ΦDecl k x xs ks a)) -> M o k xs ks a
  Join      :: !(ΦVar x) -> M o k (x ': xs) ks a
  Attempt   :: !(Maybe Int) -> !(k xs ks a) -> M o k xs ks a
  Tell      :: !(k (O ': xs) ks a) -> M o k xs ks a
  Seek      :: !(k xs ks a) -> M o k (O ': xs) ks a
  NegLook   :: !(k xs ks a) -> !(k xs ks a) -> M o k xs ks a
  Case      :: !(k (x ': xs) ks a) -> !(k (y ': xs) ks a) -> M o k (Either x y ': xs) ks a
  Choices   :: ![WQ (x -> Bool)] -> ![k xs ks a] -> k xs ks a -> M o k (x ': xs) ks a
  ChainIter :: !(ΣVar x) -> !(MVar x) -> M o k ((x -> x) ': xs) (x ': xs) a
  ChainInit :: !(ΣVar x) -> !(k xs (x ': xs) a) -> !(MVar x) -> !(k (x ': xs) ks a) -> M o k (x ': xs) ks a
  Swap      :: k (x ': y ': xs) ks a -> M o k (y ': x ': xs) ks a
  LogEnter  :: String -> !(k xs ks a) -> M o k xs ks a
  LogExit   :: String -> !(k xs ks a) -> M o k xs ks a

fmapInstr :: WQ (x -> y) -> Free3 (M o) f (y ': xs) ks a -> Free3 (M o) f (x ': xs) ks a
fmapInstr !f !m = Op3 (Push f (Op3 (Lift2 (lift' flip >*< lift' ($)) m)))

data Γ s o xs ks a = Γ { xs    :: QX xs
                       , k     :: QK (Rep o) s (Unboxed o) ks a
                       , o     :: QO o
                       , hs    :: QH s o a }

newtype AbsExec s o a x = AbsExec { runConcrete :: forall xs. X xs -> K (Rep o) s (Unboxed o) (x ': xs) a -> O# -> H s o a -> ST s (Maybe a) }
newtype QAbsExec s o a x = QAbsExec (TExpQ (AbsExec s o a x))
newtype QJoin s o a x = QJoin (TExpQ (x -> O# -> ST s (Maybe a)))
newtype IMVar = IMVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype IΦVar = IΦVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype IΣVar = IΣVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype QSTRef s x = QSTRef (TExpQ (STRef s x))
newtype QCRef s x = QCRef (TExpQ (CRef s x))
data Ctx s o a = Ctx { μs         :: DMap MVar (QAbsExec s o a)
                     , φs         :: DMap ΦVar (QJoin s o a)
                     , σs         :: DMap ΣVar (QSTRef s)
                     , stcs       :: Map IΣVar (QCRef s O)
                     , ops        :: {-# UNPACK #-} !(InputOps s o)
                     , constCount :: Int
                     , debugLevel :: Int }

more      :: Ctx s o a -> TExpQ (O -> Bool)
more      = _more      . ops
next      :: Ctx s o a -> TExpQ (O -> (# Char, O #))
next      = _next      . ops
same      :: Ctx s o a -> TExpQ (O -> O -> Bool)
same      = _same      . ops
unbox     :: Ctx s o a -> TExpQ (O -> O#)
unbox     = _unbox     . ops
box       :: Ctx s o a -> TExpQ (O# -> O)
box       = _box       . ops
newCRef   :: Ctx s o a -> TExpQ (O -> ST s (CRef s O))
newCRef   = _newCRef   . ops
readCRef  :: Ctx s o a -> TExpQ (CRef s O -> ST s O) 
readCRef  = _readCRef  . ops
writeCRef :: Ctx s o a -> TExpQ (CRef s O -> O -> ST s ())
writeCRef = _writeCRef . ops

insertM :: MVar x -> TExpQ (AbsExec s o a x) -> Ctx s o a -> Ctx s o a
insertM μ q ctx = ctx {μs = DMap.insert μ (QAbsExec q) (μs ctx)}

insertΦ :: ΦVar x -> TExpQ (x -> O# -> ST s (Maybe a)) -> Ctx s o a -> Ctx s o a
insertΦ φ qjoin ctx = ctx {φs = DMap.insert φ (QJoin qjoin) (φs ctx)}

insertΣ :: ΣVar x -> TExpQ (STRef s x) -> Ctx s o a -> Ctx s o a
insertΣ σ qref ctx = ctx {σs = DMap.insert σ (QSTRef qref) (σs ctx)}

insertSTC :: ΣVar x -> TExpQ (CRef s O) -> Ctx s o a -> Ctx s o a
insertSTC (ΣVar v) qref ctx = ctx {stcs = Map.insert v (QCRef qref) (stcs ctx)}

addConstCount :: Int -> Ctx s o a -> Ctx s o a
addConstCount x ctx = ctx {constCount = constCount ctx + x}

skipBounds :: Ctx s o a -> Bool
skipBounds ctx = constCount ctx > 0

debugUp :: Ctx s o a -> Ctx s o a
debugUp ctx = ctx {debugLevel = debugLevel ctx + 1}

debugDown :: Ctx s o a -> Ctx s o a
debugDown ctx = ctx {debugLevel = debugLevel ctx - 1}

newtype Exec s o xs ks a = Exec (Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a)))
run :: Exec s o xs ks a -> Γ s o xs ks a -> Ctx s o a -> QST s (Maybe a)
run (Exec m) γ ctx = runReader m ctx γ

type Handlers o = (HardForkHandler o, SoftForkHandler o, AttemptHandler o, NegLookHandler o, ChainHandler o, LogHandler o)
class HardForkHandler o where
  hardForkHandler :: (Γ s o xs ks a -> QST s (Maybe a)) -> Ctx s o a -> Γ s o xs ks a -> TExpQ (H s o a -> O# -> O# -> ST s (Maybe a))
class SoftForkHandler o where
  softForkHandler :: (Γ s o xs ks a -> QST s (Maybe a)) -> Ctx s o a -> Γ s o xs ks a -> TExpQ (H s o a -> O# -> O# -> ST s (Maybe a))
class AttemptHandler o where
  attemptHandler :: Ctx s o a -> TExpQ (H s o a -> O# -> O# -> ST s (Maybe a))
class NegLookHandler o where
  negLookHandler1 :: (Γ s o xs ks a -> QST s (Maybe a)) -> Ctx s o a -> Γ s o xs ks a -> TExpQ (H s o a -> O# -> O# -> ST s (Maybe a))
  negLookHandler2 :: Ctx s o a -> TExpQ (H s o a -> O# -> O# -> ST s (Maybe a))
class ChainHandler o where
  chainHandler :: (Γ s o (x ': xs) ks a -> QST s (Maybe a)) -> TExpQ (STRef s x) -> TExpQ (CRef s O) 
               -> Ctx s o a -> Γ s o (x ': xs) ks a -> TExpQ (H s o a -> O# -> O# -> ST s (Maybe a))
class LogHandler o where
  logHandler :: String -> Ctx s o a -> Γ s o xs ks a -> TExpQ (H s o a -> O# -> O# -> ST s (Maybe a))

exec :: TExpQ (PreparedInput (Rep O) s O O#) -> (Machine O a, DMap MVar (LetBinding O a), [IMVar]) -> QST s (Maybe a)
exec input (Machine !m, ms, topo) = trace ("EXECUTING: " ++ show m) [||
  do xs <- makeX
     ks <- makeK
     hs <- makeH
     let !(PreparedInput next more same offset box unbox newCRef readCRef writeCRef ) = $$input
     $$(readyCalls topo ms (readyExec m) 
         (Γ [||xs||] [||ks||] [||offset||] [||hs||])
         (Ctx DMap.empty DMap.empty DMap.empty Map.empty (InputOps [||more||] [||next||] [||same||] [||box||] [||unbox||] [||newCRef||] [||readCRef||] [||writeCRef||]) 0 0))
  ||]

readyCalls :: (Handlers o, Suspend o) => [IMVar] -> DMap MVar (LetBinding o a) -> Exec s o '[] '[] a -> Γ s o '[] '[] a -> Ctx s o a -> QST s (Maybe a)
readyCalls topo ms start γ = foldr readyFunc (run start γ) topo
  where
    readyFunc v rest (ctx :: Ctx s o a) = 
      let μ = MVar v
          LetBinding k = ms DMap.! μ
      in [|| let recu = AbsExec (\(!xs) (!ks) o# hs ->
                   $$(run (readyExec k) (Γ [||xs||] [||ks||] [||$$(box ctx) o#||] [||hs||]) 
                                        (insertM μ [||recu||] ctx)))
             in $$(rest (insertM μ [||recu||] ctx)) ||]

readyExec :: (Handlers o, Suspend o) => Free3 (M o) Void3 xs ks a -> Exec s o xs ks a
readyExec = fold3 absurd (Exec . alg)
  where
    alg :: (Handlers o, Suspend o) => M o (Exec s o) xs ks a -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
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

execHalt :: Reader (Ctx s o a) (Γ s o '[a] ks a -> QST s (Maybe a))
execHalt = return $! \γ -> [|| return $! Just $! peekX ($$(xs γ)) ||]

execRet :: Reader (Ctx s o a) (Γ s o (x ': xs) (x ': xs) a -> QST s (Maybe a))
execRet = asks $! \ctx γ -> [|| let !o# = $$(unbox ctx) $$(o γ) in $$(k γ) $$(xs γ) o# ||]

execCall :: Suspend o => MVar x -> Exec s o (x ': xs) ks a -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execCall μ (Exec k) =
  do !(QAbsExec m) <- askM μ
     mk <- k
     asks $ \ctx γ@Γ{..} -> [|| let !o# = $$(unbox ctx) $$o in runConcrete $$m $$xs $$(suspend ctx mk γ) o# $$hs ||]

execJump :: MVar x -> Reader (Ctx s o a) (Γ s o xs (x ': xs) a -> QST s (Maybe a))
execJump μ =
  do !(QAbsExec m) <- askM μ
     ub <- asks unbox
     return $! \γ@Γ{..} -> [|| let !o# = $$ub $$o in runConcrete $$m $$xs $$k o# $$hs ||]

execPush :: WQ x -> Exec s o (x ': xs) ks a -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execPush x (Exec k) = fmap (\m γ -> m (γ {xs = [|| pushX $$(_code x) $$(xs γ) ||]})) k

execPop :: Exec s o xs ks a -> Reader (Ctx s o a) (Γ s o (x ': xs) ks a -> QST s (Maybe a))
execPop (Exec k) = fmap (\m γ -> m (γ {xs = [|| popX_ $$(xs γ) ||]})) k

execLift2 :: WQ (x -> y -> z) -> Exec s o (z ': xs) ks a -> Reader (Ctx s o a) (Γ s o (y ': x ': xs) ks a -> QST s (Maybe a))
execLift2 f (Exec k) = fmap (\m γ -> m (γ {xs = [|| let (# y, xs' #) = popX $$(xs γ); (# x, xs'' #) = popX xs' in pushX ($$(_code f) x y) xs'' ||]})) k

execSat :: WQ (Char -> Bool) -> Exec s o (Char ': xs) ks a -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execSat p (Exec k) =
  do mk <- k
     asks $! \ctx γ -> nextSafe (skipBounds ctx) (ops ctx) (o γ) (_code p) (\o c -> mk (γ {xs = [|| pushX $$c $$(xs γ) ||], o = o})) (raiseΓ γ)

execEmpt :: Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execEmpt = return raiseΓ

execCommit :: Bool -> Exec s o xs ks a -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execCommit exit (Exec k) = local (\ctx -> if exit then addConstCount (-1) ctx else ctx)
                                 (fmap (\m γ -> m (γ {hs = [|| popH_ $$(hs γ) ||]})) k)

execHardFork :: HardForkHandler o => Exec s o xs ks a -> Exec s o xs ks a -> Maybe (ΦDecl (Exec s o) x xs ks a) -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execHardFork (Exec p) (Exec q) decl = setupJoinPoint decl $
  do mp <- p
     mq <- q
     asks $! \ctx γ -> setupHandlerΓ ctx γ (hardForkHandler mq ctx γ) mp

instance HardForkHandler O where
  hardForkHandler mq ctx γ = let bx = box ctx in [||\hs o# c# ->
      if $$(same ctx) ($$bx c#) ($$bx o#) then $$(mq (γ {o = [||$$bx o#||], hs = [||hs||]}))
      else raise hs ($$bx o#)
    ||]

execSoftFork :: SoftForkHandler o => Maybe Int -> Exec s o xs ks a -> Exec s o xs ks a -> Maybe (ΦDecl (Exec s o) x xs ks a) -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execSoftFork constantInput (Exec p) (Exec q) decl = setupJoinPoint decl $
  do mp <- inputSizeCheck constantInput p
     mq <- q
     asks $! \ctx γ -> setupHandlerΓ ctx γ (softForkHandler mq ctx γ) mp

instance SoftForkHandler O where
  softForkHandler mq ctx γ = [||\hs _ c# ->
      $$(mq (γ {o = [||$$(box ctx) c#||], hs = [||hs||]}))
    ||]

execJoin :: ΦVar x -> Reader (Ctx s o a) (Γ s o (x ': xs) ks a -> QST s (Maybe a))
execJoin φ = 
  do QJoin k <- asks ((DMap.! φ) . φs)
     ub <- asks unbox
     return $! \γ -> [|| $$k (peekX $$(xs γ)) ($$ub $$(o γ)) ||]

execAttempt :: AttemptHandler o => Maybe Int -> Exec s o xs ks a -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execAttempt constantInput (Exec k) = do mk <- inputSizeCheck constantInput k; asks (\ctx γ -> setupHandlerΓ ctx γ (attemptHandler ctx) mk)

instance AttemptHandler O where attemptHandler ctx = let bx = box ctx in [||\hs _ c# -> raise hs ($$bx c#)||]

execTell :: Exec s o (O ': xs) ks a -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execTell (Exec k) = fmap (\mk γ -> mk (γ {xs = [||pushX $$(o γ) $$(xs γ)||]})) k

execSeek :: Exec s o xs ks a -> Reader (Ctx s o a) (Γ s o (O ': xs) ks a -> QST s (Maybe a))
execSeek (Exec k) = fmap (\mk γ -> [||let (# o, xs' #) = popX $$(xs γ) in $$(mk (γ {xs = [||xs'||], o=[||o||]}))||]) k

execNegLook :: NegLookHandler o => Exec s o xs ks a -> Exec s o xs ks a -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execNegLook (Exec m) (Exec k) =
  do mm <- m
     mk <- k
     asks $! \ctx γ -> setupHandlerΓ ctx γ (negLookHandler2 ctx) (\γ' -> setupHandlerΓ ctx γ' (negLookHandler1 mk ctx γ) mm)

instance NegLookHandler O where
  negLookHandler1 mk ctx γ = let bx = box ctx in [||\hs _ c# -> $$(mk (γ {o = [||$$bx c#||], hs = [||popH_ hs||]}))||]
  negLookHandler2 ctx = let bx = box ctx in [||\hs _ c# -> raise hs ($$bx c#)||]

execCase :: Exec s o (x ': xs) ks a -> Exec s o (y ': xs) ks a -> Reader (Ctx s o a) (Γ s o (Either x y ': xs) ks a -> QST s (Maybe a))
execCase (Exec p) (Exec q) =
  do mp <- p
     mq <- q
     return $! \γ -> [||
         let (# e, xs' #) = popX $$(xs γ)
         in case e of
           Left x -> $$(mp (γ {xs = [||pushX x xs'||]}))
           Right y  -> $$(mq (γ {xs = [||pushX y xs'||]}))
       ||]

execChoices :: forall x xs ks a s o. [WQ (x -> Bool)] -> [Exec s o xs ks a] -> Exec s o xs ks a -> Reader (Ctx s o a) (Γ s o (x ': xs) ks a -> QST s (Maybe a))
execChoices fs ks (Exec def) = 
  do mdef <- def
     fmap (\mks γ -> [|| let !(# x, xs' #) = popX $$(xs γ) in $$(go [||x||] fs mks mdef (γ {xs = [||xs'||]})) ||]) (forM ks (\(Exec k) -> k))
  where
    go :: TExpQ x -> [WQ (x -> Bool)] -> [Γ s o xs ks a -> QST s (Maybe a)] -> (Γ s o xs ks a -> QST s (Maybe a)) -> Γ s o xs ks a -> QST s (Maybe a)
    go _ [] [] def γ = def γ
    go x (f:fs) (mk:mks) def γ = [||
        if $$(_code f) $$x then $$(mk γ)
        else $$(go x fs mks def γ)
      ||]


execChainIter :: ΣVar x -> MVar x -> Reader (Ctx s o a) (Γ s o ((x -> x) ': xs) (x ': xs) a -> QST s (Maybe a))
execChainIter σ μ =
  do !(QSTRef ref) <- askΣ σ
     !(QAbsExec l) <- askM μ
     !(QCRef cref) <- askSTC σ
     asks $! \ctx γ@Γ{..} -> [||
       do let (# g, xs' #) = popX $$xs
          modifyΣ $$ref g
          $$(writeCRef ctx) $$cref $$o
          runConcrete $$l xs' $$k ($$(unbox ctx) $$o) $$hs
       ||]

execChainInit :: ChainHandler o => ΣVar x -> Exec s o xs (x ': xs) a -> MVar x -> Exec s o (x ': xs) ks a
              -> Reader (Ctx s o a) (Γ s o (x ': xs) ks a -> QST s (Maybe a))
execChainInit σ l μ (Exec k) =
  do mk <- k
     asks $! \ctx γ@(Γ xs ks o _) -> [||
       do let (# x, xs' #) = popX $$xs
          ref <- newΣ x
          cref <- $$(newCRef ctx) $$o
          $$(setupHandlerΓ ctx γ (chainHandler mk [||ref||] [||cref||] ctx γ) (\γ' -> [||
              -- NOTE: Only the offset and the handler stack can change between interations of a chainPre
              do let loop o# =
                       $$(run l (Γ [||xs'||] [||noreturn||] [||$$(box ctx) o#||] (hs γ'))
                                (insertSTC σ [||cref||] (insertM μ [||AbsExec (\_ _ o# _ -> loop o#)||] (insertΣ σ [||ref||] ctx))))
                 loop ($$(unbox ctx) $$o)
            ||]))
      ||]

instance ChainHandler O where
  chainHandler mk ref cref ctx γ = [||\hs o# _ ->
      do c <- $$(readCRef ctx) $$cref
         if $$(same ctx) c ($$(box ctx) o#) then
            do y <- readΣ $$ref
               $$(mk (γ {xs = [|| pokeX y $$(xs γ) ||],
                         o = [|| $$(box ctx) o# ||],
                         hs = [||hs||]}))
         else raise hs ($$(box ctx) o#)
    ||]

execSwap :: Exec s o (x ': y ': xs) ks a -> Reader (Ctx s o a) (Γ s o (y ': x ': xs) ks a -> QST s (Maybe a))
execSwap (Exec k) = fmap (\mk γ -> mk (γ {xs = [||let (# y, xs' #) = popX $$(xs γ); (# x, xs'' #) = popX xs' in pushX x (pushX y xs'')||]})) k

preludeString :: String -> Char -> Γ s o xs ks a -> Ctx s o a -> String -> TExpQ String
preludeString name dir γ ctx ends = [|| concat [$$prelude, $$eof, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    offset     = o γ
    indent     = replicate (debugLevel ctx * 2) ' '
    start      = [|| max ($$offset - 5) 0 ||]
    end        = [|| $$offset + 5 ||]
    inputTrace = [|| let replace '\n' = color Green "↙"
                         replace ' '  = color White "·"
                         replace c    = return c
                         go i 
                           | i == $$end = []
                           | otherwise  = let (# c, i' #) = $$(next ctx) i in replace c ++ go i'
                     in go $$start ||]
    eof        = [|| if $$(more ctx) $$end then $$inputTrace else $$inputTrace ++ color Red "•" ||]
    prelude    = [|| concat [indent, dir : name, dir : " (", show $$offset, "): "] ||]
    caretSpace = [|| replicate (length $$prelude + $$offset - $$start) ' ' ||]

execLogEnter :: LogHandler o => String -> Exec s o xs ks a -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execLogEnter name k =
  do asks $! \ctx γ ->
      (setupHandlerΓ ctx γ (logHandler name ctx γ) (\γ' -> [|| trace $$(preludeString name '>' γ ctx "") $$(run k γ' (debugUp ctx))||]))

instance LogHandler O where
  logHandler name ctx γ = [||\hs o# _ -> trace $$(preludeString name '<' (γ {o = [||$$(box ctx) o#||]}) ctx (color Red " Fail")) (raise hs ($$(box ctx) o#)) ||]

execLogExit :: String -> Exec s o xs ks a -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
execLogExit name k = asks $! \ctx γ -> [|| trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(run k γ (debugDown ctx)) ||]

setupHandlerΓ :: Ctx s o a -> Γ s o xs ks a -> TExpQ (H s o a -> O# -> O# -> ST s (Maybe a)) ->
                                              (Γ s o xs ks a -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandlerΓ ctx γ !h !k = setupHandler (ops ctx) (hs γ) (o γ) h (\hs -> k (γ {hs = hs}))

setupJoinPoint :: Maybe (ΦDecl (Exec s o) x xs ks a) -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a)) -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
setupJoinPoint Nothing mx = mx
setupJoinPoint (Just (φ, (Exec k))) mx =
  do ctx <- ask
     fmap (\mk γ -> [||
       let join x (o# :: O#) = $$(mk (γ {xs = [||pushX x $$(xs γ)||], o = [||$$(box ctx) o#||]}))
       in $$(run (Exec mx) γ (insertΦ φ [||join||] ctx))
       ||]) k

inputSizeCheck :: Maybe Int -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a)) -> Reader (Ctx s o a) (Γ s o xs ks a -> QST s (Maybe a))
inputSizeCheck Nothing p = p
inputSizeCheck (Just n) p =
  do skip <- asks skipBounds
     mp <- local (addConstCount 1) p
     if skip then return $! mp
     else fmap (\ctx γ -> [|| 
       if $$(more ctx) (n + $$(o γ) - 1) then $$(mp γ)
       else $$(raiseΓ γ)
      ||]) ask

raiseΓ :: Γ s o xs ks a -> QST s (Maybe a)
raiseΓ γ = [|| raise $$(hs γ) $$(o γ) ||]

class Suspend o where
  suspend :: Ctx s o a -> (Γ s o (x ': xs) ks a -> QST s (Maybe a)) -> Γ s o xs ks a -> QK (Rep o) s (Unboxed o) (x ': xs) a

instance Suspend O where
  suspend ctx m γ = [|| \xs o# -> $$(m (γ {xs = [||xs||], o = [||$$(box ctx) o#||]})) ||]

askM :: MonadReader (Ctx s o a) m => MVar x -> m (QAbsExec s o a x)
askM μ = {-trace ("fetching " ++ show μ) $ -}asks (((DMap.! μ) . μs))

askΣ :: MonadReader (Ctx s o a) m => ΣVar x -> m (QSTRef s x)
askΣ σ = {-trace ("fetching " ++ show σ) $ -}asks ((DMap.! σ) . σs)

askΦ :: MonadReader (Ctx s o a) m => ΦVar x -> m (QJoin s o a x)
askΦ φ = {-trace ("fetching " ++ show φ) $ -}asks ((DMap.! φ) . φs)

askSTC :: MonadReader (Ctx s o a) m => ΣVar x -> m (QCRef s O)
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