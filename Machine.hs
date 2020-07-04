{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             RankNTypes,
             BangPatterns,
             FlexibleInstances,
             MagicHash,
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
             PatternSynonyms,
             InstanceSigs,
             MultiWayIf,
             ConstrainedClassMethods #-}
module Machine where

import MachineOps
import MachineAST
import Input                      (InputDependant(..), PositionOps(..), BoxOps(..), LogOps(..), InputOps(..), next, more, Unboxed, OffWith, UnpackedLazyByteString, Stream)
import Indexed                    (Fix4, cata4, Nat(..))
import Utils                      (code, Code, Quapplicative)
import Defunc                     (DefuncM, genDefuncM, genDefuncM1, genDefuncM2)
import Data.Functor               ((<&>))
import Data.Void                  (Void)
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
import qualified Queue                      (empty, size, null, foldr)

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
data Γ s o xs n r a = Γ { xs    :: QList xs
                        , ret   :: Code (Cont s o a r)
                        , o     :: Code o
                        , hs    :: Vec n (Code (H s o a)) }

newtype QSTRef s x = QSTRef (Code (STRef s x))
data Ctx s o a = Ctx { μs         :: DMap MVar (QAbsExec s o a)
                     , φs         :: DMap ΦVar (QJoin s o a)
                     , σs         :: DMap ΣVar (QSTRef s)
                     , debugLevel :: Int
                     , coins      :: Int
                     , piggies    :: Queue Int }
emptyCtx :: Ctx s o a
emptyCtx = Ctx DMap.empty DMap.empty DMap.empty 0 0 Queue.empty

insertM :: MVar x -> Code (AbsExec s o a x) -> Ctx s o a -> Ctx s o a
insertM μ q ctx = ctx {μs = DMap.insert μ (QAbsExec q) (μs ctx)}

insertΦ :: ΦVar x -> Code (Cont s o a x) -> Ctx s o a -> Ctx s o a
insertΦ φ qjoin ctx = ctx {φs = DMap.insert φ (QJoin qjoin) (φs ctx)}

insertΣ :: ΣVar x -> Code (STRef s x) -> Ctx s o a -> Ctx s o a
insertΣ σ qref ctx = ctx {σs = DMap.insert σ (QSTRef qref) (σs ctx)}

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
type ExecMonad s o xs n r a = Reader (Ctx s o a) (Γ s o xs n r a -> Code (ST s (Maybe a)))
newtype Exec s o xs n r a = Exec { unExec :: ExecMonad s o xs n r a }
run :: Exec s o xs n r a -> Γ s o xs n r a -> Ctx s o a -> Code (ST s (Maybe a))
run (Exec m) γ ctx = runReader m ctx γ

type Ops o = (Handlers o, KOps o, FailureOps o, JoinBuilder o, RecBuilder o, ReturnOps o, PositionOps o, BoxOps o, LogOps o)
type Handlers o = (ChainHandler o, LogHandler o)
class PositionOps o => ChainHandler o where
  chainHandler :: (Γ s o xs (Succ n) ks a -> Code (ST s (Maybe a))) -> Γ s o xs (Succ n) ks a -> Code o -> Code (H s o a)
class (BoxOps o, PositionOps o, LogOps o) => LogHandler o where
  logHandler :: (?ops :: InputOps o) => String -> Ctx s o a -> Γ s o xs (Succ n) ks a -> Code o -> Code (H s o a)

exec :: forall o q s a. (Quapplicative q, Ops o) => Code (InputDependant o) -> (Machine o a, DMap MVar (LetBinding q o a)) -> Code (ST s (Maybe a))
exec input (Machine !m, ms) = trace ("EXECUTING: " ++ show m) [||
  do let !(InputDependant next more offset) = $$input
     $$(let ?ops = InputOps [||more||] [||next||]
        in scopeBindings ms
             nameLet
             QAbsExec
             (\(LetBinding k) names -> buildRec (emptyCtx {μs = names}) (readyExec k))
             (\names -> run (readyExec m) (Γ QNil (halt @o) [||offset||] (VCons (fatal @o) VNil)) (emptyCtx {μs = names})))
  ||]

missingDependency :: MVar x -> MissingDependency
missingDependency (MVar v) = MissingDependency v
dependencyOf :: MissingDependency -> MVar x
dependencyOf (MissingDependency v) = MVar v
outOfScopeRegister :: ΣVar x -> OutOfScopeRegister
outOfScopeRegister (ΣVar σ) = OutOfScopeRegister σ

nameLet :: LetBinding q o a x -> String
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

readyExec :: (?ops :: InputOps o, Ops o, Quapplicative q) => Fix4 (M q o) xs n r a -> Exec s o xs n r a
readyExec = cata4 (Exec . alg)
  where
    alg :: (?ops :: InputOps o, Ops o, Quapplicative q) => M q o (Exec s o) xs n r a -> ExecMonad s o xs n r a
    alg Ret                 = execRet
    alg (Call μ k)          = execCall μ k
    alg (Jump μ)            = execJump μ
    alg (Push x k)          = execPush x k
    alg (Pop k)             = execPop k
    alg (Lift2 f k)         = execLift2 f k
    alg (Sat p k)           = execSat p k
    alg Empt                = execEmpt
    alg (Commit k)          = execCommit k
    alg (Catch k h)         = execCatch k h
    alg (Tell k)            = execTell k
    alg (Seek k)            = execSeek k
    alg (Case p q)          = execCase p q
    alg (Choices fs ks def) = execChoices fs ks def
    alg (Iter l μ k)        = execIter l μ k
    alg (Join φ)            = execJoin φ
    alg (MkJoin φ p k)      = execMkJoin φ p k
    alg (Swap k)            = execSwap k
    alg (Make σ k)          = execMake σ k
    alg (Get σ k)           = execGet σ k
    alg (Put σ k)           = execPut σ k
    alg (LogEnter name k)   = execLogEnter name k
    alg (LogExit name k)    = execLogExit name k
    alg (MetaM m k)         = execMeta m k

execRet :: KOps o => ExecMonad s o (x ': xs) n x a
execRet = return $! resume

execCall :: KOps o => MVar x -> Exec s o (x ': xs) (Succ n) r a -> ExecMonad s o xs (Succ n) r a
execCall μ (Exec k) =
  do !(QAbsExec m) <- askM μ
     k <&> \mk γ@Γ{..} -> runConcrete hs m (suspend mk γ) o

execJump :: BoxOps o => MVar x -> ExecMonad s o '[] (Succ n) x a
execJump μ =
  do !(QAbsExec m) <- askM μ
     return $! \γ@Γ{..} -> runConcrete hs m ret o

execPush :: (PositionOps o, Quapplicative q) => DefuncM q o x -> Exec s o (x ': xs) n r a -> ExecMonad s o xs n r a
execPush x (Exec k) = k <&> \m γ -> m (γ {xs = QCons (genDefuncM x) (xs γ)})

execPop :: Exec s o xs n r a -> ExecMonad s o (x ': xs) n r a
execPop (Exec k) = k <&> \m γ -> m (γ {xs = tailQ (xs γ)})

execLift2 :: (PositionOps o, Quapplicative q) => DefuncM q o (x -> y -> z) -> Exec s o (z ': xs) n r a -> ExecMonad s o (y ': x ': xs) n r a
execLift2 f (Exec k) = k <&> \m γ -> m (γ {xs = let QCons y (QCons x xs') = xs γ in QCons (genDefuncM2 f x y) xs'})

execSat :: (?ops :: InputOps o, PositionOps o, BoxOps o, Quapplicative q) => DefuncM q o (Char -> Bool) -> Exec s o (Char ': xs) (Succ n) r a -> ExecMonad s o xs (Succ n) r a
execSat p (Exec k) = do
  bankrupt <- asks isBankrupt
  hasChange <- asks hasCoin
  if | bankrupt -> maybeEmitCheck (Just 1) <$> k
     | hasChange -> maybeEmitCheck Nothing <$> local spendCoin k
     | otherwise -> trace "I have a piggy :)" $ local breakPiggy (maybeEmitCheck . Just <$> asks coins <*> local spendCoin k)
  where
    readChar bad k γ@Γ{..} = sat o (genDefuncM p) (\o c -> k (γ {xs = QCons c xs, o = o})) bad
    maybeEmitCheck Nothing mk γ = readChar (raiseΓ γ) mk γ
    maybeEmitCheck (Just n) mk γ =
      [|| let bad' = $$(raiseΓ γ) in $$(emitLengthCheck n (readChar [||bad'||] mk γ) [||bad'||] γ)||]

execEmpt :: BoxOps o => ExecMonad s o xs (Succ n) r a
execEmpt = return $! raiseΓ

execCommit :: Exec s o xs n r a -> ExecMonad s o xs (Succ n) r a
execCommit (Exec k) = k <&> \m γ -> let VCons _ hs' = hs γ in m (γ {hs = hs'})

execCatch :: (?ops :: InputOps o, BoxOps o) => Exec s o xs (Succ n) r a -> Exec s o (o ': xs) n r a -> ExecMonad s o xs n r a
execCatch (Exec k) (Exec h) = liftM2 (\mk mh γ -> setupHandlerΓ γ (\c -> [||\o# -> $$(mh (γ {xs = QCons c (xs γ), o = [||$$box o#||]}))||]) mk) k h

execTell :: Exec s o (o ': xs) n r a -> ExecMonad s o xs n r a
execTell (Exec k) = k <&> \mk γ -> mk (γ {xs = QCons (o γ) (xs γ)})

execSeek :: Exec s o xs n r a -> ExecMonad s o (o ': xs) n r a
execSeek (Exec k) = k <&> \mk γ -> let QCons o xs' = xs γ in mk (γ {xs = xs', o=o})

execCase :: JoinBuilder o => Exec s o (x ': xs) n r a -> Exec s o (y ': xs) n r a -> ExecMonad s o (Either x y ': xs) n r a
execCase (Exec p) (Exec q) = liftM2 (\mp mq γ ->
  let QCons e xs' = xs γ
  in [||case $$e of
    Left x -> $$(mp (γ {xs = QCons [||x||] xs'}))
    Right y  -> $$(mq (γ {xs = QCons [||y||] xs'}))||]) p q

execChoices :: (PositionOps o, Quapplicative q) => [DefuncM q o (x -> Bool)] -> [Exec s o xs n r a] -> Exec s o xs n r a -> ExecMonad s o (x ': xs) n r a
execChoices fs ks (Exec def) = liftM2 (\mdef mks γ -> let QCons x xs' = xs γ in go x fs mks mdef (γ {xs = xs'}))
  def
  (forM ks (\(Exec k) -> k))
  where
    go _ [] [] def γ = def γ
    go x (f:fs) (mk:mks) def γ = [||
        if $$(genDefuncM1 f x) then $$(mk γ)
        else $$(go x fs mks def γ)
      ||]

execIter :: (ChainHandler o, RecBuilder o, ReturnOps o)
         => Exec s o '[] One Void a -> MVar Void -> Exec s o xs (Succ n) r a
         -> ExecMonad s o xs (Succ n) r a
execIter l μ (Exec k) =
  do mk <- k
     asks $! \ctx γ@(Γ xs ks o _) -> buildIter ctx μ l (chainHandler mk γ) o

{-
Our current goal is to eliminate this handler

-}
#define deriveChainHandler(_o)                       \
instance ChainHandler _o where                       \
{                                                    \
  chainHandler mk γ c = let bx = box in [||\(!o#) -> \
      if $$same $$c ($$bx o#) then                   \
        $$(mk (γ {o = [|| $$bx o# ||]}))             \
      else $$(raise @_o (hs γ)) o#                   \
    ||]                                              \
};
inputInstances(deriveChainHandler)

execJoin :: BoxOps o => ΦVar x -> ExecMonad s o (x ': xs) n r a
execJoin φ =
  do QJoin k <- asks ((DMap.! φ) . φs)
     return $! \γ -> [|| $$k $$(headQ (xs γ)) ($$unbox $$(o γ)) ||]

execMkJoin :: JoinBuilder o => ΦVar x -> Exec s o (x ': xs) n r a -> Exec s o xs n r a -> ExecMonad s o xs n r a
execMkJoin φ p (Exec k) = setupJoinPoint φ p k

execSwap :: Exec s o (x ': y ': xs) n r a -> ExecMonad s o (y ': x ': xs) n r a
execSwap (Exec k) = k <&> (\mk γ -> mk (γ {xs = let QCons y (QCons x xs') = xs γ in QCons x (QCons y xs')}))

execMake :: ΣVar x -> Exec s o xs n r a -> ExecMonad s o (x ': xs) n r a
execMake σ k = asks $! \ctx γ -> let QCons x xs' = xs γ in [||
                  do ref <- newΣ $$x
                     $$(run k (γ {xs = xs'}) (insertΣ σ [||ref||] ctx))
                ||]

execGet :: ΣVar x -> Exec s o (x ': xs) n r a -> ExecMonad s o xs n r a
execGet σ (Exec k) =
  do !(QSTRef ref) <- askΣ σ
     k <&> \mk γ -> [||
       do x <- readΣ $$ref
          $$(mk (γ {xs = QCons [||x||] (xs γ)}))
       ||]

execPut :: ΣVar x -> Exec s o xs n r a -> ExecMonad s o (x ': xs) n r a
execPut σ (Exec k) =
  do !(QSTRef ref) <- askΣ σ
     k <&> \mk γ -> let QCons x xs' = xs γ in [||
       do writeΣ $$ref $$x
          $$(mk (γ {xs = xs'}))
       ||]

preludeString :: (?ops :: InputOps o, PositionOps o, LogOps o) => String -> Char -> Γ s o xs n r a -> Ctx s o a -> String -> Code String
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
                           | $$same i $$end || not ($$more i) = []
                           | otherwise = $$(next [||i||] (\qc qi' -> [||replace $$qc ++ go $$qi'||]))
                     in go $$start ||]
    eof        = [|| if $$more $$end then $$inputTrace else $$inputTrace ++ color Red "•" ||]
    prelude    = [|| concat [indent, dir : name, dir : " (", show ($$offToInt $$offset), "): "] ||]
    caretSpace = [|| replicate (length $$prelude + $$offToInt $$offset - $$offToInt $$start) ' ' ||]

execLogEnter :: (?ops :: InputOps o, LogHandler o) => String -> Exec s o xs (Succ (Succ n)) r a -> ExecMonad s o xs (Succ n) r a
execLogEnter name (Exec mk) =
  liftM2 (\k ctx γ -> [|| trace $$(preludeString name '>' γ ctx "") $$(setupHandlerΓ γ (logHandler name ctx γ) k)||])
    (local debugUp mk)
    ask

execLogExit :: (?ops :: InputOps o, PositionOps o, LogOps o) => String -> Exec s o xs n r a -> ExecMonad s o xs n r a
execLogExit name (Exec mk) =
  liftM2 (\k ctx γ -> [|| trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(k γ) ||])
    (local debugDown mk)
    ask

#define deriveLogHandler(_o)                                                                                      \
instance LogHandler _o where                                                                                      \
{                                                                                                                 \
  logHandler name ctx γ _ = [||\(!o#) ->                                                                          \
      trace $$(preludeString name '<' (γ {o = [||$$box o#||]}) ctx (color Red " Fail")) ($$(raise @_o (hs γ)) o#) \
    ||]                                                                                                           \
};
inputInstances(deriveLogHandler)

execMeta :: (?ops :: InputOps o, PositionOps o, BoxOps o) => MetaM n -> Exec s o xs n r a -> ExecMonad s o xs n r a
execMeta (AddCoins coins) (Exec k) =
  do requiresPiggy <- asks hasCoin
     if requiresPiggy then local (storePiggy coins) k
     else local (giveCoins coins) k <&> \mk γ -> emitLengthCheck coins (mk γ) (raiseΓ γ) γ
execMeta (FreeCoins coins) (Exec k) = local (giveCoins coins) k
execMeta (RefundCoins coins) (Exec k) = local (giveCoins coins) k
execMeta (DrainCoins coins) (Exec k) = liftM2 (\n mk γ -> emitLengthCheck n (mk γ) (raiseΓ γ) γ) (asks ((coins -) . liquidate)) k

setupHandlerΓ :: Γ s o xs n r a
              -> (Code o -> Code (H s o a))
              -> (Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))
setupHandlerΓ γ h k = setupHandler (hs γ) (o γ) h (\hs -> k (γ {hs = hs}))

raiseΓ :: BoxOps o => Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))
raiseΓ γ = let VCons h _ = hs γ in [|| $$h ($$unbox $$(o γ)) ||]

class BoxOps o => JoinBuilder o where
  setupJoinPoint :: ΦVar x -> Exec s o (x ': xs) n r a -> ExecMonad s o xs n r a -> ExecMonad s o xs n r a

#define deriveJoinBuilder(_o)                                      \
instance JoinBuilder _o where                                      \
{                                                                  \
  setupJoinPoint φ (Exec k) mx =                                   \
    liftM2 (\mk ctx γ -> [||                                       \
      let join x !(o# :: Unboxed _o) =                             \
        $$(mk (γ {xs = QCons [||x||] (xs γ), o = [||$$box o#||]})) \
      in $$(run (Exec mx) γ (insertΦ φ [||join||] ctx))            \
    ||]) (local voidCoins k) ask                                   \
};
inputInstances(deriveJoinBuilder)

class BoxOps o => RecBuilder o where
  buildIter :: ReturnOps o
            => Ctx s o a -> MVar Void -> Exec s o '[] One Void a
            -> (Code o -> Code (H s o a)) -> Code o -> Code (ST s (Maybe a))
  buildRec  :: Ctx s o a
            -> Exec s o '[] One r a
            -> Code (AbsExec s o a r)

#define deriveRecBuilder(_o)                                                      \
instance RecBuilder _o where                                                      \
{                                                                                 \
  buildIter ctx μ l h o = let bx = box in [||                                     \
      let loop !o# =                                                              \
        let handler = $$(h [||$$bx o#||]) in                                      \
        $$(let ctx' = insertM μ [||\_ (!o#) _ -> loop o#||] ctx;                  \
               γ = Γ QNil (noreturn @_o) [||$$bx o#||] (VCons [||handler||] VNil) \
           in run l γ (voidCoins ctx'))                                           \
      in loop ($$unbox $$o)                                                       \
    ||];                                                                          \
  buildRec ctx k = let bx = box in [|| \(!ret) (!o#) h ->                         \
    $$(run k (Γ QNil [||ret||] [||$$bx o#||] (VCons [||h||] VNil)) ctx) ||]       \
};
inputInstances(deriveRecBuilder)

emitLengthCheck :: (?ops :: InputOps o, PositionOps o, BoxOps o) => Int -> Code (ST s (Maybe a)) -> Code (ST s (Maybe a)) -> Γ s o xs n r a -> Code (ST s (Maybe a))
emitLengthCheck 0 good _ _   = good
emitLengthCheck 1 good bad γ = [|| if $$more $$(o γ) then $$good else $$bad ||]
emitLengthCheck n good bad γ = [||
  if $$more ($$shiftRight $$(o γ) (n - 1)) then $$good
  else $$bad ||]

class BoxOps o => KOps o where
  suspend :: (Γ s o (x ': xs) n r a -> Code (ST s (Maybe a))) -> Γ s o xs n r a -> Code (Cont s o a x)
  resume :: Γ s o (x ': xs) n x a -> Code (ST s (Maybe a))

#define deriveKOps(_o)                                                                         \
instance KOps _o where                                                                         \
{                                                                                              \
  suspend m γ = [|| \x (!o#) -> $$(m (γ {xs = QCons [||x||] (xs γ), o = [||$$box o#||]})) ||]; \
  resume γ = [|| $$(ret γ) $$(headQ (xs γ)) ($$unbox $$(o γ)) ||]                              \
};
inputInstances(deriveKOps)

askM :: MonadReader (Ctx s o a) m => MVar x -> m (QAbsExec s o a x)
askM μ = do
  mexec <- asks (((DMap.lookup μ) . μs))
  case mexec of
    Just exec -> return $! exec
    Nothing   -> throw (missingDependency μ)

askΣ :: MonadReader (Ctx s o a) m => ΣVar x -> m (QSTRef s x)
askΣ σ = do
  mref <- asks ((DMap.lookup σ) . σs)
  case mref of
    Just ref -> return $! ref
    Nothing  -> throw (outOfScopeRegister σ)

askΦ :: MonadReader (Ctx s o a) m => ΦVar x -> m (QJoin s o a x)
askΦ φ = asks ((DMap.! φ) . φs)

instance Show MissingDependency where show (MissingDependency (IMVar μ)) = "Dependency μ" ++ show μ ++ " has not been compiled"
instance Exception MissingDependency

instance Show OutOfScopeRegister where show (OutOfScopeRegister (IΣVar σ)) = "Register r" ++ show σ ++ " is out of scope"
instance Exception OutOfScopeRegister
