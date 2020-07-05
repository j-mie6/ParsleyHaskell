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
import Instructions
import Identifiers
import Input                      (InputDependant(..), PositionOps(..), BoxOps(..), LogOps(..), InputOps(..), next, more, Unboxed, OffWith, UnpackedLazyByteString, Stream)
import Indexed                    (Fix4, cata4, Nat(..))
import Utils                      (code, Code, Quapplicative)
import Defunc                     (Defunc, genDefunc, genDefunc1, genDefunc2)
import Data.Functor               ((<&>))
import Data.Void                  (Void)
import Control.Monad              (forM, join, liftM2)
import Control.Monad.ST           (ST)
import Control.Monad.Reader       (ask, asks, local, Reader, runReader, MonadReader)
import Control.Exception          (Exception, throw)
import Data.STRef                 (STRef)
import Data.STRef.Unboxed         (STRefU)
import Queue                      (Queue, enqueue, dequeue)
import Data.Dependent.Map         (DMap, DSum(..))
import Data.GADT.Compare          (GCompare)
import Debug.Trace                (trace)
import System.Console.Pretty      (color, Color(Green, White, Red, Blue))
import Data.Text                  (Text)
import Data.Functor.Const         (Const(..), getConst)
import Language.Haskell.TH        (runQ, Q, newName, Name)
import Language.Haskell.TH.Syntax (unTypeQ, unsafeTExpCoerce, Exp(VarE, LetE), Dec(FunD), Clause(Clause), Body(NormalB))
import qualified Data.Dependent.Map as DMap ((!), insert, empty, lookup, map, toList, traverseWithKey)
import qualified Queue                      (empty, size, null, foldr)

#define inputInstances(derivation) \
derivation(Int)                    \
derivation((OffWith [Char]))       \
derivation((OffWith Stream))       \
derivation(UnpackedLazyByteString) \
derivation(Text)

data Γ s o xs n r a = Γ { xs    :: QList xs
                        , ret   :: Code (Cont s o a r)
                        , o     :: Code o
                        , hs    :: Vec n (Code (H s o a)) }

newtype QSTRef s x = QSTRef (Code (STRef s x))
data Ctx s o a = Ctx { μs         :: DMap MVar (QSubRoutine s o a)
                     , φs         :: DMap ΦVar (QJoin s o a)
                     , σs         :: DMap ΣVar (QSTRef s)
                     , debugLevel :: Int
                     , coins      :: Int
                     , piggies    :: Queue Int }
emptyCtx :: Ctx s o a
emptyCtx = Ctx DMap.empty DMap.empty DMap.empty 0 0 Queue.empty

insertSub :: MVar x -> Code (SubRoutine s o a x) -> Ctx s o a -> Ctx s o a
insertSub μ q ctx = ctx {μs = DMap.insert μ (QSubRoutine q) (μs ctx)}

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
type MachineMonad s o xs n r a = Reader (Ctx s o a) (Γ s o xs n r a -> Code (ST s (Maybe a)))
newtype Machine s o xs n r a = Machine { getMachine :: MachineMonad s o xs n r a }
run :: Machine s o xs n r a -> Γ s o xs n r a -> Ctx s o a -> Code (ST s (Maybe a))
run = flip . runReader . getMachine

type Ops o = (LogHandler o, KOps o, HandlerOps o, JoinBuilder o, RecBuilder o, ReturnOps o, PositionOps o, BoxOps o, LogOps o)

exec :: forall o q s a. (Quapplicative q, Ops o) => Code (InputDependant o) -> (Program o a, DMap MVar (LetBinding q o a)) -> Code (ST s (Maybe a))
exec input (Program !p, fs) = trace ("EXECUTING: " ++ show p) [||
  do let !(InputDependant next more offset) = $$input
     $$(let ?ops = InputOps [||more||] [||next||]
        in scopeBindings fs
             nameLet
             QSubRoutine
             (\(LetBinding k) names -> buildRec (emptyCtx {μs = names}) (readyMachine k))
             (\names -> run (readyMachine p) (Γ QNil (halt @o) [||offset||] (VCons (fatal @o) VNil)) (emptyCtx {μs = names})))
  ||]

missingDependency :: MVar x -> MissingDependency
missingDependency (MVar v) = MissingDependency v
dependencyOf :: MissingDependency -> MVar x
dependencyOf (MissingDependency v) = MVar v
outOfScopeRegister :: ΣVar x -> OutOfScopeRegister
outOfScopeRegister (ΣVar σ) = OutOfScopeRegister σ

nameLet :: MVar x -> LetBinding q o a x -> String
nameLet (MVar (IMVar i)) _ = "sub" ++ show i

scopeBindings :: GCompare key => DMap key named
                              -> (forall a. key a -> named a -> String)
                              -> (forall x. Code ((x -> y) -> z) -> q x)
                              -> (forall x. named x -> DMap key q -> Code ((x -> y) -> z))
                              -> (DMap key q -> Code a)
                              -> Code a
scopeBindings bindings nameOf wrap letBuilder scoped = unsafeTExpCoerce $
  do names <- makeNames bindings
     LetE <$> generateBindings names bindings <*> unTypeQ (scoped (package names))
  where
    package = DMap.map (wrap . unsafeTExpCoerce . return . VarE . getConst)
    makeNames = DMap.traverseWithKey (\k v -> Const <$> newName (nameOf k v))
    generateBindings names = traverse makeDecl . DMap.toList
      where
        makeDecl (k :=> v) =
          do let Const name = names DMap.! k
             body <- unTypeQ (letBuilder v (package names))
             return (FunD name [Clause [] (NormalB body) []])

readyMachine :: (?ops :: InputOps o, Ops o, Quapplicative q) => Fix4 (Instr q o) xs n r a -> Machine s o xs n r a
readyMachine = cata4 (Machine . alg)
  where
    alg :: (?ops :: InputOps o, Ops o, Quapplicative q) => Instr q o (Machine s o) xs n r a -> MachineMonad s o xs n r a
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
    alg (Iter μ l k)        = execIter μ l k
    alg (Join φ)            = execJoin φ
    alg (MkJoin φ p k)      = execMkJoin φ p k
    alg (Swap k)            = execSwap k
    alg (Make σ k)          = execMake σ k
    alg (Get σ k)           = execGet σ k
    alg (Put σ k)           = execPut σ k
    alg (LogEnter name k)   = execLogEnter name k
    alg (LogExit name k)    = execLogExit name k
    alg (MetaInstr m k)     = execMeta m k

execRet :: KOps o => MachineMonad s o (x : xs) n x a
execRet = return $! ret >>= resume

execCall :: KOps o => MVar x -> Machine s o (x : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
execCall μ (Machine k) = liftM2 (\mk sub γ@Γ{..} -> callWithContinuation sub (suspend mk γ) o hs) k (askSub μ)

execJump :: BoxOps o => MVar x -> MachineMonad s o '[] (Succ n) x a
execJump μ = askSub μ <&> \sub γ@Γ{..} -> callWithContinuation sub ret o hs

execPush :: (PositionOps o, Quapplicative q) => Defunc q o x -> Machine s o (x : xs) n r a -> MachineMonad s o xs n r a
execPush x (Machine k) = k <&> \m γ -> m (γ {xs = QCons (genDefunc x) (xs γ)})

execPop :: Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
execPop (Machine k) = k <&> \m γ -> m (γ {xs = tailQ (xs γ)})

execLift2 :: (PositionOps o, Quapplicative q) => Defunc q o (x -> y -> z) -> Machine s o (z : xs) n r a -> MachineMonad s o (y : x : xs) n r a
execLift2 f (Machine k) = k <&> \m γ -> m (γ {xs = let QCons y (QCons x xs') = xs γ in QCons (genDefunc2 f x y) xs'})

execSat :: (?ops :: InputOps o, PositionOps o, BoxOps o, Quapplicative q) => Defunc q o (Char -> Bool) -> Machine s o (Char : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
execSat p (Machine k) = do
  bankrupt <- asks isBankrupt
  hasChange <- asks hasCoin
  if | bankrupt -> maybeEmitCheck (Just 1) <$> k
     | hasChange -> maybeEmitCheck Nothing <$> local spendCoin k
     | otherwise -> trace "I have a piggy :)" $ local breakPiggy (maybeEmitCheck . Just <$> asks coins <*> local spendCoin k)
  where
    readChar bad k γ@Γ{..} = sat o (genDefunc p) (\o c -> k (γ {xs = QCons c xs, o = o})) bad
    maybeEmitCheck Nothing mk γ = readChar (raiseΓ γ) mk γ
    maybeEmitCheck (Just n) mk γ =
      [|| let bad' = $$(raiseΓ γ) in $$(emitLengthCheck n (readChar [||bad'||] mk γ) [||bad'||] γ)||]

execEmpt :: BoxOps o => MachineMonad s o xs (Succ n) r a
execEmpt = return $! raiseΓ

execCommit :: Machine s o xs n r a -> MachineMonad s o xs (Succ n) r a
execCommit (Machine k) = k <&> \mk γ -> let VCons _ hs' = hs γ in mk (γ {hs = hs'})

execCatch :: (?ops :: InputOps o, BoxOps o, HandlerOps o) => Machine s o xs (Succ n) r a -> Machine s o (o : xs) n r a -> MachineMonad s o xs n r a
execCatch (Machine k) (Machine h) = liftM2 (\mk mh γ -> setupHandlerΓ γ (buildHandlerΓ γ mh) mk) k h

execTell :: Machine s o (o : xs) n r a -> MachineMonad s o xs n r a
execTell (Machine k) = k <&> \mk γ -> mk (γ {xs = QCons (o γ) (xs γ)})

execSeek :: Machine s o xs n r a -> MachineMonad s o (o : xs) n r a
execSeek (Machine k) = k <&> \mk γ -> let QCons o xs' = xs γ in mk (γ {xs = xs', o=o})

execCase :: JoinBuilder o => Machine s o (x : xs) n r a -> Machine s o (y : xs) n r a -> MachineMonad s o (Either x y : xs) n r a
execCase (Machine p) (Machine q) = liftM2 (\mp mq γ ->
  let QCons e xs' = xs γ
  in [||case $$e of
    Left x -> $$(mp (γ {xs = QCons [||x||] xs'}))
    Right y  -> $$(mq (γ {xs = QCons [||y||] xs'}))||]) p q

execChoices :: (PositionOps o, Quapplicative q) => [Defunc q o (x -> Bool)] -> [Machine s o xs n r a] -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
execChoices fs ks (Machine def) = liftM2 (\mdef mks γ -> let QCons x xs' = xs γ in go x fs mks mdef (γ {xs = xs'}))
  def
  (forM ks getMachine)
  where
    go _ [] [] def γ = def γ
    go x (f:fs) (mk:mks) def γ = [||
        if $$(genDefunc1 f x) then $$(mk γ)
        else $$(go x fs mks def γ)
      ||]

execIter :: (RecBuilder o, ReturnOps o, HandlerOps o)
         => MVar Void -> Machine s o '[] One Void a -> Machine s o (o : xs) n r a
         -> MachineMonad s o xs n r a
execIter μ l (Machine h) = liftM2 (\mh ctx γ -> buildIter ctx μ l (buildHandlerΓ γ mh) (o γ)) h ask

execJoin :: KOps o => ΦVar x -> MachineMonad s o (x : xs) n r a
execJoin φ =
  do QJoin k <- asks ((DMap.! φ) . φs)
     return $! resume k

execMkJoin :: JoinBuilder o => ΦVar x -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a
execMkJoin = setupJoinPoint

execSwap :: Machine s o (x : y : xs) n r a -> MachineMonad s o (y : x : xs) n r a
execSwap (Machine k) = k <&> (\mk γ -> mk (γ {xs = let QCons y (QCons x xs') = xs γ in QCons x (QCons y xs')}))

execMake :: ΣVar x -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
execMake σ k = asks $! \ctx γ -> let QCons x xs' = xs γ in [||
    do ref <- newΣ $$x
       $$(run k (γ {xs = xs'}) (insertΣ σ [||ref||] ctx))
  ||]

execGet :: ΣVar x -> Machine s o (x : xs) n r a -> MachineMonad s o xs n r a
execGet σ (Machine k) =
  do !(QSTRef ref) <- askΣ σ
     k <&> \mk γ -> [||
         do x <- readΣ $$ref
            $$(mk (γ {xs = QCons [||x||] (xs γ)}))
       ||]

execPut :: ΣVar x -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
execPut σ (Machine k) =
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

execLogEnter :: (?ops :: InputOps o, LogHandler o) => String -> Machine s o xs (Succ (Succ n)) r a -> MachineMonad s o xs (Succ n) r a
execLogEnter name (Machine mk) =
  liftM2 (\k ctx γ -> [|| trace $$(preludeString name '>' γ ctx "") $$(setupHandlerΓ γ (logHandler name ctx γ) k)||])
    (local debugUp mk)
    ask

execLogExit :: (?ops :: InputOps o, PositionOps o, LogOps o) => String -> Machine s o xs n r a -> MachineMonad s o xs n r a
execLogExit name (Machine mk) =
  liftM2 (\k ctx γ -> [|| trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(k γ) ||])
    (local debugDown mk)
    ask

class (BoxOps o, PositionOps o, LogOps o) => LogHandler o where
  logHandler :: (?ops :: InputOps o) => String -> Ctx s o a -> Γ s o xs (Succ n) ks a -> Code o -> Code (H s o a)

#define deriveLogHandler(_o)                                                                                      \
instance LogHandler _o where                                                                                      \
{                                                                                                                 \
  logHandler name ctx γ _ = [||\(!o#) ->                                                                          \
      trace $$(preludeString name '<' (γ {o = [||$$box o#||]}) ctx (color Red " Fail")) ($$(raise @_o (hs γ)) o#) \
    ||]                                                                                                           \
};
inputInstances(deriveLogHandler)

execMeta :: (?ops :: InputOps o, PositionOps o, BoxOps o) => MetaInstr n -> Machine s o xs n r a -> MachineMonad s o xs n r a
execMeta (AddCoins coins) (Machine k) =
  do requiresPiggy <- asks hasCoin
     if requiresPiggy then local (storePiggy coins) k
     else local (giveCoins coins) k <&> \mk γ -> emitLengthCheck coins (mk γ) (raiseΓ γ) γ
execMeta (FreeCoins coins) (Machine k) = local (giveCoins coins) k
execMeta (RefundCoins coins) (Machine k) = local (giveCoins coins) k
execMeta (DrainCoins coins) (Machine k) = liftM2 (\n mk γ -> emitLengthCheck n (mk γ) (raiseΓ γ) γ) (asks ((coins -) . liquidate)) k

setupHandlerΓ :: Γ s o xs n r a
              -> (Code o -> Code (H s o a))
              -> (Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))
setupHandlerΓ γ h k = setupHandler (hs γ) (o γ) h (\hs -> k (γ {hs = hs}))

buildHandlerΓ :: (BoxOps o, HandlerOps o)
              => Γ s o xs n r a
              -> (Γ s o (o : xs) n r a -> Code (ST s (Maybe a)))
              -> Code o -> Code (H s o a)
buildHandlerΓ γ h = buildHandler (\c o -> h (γ {xs = QCons c (xs γ), o = o}))

raiseΓ :: BoxOps o => Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))
raiseΓ γ = let VCons h _ = hs γ in [|| $$h ($$unbox $$(o γ)) ||]

class BoxOps o => JoinBuilder o where
  setupJoinPoint :: ΦVar x -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a

#define deriveJoinBuilder(_o)                                      \
instance JoinBuilder _o where                                      \
{                                                                  \
  setupJoinPoint φ (Machine k) mx =                                   \
    liftM2 (\mk ctx γ -> [||                                       \
      let join x !(o# :: Unboxed _o) =                             \
        $$(mk (γ {xs = QCons [||x||] (xs γ), o = [||$$box o#||]})) \
      in $$(run mx γ (insertΦ φ [||join||] ctx))                   \
    ||]) (local voidCoins k) ask                                   \
};
inputInstances(deriveJoinBuilder)

class BoxOps o => RecBuilder o where
  buildIter :: ReturnOps o
            => Ctx s o a -> MVar Void -> Machine s o '[] One Void a
            -> (Code o -> Code (H s o a)) -> Code o -> Code (ST s (Maybe a))
  buildRec  :: Ctx s o a
            -> Machine s o '[] One r a
            -> Code (SubRoutine s o a r)

#define deriveRecBuilder(_o)                                                    \
instance RecBuilder _o where                                                    \
{                                                                               \
  buildIter ctx μ l h o = let bx = box in [||                                   \
      let handler !o# = $$(h [||$$bx o#||]);                                    \
          loop !o# =                                                            \
        $$(run l                                                                \
            (Γ QNil (noreturn @_o) [||$$bx o#||] (VCons [||handler o#||] VNil)) \
            (voidCoins (insertSub μ [||\_ (!o#) _ -> loop o#||] ctx)))            \
      in loop ($$unbox $$o)                                                     \
    ||];                                                                        \
  buildRec ctx k = let bx = box in [|| \(!ret) (!o#) h ->                       \
    $$(run k (Γ QNil [||ret||] [||$$bx o#||] (VCons [||h||] VNil)) ctx) ||]     \
};
inputInstances(deriveRecBuilder)

emitLengthCheck :: (?ops :: InputOps o, PositionOps o, BoxOps o) => Int -> Code (ST s (Maybe a)) -> Code (ST s (Maybe a)) -> Γ s o xs n r a -> Code (ST s (Maybe a))
emitLengthCheck 0 good _ _   = good
emitLengthCheck 1 good bad γ = [|| if $$more $$(o γ) then $$good else $$bad ||]
emitLengthCheck n good bad γ = [||
  if $$more ($$shiftRight $$(o γ) (n - 1)) then $$good
  else $$bad ||]

class BoxOps o => KOps o where
  suspend :: (Γ s o (x : xs) n r a -> Code (ST s (Maybe a))) -> Γ s o xs n r a -> Code (Cont s o a x)
  resume :: Code (Cont s o a x) -> Γ s o (x : xs) n r a -> Code (ST s (Maybe a))

#define deriveKOps(_o)                                                                         \
instance KOps _o where                                                                         \
{                                                                                              \
  suspend m γ = [|| \x (!o#) -> $$(m (γ {xs = QCons [||x||] (xs γ), o = [||$$box o#||]})) ||]; \
  resume k γ = let QCons x _ = xs γ in [|| $$k $$x ($$unbox $$(o γ)) ||]                       \
};
inputInstances(deriveKOps)

askSub :: MonadReader (Ctx s o a) m => MVar x -> m (QSubRoutine s o a x)
askSub μ = do
  msub <- asks (((DMap.lookup μ) . μs))
  case msub of
    Just sub -> return $! sub
    Nothing  -> throw (missingDependency μ)

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
