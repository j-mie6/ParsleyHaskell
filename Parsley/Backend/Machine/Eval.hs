{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             RankNTypes,
             BangPatterns,
             FlexibleInstances,
             MagicHash,
             TemplateHaskell,
             ScopedTypeVariables,
             RecordWildCards,
             ConstraintKinds,
             CPP,
             ImplicitParams,
             TypeApplications,
             MultiWayIf,
             ConstrainedClassMethods #-}
module Parsley.Backend.Machine.Eval where

import Parsley.Backend.Machine.State
import Parsley.Backend.Machine.Ops
import Parsley.Backend.Machine.Instructions
import Parsley.Common.Identifiers
import Parsley.Common.Vec         (Vec(..))
import Parsley.Backend.Machine.InputImpl      (InputDependant(..), PositionOps(..), BoxOps(..), LogOps(..), InputOps(..), next, more, Unboxed, OffWith, UnpackedLazyByteString, Stream)
import Parsley.Common.Indexed     (Fix4, cata4, Nat(..))
import Parsley.Common.Utils       (Code)
import Parsley.Backend.Machine.Defunc (Defunc, genDefunc, genDefunc1, genDefunc2)
import Data.Functor               ((<&>))
import Data.Void                  (Void)
import Control.Monad              (forM, liftM2)
import Control.Monad.ST           (ST, runST)
import Control.Monad.Reader       (ask, asks, local)
import Data.Dependent.Map         (DMap, DSum(..))
import Data.GADT.Compare          (GCompare)
import Debug.Trace                (trace)
import System.Console.Pretty      (color, Color(Green, White, Red, Blue))
import Data.Text                  (Text)
import Data.Functor.Const         (Const(..), getConst)
import Language.Haskell.TH        (runQ, Q, newName, Name)
import Language.Haskell.TH.Syntax (unTypeQ, unsafeTExpCoerce, Exp(VarE, LetE), Dec(FunD), Clause(Clause), Body(NormalB))
import qualified Data.Dependent.Map as DMap ((!), map, toList, traverseWithKey)

#define inputInstances(derivation) \
derivation(Int)                    \
derivation((OffWith [Char]))       \
derivation((OffWith Stream))       \
derivation(UnpackedLazyByteString) \
derivation(Text)

type Ops o = (LogHandler o, KOps o, HandlerOps o, JoinBuilder o, RecBuilder o, ReturnOps o, PositionOps o, BoxOps o, LogOps o)

eval :: forall o s a. Ops o => Code (InputDependant o) -> (Program o a, DMap MVar (LetBinding o a)) -> Code (Maybe a)
eval input (Program !p, fs) = trace ("EVALUATING: " ++ show p) [|| runST $
  do let !(InputDependant next more offset) = $$input
     $$(let ?ops = InputOps [||more||] [||next||]
        in scopeBindings fs
             nameLet
             QSubRoutine
             (\(LetBinding k) names -> buildRec (emptyCtx {μs = names}) (readyMachine k))
             (\names -> run (readyMachine p) (Γ Empty (halt @o) [||offset||] (VCons (fatal @o) VNil)) (emptyCtx {μs = names})))
  ||]

nameLet :: MVar x -> LetBinding o a x -> String
nameLet (MVar i) _ = "sub" ++ show i

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

readyMachine :: (?ops :: InputOps o, Ops o) => Fix4 (Instr o) xs n r a -> Machine s o xs n r a
readyMachine = cata4 (Machine . alg)
  where
    alg :: (?ops :: InputOps o, Ops o) => Instr o (Machine s o) xs n r a -> MachineMonad s o xs n r a
    alg Ret                 = evalRet
    alg (Call μ k)          = evalCall μ k
    alg (Jump μ)            = evalJump μ
    alg (Push x k)          = evalPush x k
    alg (Pop k)             = evalPop k
    alg (Lift2 f k)         = evalLift2 f k
    alg (Sat p k)           = evalSat p k
    alg Empt                = evalEmpt
    alg (Commit k)          = evalCommit k
    alg (Catch k h)         = evalCatch k h
    alg (Tell k)            = evalTell k
    alg (Seek k)            = evalSeek k
    alg (Case p q)          = evalCase p q
    alg (Choices fs ks def) = evalChoices fs ks def
    alg (Iter μ l k)        = evalIter μ l k
    alg (Join φ)            = evalJoin φ
    alg (MkJoin φ p k)      = evalMkJoin φ p k
    alg (Swap k)            = evalSwap k
    alg (Dup k)             = evalDup k
    alg (Make σ k)          = evalMake σ k
    alg (Get σ k)           = evalGet σ k
    alg (Put σ k)           = evalPut σ k
    alg (LogEnter name k)   = evalLogEnter name k
    alg (LogExit name k)    = evalLogExit name k
    alg (MetaInstr m k)     = evalMeta m k

evalRet :: KOps o => MachineMonad s o (x : xs) n x a
evalRet = return $! retCont >>= resume

evalCall :: KOps o => MVar x -> Machine s o (x : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
evalCall μ (Machine k) = liftM2 (\mk sub γ@Γ{..} -> callWithContinuation sub (suspend mk γ) input handlers) k (askSub μ)

evalJump :: BoxOps o => MVar x -> MachineMonad s o '[] (Succ n) x a
evalJump μ = askSub μ <&> \sub γ@Γ{..} -> callWithContinuation sub retCont input handlers

evalPush :: Defunc x -> Machine s o (x : xs) n r a -> MachineMonad s o xs n r a
evalPush x (Machine k) = k <&> \m γ -> m (γ {operands = Op (genDefunc x) (operands γ)})

evalPop :: Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalPop (Machine k) = k <&> \m γ -> m (γ {operands = let Op _ xs = operands γ in xs})

evalLift2 :: Defunc (x -> y -> z) -> Machine s o (z : xs) n r a -> MachineMonad s o (y : x : xs) n r a
evalLift2 f (Machine k) = k <&> \m γ -> m (γ {operands = let Op y (Op x xs) = operands γ in Op (genDefunc2 f x y) xs})

evalSat :: (?ops :: InputOps o, PositionOps o, BoxOps o) => Defunc (Char -> Bool) -> Machine s o (Char : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
evalSat p (Machine k) = do
  bankrupt <- asks isBankrupt
  hasChange <- asks hasCoin
  if | bankrupt -> maybeEmitCheck (Just 1) <$> k
     | hasChange -> maybeEmitCheck Nothing <$> local spendCoin k
     | otherwise -> trace "I have a piggy :)" $ local breakPiggy (maybeEmitCheck . Just <$> asks coins <*> local spendCoin k)
  where
    readChar bad k γ@Γ{..} = sat input (genDefunc p) (\c input' -> k (γ {operands = Op c operands, input = input'})) bad
    maybeEmitCheck Nothing mk γ = readChar (raiseΓ γ) mk γ
    maybeEmitCheck (Just n) mk γ =
      [|| let bad = $$(raiseΓ γ) in $$(emitLengthCheck n (readChar [||bad||] mk γ) [||bad||] γ)||]

evalEmpt :: BoxOps o => MachineMonad s o xs (Succ n) r a
evalEmpt = return $! raiseΓ

evalCommit :: Machine s o xs n r a -> MachineMonad s o xs (Succ n) r a
evalCommit (Machine k) = k <&> \mk γ -> let VCons _ hs = handlers γ in mk (γ {handlers = hs})

evalCatch :: (?ops :: InputOps o, BoxOps o, HandlerOps o) => Machine s o xs (Succ n) r a -> Machine s o (o : xs) n r a -> MachineMonad s o xs n r a
evalCatch (Machine k) (Machine h) = liftM2 (\mk mh γ -> setupHandlerΓ γ (buildHandlerΓ γ mh) mk) k h

evalTell :: Machine s o (o : xs) n r a -> MachineMonad s o xs n r a
evalTell (Machine k) = k <&> \mk γ -> mk (γ {operands = Op (input γ) (operands γ)})

evalSeek :: Machine s o xs n r a -> MachineMonad s o (o : xs) n r a
evalSeek (Machine k) = k <&> \mk γ -> let Op input xs = operands γ in mk (γ {operands = xs, input = input})

evalCase :: JoinBuilder o => Machine s o (x : xs) n r a -> Machine s o (y : xs) n r a -> MachineMonad s o (Either x y : xs) n r a
evalCase (Machine p) (Machine q) = liftM2 (\mp mq γ ->
  let Op e xs = operands γ
  in [||case $$e of
    Left x -> $$(mp (γ {operands = Op [||x||] xs}))
    Right y  -> $$(mq (γ {operands = Op [||y||] xs}))||]) p q

evalChoices :: [Defunc (x -> Bool)] -> [Machine s o xs n r a] -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalChoices fs ks (Machine def) = liftM2 (\mdef mks γ -> let Op x xs = operands γ in go x fs mks mdef (γ {operands = xs}))
  def
  (forM ks getMachine)
  where
    go _ [] [] def γ = def γ
    go x (f:fs) (mk:mks) def γ = [||
        if $$(genDefunc1 f x) then $$(mk γ)
        else $$(go x fs mks def γ)
      ||]

evalIter :: (RecBuilder o, ReturnOps o, HandlerOps o)
         => MVar Void -> Machine s o '[] One Void a -> Machine s o (o : xs) n r a
         -> MachineMonad s o xs n r a
evalIter μ l (Machine h) = liftM2 (\mh ctx γ -> buildIter ctx μ l (buildHandlerΓ γ mh) (input γ)) h ask

evalJoin :: KOps o => ΦVar x -> MachineMonad s o (x : xs) n r a
evalJoin φ = askΦ φ <&> resume

evalMkJoin :: JoinBuilder o => ΦVar x -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalMkJoin = setupJoinPoint

evalSwap :: Machine s o (x : y : xs) n r a -> MachineMonad s o (y : x : xs) n r a
evalSwap (Machine k) = k <&> \mk γ -> mk (γ {operands = let Op y (Op x xs) = operands γ in Op x (Op y xs)})

evalDup :: Machine s o (x : x : xs) n r a -> MachineMonad s o (x : xs) n r a
evalDup (Machine k) = k <&> \mk γ -> let Op x xs = operands γ in [||
    let dupx = $$x
    in $$(mk (γ {operands = Op [||dupx||] (Op [||dupx||] xs)}))
  ||]

evalMake :: ΣVar x -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalMake σ k = asks $! \ctx γ -> let Op x xs = operands γ in [||
    do ref <- newΣ $$x
       $$(run k (γ {operands = xs}) (insertΣ σ [||ref||] ctx))
  ||]

evalGet :: ΣVar x -> Machine s o (x : xs) n r a -> MachineMonad s o xs n r a
evalGet σ (Machine k) = liftM2 (\mk ref γ -> [||
    do x <- readΣ $$ref
       $$(mk (γ {operands = Op [||x||] (operands γ)}))
  ||]) k (askΣ σ)

evalPut :: ΣVar x -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalPut σ (Machine k) = liftM2 (\mk ref γ ->
    let Op x xs = operands γ in [||
    do writeΣ $$ref $$x
       $$(mk (γ {operands = xs}))
  ||]) k (askΣ σ)

preludeString :: (?ops :: InputOps o, PositionOps o, LogOps o) => String -> Char -> Γ s o xs n r a -> Ctx s o a -> String -> Code String
preludeString name dir γ ctx ends = [|| concat [$$prelude, $$eof, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    offset     = input γ
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

evalLogEnter :: (?ops :: InputOps o, LogHandler o) => String -> Machine s o xs (Succ (Succ n)) r a -> MachineMonad s o xs (Succ n) r a
evalLogEnter name (Machine mk) =
  liftM2 (\k ctx γ -> [|| trace $$(preludeString name '>' γ ctx "") $$(setupHandlerΓ γ (logHandler name ctx γ) k)||])
    (local debugUp mk)
    ask

evalLogExit :: (?ops :: InputOps o, PositionOps o, LogOps o) => String -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalLogExit name (Machine mk) =
  liftM2 (\k ctx γ -> [|| trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(k γ) ||])
    (local debugDown mk)
    ask

class (BoxOps o, PositionOps o, LogOps o) => LogHandler o where
  logHandler :: (?ops :: InputOps o) => String -> Ctx s o a -> Γ s o xs (Succ n) ks a -> Code o -> Code (Handler s o a)

#define deriveLogHandler(_o)                                                                                                \
instance LogHandler _o where                                                                                                \
{                                                                                                                           \
  logHandler name ctx γ _ = [||\(!o#) ->                                                                                    \
      trace $$(preludeString name '<' (γ {input = [||$$box o#||]}) ctx (color Red " Fail")) ($$(raise @_o (handlers γ)) o#) \
    ||]                                                                                                                     \
};
inputInstances(deriveLogHandler)

evalMeta :: (?ops :: InputOps o, PositionOps o, BoxOps o) => MetaInstr n -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalMeta (AddCoins coins) (Machine k) =
  do requiresPiggy <- asks hasCoin
     if requiresPiggy then local (storePiggy coins) k
     else local (giveCoins coins) k <&> \mk γ -> emitLengthCheck coins (mk γ) (raiseΓ γ) γ
evalMeta (FreeCoins coins) (Machine k) = local (giveCoins coins) k
evalMeta (RefundCoins coins) (Machine k) = local (giveCoins coins) k
evalMeta (DrainCoins coins) (Machine k) = liftM2 (\n mk γ -> emitLengthCheck n (mk γ) (raiseΓ γ) γ) (asks ((coins -) . liquidate)) k

setupHandlerΓ :: Γ s o xs n r a
              -> (Code o -> Code (Handler s o a))
              -> (Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))
setupHandlerΓ γ h k = setupHandler (handlers γ) (input γ) h (\hs -> k (γ {handlers = hs}))

buildHandlerΓ :: (BoxOps o, HandlerOps o)
              => Γ s o xs n r a
              -> (Γ s o (o : xs) n r a -> Code (ST s (Maybe a)))
              -> Code o -> Code (Handler s o a)
buildHandlerΓ γ h = buildHandler (\c o -> h (γ {operands = Op c (operands γ), input = o}))

raiseΓ :: BoxOps o => Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))
raiseΓ γ = let VCons h _ = handlers γ in [|| $$h ($$unbox $$(input γ)) ||]

class BoxOps o => JoinBuilder o where
  setupJoinPoint :: ΦVar x -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a

#define deriveJoinBuilder(_o)                                                   \
instance JoinBuilder _o where                                                   \
{                                                                               \
  setupJoinPoint φ (Machine k) mx =                                             \
    liftM2 (\mk ctx γ -> [||                                                    \
      let join x !(o# :: Unboxed _o) =                                          \
        $$(mk (γ {operands = Op [||x||] (operands γ), input = [||$$box o#||]})) \
      in $$(run mx γ (insertΦ φ [||join||] ctx))                                \
    ||]) (local voidCoins k) ask                                                \
};
inputInstances(deriveJoinBuilder)

class BoxOps o => RecBuilder o where
  buildIter :: ReturnOps o
            => Ctx s o a -> MVar Void -> Machine s o '[] One Void a
            -> (Code o -> Code (Handler s o a)) -> Code o -> Code (ST s (Maybe a))
  buildRec  :: Ctx s o a
            -> Machine s o '[] One r a
            -> Code (SubRoutine s o a r)

#define deriveRecBuilder(_o)                                                     \
instance RecBuilder _o where                                                     \
{                                                                                \
  buildIter ctx μ l h o = let bx = box in [||                                    \
      let handler !o# = $$(h [||$$bx o#||]);                                     \
          loop !o# =                                                             \
        $$(run l                                                                 \
            (Γ Empty (noreturn @_o) [||$$bx o#||] (VCons [||handler o#||] VNil)) \
            (voidCoins (insertSub μ [||\_ (!o#) _ -> loop o#||] ctx)))           \
      in loop ($$unbox $$o)                                                      \
    ||];                                                                         \
  buildRec ctx k = let bx = box in [|| \(!ret) (!o#) h ->                        \
    $$(run k (Γ Empty [||ret||] [||$$bx o#||] (VCons [||h||] VNil)) ctx) ||]     \
};
inputInstances(deriveRecBuilder)

emitLengthCheck :: (?ops :: InputOps o, PositionOps o, BoxOps o) => Int -> Code (ST s (Maybe a)) -> Code (ST s (Maybe a)) -> Γ s o xs n r a -> Code (ST s (Maybe a))
emitLengthCheck 0 good _ _   = good
emitLengthCheck 1 good bad γ = [|| if $$more $$(input γ) then $$good else $$bad ||]
emitLengthCheck n good bad γ = [||
  if $$more ($$shiftRight $$(input γ) (n - 1)) then $$good
  else $$bad ||]

class BoxOps o => KOps o where
  suspend :: (Γ s o (x : xs) n r a -> Code (ST s (Maybe a))) -> Γ s o xs n r a -> Code (Cont s o a x)
  resume :: Code (Cont s o a x) -> Γ s o (x : xs) n r a -> Code (ST s (Maybe a))

#define deriveKOps(_o)                                                          \
instance KOps _o where                                                          \
{                                                                               \
  suspend m γ = [|| \x (!o#) -> $$(m (γ {operands = Op [||x||] (operands γ),    \
                                         input = [||$$box o#||]})) ||];         \
  resume k γ = let Op x _ = operands γ in [|| $$k $$x ($$unbox $$(input γ)) ||] \
};
inputInstances(deriveKOps)
