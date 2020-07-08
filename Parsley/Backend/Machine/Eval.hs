{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             TemplateHaskell,
             ScopedTypeVariables,
             RecordWildCards,
             ImplicitParams,
             TypeApplications,
             BangPatterns,
             MultiWayIf #-}
module Parsley.Backend.Machine.Eval (eval, Ops) where

import Parsley.Backend.Machine.State
import Parsley.Backend.Machine.Ops
import Parsley.Backend.Machine.Instructions
import Parsley.Backend.Machine.LetRecBuilder
import Parsley.Common.Identifiers
import Parsley.Common.Vec         (Vec(..))
import Parsley.Backend.Machine.InputImpl (InputDependant(..), PositionOps, BoxOps, LogOps, InputOps(InputOps))
import Parsley.Common.Indexed     (Fix4, cata4, Nat(..), One)
import Parsley.Common.Utils       (Code)
import Data.Dependent.Map         (DMap)
import Parsley.Backend.Machine.Defunc (Defunc, genDefunc, genDefunc1, genDefunc2)
import Data.Functor               ((<&>))
import Data.Void                  (Void)
import Control.Monad              (forM, liftM2)
import Control.Monad.ST           (ST, runST)
import Control.Monad.Reader       (ask, asks, local)
import Debug.Trace                (trace)
import System.Console.Pretty      (color, Color(Green))

eval :: forall o s a. Ops o => Code (InputDependant o) -> (Program o a, DMap MVar (LetBinding o a)) -> Code (Maybe a)
eval input (Program !p, fs) = trace ("EVALUATING: " ++ show p) [|| runST $
  do let !(InputDependant next more offset) = $$input
     $$(let ?ops = InputOps [||more||] [||next||]
        in letRec fs
             nameLet
             QSubRoutine
             (\(LetBinding k) names -> buildRec (emptyCtx {μs = names}) (readyMachine k))
             (\names -> run (readyMachine p) (Γ Empty (halt @o) [||offset||] (VCons (fatal @o) VNil)) (emptyCtx {μs = names})))
  ||]
  where
    nameLet :: MVar x -> LetBinding o a x -> String
    nameLet (MVar i) _ = "sub" ++ show i

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
    maybeEmitCheck Nothing mk γ = readChar (raise γ) mk γ
    maybeEmitCheck (Just n) mk γ =
      [|| let bad = $$(raise γ) in $$(emitLengthCheck n (readChar [||bad||] mk γ) [||bad||] γ)||]

evalEmpt :: BoxOps o => MachineMonad s o xs (Succ n) r a
evalEmpt = return $! raise

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

evalMeta :: (?ops :: InputOps o, PositionOps o, BoxOps o) => MetaInstr n -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalMeta (AddCoins coins) (Machine k) =
  do requiresPiggy <- asks hasCoin
     if requiresPiggy then local (storePiggy coins) k
     else local (giveCoins coins) k <&> \mk γ -> emitLengthCheck coins (mk γ) (raise γ) γ
evalMeta (FreeCoins coins) (Machine k) = local (giveCoins coins) k
evalMeta (RefundCoins coins) (Machine k) = local (giveCoins coins) k
evalMeta (DrainCoins coins) (Machine k) = liftM2 (\n mk γ -> emitLengthCheck n (mk γ) (raise γ) γ) (asks ((coins -) . liquidate)) k