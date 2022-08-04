{-# LANGUAGE ImplicitParams,
             MultiWayIf,
             PatternSynonyms,
             RecordWildCards,
             TypeApplications #-}
module Parsley.Internal.Backend.Machine.Eval (eval) where

import Data.Dependent.Map                             (DMap)
import Data.Functor                                   ((<&>))
import Data.Void                                      (Void)
import Control.Monad                                  (forM, liftM2)
import Control.Monad.Reader                           (ask, asks, local)
import Control.Monad.ST                               (runST)
import Parsley.Internal.Backend.Machine.Defunc        (Defunc(LAM, SAME, INPUT), pattern FREEVAR, genDefunc, ap, ap2, _if)
import Parsley.Internal.Backend.Machine.Identifiers   (MVar(..), ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.InputOps      (InputDependant(..), PositionOps, BoxOps, LogOps, InputOps(InputOps))
import Parsley.Internal.Backend.Machine.Instructions  (Instr(..), MetaInstr(..), Access(..), PosSelector(..))
import Parsley.Internal.Backend.Machine.LetBindings   (LetBinding(..))
import Parsley.Internal.Backend.Machine.LetRecBuilder
import Parsley.Internal.Backend.Machine.Ops
import Parsley.Internal.Backend.Machine.Types.Coins   (willConsume)
import Parsley.Internal.Backend.Machine.Types.State
import Parsley.Internal.Common                        (Fix3, cata3, One, Code, Vec(..), Nat(..))
import Parsley.Internal.Core                          (CharPred)
import Parsley.Internal.Trace                         (Trace(trace))
import System.Console.Pretty                          (color, Color(Green))

import Parsley.Internal.Core.Lam (Lam(Abs))

import qualified Debug.Trace (trace)
import qualified Parsley.Internal.Backend.Machine.Instructions as Instructions (Handler(..))

eval :: forall o a. (Trace, Ops o) => Code (InputDependant o) -> LetBinding o a -> DMap MVar (LetBinding o) -> Code (Maybe a)
eval input binding fs = trace "EVALUATING TOP LEVEL" [|| runST $
  do let !(InputDependant next more offset) = $$input
     $$(let ?ops = InputOps [||more||] [||next||]
        in letRec fs
             nameLet
             (\μ exp rs names _meta -> buildRec μ rs (emptyCtx names) (readyMachine exp))
             (run (readyMachine (body binding)) (Γ Empty (halt @o) [||offset||] ([||1||], [||1||]) (VCons (fatal @o) VNil)) . emptyCtx))
  ||]
  where
    nameLet :: MVar x -> String
    nameLet (MVar i) = "sub" ++ show i

readyMachine :: (?ops :: InputOps o, Ops o, Trace) => Fix3 (Instr o) xs n r -> Machine s o a xs n r
readyMachine = cata3 (Machine . alg)
  where
    alg :: (?ops :: InputOps o, Ops o) => Instr o (Machine s o a) xs n r -> MachineMonad s o a xs n r
    alg Ret                 = evalRet
    alg (Call μ k)          = evalCall μ k
    alg (Jump μ)            = evalJump μ
    alg (Push x k)          = evalPush x k
    alg (Pop k)             = evalPop k
    alg (Lift2 f k)         = evalLift2 f k
    alg (Sat p k)           = evalSat p k
    alg Empt                = evalEmpt
    alg (Commit k)          = evalCommit k
    alg (Catch k h)         = evalCatch k (evalHandler h)
    alg (Tell k)            = evalTell k
    alg (Seek k)            = evalSeek k
    alg (Case p q)          = evalCase p q
    alg (Choices fs ks def) = evalChoices fs ks def
    alg (Iter μ l k)        = evalIter μ l (evalHandler k)
    alg (Join φ)            = evalJoin φ
    alg (MkJoin φ p k)      = evalMkJoin φ p k
    alg (Swap k)            = evalSwap k
    alg (Dup k)             = evalDup k
    alg (Make σ c k)        = evalMake σ c k
    alg (Get σ c k)         = evalGet σ c k
    alg (Put σ c k)         = evalPut σ c k
    alg (SelectPos sel k)   = evalSelectPos sel k
    alg (LogEnter name k)   = evalLogEnter name k
    alg (LogExit name k)    = evalLogExit name k
    alg (MetaInstr m k)     = evalMeta m k

evalRet :: ContOps o => MachineMonad s o a (x : xs) n x
evalRet = return $! retCont >>= resume

evalCall :: ContOps o => MVar x -> Machine s o a (x : xs) (Succ n) r -> MachineMonad s o a xs (Succ n) r
evalCall μ (Machine k) = liftM2 (\mk sub γ@Γ{..} -> callWithContinuation sub (suspend mk γ) input pos handlers) k (askSub μ)

evalJump :: ContOps o => MVar x -> MachineMonad s o a '[] (Succ n) x
evalJump μ = askSub μ <&> \sub Γ{..} -> callWithContinuation sub retCont input pos handlers

evalPush :: Defunc x -> Machine s o a (x : xs) n r -> MachineMonad s o a xs n r
evalPush x (Machine k) = k <&> \m γ -> m (γ {operands = Op x (operands γ)})

evalPop :: Machine s o a xs n r -> MachineMonad s o a (x : xs) n r
evalPop (Machine k) = k <&> \m γ -> m (γ {operands = let Op _ xs = operands γ in xs})

evalLift2 :: Defunc (x -> y -> z) -> Machine s o a (z : xs) n r -> MachineMonad s o a (y : x : xs) n r
evalLift2 f (Machine k) = k <&> \m γ -> m (γ {operands = let Op y (Op x xs) = operands γ in Op (ap2 f x y) xs})

evalSat :: (?ops :: InputOps o, PositionOps o, BoxOps o, HandlerOps o, Trace) => CharPred -> Machine s o a (Char : xs) (Succ n) r -> MachineMonad s o a xs (Succ n) r
evalSat p (Machine k) = do
  bankrupt <- asks isBankrupt
  hasChange <- asks hasCoin
  if | bankrupt -> maybeEmitCheck (Just 1) <$> k
     | hasChange -> maybeEmitCheck Nothing <$> local spendCoin k
     | otherwise -> trace "I have a piggy :)" $ local breakPiggy (asks ((maybeEmitCheck . Just) . coins) <*> local spendCoin k)
  where
    maybeEmitCheck Nothing mk γ = sat p mk (raise γ) γ
    maybeEmitCheck (Just n) mk γ =
      [|| let bad = $$(raise γ) in $$(emitLengthCheck n (sat p mk [||bad||]) [||bad||] γ)||]

evalEmpt :: (BoxOps o, HandlerOps o) => MachineMonad s o a xs (Succ n) r
evalEmpt = return $! raise

evalCommit :: Machine s o a xs n r -> MachineMonad s o a xs (Succ n) r
evalCommit (Machine k) = k <&> \mk γ -> let VCons _ hs = handlers γ in mk (γ {handlers = hs})

evalCatch :: (BoxOps o, HandlerOps o) => Machine s o a xs (Succ n) r -> Machine s o a (o : xs) n r -> MachineMonad s o a xs n r
evalCatch (Machine k) (Machine h) = liftM2 (\mk mh γ -> setupHandler γ (buildHandler γ mh) mk) k h

evalHandler :: PositionOps o => Instructions.Handler o (Machine s o a) (o : xs) n r -> Machine s o a (o : xs) n r
evalHandler (Instructions.Always _ k) = k
evalHandler (Instructions.Same _ yes _ no) =
  Machine (evalDup (
    Machine (evalTell (
      Machine (evalLift2 SAME (
        Machine (evalChoices [LAM (Abs id)] [Machine (evalPop yes)] no)))))))

evalTell :: Machine s o a (o : xs) n r -> MachineMonad s o a xs n r
evalTell (Machine k) = k <&> \mk γ -> mk (γ {operands = Op (INPUT (input γ) (pos γ)) (operands γ)})

evalSeek :: Machine s o a xs n r -> MachineMonad s o a (o : xs) n r
evalSeek (Machine k) = k <&> \mk γ -> let Op (INPUT input pos) xs = operands γ in mk (γ {operands = xs, input = input, pos = pos})

evalCase :: Machine s o a (x : xs) n r -> Machine s o a (y : xs) n r -> MachineMonad s o a (Either x y : xs) n r
evalCase (Machine p) (Machine q) = liftM2 (\mp mq γ ->
  let Op e xs = operands γ
  in [||case $$(genDefunc e) of
    Left x -> $$(mp (γ {operands = Op (FREEVAR [||x||]) xs}))
    Right y  -> $$(mq (γ {operands = Op (FREEVAR [||y||]) xs}))||]) p q

evalChoices :: [Defunc (x -> Bool)] -> [Machine s o a xs n r] -> Machine s o a xs n r -> MachineMonad s o a (x : xs) n r
evalChoices fs ks (Machine def) = liftM2 (\mdef mks γ -> let Op x xs = operands γ in go x fs mks mdef (γ {operands = xs}))
  def
  (forM ks getMachine)
  where
    go x (f:fs) (mk:mks) def γ = _if (ap f x) (mk γ) (go x fs mks def γ)
    go _ _ _ def γ = def γ

evalIter :: (RecBuilder o, ReturnOps o, HandlerOps o)
         => MVar Void -> Machine s o a '[] One Void -> Machine s o a (o : xs) n r
         -> MachineMonad s o a xs n r
evalIter μ l (Machine h) = liftM2 (\mh ctx γ -> buildIter ctx μ l (buildHandler γ mh) (input γ) (pos γ)) h ask

evalJoin :: ContOps o => ΦVar x -> MachineMonad s o a (x : xs) n r
evalJoin φ = askΦ φ <&> resume

evalMkJoin :: JoinBuilder o => ΦVar x -> Machine s o a (x : xs) n r -> Machine s o a xs n r -> MachineMonad s o a xs n r
evalMkJoin = setupJoinPoint

evalSwap :: Machine s o a (x : y : xs) n r -> MachineMonad s o a (y : x : xs) n r
evalSwap (Machine k) = k <&> \mk γ -> mk (γ {operands = let Op y (Op x xs) = operands γ in Op x (Op y xs)})

evalDup :: Machine s o a (x : x : xs) n r -> MachineMonad s o a (x : xs) n r
evalDup (Machine k) = k <&> \mk γ ->
  let Op x xs = operands γ
  in dup x $ \dupx -> mk (γ {operands = Op dupx (Op dupx xs)})

evalMake :: ΣVar x -> Access -> Machine s o a xs n r -> MachineMonad s o a (x : xs) n r
evalMake σ a k = asks $ \ctx γ ->
  let Op x xs = operands γ
  in newΣ σ a x (run k (γ {operands = xs})) ctx

evalGet :: ΣVar x -> Access -> Machine s o a (x : xs) n r -> MachineMonad s o a xs n r
evalGet σ a k = asks $ \ctx γ -> readΣ σ a (\x -> run k (γ {operands = Op x (operands γ)})) ctx

evalPut :: ΣVar x -> Access -> Machine s o a xs n r -> MachineMonad s o a (x : xs) n r
evalPut σ a k = asks $ \ctx γ ->
  let Op x xs = operands γ
  in writeΣ σ a x (run k (γ {operands = xs})) ctx

evalSelectPos :: PosSelector -> Machine s o a (Int : xs) n r -> MachineMonad s o a xs n r
evalSelectPos Line (Machine k) = k <&> \m γ -> m (γ {operands = Op (FREEVAR (fst (pos γ))) (operands γ)})
evalSelectPos Col (Machine k) = k <&> \m γ -> m (γ {operands = Op (FREEVAR (snd (pos γ))) (operands γ)})

evalLogEnter :: (?ops :: InputOps o, LogHandler o) => String -> Machine s o a xs (Succ (Succ n)) r -> MachineMonad s o a xs (Succ n) r
evalLogEnter name (Machine mk) =
  liftM2 (\k ctx γ -> [|| Debug.Trace.trace $$(preludeString name '>' γ ctx "") $$(setupHandler γ (logHandler name ctx γ) k)||])
    (local debugUp mk)
    ask

evalLogExit :: (?ops :: InputOps o, PositionOps o, LogOps o) => String -> Machine s o a xs n r -> MachineMonad s o a xs n r
evalLogExit name (Machine mk) =
  liftM2 (\k ctx γ -> [|| Debug.Trace.trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(k γ) ||])
    (local debugDown mk)
    ask

evalMeta :: (?ops :: InputOps o, PositionOps o, BoxOps o, HandlerOps o) => MetaInstr n -> Machine s o a xs n r -> MachineMonad s o a xs n r
evalMeta (AddCoins coins') (Machine k) =
  do requiresPiggy <- asks hasCoin
     let coins = willConsume coins'
     if requiresPiggy then local (storePiggy coins) k
     else local (giveCoins coins) k <&> \mk γ -> emitLengthCheck coins mk (raise γ) γ
evalMeta (RefundCoins coins) (Machine k) = local (giveCoins (willConsume coins)) k
evalMeta (DrainCoins coins) (Machine k) =
  -- If there are enough coins left to cover the cost, no length check is required
  -- Otherwise, the full length check is required (partial doesn't work until the right offset is reached)
  liftM2 (\canAfford mk γ -> if canAfford then mk γ else emitLengthCheck (willConsume coins) mk (raise γ) γ)
         (asks (canAfford (willConsume coins)))
         k
evalMeta (GiveBursary coins) (Machine k) = local (giveCoins (willConsume coins)) k
evalMeta (PrefetchChar check) (Machine k) =
  do requiresPiggy <- asks hasCoin
     if | not check     -> k
        | requiresPiggy -> local (storePiggy 1) k
        | otherwise     -> local (giveCoins 1) k <&> \mk γ -> emitLengthCheck 1 mk (raise γ) γ
evalMeta BlockCoins (Machine k) = k
