{-# LANGUAGE ImplicitParams,
             MultiWayIf,
             PatternSynonyms,
             RecordWildCards,
             TypeApplications,
             UnboxedTuples #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Eval
Description : Entry point for the evaluator
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module exports the `eval` functions used to convert a machine into code.

@since 1.0.0.0
-}
module Parsley.Internal.Backend.Machine.Eval (eval) where

import Data.Dependent.Map                             (DMap)
import Data.Functor                                   ((<&>))
import Data.Void                                      (Void)
import Control.Monad                                  (forM, liftM2, liftM3)
import Control.Monad.Reader                           (ask, asks, local)
import Control.Monad.ST                               (runST)
import Parsley.Internal.Backend.Machine.Defunc        (Defunc(OFFSET), pattern FREEVAR, genDefunc, ap, ap2, _if)
import Parsley.Internal.Backend.Machine.Identifiers   (MVar(..), ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.InputOps      (InputDependant, InputOps(InputOps))
import Parsley.Internal.Backend.Machine.InputRep      (Rep)
import Parsley.Internal.Backend.Machine.Instructions  (Instr(..), MetaInstr(..), Access(..), Handler(..))
import Parsley.Internal.Backend.Machine.LetBindings   (LetBinding(body))
import Parsley.Internal.Backend.Machine.LetRecBuilder (letRec)
import Parsley.Internal.Backend.Machine.Ops
import Parsley.Internal.Backend.Machine.Types         (MachineMonad, Machine(..), run)
import Parsley.Internal.Backend.Machine.Types.Context
import Parsley.Internal.Backend.Machine.Types.Coins   (willConsume)
import Parsley.Internal.Backend.Machine.Types.Offset  (mkOffset, offset)
import Parsley.Internal.Backend.Machine.Types.State   (Γ(..), OpStack(..))
import Parsley.Internal.Common                        (Fix4, cata4, One, Code, Vec(..), Nat(..))
import Parsley.Internal.Trace                         (Trace(trace))
import System.Console.Pretty                          (color, Color(Green))

import qualified Debug.Trace (trace)

{-|
This function performs the evaluation on the top-level let-bound parser to convert it into code.

@since 1.0.0.0
-}
eval :: forall o a. (Trace, Ops o)
     => Code (InputDependant (Rep o)) -- ^ The input as provided by the user.
     -> LetBinding o a a              -- ^ The binding to be generated.
     -> DMap MVar (LetBinding o a)    -- ^ The map of all other required bindings.
     -> Code (Maybe a)                -- ^ The code for this parser.
eval input binding fs = trace "EVALUATING TOP LEVEL" [|| runST $
  do let !(# next, more, offset #) = $$input
     $$(let ?ops = InputOps [||more||] [||next||]
        in letRec fs
             nameLet
             (\μ exp rs names -> buildRec μ rs (emptyCtx names) (readyMachine exp))
             (run (readyMachine (body binding)) (Γ Empty halt (mkOffset [||offset||] 0) (VCons fatal VNil)) . nextUnique . emptyCtx))
  ||]
  where
    nameLet :: MVar x -> String
    nameLet (MVar i) = "sub" ++ show i

readyMachine :: (?ops :: InputOps (Rep o), Ops o, Trace) => Fix4 (Instr o) xs n r a -> Machine s o xs n r a
readyMachine = cata4 (Machine . alg)
  where
    alg :: (?ops :: InputOps (Rep o), Ops o) => Instr o (Machine s o) xs n r a -> MachineMonad s o xs n r a
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
    alg (Make σ c k)        = evalMake σ c k
    alg (Get σ c k)         = evalGet σ c k
    alg (Put σ c k)         = evalPut σ c k
    alg (LogEnter name k)   = evalLogEnter name k
    alg (LogExit name k)    = evalLogExit name k
    alg (MetaInstr m k)     = evalMeta m k

evalRet :: MachineMonad s o (x : xs) n x a
evalRet = return $! retCont >>= resume

evalCall :: forall s o a x xs n r. MarshalOps o => MVar x -> Machine s o (x : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
evalCall μ (Machine k) = freshUnique $ \u -> liftM2 (callCC u) (askSub μ) k

evalJump :: forall s o a x n. MarshalOps o => MVar x -> MachineMonad s o '[] (Succ n) x a
evalJump μ = askSub μ <&> \sub Γ{..} -> callWithContinuation @o sub retCont (offset input) handlers

evalPush :: Defunc x -> Machine s o (x : xs) n r a -> MachineMonad s o xs n r a
evalPush x (Machine k) = k <&> \m γ -> m (γ {operands = Op x (operands γ)})

evalPop :: Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalPop (Machine k) = k <&> \m γ -> m (γ {operands = let Op _ xs = operands γ in xs})

evalLift2 :: Defunc (x -> y -> z) -> Machine s o (z : xs) n r a -> MachineMonad s o (y : x : xs) n r a
evalLift2 f (Machine k) = k <&> \m γ -> m (γ {operands = let Op y (Op x xs) = operands γ in Op (ap2 f x y) xs})

evalSat :: (?ops :: InputOps (Rep o), PositionOps (Rep o), Trace) => Defunc (Char -> Bool) -> Machine s o (Char : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
evalSat p (Machine k) = do
  bankrupt <- asks isBankrupt
  hasChange <- asks hasCoin
  if | bankrupt -> maybeEmitCheck (Just 1) <$> k
     | hasChange -> maybeEmitCheck Nothing <$> local spendCoin k
     | otherwise -> trace "I have a piggy :)" $ local breakPiggy (asks ((maybeEmitCheck . Just) . coins) <*> local spendCoin k)
  where
    maybeEmitCheck Nothing mk γ = sat (ap p) mk (raise γ) γ
    maybeEmitCheck (Just n) mk γ =
      --[|| let bad = $$(raise γ) in $$(emitLengthCheck n (sat (ap p) mk [||bad||]) [||bad||] γ)||]
      emitLengthCheck n (sat (ap p) mk (raise γ) γ) (raise γ) (input γ)

evalEmpt :: MachineMonad s o xs (Succ n) r a
evalEmpt = return $! raise

evalCommit :: Machine s o xs n r a -> MachineMonad s o xs (Succ n) r a
evalCommit (Machine k) = k <&> \mk γ -> let VCons _ hs = handlers γ in mk (γ {handlers = hs})

evalCatch :: (PositionOps (Rep o), HandlerOps o) => Machine s o xs (Succ n) r a -> Handler o (Machine s o) (o : xs) n r a -> MachineMonad s o xs n r a
evalCatch (Machine k) h = freshUnique $ \u -> case h of
  Always (Machine h) ->
    liftM2 (\mk mh γ -> bindAlwaysHandler γ (buildHandler γ mh u) mk) k h
  Same (Machine yes) (Machine no) ->
    liftM3 (\mk myes mno γ -> bindSameHandler γ (buildYesHandler γ myes u) (buildHandler γ mno u) mk) k yes no

evalTell :: Machine s o (o : xs) n r a -> MachineMonad s o xs n r a
evalTell (Machine k) = k <&> \mk γ -> mk (γ {operands = Op (OFFSET (input γ)) (operands γ)})

evalSeek :: Machine s o xs n r a -> MachineMonad s o (o : xs) n r a
evalSeek (Machine k) = k <&> \mk γ -> let Op (OFFSET input) xs = operands γ in mk (γ {operands = xs, input = input})

evalCase :: Machine s o (x : xs) n r a -> Machine s o (y : xs) n r a -> MachineMonad s o (Either x y : xs) n r a
evalCase (Machine p) (Machine q) = liftM2 (\mp mq γ ->
  let Op e xs = operands γ
  in [||case $$(genDefunc e) of
    Left x -> $$(mp (γ {operands = Op (FREEVAR [||x||]) xs}))
    Right y  -> $$(mq (γ {operands = Op (FREEVAR [||y||]) xs}))||]) p q

evalChoices :: [Defunc (x -> Bool)] -> [Machine s o xs n r a] -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalChoices fs ks (Machine def) = liftM2 (\mdef mks γ -> let Op x xs = operands γ in go x fs mks mdef (γ {operands = xs}))
  def
  (forM ks getMachine)
  where
    go x (f:fs) (mk:mks) def γ = _if (ap f x) (mk γ) (go x fs mks def γ)
    go _ _      _        def γ = def γ

evalIter :: (RecBuilder o, PositionOps (Rep o), HandlerOps o)
         => MVar Void -> Machine s o '[] One Void a -> Handler o (Machine s o) (o : xs) n r a
         -> MachineMonad s o xs n r a
evalIter μ l h =
  freshUnique $ \u1 ->   -- This one is used for the handler's offset from point of failure
    freshUnique $ \u2 -> -- This one is used for the handler's check and loop offset
      case h of
        Always (Machine h) ->
          liftM2 (\mh ctx γ -> buildIterAlways ctx μ l (buildHandler γ mh u1) (input γ) u2) h ask
        Same (Machine yes) (Machine no) ->
          liftM3 (\myes mno ctx γ ->  buildIterSame ctx μ l (buildYesHandler γ myes u1) (buildHandler γ mno u1) (input γ) u2) yes no ask

evalJoin :: ΦVar x -> MachineMonad s o (x : xs) n r a
evalJoin φ = askΦ φ <&> resume

evalMkJoin :: JoinBuilder o => ΦVar x -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalMkJoin = setupJoinPoint

evalSwap :: Machine s o (x : y : xs) n r a -> MachineMonad s o (y : x : xs) n r a
evalSwap (Machine k) = k <&> \mk γ -> mk (γ {operands = let Op y (Op x xs) = operands γ in Op x (Op y xs)})

evalDup :: Machine s o (x : x : xs) n r a -> MachineMonad s o (x : xs) n r a
evalDup (Machine k) = k <&> \mk γ ->
  let Op x xs = operands γ
  in dup x $ \dupx -> mk (γ {operands = Op dupx (Op dupx xs)})

evalMake :: ΣVar x -> Access -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalMake σ a k = asks $ \ctx γ ->
  let Op x xs = operands γ
  in newΣ σ a x (run k (γ {operands = xs})) ctx

evalGet :: ΣVar x -> Access -> Machine s o (x : xs) n r a -> MachineMonad s o xs n r a
evalGet σ a k = asks $ \ctx γ -> readΣ σ a (\x -> run k (γ {operands = Op x (operands γ)})) ctx

evalPut :: ΣVar x -> Access -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalPut σ a k = asks $ \ctx γ ->
  let Op x xs = operands γ
  in writeΣ σ a x (run k (γ {operands = xs})) ctx

evalLogEnter :: (?ops :: InputOps (Rep o), LogHandler o, HandlerOps o)
             => String -> Machine s o xs (Succ (Succ n)) r a -> MachineMonad s o xs (Succ n) r a
evalLogEnter name (Machine mk) = freshUnique $ \u ->
  liftM2 (\k ctx γ -> [|| Debug.Trace.trace $$(preludeString name '>' γ ctx "") $$(bindAlwaysHandler γ (logHandler name ctx γ u) k)||])
    (local debugUp mk)
    ask

evalLogExit :: (?ops :: InputOps (Rep o), PositionOps (Rep o), LogOps (Rep o)) => String -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalLogExit name (Machine mk) =
  liftM2 (\k ctx γ -> [|| Debug.Trace.trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(k γ) ||])
    (local debugDown mk)
    ask

evalMeta :: (?ops :: InputOps (Rep o), PositionOps (Rep o)) => MetaInstr n -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalMeta (AddCoins coins) (Machine k) =
  do requiresPiggy <- asks hasCoin
     if requiresPiggy then local (storePiggy coins) k
     else local (giveCoins coins) k <&> \mk γ -> emitLengthCheck (willConsume coins) (mk γ) (raise γ) (input γ)
evalMeta (RefundCoins coins) (Machine k) = local (refundCoins coins) k
-- No interaction with input reclamation here!
evalMeta (DrainCoins coins) (Machine k) = liftM2 (\n mk γ -> emitLengthCheck n (mk γ) (raise γ) (input γ)) (asks ((willConsume coins -) . liquidate)) k