{-# LANGUAGE ImplicitParams,
             MagicHash,
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

import Data.Dependent.Map                                  (DMap)
import Data.Functor                                        ((<&>))
import Data.Void                                           (Void)
import Control.Monad                                       (forM, liftM2, liftM3)
import Control.Monad.Reader                                (Reader, ask, asks, reader, local)
import Control.Monad.ST                                    (runST)
import Parsley.Internal.Backend.Machine.Defunc             (Defunc(INPUT, LAM), pattern FREEVAR, genDefunc, ap, ap2, _if)
import Parsley.Internal.Backend.Machine.Identifiers        (MVar(..), ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.InputOps           (InputOps, DynOps)
import Parsley.Internal.Backend.Machine.InputRep           (StaRep)
import Parsley.Internal.Backend.Machine.Instructions       (Instr(..), MetaInstr(..), Access(..), Handler(..), PosSelector(..))
import Parsley.Internal.Backend.Machine.LetBindings        (LetBinding(body))
import Parsley.Internal.Backend.Machine.LetRecBuilder      (letRec)
import Parsley.Internal.Backend.Machine.Ops
import Parsley.Internal.Backend.Machine.Types              (MachineMonad, Machine(..), run, qSubroutine)
import Parsley.Internal.Backend.Machine.PosOps             (initPos)
import Parsley.Internal.Backend.Machine.Types.Context
import Parsley.Internal.Backend.Machine.Types.Coins        (Coins(knownPreds, willConsume, willCache), one, minus)
import Parsley.Internal.Backend.Machine.Types.Input        (Input(off), mkInput, forcePos, updatePos, updateOffset)
import Parsley.Internal.Backend.Machine.Types.Input.Offset (Offset(offset), unsafeDeepestKnown)
import Parsley.Internal.Backend.Machine.Types.State        (Γ(..), OpStack(..))
import Parsley.Internal.Common                             (Fix4, cata4, One, Code, Vec(..), Nat(..))
import Parsley.Internal.Core.CharPred                      (CharPred(UserPred), pattern Item, lamTerm, optimisePredGiven)
import Parsley.Internal.Trace                              (Trace(trace))
import System.Console.Pretty                               (color, Color(Green))

import qualified Debug.Trace (trace)

{-|
This function performs the evaluation on the top-level let-bound parser to convert it into code.

@since 1.0.0.0
-}
eval :: forall o a. (Trace, Ops o, ?ops :: InputOps (StaRep o))
     => LetBinding o a a              -- ^ The binding to be generated.
     -> DMap MVar (LetBinding o a)    -- ^ The map of all other required bindings.
     -> StaRep o
     -> Code (Maybe a)                -- ^ The code for this parser.
eval binding fs offset  = trace "EVALUATING TOP LEVEL" [||
    runST $$(letRec fs
             nameLet
             (\μ exp rs names -> buildRec μ rs (emptyCtx names) (readyMachine exp))
             qSubroutine
             (run (readyMachine (body binding)) (Γ Empty halt (mkInput offset initPos) (VCons fatal VNil)) . nextUnique . emptyCtx))
  ||]
  where
    nameLet :: MVar x -> String
    nameLet (MVar i) = "sub" ++ show i

readyMachine :: (?ops :: InputOps (StaRep o), Ops o, Trace) => Fix4 (Instr o) xs n r a -> Machine s o xs n r a
readyMachine = cata4 (Machine . alg)
  where
    alg :: (?ops :: InputOps (StaRep o), Ops o) => Instr o (Machine s o) xs n r a -> MachineMonad s o xs n r a
    alg Ret                 = evalRet
    alg (Call μ k)          = evalCall μ k
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
    alg (SelectPos sel k)   = evalSelectPos sel k
    alg (LogEnter name k)   = evalLogEnter name k
    alg (LogExit name k)    = evalLogExit name k
    alg (MetaInstr m k)     = evalMeta m k

evalRet :: DynOps o => MachineMonad s o (x : xs) n x a
evalRet = return $! retCont >>= resume

evalCall :: forall s o a x xs n r. (MarshalOps o, DynOps o) => MVar x -> Machine s o (x : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
evalCall μ (Machine k) = freshUnique $ \u -> liftM2 (callCC u) (askSub μ) k

evalPush :: Defunc x -> Machine s o (x : xs) n r a -> MachineMonad s o xs n r a
evalPush x (Machine k) = k <&> \m γ -> m (γ {operands = Op x (operands γ)})

evalPop :: Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalPop (Machine k) = k <&> \m γ -> m (γ {operands = let Op _ xs = operands γ in xs})

evalLift2 :: Defunc (x -> y -> z) -> Machine s o (z : xs) n r a -> MachineMonad s o (y : x : xs) n r a
evalLift2 f (Machine k) = k <&> \m γ -> m (γ {operands = let Op y (Op x xs) = operands γ in Op (ap2 f x y) xs})

evalSat :: forall s o xs n r a. (?ops :: InputOps (StaRep o), DynOps o, Trace) => CharPred -> Machine s o (Char : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
evalSat p k = do
  bankrupt <- asks isBankrupt
  hasChange <- asks hasCoin
  if | bankrupt -> emitCheckAndFetch (one p) k
     | hasChange -> satFetch k
     | otherwise -> trace "I have a piggy :)" $ state breakPiggy $ \coins -> emitCheckAndFetch coins k
  where
    satFetch :: Machine s o (Char : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
    satFetch mk = reader $ \ctx γ ->
      readChar (spendCoin ctx) p (fetch (off (input γ))) $ \c staOldPred staPosPred offset' ctx' ->
        let staPredC' = optimisePredGiven p staOldPred
        in sat (ap (LAM (lamTerm staPredC'))) c (continue mk γ (updatePos (updateOffset offset' (input γ)) c staPosPred) ctx')
                                                (raise γ)

    emitCheckAndFetch :: Coins -> Machine s o (Char : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
    emitCheckAndFetch coins = withLengthCheckAndCoins coins . satFetch

    continue mk γ input' ctx v = run mk (γ {input = input', operands = Op v (operands γ)}) ctx

evalEmpt :: DynOps o => MachineMonad s o xs (Succ n) r a
evalEmpt = return $! raise

evalCommit :: Machine s o xs n r a -> MachineMonad s o xs (Succ n) r a
evalCommit (Machine k) = k <&> \mk γ -> let VCons _ hs = handlers γ in mk (γ {handlers = hs})

evalCatch :: (PositionOps (StaRep o), HandlerOps o, DynOps o) => Machine s o xs (Succ n) r a -> Handler o (Machine s o) (o : xs) n r a -> MachineMonad s o xs n r a
evalCatch (Machine k) h = freshUnique $ \u -> case h of
  Always gh (Machine h) ->
    liftM2 (\mk mh γ -> bindAlwaysHandler γ gh (buildHandler γ mh u) mk) k h
  Same gyes (Machine yes) gno (Machine no) ->
    liftM3 (\mk myes mno γ -> bindSameHandler γ gyes (buildYesHandler γ myes{- u-}) gno (buildHandler γ mno u) mk) k yes no

evalTell :: Machine s o (o : xs) n r a -> MachineMonad s o xs n r a
evalTell (Machine k) = k <&> \mk γ -> mk (γ {operands = Op (INPUT (input γ)) (operands γ)})

evalSeek :: Machine s o xs n r a -> MachineMonad s o (o : xs) n r a
evalSeek (Machine k) = k <&> \mk γ -> let Op (INPUT input) xs = operands γ in mk (γ {operands = xs, input = input})

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

evalIter :: (RecBuilder o, PositionOps (StaRep o), HandlerOps o, DynOps o)
         => MVar Void -> Machine s o '[] One Void a -> Handler o (Machine s o) (o : xs) n r a
         -> MachineMonad s o xs n r a
evalIter μ l h =
  freshUnique $ \u1 ->   -- This one is used for the handler's offset from point of failure
    freshUnique $ \u2 -> -- This one is used for the handler's check and loop offset
      case h of
        Always gh (Machine h) ->
          liftM2 (\mh ctx γ -> bindIterAlways ctx μ l gh (buildHandler γ mh u1) (input γ) u2) h ask
        Same gyes (Machine yes) gno (Machine no) ->
          liftM3 (\myes mno ctx γ -> bindIterSame ctx μ l gyes (buildIterYesHandler γ myes u1) gno (buildHandler γ mno u1) (input γ) u2) yes no ask

evalJoin :: DynOps o => ΦVar x -> MachineMonad s o (x : xs) n r a
evalJoin φ = askΦ φ <&> resume

evalMkJoin :: DynOps o => JoinBuilder o => ΦVar x -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalMkJoin = setupJoinPoint

evalSwap :: Machine s o (x : y : xs) n r a -> MachineMonad s o (y : x : xs) n r a
evalSwap (Machine k) = k <&> \mk γ -> mk (γ {operands = let Op y (Op x xs) = operands γ in Op x (Op y xs)})

evalDup :: Machine s o (x : x : xs) n r a -> MachineMonad s o (x : xs) n r a
evalDup (Machine k) = k <&> \mk γ ->
  let Op x xs = operands γ
  in dup x $ \dupx -> mk (γ {operands = Op dupx (Op dupx xs)})

evalMake :: ΣVar x -> Access -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalMake σ a k = reader $ \ctx γ ->
  let Op x xs = operands γ
  in newΣ σ a x (run k (γ {operands = xs})) ctx

evalGet :: ΣVar x -> Access -> Machine s o (x : xs) n r a -> MachineMonad s o xs n r a
evalGet σ a k = reader $ \ctx γ -> readΣ σ a (\x -> run k (γ {operands = Op x (operands γ)})) ctx

evalPut :: ΣVar x -> Access -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalPut σ a k = reader $ \ctx γ ->
  let Op x xs = operands γ
  in writeΣ σ a x (run k (γ {operands = xs})) ctx

evalSelectPos :: PosSelector -> Machine s o (Int : xs) n r a -> MachineMonad s o xs n r a
evalSelectPos sel (Machine k) = k <&> \m γ -> forcePos (input γ) sel $ \component input' ->
  m (γ {operands = Op (FREEVAR component) (operands γ), input = input'})

evalLogEnter :: (?ops :: InputOps (StaRep o), LogHandler o, HandlerOps o)
             => String -> Machine s o xs (Succ (Succ n)) r a -> MachineMonad s o xs (Succ n) r a
evalLogEnter name (Machine mk) = freshUnique $ \u ->
  liftM2 (\k ctx γ -> [|| Debug.Trace.trace $$(preludeString name '>' γ ctx "") $$(bindAlwaysHandler γ True (logHandler name ctx γ u) k)||])
    (local debugUp mk)
    ask

evalLogExit :: (?ops :: InputOps (StaRep o), PositionOps (StaRep o), LogOps (StaRep o), DynOps o) => String -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalLogExit name (Machine mk) =
  liftM2 (\k ctx γ -> [|| Debug.Trace.trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(k γ) ||])
    (local debugDown mk)
    ask

evalMeta :: (?ops :: InputOps (StaRep o), DynOps o) => MetaInstr n -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalMeta (AddCoins coins) (Machine k) =
  -- when there are coins available, this cannot be discharged, and will wait until the current amounts
  -- are exhausted. Because it might have been the case that lookahead was performed to refund, the
  -- over-imbursement cannot be done in advance, and is instead done here, deducting the net-worth
  -- of the coin count to ensure that only enough to make up the change is put in the piggy-banks
  do net <- asks netWorth
     let requiresPiggy = net /= 0
     if requiresPiggy then local (storePiggy (coins `minus` net)) k
     else withLengthCheckAndCoins coins k
evalMeta (RefundCoins coins) (Machine k) = local (refundCoins coins) k
-- No interaction with input reclamation here!
evalMeta (DrainCoins coins) (Machine k) =
  liftM3 drain
         (asks isBankrupt)
         (asks (canAfford coins))
         k
  where
    -- there are enough coins to pay in full
    drain _ Nothing mk γ = mk γ
    drain bankrupt ~(Just m) mk γ
      -- full length check required
      | bankrupt = emitLengthCheck coins 0 Nothing (\off _ -> withUpdatedOffset mk γ off) (raise γ) (off (input γ)) offset
      -- can be partially paid from last known deepest offset
      | otherwise = emitLengthCheck (m + 1) 0 Nothing (\off _ -> withUpdatedOffset mk γ off) (raise γ) (off (input γ)) unsafeDeepestKnown
evalMeta (GiveBursary coins) (Machine k) = local (giveCoins coins) k
evalMeta BlockCoins{} (Machine k) = k

withUpdatedOffset :: (Γ s o xs n r a -> t) -> Γ s o xs n r a -> Offset o -> t
withUpdatedOffset k γ off = k (γ { input = updateOffset off (input γ)})

withLengthCheckAndCoins :: (?ops::InputOps (StaRep o), DynOps o) => Coins -> MachineMonad s o xs (Succ n) r a -> MachineMonad s o xs (Succ n) r a
withLengthCheckAndCoins coins k = reader $ \ctx γ ->
    -- it seems like _specific_ prefetching must not move out of the scope of a handler that rolls back (like try)
    -- It does work, however, if exactly one character is considered (see take 1 below) and then n-1 Items, which cannot fail
    let prefetch ((c, offset'), pred) k = k . addChar pred c offset'
        remainder deepest ctx = withUpdatedOffset (flip (run (Machine k)) (giveCoins (willConsume coins) ctx)) γ deepest
        staPred = knownPreds coins >>= onlyStatic
        preds = maybe id (:) staPred (repeat Item) -- these are fed in to ensure the right checked pred is accounted for
        headCheck = staPred <&> \pred c good -> sat (ap (LAM (lamTerm pred))) c (const good) (raise γ)
        good deepest cached = foldr prefetch (remainder deepest) (zip cached preds) ctx
    in emitLengthCheck (willConsume coins) (willCache coins) headCheck good (raise γ) (off (input γ)) offset
        -- this is needed because a cached predicate cannot be compared for equality if it's user-pred, and it'll duplicate!
  where onlyStatic UserPred{} = Nothing
        onlyStatic p          = Just p

state :: (r -> (a, r)) -> (a -> Reader r b) -> Reader r b
state f k = do
  (x, r) <- asks f
  local (const r) (k x)
