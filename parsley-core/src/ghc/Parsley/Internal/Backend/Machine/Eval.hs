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
import Data.Some                                           (Some (..), withSome)
import Control.Monad                                       (forM, liftM2, liftM4)
import Control.Monad.Reader                                (Reader, ask, asks, reader, local)
import Control.Monad.ST                                    (runST)
import Parsley.Internal.Backend.Machine.Defunc             (Defunc(INPUT, LAM), pattern FREEVAR, genDefunc, ap, ap2, _if)
import Parsley.Internal.Backend.Machine.Identifiers        (MVar(..), ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.InputOps           (InputOps, DynOps)
import Parsley.Internal.Backend.Machine.InputRep           (StaRep)
import Parsley.Internal.Backend.Machine.Instructions       (Instr(..), MetaInstr(..), Access(..), Handler(..), PosSelector(..))
import Parsley.Internal.Backend.Machine.LetBindings        (LetBinding(body))
import Parsley.Internal.Backend.Machine.Types.Registers    (Regs (..))
import Parsley.Internal.Backend.Machine.LetRecBuilder      (letRec)
import Parsley.Internal.Backend.Machine.Ops
import Parsley.Internal.Backend.Machine.Types              (MachineMonad, Machine(..), run, qSubroutine)
import Parsley.Internal.Backend.Machine.PosOps             (initPos)
import Parsley.Internal.Backend.Machine.Types.Context
import Parsley.Internal.Backend.Machine.Types.Statics      (SomeCallableSubroutine(..), QStaCont (..))
import Parsley.Internal.Backend.Machine.Types.Coins        (Coins(knownPreds, willConsume, willCache), one, minus)
import Parsley.Internal.Backend.Machine.Types.Input        (Input(off), mkInput, forcePos, updatePos, updateOffset)
import Parsley.Internal.Backend.Machine.Types.Input.Offset (Offset(offset), unsafeDeepestKnown)
import Parsley.Internal.Backend.Machine.Types.State        (Γ(..), OpStack(..))
import Parsley.Internal.Common                             (Fix4, cata4, One, Code, Vec(..), Nat(..))
import Parsley.Internal.Core.CharPred                      (CharPred(UserPred), pattern Item, lamTerm, optimisePredGiven)
import Parsley.Internal.Trace                              (Trace(trace))
import System.Console.Pretty                               (color, Color(Green))

import qualified Debug.Trace (trace)
import qualified Parsley.Internal.Opt as Opt

{-|
This function performs the evaluation on the top-level let-bound parser to convert it into code.

@since 1.0.0.0
-}
eval :: forall o a. (Trace, Ops o, ?ops :: InputOps (StaRep o), ?flags :: Opt.Flags)
     => LetBinding o a a              -- ^ The binding to be generated.
     -> DMap MVar (LetBinding o a)    -- ^ The map of all other required bindings.
     -> StaRep o
     -> Code (Maybe a)                -- ^ The code for this parser.
eval binding fs offset  = trace "EVALUATING TOP LEVEL" [||
    runST $$(letRec fs
             nameLet
             (\μ func exp rs hs rregs names -> buildRec μ func rs hs rregs (emptyCtx names) (readyMachine exp))
             qSubroutine
             (run (readyMachine (body binding)) (Γ Empty (QStaCont halt NoRegs) (mkInput offset initPos) (VCons fatal VNil)) . nextUnique . emptyCtx))
  ||]
  where
    nameLet :: MVar x -> String
    nameLet (MVar i) = "sub" ++ show i

readyMachine :: (?ops :: InputOps (StaRep o), Ops o, Trace, ?flags :: Opt.Flags) => Fix4 (Instr o) xs n r a -> Machine s o xs n r a
readyMachine = trace "starting readymachine" $ cata4 (Machine . alg)
  where
    alg :: (?ops :: InputOps (StaRep o), Ops o, ?flags :: Opt.Flags) => Instr o (Machine s o) xs n r a -> MachineMonad s o xs n r a
    alg Ret                 = evalRet
    alg (Call μ k)        = evalCall μ k
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
    alg (Iter μ regs l k)   = evalIter μ regs l k
    alg (Join φ)            = evalJoin φ
    alg (MkJoin φ rs p k)   = evalMkJoin φ rs p k
    alg (Swap k)            = evalSwap k
    alg (Dup k)             = evalDup k
    alg (Make σ c k)        = evalMake σ c k
    alg (Get σ c k)         = evalGet σ c k
    alg (Put σ c k)         = evalPut σ c k
    alg (SelectPos sel k)   = evalSelectPos sel k
    alg (LogEnter name k)   = evalLogEnter name k
    alg (LogExit name k)    = evalLogExit name k
    alg (MetaInstr m k)     = evalMeta m k

evalRet :: (DynOps o, ?flags :: Opt.Flags) => MachineMonad s o (x : xs) n x a
evalRet = reader $ \ctx γ ->
  case retCont γ of  
    QStaCont rc regs -> resume rc ctx regs γ

evalCall :: forall s o a x xs n r. (MarshalOps o, DynOps o, ?flags :: Opt.Flags) => MVar x  -> Machine s o (x : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
evalCall μ k = freshUnique $ \u -> do 
  someSub <- askSub μ
  case someSub of 
    SomeCallableSubroutine sub hregs rregs -> do 
      ctx <- ask
      return $ \γ -> callCC u sub hregs rregs k ctx γ 

evalPush :: Defunc x -> Machine s o (x : xs) n r a -> MachineMonad s o xs n r a
evalPush x (Machine k) = k <&> \m γ -> m (γ {operands = Op x (operands γ)})

evalPop :: Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalPop (Machine k) = k <&> \m γ -> m (γ {operands = let Op _ xs = operands γ in xs})

evalLift2 :: (?flags :: Opt.Flags) => Defunc (x -> y -> z) -> Machine s o (z : xs) n r a -> MachineMonad s o (y : x : xs) n r a
evalLift2 f (Machine k) = k <&> \m γ -> m (γ {operands = let Op y (Op x xs) = operands γ in Op (ap2 f x y) xs})

evalSat :: forall s o xs n r a. (?ops :: InputOps (StaRep o), DynOps o, Trace, ?flags :: Opt.Flags) => CharPred -> Machine s o (Char : xs) (Succ n) r a -> MachineMonad s o xs (Succ n) r a
evalSat p mk = do
  bankrupt <- asks isBankrupt
  hasChange <- asks hasCoin
  if | bankrupt -> withLengthCheckAndCoins (one p) satFetch
     | hasChange -> satFetch
     | otherwise -> trace "I have a piggy :)" $ state breakPiggy $ \coins -> withLengthCheckAndCoins coins satFetch
  where
    satFetch :: MachineMonad s o xs (Succ n) r a
    satFetch = reader $ \ctx γ ->
      readChar (spendCoin ctx) p (fetch (off (input γ))) $ \c staOldPred staPosPred offset' ctx' ->
        let staPredC' = optimisePredGiven p staOldPred
        in sat (ap (LAM (lamTerm staPredC'))) c (continue mk γ (updatePos (updateOffset offset' (input γ)) c staPosPred) ctx')
                                                (raise ctx' γ)

    continue mk γ input' ctx v = run mk (γ {input = input', operands = Op v (operands γ)}) ctx

evalEmpt :: (DynOps o, ?flags :: Opt.Flags) => MachineMonad s o xs (Succ n) r a
evalEmpt = reader $ \ctx γ -> raise ctx γ

evalCommit :: Machine s o xs n r a -> MachineMonad s o xs (Succ n) r a
evalCommit (Machine k) = k <&> \mk γ -> let VCons _ hs = handlers γ in mk (γ {handlers = hs})

evalCatch :: (PositionOps (StaRep o), HandlerOps o, DynOps o) => Machine s o xs (Succ n) r a -> Handler o (Machine s o) (o : xs) n r a -> MachineMonad s o xs n r a
evalCatch (Machine k) h = freshUnique $ \u -> case h of
  Always (Just (Some hregs)) gh h ->
    liftM2 (\ctx mk γ -> bindAlwaysHandler γ gh (buildHandler γ ctx h hregs u) hregs mk) ask k 
  Same (Just (Some hregs)) gyes yes gno no ->
    liftM2 (\ctx mk γ -> bindSameHandler γ gyes (buildYesHandler γ ctx yes hregs) gno (buildHandler γ ctx no hregs u) hregs mk) ask k
  _ -> undefined -- Should have already figured out free register data.

evalTell :: Machine s o (o : xs) n r a -> MachineMonad s o xs n r a
evalTell (Machine k) = k <&> \mk γ -> mk (γ {operands = Op (INPUT (input γ)) (operands γ)})

evalSeek :: Machine s o xs n r a -> MachineMonad s o (o : xs) n r a
evalSeek (Machine k) = k <&> \mk γ -> let Op (INPUT input) xs = operands γ in mk (γ {operands = xs, input = input})

evalCase :: (?flags :: Opt.Flags) => Machine s o (x : xs) n r a -> Machine s o (y : xs) n r a -> MachineMonad s o (Either x y : xs) n r a
evalCase (Machine p) (Machine q) = liftM2 (\mp mq γ ->
  let Op e xs = operands γ
  in [||case $$(genDefunc e) of
    Left x -> $$(mp (γ {operands = Op (FREEVAR [||x||]) xs}))
    Right y  -> $$(mq (γ {operands = Op (FREEVAR [||y||]) xs}))||]) p q

evalChoices :: (?flags :: Opt.Flags) => [Defunc (x -> Bool)] -> [Machine s o xs n r a] -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalChoices fs ks (Machine def) = liftM2 (\mdef mks γ -> let Op x xs = operands γ in go x fs mks mdef (γ {operands = xs}))
  def
  (forM ks getMachine)
  where
    go x (f:fs) (mk:mks) def γ = _if (ap f x) (mk γ) (go x fs mks def γ)
    go _ _      _        def γ = def γ

evalIter :: (RecBuilder o, PositionOps (StaRep o), HandlerOps o, DynOps o)
         => MVar Void -> Maybe (Some Regs) -> Machine s o '[] One Void a -> Handler o (Machine s o) (o : xs) n r a
         -> MachineMonad s o xs n r a
evalIter _ Nothing _ _ = undefined -- We should have already attached register data!
evalIter μ (Just regs) l h =
  freshUnique $ \u1 ->   -- This one is used for the handler's offset from point of failure
    freshUnique $ \u2 -> -- This one is used for the handler's check and loop offset
      local voidCoins $  -- We must not allow factored input to pass through to iterative handlers, they have rolling inputs
        case h of
          Always (Just (Some hregs)) gh h -> 
            reader $ \ctx γ -> withSome regs (\regs -> bindIterAlways ctx μ regs l gh (buildHandler γ ctx h hregs u1) hregs (input γ) u2)
          Same (Just (Some hregs)) gyes yes gno no ->
            reader $ \ ctx γ -> withSome regs (\regs -> bindIterSame ctx μ regs l gyes (buildIterYesHandler γ ctx yes hregs u1) gno (buildHandler γ ctx no hregs u1) hregs (input γ) u2)
          _ -> undefined -- Should have attached register data already.

evalJoin :: (DynOps o, ?flags :: Opt.Flags) => ΦVar x -> MachineMonad s o (x : xs) n r a
evalJoin φ = do 
  qjoin <- askΦ φ
  ctx <- ask
  case qjoin of 
    QJoin joinpt regs -> return $ resume joinpt ctx regs

evalMkJoin :: (DynOps o, ?flags :: Opt.Flags) => JoinBuilder o => ΦVar x -> Maybe (Some Regs) -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalMkJoin _ Nothing            = undefined  -- shouldn't happen
evalMkJoin x (Just (Some regs)) = setupJoinPoint x regs

evalSwap :: Machine s o (x : y : xs) n r a -> MachineMonad s o (y : x : xs) n r a
evalSwap (Machine k) = k <&> \mk γ -> mk (γ {operands = let Op y (Op x xs) = operands γ in Op x (Op y xs)})

evalDup :: (?flags :: Opt.Flags) => Machine s o (x : x : xs) n r a -> MachineMonad s o (x : xs) n r a
evalDup (Machine k) = k <&> \mk γ ->
  let Op x xs = operands γ
  in dup x $ \dupx -> mk (γ {operands = Op dupx (Op dupx xs)})

evalMake :: (?flags :: Opt.Flags) => ΣVar x -> Access -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalMake σ a k = reader $ \ctx γ ->
  let Op x xs = operands γ
  in newΣ σ a x (run k (γ {operands = xs})) ctx

evalGet :: (?flags :: Opt.Flags) => ΣVar x -> Access -> Machine s o (x : xs) n r a -> MachineMonad s o xs n r a
evalGet σ a k = reader $ \ctx γ -> readΣ σ a (\x -> run k (γ {operands = Op x (operands γ)})) ctx

evalPut :: (?flags :: Opt.Flags) => ΣVar x -> Access -> Machine s o xs n r a -> MachineMonad s o (x : xs) n r a
evalPut σ a k = reader $ \ctx γ ->
  let Op x xs = operands γ
  in writeΣ σ a x (run k (γ {operands = xs})) ctx

evalSelectPos :: (?flags :: Opt.Flags) => PosSelector -> Machine s o (Int : xs) n r a -> MachineMonad s o xs n r a
evalSelectPos sel (Machine k) = k <&> \m γ -> forcePos (input γ) sel $ \component input' ->
  m (γ {operands = Op (FREEVAR component) (operands γ), input = input'})

evalLogEnter :: (?ops :: InputOps (StaRep o), LogHandler o, HandlerOps o, ?flags :: Opt.Flags)
             => String -> Machine s o xs (Succ (Succ n)) r a -> MachineMonad s o xs (Succ n) r a
evalLogEnter name (Machine mk) = freshUnique $ \u ->
  liftM2 (\k ctx γ -> [|| Debug.Trace.trace $$(preludeString name '>' γ ctx "") $$(bindAlwaysHandler γ True (logHandler name ctx γ u) NoRegs k)||])
    (local debugUp mk)
    ask

evalLogExit :: (?ops :: InputOps (StaRep o), PositionOps (StaRep o), LogOps (StaRep o), DynOps o) => String -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalLogExit name (Machine mk) =
  liftM2 (\k ctx γ -> [|| Debug.Trace.trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(k γ) ||])
    (local debugDown mk)
    ask

evalMeta :: (?ops :: InputOps (StaRep o), DynOps o, ?flags :: Opt.Flags) => MetaInstr n -> Machine s o xs n r a -> MachineMonad s o xs n r a
evalMeta _ (Machine k) | not (Opt.lengthCheckFactoring ?flags) = k
evalMeta (AddCoins coins) (Machine k) =
  -- when there are coins available, this cannot be discharged, and will wait until the current amounts
  -- are exhausted. Because it might have been the case that lookahead was performed to refund, the
  -- over-imbursement cannot be done in advance, and is instead done here, deducting the net-worth
  -- of the coin count to ensure that only enough to make up the change is put in the piggy-banks
  do net <- asks netWorth
     let requiresPiggy = net /= 0
     if requiresPiggy then local (storePiggy (coins `minus` net)) k
     else withLengthCheckAndCoins coins k
evalMeta (RefundCoins coins) (Machine k)
  | Opt.reclaimInput ?flags = local (refundCoins coins) k
  | otherwise               = local (giveCoins coins) k
-- No interaction with input reclamation here!
evalMeta (DrainCoins coins) (Machine k) =
  liftM4 drain
         ask
         (asks isBankrupt)
         (asks (canAfford coins))
         k
  where
    -- there are enough coins to pay in full
    drain _ _ Nothing mk γ = mk γ
    drain ctx bankrupt ~(Just m) mk γ
      -- full length check required
      | bankrupt = emitLengthCheck coins 0 Nothing (\off _ -> withUpdatedOffset mk γ off) (raise ctx γ) (off (input γ)) offset
      -- can be partially paid from last known deepest offset
      | otherwise = emitLengthCheck (m + 1) 0 Nothing (\off _ -> withUpdatedOffset mk γ off) (raise ctx γ) (off (input γ)) unsafeDeepestKnown
evalMeta (GiveBursary coins) (Machine k) = local (giveCoins coins) k
evalMeta BlockCoins{} (Machine k) = k

withUpdatedOffset :: (Γ s o xs n r a -> t) -> Γ s o xs n r a -> Offset o -> t
withUpdatedOffset k γ off = k (γ { input = updateOffset off (input γ)})

withLengthCheckAndCoins :: (?ops::InputOps (StaRep o), DynOps o, ?flags :: Opt.Flags) => Coins -> MachineMonad s o xs (Succ n) r a -> MachineMonad s o xs (Succ n) r a
withLengthCheckAndCoins coins k = reader $ \ctx γ ->
    -- it seems like _specific_ prefetching must not move out of the scope of a handler that rolls back (like try)
    -- It does work, however, if exactly one character is considered (see take 1 below) and then n-1 Items, which cannot fail
    let prefetch ((c, offset'), pred) k = k . addChar pred c offset'
        remainder deepest ctx = withUpdatedOffset (flip (run (Machine k)) (giveCoins (willConsume coins) ctx)) γ deepest
        staPred = knownPreds coins >>= onlyStatic
        preds = maybe id (:) staPred (repeat Item) -- these are fed in to ensure the right checked pred is accounted for
        headCheck = staPred <&> \pred c good -> sat (ap (LAM (lamTerm pred))) c (const good) (raise ctx γ)
        good deepest cached = foldr prefetch (remainder deepest) (zip cached preds) ctx
    in emitLengthCheck (willConsume coins) (willCache coins) headCheck good (raise ctx γ) (off (input γ)) offset
        -- this is needed because a cached predicate cannot be compared for equality if it's user-pred, and it'll duplicate!
  where onlyStatic UserPred{}                       = Nothing
        onlyStatic p | Opt.leadCharFactoring ?flags = Just p
        onlyStatic _                                = Nothing

state :: (r -> (a, r)) -> (a -> Reader r b) -> Reader r b
state f k = do
  (x, r) <- asks f
  local (const r) (k x)
