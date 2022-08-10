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
import Control.Monad                                       (forM, liftM2, liftM3, when)
import Control.Monad.Reader                                (ask, asks, reader, local)
import Control.Monad.ST                                    (runST)
import Parsley.Internal.Backend.Machine.Defunc             (Defunc(INPUT, LAM), pattern FREEVAR, genDefunc, ap, ap2, _if)
import Parsley.Internal.Backend.Machine.Identifiers        (MVar(..), ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.InputOps           (InputDependant, InputOps(InputOps), PositionOps(extractRawOffset))
import Parsley.Internal.Backend.Machine.InputRep           (Rep)
import Parsley.Internal.Backend.Machine.Instructions       (Instr(..), MetaInstr(..), Access(..), Handler(..), PosSelector(..))
import Parsley.Internal.Backend.Machine.LetBindings        (LetBinding(body))
import Parsley.Internal.Backend.Machine.LetRecBuilder      (letRec)
import Parsley.Internal.Backend.Machine.Ops
import Parsley.Internal.Backend.Machine.Types              (MachineMonad, Machine(..), run)
import Parsley.Internal.Backend.Machine.PosOps             (initPos)
import Parsley.Internal.Backend.Machine.Types.Context
import Parsley.Internal.Backend.Machine.Types.Coins        (willConsume, int)
import Parsley.Internal.Backend.Machine.Types.Errors       (DefuncGhosts(EmptyGhosts), emptyError)
import Parsley.Internal.Backend.Machine.Types.Input        (Input(off), mkInput, forcePos, updatePos)
import Parsley.Internal.Backend.Machine.Types.State        (Γ(..), OpStack(..))
import Parsley.Internal.Common                             (Fix3, cata3, One, Code, Vec(..), Nat(..))
import Parsley.Internal.Core.CharPred                      (CharPred, lamTerm, optimisePredGiven)
import Parsley.Internal.Core.Result                        (Result(..))
import Parsley.Internal.Trace                              (Trace(trace))
import System.Console.Pretty                               (color, Color(Green))

import qualified Debug.Trace (trace)

{-|
This function performs the evaluation on the top-level let-bound parser to convert it into code.

@since 1.0.0.0
-}
eval :: (Trace, Ops o)
     => Code (InputDependant (Rep o)) -- ^ The input as provided by the user.
     -> LetBinding o a                -- ^ The binding to be generated.
     -> DMap MVar (LetBinding o)      -- ^ The map of all other required bindings.
     -> Code (Result err a)           -- ^ The code for this parser.
eval input binding fs = trace "EVALUATING TOP LEVEL" [|| runST $
  do let !(# next, more, offset #) = $$input
     $$(let ?ops = InputOps [||more||] [||next||]
        in letRec fs
             nameLet
             (\μ exp rs names -> buildRec μ rs (emptyCtx names) (readyMachine exp))
             (run (readyMachine (body binding))
                  (Γ Empty halt (mkInput [||offset||] initPos) (VCons fatal VNil) [] [||EmptyGhosts||] [] (extractRawOffset [||offset||]))
                 . nextUnique . emptyCtx))
  ||]
  where
    nameLet :: MVar x -> String
    nameLet (MVar i) = "sub" ++ show i

readyMachine :: (?ops :: InputOps (Rep o), Ops o, Trace) => Fix3 (Instr o) xs n r -> Machine s o err a xs n r
readyMachine = cata3 (Machine . alg)
  where
    alg :: (?ops :: InputOps (Rep o), Ops o) => Instr o (Machine s o err a) xs n r -> MachineMonad s o err a xs n r
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
    alg (SelectPos sel k)   = evalSelectPos sel k
    alg (LogEnter name k)   = evalLogEnter name k
    alg (LogExit name k)    = evalLogExit name k
    alg (MetaInstr m k)     = evalMeta m k

evalRet :: MachineMonad s o err a (x : xs) n x
evalRet = return $! retCont >>= resume

evalCall :: MarshalOps o => MVar x -> Machine s o err a (x : xs) (Succ n) r -> MachineMonad s o err a xs (Succ n) r
evalCall μ (Machine k) = freshUnique $ \u -> liftM2 (callCC u) (askSub μ) k

evalJump :: forall s o err a x n. MarshalOps o => MVar x -> MachineMonad s o err a '[] (Succ n) x
evalJump μ = askSub μ <&> \sub Γ{..} -> callWithContinuation @o sub retCont input handlers

evalPush :: Defunc x -> Machine s o err a (x : xs) n r -> MachineMonad s o err a xs n r
evalPush x (Machine k) = k <&> \m γ -> m (γ {operands = Op x (operands γ)})

evalPop :: Machine s o err a xs n r -> MachineMonad s o err a (x : xs) n r
evalPop (Machine k) = k <&> \m γ -> m (γ {operands = let Op _ xs = operands γ in xs})

evalLift2 :: Defunc (x -> y -> z) -> Machine s o err a (z : xs) n r -> MachineMonad s o err a (y : x : xs) n r
evalLift2 f (Machine k) = k <&> \m γ -> m (γ {operands = let Op y (Op x xs) = operands γ in Op (ap2 f x y) xs})

evalSat :: forall s o err a xs n r. (?ops :: InputOps (Rep o), PositionOps (Rep o), Trace) => CharPred -> Machine s o err a (Char : xs) (Succ n) r -> MachineMonad s o err a xs (Succ n) r
evalSat p k@(Machine k') = do
  bankrupt <- asks isBankrupt
  hasChange <- asks hasCoin
  if | bankrupt -> emitCheckAndFetch 1 k
     | hasChange -> local spendCoin (satFetch k)
     | otherwise -> trace "I have a piggy :)" $
        local breakPiggy $
          do check <- asks (emitCheckAndFetch . coins)
             check (Machine (local spendCoin k'))
  where
    satFetch :: Machine s o err a (Char : xs) (Succ n) r -> MachineMonad s o err a xs (Succ n) r
    satFetch mk = reader $ \ctx γ ->
      readChar ctx p (fetch (input γ)) $ \c staOldPred staPosPred input' ctx' ->
        let staPredC' = optimisePredGiven p staOldPred
        in sat (ap (LAM (lamTerm staPredC'))) c (continue mk γ (updatePos input' c staPosPred) ctx')
                                                (raise {- TODO: -} [||emptyError||] γ)

    emitCheckAndFetch :: Int -> Machine s o err a (Char : xs) (Succ n) r -> MachineMonad s o err a xs (Succ n) r
    emitCheckAndFetch n mk = do
      sat <- satFetch mk
      return $ \γ -> emitLengthCheck n (sat γ) (raise {- TODO: -} [||emptyError||] γ) (off (input γ))

    continue mk γ input' ctx v = run mk (γ {input = input', operands = Op v (operands γ)}) ctx

evalEmpt :: PositionOps (Rep o) => MachineMonad s o err a xs (Succ n) r
evalEmpt = return $! raise [||emptyError||]

evalCommit :: Machine s o err a xs n r -> MachineMonad s o err a xs (Succ n) r
evalCommit (Machine k) = k <&> \mk γ -> let VCons _ hs = handlers γ in mk (γ {handlers = hs})

evalCatch :: (PositionOps (Rep o), HandlerOps o) => Machine s o err a xs (Succ n) r -> Handler o (Machine s o err a) (o : xs) n r -> MachineMonad s o err a xs n r
evalCatch (Machine k) h = freshUnique $ \u -> case h of
  Always gh (Machine h) ->
    liftM2 (\mk mh γ -> bindAlwaysHandler γ gh (buildHandler γ mh u) mk) k h
  Same gyes (Machine yes) gno (Machine no) ->
    liftM3 (\mk myes mno γ -> bindSameHandler γ gyes (buildYesHandler γ myes{- u-}) gno (buildHandler γ mno u) mk) k yes no

evalTell :: Machine s o err a (o : xs) n r -> MachineMonad s o err a xs n r
evalTell (Machine k) = k <&> \mk γ -> mk (γ {operands = Op (INPUT (input γ)) (operands γ)})

evalSeek :: Machine s o err a xs n r -> MachineMonad s o err a (o : xs) n r
evalSeek (Machine k) = k <&> \mk γ -> let Op (INPUT input) xs = operands γ in mk (γ {operands = xs, input = input})

evalCase :: Machine s o err a (x : xs) n r -> Machine s o err a (y : xs) n r -> MachineMonad s o err a (Either x y : xs) n r
evalCase (Machine p) (Machine q) = liftM2 (\mp mq γ ->
  let Op e xs = operands γ
  in [||case $$(genDefunc e) of
    Left x -> $$(mp (γ {operands = Op (FREEVAR [||x||]) xs}))
    Right y  -> $$(mq (γ {operands = Op (FREEVAR [||y||]) xs}))||]) p q

evalChoices :: [Defunc (x -> Bool)] -> [Machine s o err a xs n r] -> Machine s o err a xs n r -> MachineMonad s o err a (x : xs) n r
evalChoices fs ks (Machine def) = liftM2 (\mdef mks γ -> let Op x xs = operands γ in go x fs mks mdef (γ {operands = xs}))
  def
  (forM ks getMachine)
  where
    go x (f:fs) (mk:mks) def γ = _if (ap f x) (mk γ) (go x fs mks def γ)
    go _ _      _        def γ = def γ

evalIter :: (RecBuilder o, PositionOps (Rep o), HandlerOps o)
         => MVar Void -> Machine s o err a '[] One Void -> Handler o (Machine s o err a) (o : xs) n r
         -> MachineMonad s o err a xs n r
evalIter μ l h =
  freshUnique $ \u1 ->   -- This one is used for the handler's offset from point of failure
    freshUnique $ \u2 -> -- This one is used for the handler's check and loop offset
      case h of
        Always gh (Machine h) ->
          liftM2 (\mh ctx γ -> bindIterAlways ctx μ l gh (buildHandler γ mh u1) (input γ) u2) h ask
        Same gyes (Machine yes) gno (Machine no) ->
          liftM3 (\myes mno ctx γ -> bindIterSame ctx μ l gyes (buildIterYesHandler γ myes u1) gno (buildHandler γ mno u1) (input γ) u2) yes no ask

evalJoin :: ΦVar x -> MachineMonad s o err a (x : xs) n r
evalJoin φ = askΦ φ <&> resume

evalMkJoin :: JoinBuilder o => ΦVar x -> Machine s o err a (x : xs) n r -> Machine s o err a xs n r -> MachineMonad s o err a xs n r
evalMkJoin = setupJoinPoint

evalSwap :: Machine s o err a (x : y : xs) n r -> MachineMonad s o err a (y : x : xs) n r
evalSwap (Machine k) = k <&> \mk γ -> mk (γ {operands = let Op y (Op x xs) = operands γ in Op x (Op y xs)})

evalDup :: Machine s o err a (x : x : xs) n r -> MachineMonad s o err a (x : xs) n r
evalDup (Machine k) = k <&> \mk γ ->
  let Op x xs = operands γ
  in dup x $ \dupx -> mk (γ {operands = Op dupx (Op dupx xs)})

evalMake :: ΣVar x -> Access -> Machine s o err a xs n r -> MachineMonad s o err a (x : xs) n r
evalMake σ a k = reader $ \ctx γ ->
  let Op x xs = operands γ
  in newΣ σ a x (run k (γ {operands = xs})) ctx

evalGet :: ΣVar x -> Access -> Machine s o err a (x : xs) n r -> MachineMonad s o err a xs n r
evalGet σ a k = reader $ \ctx γ -> readΣ σ a (\x -> run k (γ {operands = Op x (operands γ)})) ctx

evalPut :: ΣVar x -> Access -> Machine s o err a xs n r -> MachineMonad s o err a (x : xs) n r
evalPut σ a k = reader $ \ctx γ ->
  let Op x xs = operands γ
  in writeΣ σ a x (run k (γ {operands = xs})) ctx

evalSelectPos :: PosSelector -> Machine s o err a (Int : xs) n r -> MachineMonad s o err a xs n r
evalSelectPos sel (Machine k) = k <&> \m γ -> forcePos (input γ) sel $ \component input' ->
  m (γ {operands = Op (FREEVAR component) (operands γ), input = input'})

evalLogEnter :: (?ops :: InputOps (Rep o), LogHandler o, HandlerOps o)
             => String -> Machine s o err a xs (Succ (Succ n)) r -> MachineMonad s o err a xs (Succ n) r
evalLogEnter name (Machine mk) = freshUnique $ \u ->
  liftM2 (\k ctx γ -> [|| Debug.Trace.trace $$(preludeString name '>' γ ctx "") $$(bindAlwaysHandler γ True (logHandler name ctx γ u) k)||])
    (local debugUp mk)
    ask

evalLogExit :: (?ops :: InputOps (Rep o), PositionOps (Rep o), LogOps (Rep o)) => String -> Machine s o err a xs n r -> MachineMonad s o err a xs n r
evalLogExit name (Machine mk) =
  liftM2 (\k ctx γ -> [|| Debug.Trace.trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(k γ) ||])
    (local debugDown mk)
    ask

-- TODO: What errors go here?
evalMeta :: (?ops :: InputOps (Rep o), PositionOps (Rep o)) => MetaInstr n -> Machine s o err a xs n r -> MachineMonad s o err a xs n r
evalMeta (AddCoins coins) (Machine k) =
  do requiresPiggy <- asks hasCoin
     if requiresPiggy then local (storePiggy coins) k
     else local (giveCoins coins) k <&> \mk γ -> emitLengthCheck (willConsume coins) (mk γ) (raise [||emptyError||] γ) (off (input γ))
evalMeta (RefundCoins coins) (Machine k) = local (refundCoins coins) k
-- No interaction with input reclamation here!
evalMeta (DrainCoins coins) (Machine k) =
  -- If there are enough coins left to cover the cost, no length check is required
  -- Otherwise, the full length check is required (partial doesn't work until the right offset is reached)
  liftM2 (\canAfford mk γ -> if canAfford then mk γ else emitLengthCheck (willConsume coins) (mk γ) (raise [||emptyError||] γ) (off (input γ)))
         (asks (canAfford (willConsume coins)))
         k
evalMeta (GiveBursary coins) (Machine k) = local (giveCoins coins) k
evalMeta (PrefetchChar check) k =
  do bankrupt <- asks isBankrupt
     when (not bankrupt && check) (error "must be bankrupt to generate a prefetch check")
     mkCheck check (reader $ \ctx γ -> prefetch (input γ) ctx (run k γ))
  where
    mkCheck True  k = local (giveCoins (int 1)) k <&> \mk γ -> emitLengthCheck 1 (mk γ) (raise [||emptyError||] γ) (off (input γ))
    mkCheck False k = k
    prefetch o ctx k = fetch o (\c o' -> k (addChar c o' ctx))
evalMeta BlockCoins (Machine k) = k
