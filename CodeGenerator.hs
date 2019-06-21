{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
module CodeGenerator (codeGen, halt, ret) where

import ParserAST                  (ParserF(..))
import Machine                    (M(..), ΣVar(..), ΣState(..), ΣVars, IMVar, IΦVar, IΣVar, MVar(..), ΦVar(..), ΦDecl, fmapInstr)
import Indexed                    (IFunctor, Free, Free3(Op3), History(Era), Void, Void3, imap, histo, present, (|>), absurd)
import Utils                      (TExpQ, lift', (>*<), WQ(..))
import Control.Applicative        (liftA2)
import Control.Monad              ((<$!>))
import Control.Monad.Reader       (ReaderT, ask, asks, runReaderT, local, MonadReader)
import Control.Monad.State.Strict (State, get, modify', runState, MonadState)
import Fresh                      (VFreshT, HFreshT, runFreshT, evalFreshT, construct, MonadFresh(..), mapVFreshT)
import Control.Monad.Trans        (lift)
import Data.Set                   (Set)
import Data.Maybe                 (isJust, fromJust)
import Debug.Trace                (traceShow)
import qualified Data.Set as Set

type CodeGenStack a = VFreshT IΦVar (VFreshT IMVar (HFreshT IΣVar (ReaderT (Set IMVar) (State ΣVars)))) a
runCodeGenStack :: CodeGenStack a -> IMVar -> IΦVar -> IΣVar -> Set IMVar -> ΣVars -> ((a, IΣVar), ΣVars)
runCodeGenStack m μ0 φ0 σ0 seen0 vs0 = 
  (flip runState vs0 . 
   flip runReaderT seen0 . 
   flip runFreshT σ0 . 
   flip evalFreshT μ0 . 
   flip evalFreshT φ0) m

newtype CodeGen b a = 
  CodeGen {runCodeGen :: forall xs' ks'. Free3 M Void3 (a ': xs') ks' b -> CodeGenStack (Free3 M Void3 xs' ks' b)}

halt :: Free3 M Void3 '[a] '[] a
halt = Op3 Halt

ret :: Free3 M Void3 (x ': xs) ((x ': xs) ': ks) a
ret = Op3 Ret

codeGen :: Free ParserF Void a -> Free3 M Void3 (a ': xs) ks b -> IMVar -> IΣVar -> (Free3 M Void3 xs ks b, ΣVars, IΣVar)
codeGen p terminal μ0 σ0 = traceShow m (m, vs, maxΣ)
  where
    ((m, maxΣ), vs) = runCodeGenStack (runCodeGen (histo absurd alg (traceShow p p)) terminal) μ0 0 σ0 Set.empty []
    alg = peephole |> (direct . imap present)

peephole :: ParserF (History ParserF (CodeGen b)) a -> Maybe (CodeGen b a)
peephole !(Era _ (Pure f) :<*>: Era p _) = Just $ CodeGen $ \(!m) -> runCodeGen p (fmapInstr f m)
peephole !(Era _ (Era _ (Pure f) :<*>: Era p _) :<*>: Era q _) = Just $ CodeGen $ \(!m) ->
  do qc <- runCodeGen q (Op3 (Lift2 f m))
     runCodeGen p qc
peephole !(Era _ (Try n (Era p _)) :<|>: Era q _) = Just $ CodeGen $ \(!m) ->
  do (decl, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation (isJust n) φ))
     qc <- freshΦ (runCodeGen q φ)
     return $! Op3 (SoftFork n pc qc decl)
peephole !(Era _ (Era _ (Try n (Era p _)) :*>: Era _ (Pure x)) :<|>: Era q _) = Just $ CodeGen $ \(!m) ->
  do (decl, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation (isJust n) (Op3 (Pop (Op3 (Push x φ))))))
     qc <- freshΦ (runCodeGen q φ)
     return $! Op3 (SoftFork n pc qc decl)
-- TODO: One more for fmap try
peephole !(ChainPost (Era _ (Pure x)) (Era op _)) = Just $ CodeGen $ \(!m) ->
  do μ <- askM
     σ <- freshΣ (_val x) (_code x)
     opc <- freshM (runCodeGen op (Op3 (ChainIter σ μ)))
     return $! Op3 (Push x (Op3 (ChainInit x σ opc μ m)))
peephole _ = Nothing

direct :: ParserF (CodeGen b) a -> CodeGen b a
direct !(Pure x)          = CodeGen $ \(!m) -> do return $! (Op3 (Push x m))
direct !(Satisfy p)       = CodeGen $ \(!m) -> do return $! (Op3 (Sat p m))
direct !(pf :<*>: px)     = CodeGen $ \(!m) -> do !pxc <- runCodeGen px (Op3 (Lift2 (lift' ($)) m)); runCodeGen pf pxc
direct !(p :*>: q)        = CodeGen $ \(!m) -> do !qc <- runCodeGen q m; runCodeGen p (Op3 (Pop qc))
direct !(p :<*: q)        = CodeGen $ \(!m) -> do !qc <- runCodeGen q (Op3 (Pop m)); runCodeGen p qc
direct !Empty             = CodeGen $ \(!m) -> do return $! Op3 Empt
direct !(p :<|>: q)       = CodeGen $ \(!m) ->
  do (decl, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation False φ))
     qc <- freshΦ (runCodeGen q φ)
     return $! Op3 (HardFork pc qc decl)
direct !(Try n p)         = CodeGen $ \(!m) -> do fmap (Op3 . Attempt n) (runCodeGen p (deadCommitOptimisation (isJust n) m))
direct !(LookAhead p)     = CodeGen $ \(!m) -> do fmap (Op3 . Look) (runCodeGen p (Op3 (Restore m)))
direct !(NotFollowedBy p) = CodeGen $ \(!m) -> do liftA2 (\p q -> Op3 (NegLook p q)) (runCodeGen p (Op3 (Restore (Op3 Empt)))) (return (Op3 (Push (lift' ()) m)))
direct !(Branch b p q)    = CodeGen $ \(!m) -> do !pc <- runCodeGen p (Op3 (Lift2 (WQ (flip ($)) [||flip ($)||]) m))
                                                  !qc <- runCodeGen q (Op3 (Lift2 (WQ (flip ($)) [||flip ($)||]) m))
                                                  runCodeGen b (Op3 (Case pc qc))
direct !(Match p fs qs)   = CodeGen $ \(!m) -> do !qcs <- traverse (flip runCodeGen m) qs
                                                  runCodeGen p (Op3 (Choices fs qcs))
direct !(Let _ !μ _)  = CodeGen $ \(!m) -> return $! tailCallOptimise μ m
direct !(ChainPre op p) = CodeGen $ \(!m) ->
  do μ <- askM
     σ <- freshΣ id [||id||]
     opc <- freshM (runCodeGen op (fmapInstr (lift' flip >*< lift' (.)) (Op3 (ChainIter σ μ))))
     pc <- freshM (runCodeGen p (Op3 (Lift2 (lift' ($)) m)))
     return $! Op3 (Push (lift' id) (Op3 (ChainInit (lift' id) σ opc μ pc)))
direct !(ChainPost p op) = CodeGen $ \(!m) ->
  do μ <- askM
     σ <- freshΣ Nothing [||Nothing||]
     opc <- freshM (runCodeGen op (fmapInstr (lift' (<$!>)) (Op3 (ChainIter σ μ))))
     let m' = Op3 (ChainInit (WQ Nothing [||Nothing||]) σ opc μ (fmapInstr (lift' fromJust) m))
     freshM (runCodeGen p (fmapInstr (lift' Just) m'))
direct !(Debug name p) = CodeGen $ \(!m) -> fmap (Op3 . LogEnter name) (runCodeGen p (Op3 (LogExit name m)))

tailCallOptimise :: MVar x -> Free3 M Void3 (x ': xs) ks a -> Free3 M Void3 xs ks a
tailCallOptimise μ (Op3 Ret) = Op3 (Jump μ)
tailCallOptimise μ k         = Op3 (Call μ k)

-- Thanks to the optimisation applied to the K stack, commit is deadcode before Ret or Halt
-- However, I'm not yet sure about the interactions with try yet...
deadCommitOptimisation :: Bool -> Free3 M Void3 xs ks a -> Free3 M Void3 xs ks a
deadCommitOptimisation True m       = Op3 (Commit True m)
deadCommitOptimisation _ (Op3 Ret)  = Op3 Ret
deadCommitOptimisation _ (Op3 Halt) = Op3 Halt
deadCommitOptimisation b m          = Op3 (Commit b m)

-- Refactor with asks
askM :: CodeGenStack (MVar a)
askM = lift (construct MVar)

askΦ :: CodeGenStack (ΦVar a)
askΦ = construct ΦVar

freshM :: CodeGenStack a -> CodeGenStack a
freshM = mapVFreshT newScope

freshΦ :: CodeGenStack a -> CodeGenStack a
freshΦ = newScope

ifSeenM :: MonadReader (Set IMVar) m => MVar x -> m a -> m a -> m a
ifSeenM (MVar v) seen unseen = 
  do isSeen <- asks (Set.member v)
     if isSeen then do seen 
     else do unseen

addM :: MonadReader (Set IMVar) m => MVar x -> m a -> m a
addM (MVar v) = local (Set.insert v)

makeΦ :: Free3 M Void3 (x ': xs) ks a -> CodeGenStack (Maybe (ΦDecl (Free3 M Void3) x xs ks a), Free3 M Void3 (x ': xs) ks a)
makeΦ m | elidable m = return $! (Nothing, m)
  where 
    -- This is double-φ optimisation:   If a φ-node points directly to another φ-node, then it can be elided
    elidable (Op3 (Join _)) = True
    -- This is terminal-φ optimisation: If a φ-node points directly to a terminal operation, then it can be elided
    elidable (Op3 Ret)      = True
    elidable (Op3 Halt)     = True
    elidable _              = False
makeΦ m =
  do φ <- askΦ
     let !decl = Just (φ, m)
     let !join = Op3 (Join φ)
     return $! (decl, join)

freshΣ :: a -> TExpQ a -> CodeGenStack (ΣVar a)
freshΣ x qx = 
  do σ <- lift (lift (construct ΣVar))
     modify' (ΣState x qx σ:)
     return $! σ
