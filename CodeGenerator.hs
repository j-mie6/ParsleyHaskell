{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
module CodeGenerator (codeGen) where

import ParserAST                  (ParserF(..))
import Machine                    (M(..), ΣVar(..), ΣState(..), ΣVars, IMVar, IΦVar, MVar(..), ΦVar(..), ΦDecl, fmapInstr, abstract)
import Indexed                    (IFunctor, Free(Op), History(Era), Void, imap, histo, present, (|>), absurd)
import Utils                      (TExpQ, lift', (>*<), WQ(..))
import Control.Applicative        (liftA2)
import Control.Monad              ((<$!>))
import Control.Monad.Reader       (ReaderT, ask, asks, runReaderT, local, MonadReader)
import Control.Monad.State.Strict (State, get, put, runState, MonadState)
import Fresh                      (VFreshT, runFreshT, evalFreshT, construct, MonadFresh(..))
import Data.Map.Strict            (Map)
import Data.Maybe                 (isJust, fromJust)
import Debug.Trace                (traceShow)
import qualified Data.Map.Strict as Map

newtype CodeGen b xs ks a i = CodeGen {runCodeGen :: forall xs' ks'. Free M Void (a ': xs') ks' b i
                                                  -> VFreshT IΦVar (ReaderT (Map IMVar IMVar, IMVar) (State ΣVars)) (Free M Void xs' ks' b i)}

codeGen :: Free ParserF Void '[] '[] a i -> (Free M Void '[] '[] a i, ΣVars)
codeGen p = traceShow m (m, vs)
  where
    (m, vs) = runState (runReaderT (evalFreshT (runCodeGen (histo absurd alg (traceShow p p)) (Op Halt)) 0) (Map.empty, 0)) []
    alg = peephole |> (direct . imap present)

peephole :: ParserF (History ParserF (CodeGen b)) xs ks a i -> Maybe (CodeGen b xs ks a i)
peephole !(Era _ (Pure f) :<*>: Era p _) = Just $ CodeGen $ \(!m) -> runCodeGen p (fmapInstr f m)
peephole !(Era _ (Era _ (Pure f) :<*>: Era p _) :<*>: Era q _) = Just $ CodeGen $ \(!m) ->
  do qc <- runCodeGen q (Op (Lift2 f m))
     runCodeGen p qc
peephole !(Era _ (Try n (Era p _)) :<|>: Era q _) = Just $ CodeGen $ \(!m) ->
  do (decl, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (Op (Commit (isJust n) φ)))
     qc <- freshΦ (runCodeGen q φ)
     return $! Op (SoftFork n pc qc decl)
peephole !(Era _ (Era _ (Try n (Era p _)) :*>: Era _ (Pure x)) :<|>: Era q _) = Just $ CodeGen $ \(!m) ->
  do (decl, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (Op (Commit (isJust n) (Op (Pop (Op (Push x φ)))))))
     qc <- freshΦ (runCodeGen q φ)
     return $! Op (SoftFork n pc qc decl)
-- TODO: One more for fmap try
peephole !(ChainPost (Era _ (Pure x)) (Era op _)) = Just $ CodeGen $ \(!m) ->
  do μ <- askM
     σ <- freshΣ (_val x) (_code x)
     opc <- freshM (runCodeGen op (Op (ChainIter σ μ)))
     return $! Op (Push x (Op (ChainInit x σ opc μ m)))
peephole _ = Nothing

direct :: ParserF (CodeGen b) xs ks a i -> CodeGen b xs ks a i
direct !(Pure x)          = CodeGen $ \(!m) -> do return $! (Op (Push x m))
direct !(Satisfy p)       = CodeGen $ \(!m) -> do return $! (Op (Sat p m))
direct !(pf :<*>: px)     = CodeGen $ \(!m) -> do !pxc <- runCodeGen px (Op (Lift2 (lift' ($)) m)); runCodeGen pf pxc
direct !(p :*>: q)        = CodeGen $ \(!m) -> do !qc <- runCodeGen q m; runCodeGen p (Op (Pop qc))
direct !(p :<*: q)        = CodeGen $ \(!m) -> do !qc <- runCodeGen q (Op (Pop m)); runCodeGen p qc
direct !Empty             = CodeGen $ \(!m) -> do return $! Op Empt
direct !(p :<|>: q)       = CodeGen $ \(!m) ->
  do (decl, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (Op (Commit False φ)))
     qc <- freshΦ (runCodeGen q φ)
     return $! Op (HardFork pc qc decl)
direct !(Try n p)         = CodeGen $ \(!m) -> do fmap (Op . Attempt n) (runCodeGen p (Op (Commit (isJust n) m)))
direct !(LookAhead p)     = CodeGen $ \(!m) -> do fmap (Op . Look) (runCodeGen p (Op (Restore m)))
direct !(NotFollowedBy p) = CodeGen $ \(!m) -> do liftA2 (\p q -> Op (NegLook p q)) (runCodeGen p (Op (Restore (Op Empt)))) (return (Op (Push (lift' ()) m)))
direct !(Branch b p q)    = CodeGen $ \(!m) -> do !pc <- runCodeGen p (Op (Lift2 (WQ (flip ($)) [||flip ($)||]) m))
                                                  !qc <- runCodeGen q (Op (Lift2 (WQ (flip ($)) [||flip ($)||]) m))
                                                  runCodeGen b (Op (Case pc qc))
direct !(Match p fs qs)   = CodeGen $ \(!m) -> do !qcs <- traverse (flip runCodeGen m) qs
                                                  runCodeGen p (Op (Choices fs qcs))
direct !(Rec !v !q)     = CodeGen $ \(!m) ->
  do seen <- lookupM v; case seen of
       Just μ -> do return $! Op (MuCall μ m)
       Nothing  -> do μ <- askM
                      n <- renameM v μ (runCodeGen q (Op Ret))
                      return $! Op (Call (abstract n) μ m)
direct !(ChainPre op p) = CodeGen $ \(!m) ->
  do μ <- askM
     σ <- freshΣ id [||id||]
     opc <- freshM (runCodeGen op (fmapInstr (lift' flip >*< lift' (.)) (Op (ChainIter σ μ))))
     pc <- freshM (runCodeGen p (Op (Lift2 (lift' ($)) m)))
     return $! Op (Push (lift' id) (Op (ChainInit (lift' id) σ opc μ pc)))
direct !(ChainPost p op) = CodeGen $ \(!m) ->
  do μ <- askM
     σ <- freshΣ Nothing [||Nothing||]
     opc <- freshM (runCodeGen op (fmapInstr (lift' (<$!>)) (Op (ChainIter σ μ))))
     let m' = Op (ChainInit (WQ Nothing [||Nothing||]) σ opc μ (fmapInstr (lift' fromJust) m))
     freshM (runCodeGen p (fmapInstr (lift' Just) m'))
direct !(Debug name p) = CodeGen $ \(!m) -> fmap (Op . LogEnter name) (runCodeGen p (Op (LogExit name m)))

(><) :: (a -> x) -> (b -> y) -> (a, b) -> (x, y)
(f >< g) (x, y) = (f x, g y)

-- Refactor with asks
askM :: MonadReader (r1, IMVar) m => m (MVar a)
askM = asks (MVar . snd)

askΦ :: MonadFresh IΦVar m => m (ΦVar a)
askΦ = construct ΦVar

lookupM :: MonadReader (Map IMVar IMVar, IMVar) m => IMVar -> m (Maybe (MVar a))
lookupM v = asks (fmap MVar . Map.lookup v . fst)

freshM :: MonadReader (r1, IMVar) m => m a -> m a
freshM = local (id >< (+1))

freshΦ :: MonadFresh IΦVar m => m a -> m a
freshΦ = newScope

renameM :: MonadReader (Map IMVar IMVar, IMVar) m => IMVar -> MVar x -> m a -> m a
renameM old (MVar new) = local ((Map.insert old new) >< (const (new+1)))

makeΦ :: MonadFresh IΦVar m => Free M Void (x ': xs) ks a i -> m (Maybe (ΦDecl (Free M Void) x xs ks a i), Free M Void (x ': xs) ks a i)
-- This is double-φ optimisation: If a φ-node points directly to another φ-node, then it can be elided
makeΦ m@(Op (Join _)) = return $! (Nothing, m)
makeΦ m =
  do φ <- askΦ
     let !decl = Just (φ, m)
     let !join = Op (Join φ)
     return $! (decl, join)

freshΣ :: MonadState ΣVars m => a -> TExpQ a -> m (ΣVar a)
freshΣ x qx = 
  do σs <- get
     let σ = nextΣ σs
     put (ΣState x qx σ:σs)
     return $! σ
  where
    nextΣ []                      = ΣVar 0
    nextΣ (ΣState _ _ (ΣVar x):_) = ΣVar (x+1)