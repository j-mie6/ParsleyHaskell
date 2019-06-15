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
import Machine                    (M(..), ΣVar(..), ΣState(..), ΣVars, IMVar, IΦVar, IΣVar, MVar(..), ΦVar(..), ΦDecl, fmapInstr, abstract, AbstractedStack)
import Indexed                    (IFunctor, Free(Op), History(Era), Void, imap, histo, present, (|>), absurd)
import Utils                      (TExpQ, lift', (>*<), WQ(..))
import Control.Applicative        (liftA2)
import Control.Monad              ((<$!>))
import Control.Monad.Reader       (ReaderT, ask, asks, runReaderT, local, MonadReader)
import Control.Monad.State.Strict (State, get, put, runState, MonadState)
import Fresh                      (VFreshT, HFreshT, runFreshT, evalFreshT, construct, MonadFresh(..), mapVFreshT)
import Control.Monad.Trans        (lift)
import Data.Set                   (Set)
import Data.Maybe                 (isJust, fromJust)
import Debug.Trace                (traceShow)
import qualified Data.Set as Set

type CodeGenStack a = VFreshT IΦVar (VFreshT IMVar (HFreshT IΣVar (ReaderT (Set IMVar) (State ΣVars)))) a
runCodeGenStack :: CodeGenStack a -> IMVar -> IΦVar -> IΣVar -> Set IMVar -> ΣVars -> (a, ΣVars)
runCodeGenStack m μ0 φ0 σ0 seen0 vs0 = 
  (flip runState vs0 . 
   flip runReaderT seen0 . 
   flip evalFreshT σ0 . 
   flip evalFreshT μ0 . 
   flip evalFreshT φ0) m

newtype CodeGen b xs ks a i = 
  CodeGen {runCodeGen :: forall xs' ks'. Free M Void (a ': xs') ks' b i -> CodeGenStack (Free M Void xs' ks' b i)}

codeGen :: Free ParserF Void '[] '[] a i -> IMVar -> (Free M Void '[] '[] a i, ΣVars)
codeGen p μ0 = traceShow m (m, vs)
  where
    (m, vs) = runCodeGenStack (runCodeGen (histo absurd alg (traceShow p p)) (Op Halt)) μ0 0 0 Set.empty []
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
direct !(Rec !μ !q)     = CodeGen $ \(!m) ->
  do ifSeenM μ
       (do return $! tailCallOptimise Nothing (MVar μ) m)
       (do n <- addM μ (runCodeGen q (Op Ret))
           return $! tailCallOptimise (Just (abstract n)) (MVar μ) m)
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

tailCallOptimise :: Maybe (AbstractedStack (Free M Void) x a i) -> MVar x -> Free M Void (x ': xs) ks a i -> Free M Void xs ks a i
tailCallOptimise body μ (Op Ret) = Op (Jump body μ)
tailCallOptimise body μ k        = Op (Call body μ k)

(><) :: (a -> x) -> (b -> y) -> (a, b) -> (x, y)
(f >< g) (x, y) = (f x, g y)

-- Refactor with asks
askM :: CodeGenStack (MVar a)
askM = lift (construct MVar)

askΦ :: CodeGenStack (ΦVar a)
askΦ = construct ΦVar

freshM :: CodeGenStack a -> CodeGenStack a
freshM = mapVFreshT newScope

freshΦ :: CodeGenStack a -> CodeGenStack a
freshΦ = newScope

ifSeenM :: MonadReader (Set IMVar) m => IMVar -> m a -> m a -> m a
ifSeenM v seen unseen = 
  do isSeen <- asks (Set.member v)
     if isSeen then do seen 
     else do unseen

addM :: MonadReader (Set IMVar) m => IMVar -> m a -> m a
addM μ = local (Set.insert μ)

makeΦ :: Free M Void (x ': xs) ks a i -> CodeGenStack (Maybe (ΦDecl (Free M Void) x xs ks a i), Free M Void (x ': xs) ks a i)
makeΦ m | elidable m = return $! (Nothing, m)
  where 
    -- This is double-φ optimisation:   If a φ-node points directly to another φ-node, then it can be elided
    elidable (Op (Join _)) = True
    -- This is terminal-φ optimisation: If a φ-node points directly to a terminal operation, then it can be elided
    elidable (Op Ret)      = True
    elidable (Op Halt)     = True
    elidable _             = False
makeΦ m =
  do φ <- askΦ
     let !decl = Just (φ, m)
     let !join = Op (Join φ)
     return $! (decl, join)

freshΣ :: a -> TExpQ a -> CodeGenStack (ΣVar a)
freshΣ x qx = 
  do σs <- get
     σ <- lift (lift (construct ΣVar))
     put (ΣState x qx σ:σs)
     return $! σ