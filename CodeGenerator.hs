{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}
module CodeGenerator (codeGen, halt, ret) where

import ParserAST                  (ParserF(..))
import Machine                    (M(..), IMVar, IΦVar, IΣVar, MVar(..), ΦVar(..), ΣVar(..), ΦDecl, _Fmap, _App, _Modify)
import Indexed                    (IFunctor, Free, Free3(Op3), History(Era), Void1, Void3, imap, histo, present, (|>), absurd)
import Utils                      (code, (>*<), WQ(..))
import Control.Applicative        (liftA2)
import Control.Monad.Reader       (Reader, ask, asks, runReader, local, MonadReader)
import Control.Monad.State.Strict (State, get, modify', runState, MonadState)
import Fresh                      (VFreshT, HFresh, runFreshT, runFresh, evalFreshT, construct, MonadFresh(..), mapVFreshT)
import Control.Monad.Trans        (lift)
import Data.Set                   (Set)
import Data.Maybe                 (isJust)
import Debug.Trace                (traceShow, trace)
import Data.Void                  (Void)
import qualified Data.Set as Set

type CodeGenStack a = VFreshT IΦVar (VFreshT IMVar (HFresh IΣVar)) a
runCodeGenStack :: CodeGenStack a -> IMVar -> IΦVar -> IΣVar -> (a, IΣVar)
runCodeGenStack m μ0 φ0 σ0 = 
  (flip runFresh σ0 . 
   flip evalFreshT μ0 . 
   flip evalFreshT φ0) m

newtype CodeGen o b a = 
  CodeGen {runCodeGen :: forall xs r. Free3 (M o) Void3 (a ': xs) r b -> CodeGenStack (Free3 (M o) Void3 xs r b)}

halt :: Free3 (M o) Void3 '[a] Void a
halt = Op3 Halt

ret :: Free3 (M o) Void3 '[x] x a
ret = Op3 Ret

codeGen :: Free ParserF Void1 a -> Free3 (M o) Void3 (a ': xs) r b -> IMVar -> IΣVar -> (Free3 (M o) Void3 xs r b, IΣVar)
codeGen p terminal μ0 σ0 = trace ("GENERATING: " ++ show p ++ "\nMACHINE: " ++ show m) $ (m, maxΣ)
  where
    (m, maxΣ) = runCodeGenStack (runCodeGen (histo absurd alg p) terminal) μ0 0 σ0
    alg = peephole |> (\x -> CodeGen (direct (imap present x)))

pattern f :<$>: p <- Era _ (Pure f) :<*>: Era p _
pattern p :$>: x <- Era _ p :*>: Era _ (Pure x)
pattern LiftA2 f p q <- Era _ (Era _ (Pure f) :<*>: Era p _) :<*>: Era q _
pattern TryOrElse n p q <- Era _ (Try n (Era p _)) :<|>: Era q _

peephole :: ParserF (History ParserF (CodeGen o b)) a -> Maybe (CodeGen o b a)
peephole (f :<$>: p) = Just $ CodeGen $ \m -> runCodeGen p (Op3 (_Fmap f m))
peephole (LiftA2 f p q) = Just $ CodeGen $ \m ->
  do qc <- runCodeGen q (Op3 (Lift2 f m))
     runCodeGen p qc
peephole (TryOrElse n p q) = Just $ CodeGen $ \m ->
  do (decl, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation (isJust n) φ))
     qc <- freshΦ (runCodeGen q φ)
     return $! Op3 (SoftFork n pc qc decl)
peephole (Era _ ((Try n (Era p _)) :$>: x) :<|>: Era q _) = Just $ CodeGen $ \m ->
  do (decl, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation (isJust n) (Op3 (Pop (Op3 (Push x φ))))))
     qc <- freshΦ (runCodeGen q φ)
     return $! Op3 (SoftFork n pc qc decl)
-- TODO: One more for fmap try
peephole _ = Nothing

direct :: ParserF (CodeGen o b) a -> Free3 (M o) Void3 (a ': xs) r b -> CodeGenStack (Free3 (M o) Void3 xs r b)
direct (Pure x)      m = do return $! (Op3 (Push x m))
direct (Satisfy p)   m = do return $! (Op3 (Sat p m))
direct (pf :<*>: px) m = do pxc <- runCodeGen px (Op3 (_App m)); runCodeGen pf pxc
direct (p :*>: q)    m = do qc <- runCodeGen q m; runCodeGen p (Op3 (Pop qc))
direct (p :<*: q)    m = do qc <- runCodeGen q (Op3 (Pop m)); runCodeGen p qc
direct Empty         m = do return $! Op3 Empt
direct (p :<|>: q)   m =
  do (decl, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation False φ))
     qc <- freshΦ (runCodeGen q φ)
     return $! Op3 (HardFork pc qc decl)
direct (Try n p)         m = do fmap (Op3 . Attempt n) (runCodeGen p (deadCommitOptimisation (isJust n) m))
direct (LookAhead p)     m = do fmap (Op3 . Tell) (runCodeGen p (Op3 (Swap (Op3 (Seek m)))))
direct (NotFollowedBy p) m = do pc <- runCodeGen p (Op3 (Pop (Op3 (Seek (Op3 (Commit False (Op3 Empt)))))))
                                return $! Op3 (SoftFork Nothing (Op3 (Tell pc)) (Op3 (Push (code ()) m)) Nothing)
direct (Branch b p q)    m = do (decl, φ) <- makeΦ m
                                pc <- freshΦ (runCodeGen p (Op3 (Swap (Op3 (_App φ)))))
                                qc <- freshΦ (runCodeGen q (Op3 (Swap (Op3 (_App φ)))))
                                runCodeGen b (Op3 (Case pc qc decl))
direct (Match p fs qs def) m = do (decl, φ) <- makeΦ m
                                  qcs <- traverse (freshΦ . flip runCodeGen φ) qs
                                  defc <- freshΦ (runCodeGen def φ)
                                  runCodeGen p (Op3 (Choices fs qcs defc decl))
direct (Let _ !μ _) m = return $! tailCallOptimise μ m
direct (ChainPre op p) m =
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (Op3 (_Fmap ([flip (code (.))]) (Op3 (_Modify σ (Op3 (ChainIter σ μ)))))))
     pc <- freshM (runCodeGen p (Op3 (_App m)))
     return $! Op3 (Push (code id) (Op3 (Make σ (Op3 (ChainInit σ opc μ (Op3 (Get σ pc)))))))
direct (ChainPost p op) m =
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (Op3 (_Modify σ (Op3 (ChainIter σ μ)))))
     freshM (runCodeGen p (Op3 (Make σ (Op3 (ChainInit σ opc μ (Op3 (Get σ m)))))))
direct (Debug name p) m = do fmap (Op3 . LogEnter name) (runCodeGen p (Op3 (LogExit name m)))

tailCallOptimise :: MVar x -> Free3 (M o) Void3 (x ': xs) r a -> Free3 (M o) Void3 xs r a
tailCallOptimise μ (Op3 Ret) = Op3 (Jump μ)
tailCallOptimise μ k         = Op3 (Call μ k)

-- Thanks to the optimisation applied to the K stack, commit is deadcode before Ret or Halt
-- However, I'm not yet sure about the interactions with try yet...
deadCommitOptimisation :: Bool -> Free3 (M o) Void3 xs r a -> Free3 (M o) Void3 xs r a
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

makeΦ :: Free3 (M o) Void3 (x ': xs) r a -> CodeGenStack (Maybe (ΦDecl (Free3 (M o) Void3) x xs r a), Free3 (M o) Void3 (x ': xs) r a)
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
     let decl = Just (φ, m)
     let join = Op3 (Join φ)
     return $! (decl, join)

freshΣ :: CodeGenStack (ΣVar a)
freshΣ = lift (lift (construct ΣVar))
