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

import ParserAST                  (ParserF(..){- MetaP(..), CoinType(..)-})
import MachineAST                 (M(..), MetaM(..), IMVar, IΦVar, IΣVar, MVar(..), ΦVar(..), ΣVar(..), _Fmap, _App, _Modify)
import Indexed                    (IFunctor, Fix, Fix3(In3), Cofree(..), imap, histo, extract, (|>))
import Utils                      (code, (>*<), WQ(..))
import Defunc                     (Defunc(BLACK))
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
  CodeGen {runCodeGen :: forall xs r. Fix3 (M o) (a ': xs) r b -> CodeGenStack (Fix3 (M o) xs r b)}

halt :: Fix3 (M o) '[a] Void a
halt = In3 Halt

ret :: Fix3 (M o) '[x] x a
ret = In3 Ret

codeGen :: Fix ParserF a -> Fix3 (M o) (a ': xs) r b -> IMVar -> IΣVar -> (Fix3 (M o) xs r b, IΣVar)
codeGen p terminal μ0 σ0 = trace ("GENERATING: " ++ show p ++ "\nMACHINE: " ++ show m) $ (m, maxΣ)
  where
    (m, maxΣ) = runCodeGenStack (runCodeGen (histo alg p) terminal) μ0 0 σ0
    alg = {-peephole |> -}(\x -> CodeGen (direct (imap extract x)))

--pattern f :<$>: p <- (_ :< Pure f) :<*>: (p :< _)
--pattern p :$>: x <- (_ :< p) :*>: (_ :< Pure x)
--pattern LiftA2 f p q <- (_ :< ((_ :< Pure f) :<*>: (p :< _))) :<*>: (q :< _)
--pattern TryOrElse p q <- (_ :< Try (p :< _)) :<|>: (q :< _)

{-peephole :: ParserF (Cofree ParserF (CodeGen o b)) a -> Maybe (CodeGen o b a)
peephole (f :<$>: p) = Just $ CodeGen $ \m -> runCodeGen p (In3 (_Fmap f m))
peephole (LiftA2 f p q) = Just $ CodeGen $ \m ->
  do qc <- runCodeGen q (In3 (Lift2 (BLACK f) m))
     runCodeGen p qc
peephole (TryOrElse p q) = Just $ CodeGen $ \m ->
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     fmap (binder . In3 . SoftFork pc) (freshΦ (runCodeGen q φ))
peephole ((_ :< ((Try (p :< _)) :$>: x)) :<|>: (q :< _)) = Just $ CodeGen $ \m ->
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation (In3 (Pop (In3 (Push x φ))))))
     fmap (binder . In3 . SoftFork pc) (freshΦ (runCodeGen q φ))
-- TODO: One more for fmap try
peephole _ = Nothing-}

direct :: ParserF (CodeGen o b) a -> Fix3 (M o) (a ': xs) r b -> CodeGenStack (Fix3 (M o) xs r b)
direct (Pure x)      m = do return $! (In3 (Push x m))
direct (Satisfy p)   m = do return $! (In3 (Sat p m))
direct (pf :<*>: px) m = do pxc <- runCodeGen px (In3 (_App m)); runCodeGen pf pxc
direct (p :*>: q)    m = do qc <- runCodeGen q m; runCodeGen p (In3 (Pop qc))
direct (p :<*: q)    m = do qc <- runCodeGen q (In3 (Pop m)); runCodeGen p qc
direct Empty         m = do return $! In3 Empt
direct (p :<|>: q)   m =
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     fmap (binder . In3 . HardFork pc) (freshΦ (runCodeGen q φ))
direct (Try p)           m = do fmap (In3 . Attempt) (runCodeGen p (deadCommitOptimisation m))
direct (LookAhead p)     m = do fmap (In3 . Tell) (runCodeGen p (In3 (Swap (In3 (Seek m)))))
direct (NotFollowedBy p) m = do pc <- runCodeGen p (In3 (Pop (In3 (Seek (In3 (Commit (In3 Empt)))))))
                                return $! In3 (SoftFork (In3 (Tell pc)) (In3 (Push (code ()) m)))
direct (Branch b p q)    m = do (binder, φ) <- makeΦ m
                                pc <- freshΦ (runCodeGen p (In3 (Swap (In3 (_App φ)))))
                                qc <- freshΦ (runCodeGen q (In3 (Swap (In3 (_App φ)))))
                                fmap binder (runCodeGen b (In3 (Case pc qc)))
direct (Match p fs qs def) m = do (binder, φ) <- makeΦ m
                                  qcs <- traverse (freshΦ . flip runCodeGen φ) qs
                                  defc <- freshΦ (runCodeGen def φ)
                                  fmap binder (runCodeGen p (In3 (Choices fs qcs defc)))
direct (Let _ !μ _) m = return $! tailCallOptimise μ m
direct (ChainPre op p) m =
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In3 (_Fmap ([flip (code (.))]) (In3 (_Modify σ (In3 (ChainIter σ μ)))))))
     pc <- freshM (runCodeGen p (In3 (_App m)))
     return $! In3 (Push (code id) (In3 (Make σ (In3 (ChainInit σ opc μ (In3 (Get σ pc)))))))
direct (ChainPost p op) m =
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In3 (_Modify σ (In3 (ChainIter σ μ)))))
     freshM (runCodeGen p (In3 (Make σ (In3 (ChainInit σ opc μ (In3 (Get σ m)))))))
direct (Debug name p) m = do fmap (In3 . LogEnter name) (runCodeGen p (In3 (LogExit name m)))
--direct (MetaP (ConstInput Costs n) p) m    = do fmap (In3 . MetaM (AddCoins n)) (runCodeGen p m)
--direct (MetaP (ConstInput Refunded n) p) m = do fmap (In3 . MetaM (AddCoins n)) (runCodeGen p m)
--direct (MetaP (ConstInput Free n) p) m     = do runCodeGen p (In3 (MetaM (RefundCoins n) m))
--direct (MetaP (ConstInput Transports n) p) m   = do runCodeGen p (In3 (MetaM (RefundCoins n) m))
--direct (MetaP _ p) m = runCodeGen p m

tailCallOptimise :: MVar x -> Fix3 (M o) (x ': xs) r a -> Fix3 (M o) xs r a
tailCallOptimise μ (In3 Ret) = In3 (Jump μ)
tailCallOptimise μ k         = In3 (Call μ k)

-- Thanks to the optimisation applied to the K stack, commit is deadcode before Ret or Halt
-- However, I'm not yet sure about the interactions with try yet...
deadCommitOptimisation :: Fix3 (M o) xs r a -> Fix3 (M o) xs r a
deadCommitOptimisation (In3 Ret)  = In3 Ret
deadCommitOptimisation (In3 Halt) = In3 Halt
deadCommitOptimisation m          = In3 (Commit m)

-- Refactor with asks
askM :: CodeGenStack (MVar a)
askM = lift (construct MVar)

askΦ :: CodeGenStack (ΦVar a)
askΦ = construct ΦVar

freshM :: CodeGenStack a -> CodeGenStack a
freshM = mapVFreshT newScope

freshΦ :: CodeGenStack a -> CodeGenStack a
freshΦ = newScope

makeΦ :: Fix3 (M o) (x ': xs) r a -> CodeGenStack (Fix3 (M o) xs r a -> Fix3 (M o) xs r a, Fix3 (M o) (x ': xs) r a)
makeΦ m | elidable m = return $! (id, m)
  where
    -- This is double-φ optimisation:   If a φ-node points directly to another φ-node, then it can be elided
    elidable (In3 (Join _)) = True
    -- This is terminal-φ optimisation: If a φ-node points directly to a terminal operation, then it can be elided
    elidable (In3 Ret)      = True
    elidable (In3 Halt)     = True
    elidable _              = False
makeΦ m@(In3 (MetaM (RefundCoins n) _)) = fmap (\φ -> (In3 . MkJoin φ m, In3 (MetaM (DrainCoins n) (In3 (Join φ))))) askΦ
makeΦ m = fmap (\φ -> (In3 . MkJoin φ m, In3 (Join φ))) askΦ

freshΣ :: CodeGenStack (ΣVar a)
freshΣ = lift (lift (construct ΣVar))
