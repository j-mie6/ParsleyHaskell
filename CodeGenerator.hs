{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}
module CodeGenerator (codeGen) where

import ParserAST                  (ParserF(..), MetaP(..))
import MachineAST                 (M(..), Handler(..), MetaM(..), IMVar, IΦVar, IΣVar, MVar(..), ΦVar(..), ΣVar(..), _Fmap, _App, _Modify, addCoins, refundCoins, drainCoins, freeCoins)
import MachineAnalyser            (coinsNeeded)
import Indexed                    (IFunctor, Fix, Fix3(In3), Cofree(..), imap, histo, extract, (|>))
import Utils                      (code, Quapplicative((>*<)))
import Defunc                     (Defunc(BLACK, COMPOSE, UNIT, ID), pattern FLIP_H)
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

newtype CodeGen q o b a = 
  CodeGen {runCodeGen :: forall xs r. Fix3 (M q o) (a ': xs) r b -> CodeGenStack (Fix3 (M q o) xs r b)}

-- TODO, ensure that let-bound parsers do not use finalise to add coins!
codeGen :: Quapplicative q => Bool -> Fix (ParserF q) a -> IMVar -> IΣVar -> (Fix3 (M q o) '[] a b, IΣVar)
codeGen letBound p μ0 σ0 = trace ("GENERATING: " ++ show p ++ "\nMACHINE: " ++ show m) $ (m, maxΣ)
  where
    (m, maxΣ) = finalise (histo alg p)
    alg = peephole |> (\x -> CodeGen (direct (imap extract x)))
    finalise cg = 
      let (m, maxΣ) = runCodeGenStack (runCodeGen cg (In3 Ret)) μ0 0 σ0 
          n = coinsNeeded m
      in (if letBound then m else addCoins n m, maxΣ)

pattern f :<$>: p <- (_ :< Pure f) :<*>: (p :< _)
pattern p :$>: x <- (_ :< p) :*>: (_ :< Pure x)
pattern LiftA2 f p q <- (_ :< ((_ :< Pure f) :<*>: (p :< _))) :<*>: (q :< _)
pattern TryOrElse p q <- (_ :< Try (p :< _)) :<|>: (q :< _)

rollbackHandler :: Fix3 (M q o) (o : xs) r a
rollbackHandler = In3 (Seek (In3 Empt))

peephole :: Quapplicative q => ParserF q (Cofree (ParserF q) (CodeGen q o b)) a -> Maybe (CodeGen q o b a)
peephole (f :<$>: p) = Just $ CodeGen $ \m -> runCodeGen p (In3 (_Fmap f m))
peephole (LiftA2 f p q) = Just $ CodeGen $ \m ->
  do qc <- runCodeGen q (In3 (Lift2 f m))
     runCodeGen p qc
peephole (TryOrElse p q) = Just $ CodeGen $ \m -> -- FIXME!
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     fmap (binder . In3 . Catch pc . In3 . Seek) (freshΦ (runCodeGen q φ))
peephole ((_ :< ((Try (p :< _)) :$>: x)) :<|>: (q :< _)) = Just $ CodeGen $ \m ->
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation (In3 (Pop (In3 (Push x φ))))))
     fmap (binder . In3 . Catch pc . In3 . Seek) (freshΦ (runCodeGen q φ))
peephole (MetaP RequiresCut (_ :< ((p :< _) :<|>: (q :< _)))) = Just $ CodeGen $ \m -> 
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     qc <- freshΦ (runCodeGen q φ)
     return $! binder (In3 (Catch pc (In3 (Handler (Parsec qc)))))
peephole (MetaP RequiresCut (_ :< ChainPre (op :< _) (p :< _))) = Just $ CodeGen $ \m -> 
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In3 (_Fmap (FLIP_H COMPOSE) (In3 (_Modify σ (In3 (ChainIter σ μ)))))))
     pc <- freshM (runCodeGen p (In3 (_App m)))
     return $! In3 (Push ID (In3 (Make σ (In3 (ChainInit σ opc μ (In3 (Get σ (addCoins (coinsNeeded pc) pc))))))))
peephole (MetaP RequiresCut (_ :< ChainPost (p :< _) (op :< _))) = Just $ CodeGen $ \m -> 
  do μ <- askM
     σ <- freshΣ
     let nm = coinsNeeded m
     opc <- freshM (runCodeGen op (In3 (_Modify σ (In3 (ChainIter σ μ)))))
     freshM (runCodeGen p (In3 (Make σ (In3 (ChainInit σ opc μ (In3 (Get σ (addCoins nm m))))))))
peephole (MetaP Cut (_ :< ChainPre (op :< _) (p :< _))) = Just $ CodeGen $ \m -> 
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In3 (_Fmap (FLIP_H COMPOSE) (In3 (_Modify σ (In3 (ChainIter σ μ)))))))
     let nop = coinsNeeded opc
     pc <- freshM (runCodeGen p (In3 (_App m)))
     return $! In3 (Push ID (In3 (Make σ (In3 (ChainInit σ (addCoins nop opc) μ (In3 (Get σ (addCoins (coinsNeeded pc) pc))))))))
-- TODO: One more for fmap try
peephole _ = Nothing

direct :: Quapplicative q => ParserF q (CodeGen q o b) a -> Fix3 (M q o) (a ': xs) r b -> CodeGenStack (Fix3 (M q o) xs r b)
direct (Pure x)      m = do return $! In3 (Push x m)
direct (Satisfy p)   m = do return $! In3 (Sat p m)
direct (pf :<*>: px) m = do pxc <- runCodeGen px (In3 (_App m)); runCodeGen pf pxc
direct (p :*>: q)    m = do qc <- runCodeGen q m; runCodeGen p (In3 (Pop qc))
direct (p :<*: q)    m = do qc <- runCodeGen q (In3 (Pop m)); runCodeGen p qc  
direct Empty         m = do return $! In3 Empt
direct (p :<|>: q) m = 
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     qc <- freshΦ (runCodeGen q φ)
     let np = coinsNeeded pc
     let nq = coinsNeeded qc
     let dp = np - (min np nq)
     let dq = nq - (min np nq)
     return $! binder (In3 (Catch (addCoins dp pc) (In3 (Handler (Parsec (addCoins dq qc))))))
direct (Try p)       m = do fmap (In3 . flip Catch rollbackHandler) (runCodeGen p (deadCommitOptimisation m))
direct (LookAhead p) m = 
  do n <- fmap coinsNeeded (runCodeGen p (In3 Empt)) -- Dodgy hack, but oh well
     fmap (In3 . Tell) (runCodeGen p (In3 (Swap (In3 (Seek (refundCoins n m))))))
direct (NotFollowedBy p) m = 
  do pc <- runCodeGen p (In3 (Pop (In3 (Seek (In3 (Commit (In3 Empt)))))))
     let np = coinsNeeded pc
     let nm = coinsNeeded m
     return $! In3 (Catch (addCoins (max (np - nm) 0) (In3 (Tell pc))) (In3 (Seek (In3 (Push UNIT m)))))
direct (Branch b p q) m = 
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (In3 (Swap (In3 (_App φ)))))
     qc <- freshΦ (runCodeGen q (In3 (Swap (In3 (_App φ)))))
     let minc = coinsNeeded (In3 (Case pc qc))
     let dp = max 0 (coinsNeeded pc - minc)
     let dq = max 0 (coinsNeeded qc - minc)
     fmap binder (runCodeGen b (In3 (Case (addCoins dp pc) (addCoins dq qc))))
direct (Match p fs qs def) m = 
  do (binder, φ) <- makeΦ m
     qcs <- traverse (\q -> freshΦ (runCodeGen q φ)) qs
     defc <- freshΦ (runCodeGen def φ)
     let minc = coinsNeeded (In3 (Choices fs qcs defc))
     let defc':qcs' = map (max 0 . subtract minc . coinsNeeded >>= addCoins) (defc:qcs)
     fmap binder (runCodeGen p (In3 (Choices fs qcs' defc')))
direct (Let _ μ _) m = return $! tailCallOptimise μ m
direct (ChainPre op p) m =
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In3 (_Fmap (FLIP_H COMPOSE) (In3 (_Modify σ (In3 (ChainIter σ μ)))))))
     let nop = coinsNeeded opc
     pc <- freshM (runCodeGen p (In3 (_App m)))
     return $! In3 (Push ID (In3 (Make σ (In3 (ChainInit σ (addCoins nop opc) μ (In3 (Get σ pc)))))))
direct (ChainPost p op) m =
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In3 (_Modify σ (In3 (ChainIter σ μ)))))
     let nop = coinsNeeded opc
     freshM (runCodeGen p (In3 (Make σ (In3 (ChainInit σ (addCoins nop opc) μ (In3 (Get σ m)))))))
direct (Debug name p) m = do fmap (In3 . LogEnter name . In3 . flip Catch (In3 (Handler (Log name)))) (runCodeGen p (In3 (LogExit name m)))
direct (MetaP Cut p) m = do runCodeGen p (addCoins (coinsNeeded m) m)

tailCallOptimise :: MVar x -> Fix3 (M q o) (x ': xs) r a -> Fix3 (M q o) xs r a
tailCallOptimise μ (In3 Ret) = In3 (Jump μ)
tailCallOptimise μ k         = In3 (Call μ k)

-- Thanks to the optimisation applied to the K stack, commit is deadcode before Ret or Halt
-- However, I'm not yet sure about the interactions with try yet...
deadCommitOptimisation :: Fix3 (M q o) xs r a -> Fix3 (M q o) xs r a
deadCommitOptimisation (In3 Ret) = In3 Ret
deadCommitOptimisation m         = In3 (Commit m)

-- Refactor with asks
askM :: CodeGenStack (MVar a)
askM = lift (construct MVar)

askΦ :: CodeGenStack (ΦVar a)
askΦ = construct ΦVar

freshM :: CodeGenStack a -> CodeGenStack a
freshM = mapVFreshT newScope

freshΦ :: CodeGenStack a -> CodeGenStack a
freshΦ = newScope

makeΦ :: Fix3 (M q o) (x ': xs) r a -> CodeGenStack (Fix3 (M q o) xs r a -> Fix3 (M q o) xs r a, Fix3 (M q o) (x ': xs) r a)
makeΦ m | elidable m = return $! (id, m)
  where
    -- This is double-φ optimisation:   If a φ-node points directly to another φ-node, then it can be elided
    elidable (In3 (Join _)) = True
    -- This is terminal-φ optimisation: If a φ-node points directly to a terminal operation, then it can be elided
    elidable (In3 Ret)      = True
    elidable _              = False
makeΦ m = let n = coinsNeeded m in fmap (\φ -> (In3 . MkJoin φ (addCoins n m), drainCoins n (In3 (Join φ)))) askΦ

freshΣ :: CodeGenStack (ΣVar a)
freshΣ = lift (lift (construct ΣVar))
