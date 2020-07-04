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
import MachineAST                 (M(..), MetaM(..), IMVar, IΦVar, IΣVar, MVar(..), ΦVar(..), ΣVar(..), One, _Fmap, _App, _Modify, _If, addCoins, refundCoins, drainCoins, freeCoins)
import MachineAnalyser            (coinsNeeded)
import Indexed                    (IFunctor, Fix, Fix4(In4), Cofree(..), Nat(..), imap, histo, extract, (|>))
import Utils                      (code, Quapplicative((>*<)))
import Defunc                     (Defunc(BLACK, COMPOSE, UNIT, ID), DefuncM(USER, SAME), pattern FLIP_H)
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
  CodeGen {runCodeGen :: forall xs n r. Fix4 (M q o) (a : xs) (Succ n) r b -> CodeGenStack (Fix4 (M q o) xs (Succ n) r b)}

-- TODO, ensure that let-bound parsers do not use finalise to add coins!
codeGen :: Quapplicative q => Bool -> Fix (ParserF q) a -> IMVar -> IΣVar -> (Fix4 (M q o) '[] One a b, IΣVar)
codeGen letBound p μ0 σ0 = trace ("GENERATING: " ++ show p ++ "\nMACHINE: " ++ show m) $ (m, maxΣ)
  where
    (m, maxΣ) = finalise (histo alg p)
    alg = peephole |> (\x -> CodeGen (direct (imap extract x)))
    finalise cg =
      let (m, maxΣ) = runCodeGenStack (runCodeGen cg (In4 Ret)) μ0 0 σ0
          n = coinsNeeded m
      in (if letBound then m else addCoins n m, maxΣ)

pattern f :<$>: p <- (_ :< Pure f) :<*>: (p :< _)
pattern p :$>: x <- (_ :< p) :*>: (_ :< Pure x)
pattern LiftA2 f p q <- (_ :< ((_ :< Pure f) :<*>: (p :< _))) :<*>: (q :< _)
pattern TryOrElse p q <- (_ :< Try (p :< _)) :<|>: (q :< _)

rollbackHandler :: Fix4 (M q o) (o : xs) (Succ n) r a
rollbackHandler = In4 (Seek (In4 Empt))

parsecHandler :: Fix4 (M q o) xs (Succ n) r a -> Fix4 (M q o) (o : xs) (Succ n) r a
parsecHandler k = In4 (Tell (In4 (Lift2 SAME (In4 (_If k (In4 Empt))))))

peephole :: Quapplicative q => ParserF q (Cofree (ParserF q) (CodeGen q o b)) a -> Maybe (CodeGen q o b a)
peephole (f :<$>: p) = Just $ CodeGen $ \m -> runCodeGen p (In4 (_Fmap (USER f) m))
peephole (LiftA2 f p q) = Just $ CodeGen $ \m ->
  do qc <- runCodeGen q (In4 (Lift2 (USER f) m))
     runCodeGen p qc
peephole (TryOrElse p q) = Just $ CodeGen $ \m -> -- FIXME!
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     fmap (binder . In4 . Catch pc . In4 . Seek) (freshΦ (runCodeGen q φ))
peephole ((_ :< ((Try (p :< _)) :$>: x)) :<|>: (q :< _)) = Just $ CodeGen $ \m ->
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation (In4 (Pop (In4 (Push (USER x) φ))))))
     fmap (binder . In4 . Catch pc . In4 . Seek) (freshΦ (runCodeGen q φ))
peephole (MetaP RequiresCut (_ :< ((p :< _) :<|>: (q :< _)))) = Just $ CodeGen $ \m ->
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     qc <- freshΦ (runCodeGen q φ)
     return $! binder (In4 (Catch pc (parsecHandler qc)))
peephole (MetaP RequiresCut (_ :< ChainPre (op :< _) (p :< _))) = Just $ CodeGen $ \m ->
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In4 (_Fmap (USER (FLIP_H COMPOSE)) (In4 (_Modify σ (In4 (Jump μ)))))))
     pc <- freshM (runCodeGen p (In4 (_App m)))
     return $! In4 (Push (USER ID) (In4 (Make σ (In4 (Iter μ opc (parsecHandler (In4 (Get σ (addCoins (coinsNeeded pc) pc)))))))))
peephole (MetaP RequiresCut (_ :< ChainPost (p :< _) (op :< _))) = Just $ CodeGen $ \m ->
  do μ <- askM
     σ <- freshΣ
     let nm = coinsNeeded m
     opc <- freshM (runCodeGen op (In4 (_Modify σ (In4 (Jump μ)))))
     freshM (runCodeGen p (In4 (Make σ (In4 (Iter μ opc (parsecHandler (In4 (Get σ (addCoins nm m)))))))))
peephole (MetaP Cut (_ :< ChainPre (op :< _) (p :< _))) = Just $ CodeGen $ \m ->
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In4 (_Fmap (USER (FLIP_H COMPOSE)) (In4 (_Modify σ (In4 (Jump μ)))))))
     let nop = coinsNeeded opc
     pc <- freshM (runCodeGen p (In4 (_App m)))
     return $! In4 (Push (USER ID) (In4 (Make σ (In4 (Iter μ (addCoins nop opc) (parsecHandler (In4 (Get σ (addCoins (coinsNeeded pc) pc)))))))))
-- TODO: One more for fmap try
peephole _ = Nothing

direct :: Quapplicative q => ParserF q (CodeGen q o b) a -> Fix4 (M q o) (a : xs) (Succ n) r b -> CodeGenStack (Fix4 (M q o) xs (Succ n) r b)
direct (Pure x)      m = do return $! In4 (Push (USER x) m)
direct (Satisfy p)   m = do return $! In4 (Sat (USER p) m)
direct (pf :<*>: px) m = do pxc <- runCodeGen px (In4 (_App m)); runCodeGen pf pxc
direct (p :*>: q)    m = do qc <- runCodeGen q m; runCodeGen p (In4 (Pop qc))
direct (p :<*: q)    m = do qc <- runCodeGen q (In4 (Pop m)); runCodeGen p qc
direct Empty         m = do return $! In4 Empt
direct (p :<|>: q) m =
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     qc <- freshΦ (runCodeGen q φ)
     let np = coinsNeeded pc
     let nq = coinsNeeded qc
     let dp = np - (min np nq)
     let dq = nq - (min np nq)
     return $! binder (In4 (Catch (addCoins dp pc) (parsecHandler (addCoins dq qc))))
direct (Try p)       m = do fmap (In4 . flip Catch rollbackHandler) (runCodeGen p (deadCommitOptimisation m))
direct (LookAhead p) m =
  do n <- fmap coinsNeeded (runCodeGen p (In4 Empt)) -- Dodgy hack, but oh well
     fmap (In4 . Tell) (runCodeGen p (In4 (Swap (In4 (Seek (refundCoins n m))))))
direct (NotFollowedBy p) m =
  do pc <- runCodeGen p (In4 (Pop (In4 (Seek (In4 (Commit (In4 Empt)))))))
     let np = coinsNeeded pc
     let nm = coinsNeeded m
     return $! In4 (Catch (addCoins (max (np - nm) 0) (In4 (Tell pc))) (In4 (Seek (In4 (Push (USER UNIT) m)))))
direct (Branch b p q) m =
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (In4 (Swap (In4 (_App φ)))))
     qc <- freshΦ (runCodeGen q (In4 (Swap (In4 (_App φ)))))
     let minc = coinsNeeded (In4 (Case pc qc))
     let dp = max 0 (coinsNeeded pc - minc)
     let dq = max 0 (coinsNeeded qc - minc)
     fmap binder (runCodeGen b (In4 (Case (addCoins dp pc) (addCoins dq qc))))
direct (Match p fs qs def) m =
  do (binder, φ) <- makeΦ m
     qcs <- traverse (\q -> freshΦ (runCodeGen q φ)) qs
     defc <- freshΦ (runCodeGen def φ)
     let minc = coinsNeeded (In4 (Choices (map USER fs) qcs defc))
     let defc':qcs' = map (max 0 . subtract minc . coinsNeeded >>= addCoins) (defc:qcs)
     fmap binder (runCodeGen p (In4 (Choices (map USER fs) qcs' defc')))
direct (Let _ μ _) m = return $! tailCallOptimise μ m
direct (ChainPre op p) m =
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In4 (_Fmap (USER (FLIP_H COMPOSE)) (In4 (_Modify σ (In4 (Jump μ)))))))
     let nop = coinsNeeded opc
     pc <- freshM (runCodeGen p (In4 (_App m)))
     return $! In4 (Push (USER ID) (In4 (Make σ (In4 (Iter μ (addCoins nop opc) (parsecHandler (In4 (Get σ pc))))))))
direct (ChainPost p op) m =
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In4 (_Modify σ (In4 (Jump μ)))))
     let nop = coinsNeeded opc
     freshM (runCodeGen p (In4 (Make σ (In4 (Iter μ (addCoins nop opc) (parsecHandler (In4 (Get σ m))))))))
direct (Debug name p) m = do fmap (In4 . LogEnter name) (runCodeGen p (In4 (Commit (In4 (LogExit name m)))))
direct (MetaP Cut p) m = do runCodeGen p (addCoins (coinsNeeded m) m)

tailCallOptimise :: MVar x -> Fix4 (M q o) (x : xs) (Succ n) r a -> Fix4 (M q o) xs (Succ n) r a
tailCallOptimise μ (In4 Ret) = In4 (Jump μ)
tailCallOptimise μ k         = In4 (Call μ k)

-- Thanks to the optimisation applied to the K stack, commit is deadcode before Ret or Halt
-- However, I'm not yet sure about the interactions with try yet...
deadCommitOptimisation :: Fix4 (M q o) xs n r a -> Fix4 (M q o) xs (Succ n) r a
deadCommitOptimisation (In4 Ret) = In4 Ret
deadCommitOptimisation m         = In4 (Commit m)

-- Refactor with asks
askM :: CodeGenStack (MVar a)
askM = lift (construct MVar)

askΦ :: CodeGenStack (ΦVar a)
askΦ = construct ΦVar

freshM :: CodeGenStack a -> CodeGenStack a
freshM = mapVFreshT newScope

freshΦ :: CodeGenStack a -> CodeGenStack a
freshΦ = newScope

makeΦ :: Fix4 (M q o) (x ': xs) (Succ n) r a -> CodeGenStack (Fix4 (M q o) xs (Succ n) r a -> Fix4 (M q o) xs (Succ n) r a, Fix4 (M q o) (x : xs) (Succ n) r a)
makeΦ m | elidable m = return $! (id, m)
  where
    -- This is double-φ optimisation:   If a φ-node points directly to another φ-node, then it can be elided
    elidable (In4 (Join _)) = True
    -- This is terminal-φ optimisation: If a φ-node points directly to a terminal operation, then it can be elided
    elidable (In4 Ret)      = True
    elidable _              = False
makeΦ m = let n = coinsNeeded m in fmap (\φ -> (In4 . MkJoin φ (addCoins n m), drainCoins n (In4 (Join φ)))) askΦ

freshΣ :: CodeGenStack (ΣVar a)
freshΣ = lift (lift (construct ΣVar))
