{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Parsley.Internal.Backend.CodeGenerator
Description : Translation of Combinator AST into Machine
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module exports `codeGen` used to translation from the high-level representation
to the low-level representation.

@since 1.0.0.0
-}
module Parsley.Internal.Backend.CodeGenerator (codeGen) where

import Data.Maybe                          (isJust)
import Data.Set                            (Set, elems)
import Control.Monad.Trans                 (lift)
import Parsley.Internal.Backend.Machine    (user, userBool, LetBinding, makeLetBinding, newMeta, Instr(..), Handler(..),
                                            _Fmap, _App, _Modify, _Get, _Put, _Make,
                                            addCoins, refundCoins, drainCoins,
                                            minus, minCoins, maxCoins, zero,
                                            IMVar, IΦVar, IΣVar, MVar(..), ΦVar(..), ΣVar(..), SomeΣVar)
import Parsley.Internal.Backend.Analysis   (coinsNeeded)
import Parsley.Internal.Common.Fresh       (VFreshT, HFresh, evalFreshT, evalFresh, construct, MonadFresh(..), mapVFreshT)
import Parsley.Internal.Common.Indexed     (Fix, Fix4(In4), Cofree(..), Nat(..), imap, histo, extract, (|>))
import Parsley.Internal.Core.CombinatorAST (Combinator(..), MetaCombinator(..))
import Parsley.Internal.Core.Defunc        (Defunc(COMPOSE, ID), pattern FLIP_H, pattern UNIT)
import Parsley.Internal.Trace              (Trace(trace))

import Parsley.Internal.Core.Defunc as Core (Defunc)

type CodeGenStack a = VFreshT IΦVar (VFreshT IMVar (HFresh IΣVar)) a
runCodeGenStack :: CodeGenStack a -> IMVar -> IΦVar -> IΣVar -> a
runCodeGenStack m μ0 φ0 = evalFresh (evalFreshT (evalFreshT m φ0) μ0)

newtype CodeGen o a x =
  CodeGen {runCodeGen :: forall xs n r. Fix4 (Instr o) (x : xs) (Succ n) r a -> CodeGenStack (Fix4 (Instr o) xs (Succ n) r a)}

{-|
Translates a parser represented with combinators into its machine representation.

@since 1.0.0.0
-}
{-# INLINEABLE codeGen #-}
codeGen :: Trace
        => Maybe (MVar x)   -- ^ The name of the parser, if it exists.
        -> Fix Combinator x -- ^ The definition of the parser.
        -> Set SomeΣVar     -- ^ The free registers it requires to run.
        -> IMVar            -- ^ The binding identifier to start name generation from.
        -> IΣVar            -- ^ The register identifier to start name generation from.
        -> LetBinding o a x
codeGen letBound p rs μ0 σ0 = trace ("GENERATING " ++ name ++ ": " ++ show p ++ "\nMACHINE: " ++ show (elems rs) ++ " => " ++ show m) $ makeLetBinding m rs newMeta
  where
    name = maybe "TOP LEVEL" show letBound
    m = finalise (histo alg p)
    alg :: Combinator (Cofree Combinator (CodeGen o a)) x -> CodeGen o a x
    alg = deep |> (\x -> CodeGen (shallow (imap extract x)))
    finalise cg =
      let m = runCodeGenStack (runCodeGen cg (In4 Ret)) μ0 0 σ0
      in if isJust letBound then m else addCoins (coinsNeeded m) m

pattern (:<$>:) :: Core.Defunc (a -> b) -> Cofree Combinator k a -> Combinator (Cofree Combinator k) b
pattern f :<$>: p <- (_ :< Pure f) :<*>: p
pattern (:$>:) :: Combinator (Cofree Combinator k) a -> Core.Defunc b -> Combinator (Cofree Combinator k) b
pattern p :$>: x <- (_ :< p) :*>: (_ :< Pure x)
pattern TryOrElse ::  k a -> k a -> Combinator (Cofree Combinator k) a
pattern TryOrElse p q <- (_ :< Try (p :< _)) :<|>: (q :< _)

rollbackHandler :: Handler o (Fix4 (Instr o)) (o : xs) (Succ n) r a
rollbackHandler = Always (In4 (Seek (In4 Empt)))

parsecHandler :: Fix4 (Instr o) xs (Succ n) r a -> Handler o (Fix4 (Instr o)) (o : xs) (Succ n) r a
parsecHandler k = Same k (In4 Empt)

altNoCutCompile :: CodeGen o a y -> CodeGen o a x
                -> (forall n xs r. Fix4 (Instr o) xs (Succ n) r a -> Handler o (Fix4 (Instr o)) (o : xs) (Succ n) r a)
                -> (forall n xs r. Fix4 (Instr o) (x : xs) n r a  -> Fix4 (Instr o) (y : xs) n r a)
                -> Fix4 (Instr o) (x : xs) (Succ n) r a -> CodeGenStack (Fix4 (Instr o) xs (Succ n) r a)
altNoCutCompile p q handler post m =
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation (post φ)))
     qc <- freshΦ (runCodeGen q φ)
     let np = coinsNeeded pc
     let nq = coinsNeeded qc
     let dp = np `minus` minCoins np nq
     let dq = nq `minus` minCoins np nq
     return $! binder (In4 (Catch (addCoins dp pc) (handler (addCoins dq qc))))

chainPreCompile :: CodeGen o a (x -> x) -> CodeGen o a x
                -> (forall n xs r. Fix4 (Instr o) xs (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a)
                -> (forall n xs r. Fix4 (Instr o) xs (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a)
                -> Fix4 (Instr o) (x : xs) (Succ n) r a -> CodeGenStack (Fix4 (Instr o) xs (Succ n) r a)
chainPreCompile op p preOp preP m =
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In4 (_Fmap (user (FLIP_H COMPOSE)) (In4 (_Modify σ (In4 (Jump μ)))))))
     pc <- freshM (runCodeGen p (In4 (_App m)))
     return $! In4 (Push (user ID) (In4 (_Make σ (In4 (Iter μ (preOp opc) (parsecHandler (In4 (_Get σ (preP pc)))))))))

chainPostCompile :: CodeGen o a x -> CodeGen o a (x -> x)
                 -> (forall n xs r. Fix4 (Instr o) xs (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a)
                 -> (forall n xs r. Fix4 (Instr o) xs (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a)
                 -> Fix4 (Instr o) (x : xs) (Succ n) r a -> CodeGenStack (Fix4 (Instr o) xs (Succ n) r a)
chainPostCompile p op preOp preM m =
  do μ <- askM
     σ <- freshΣ
     opc <- freshM (runCodeGen op (In4 (_Modify σ (In4 (Jump μ)))))
     freshM (runCodeGen p (In4 (_Make σ (In4 (Iter μ (preOp opc) (parsecHandler (In4 (_Get σ (preM m)))))))))

deep :: Combinator (Cofree Combinator (CodeGen o a)) x -> Maybe (CodeGen o a x)
deep (f :<$>: (p :< _)) = Just $ CodeGen $ \m -> runCodeGen p (In4 (_Fmap (user f) m))
deep (TryOrElse p q) = Just $ CodeGen $ altNoCutCompile p q (Always . In4 . Seek) id
deep ((_ :< (Try (p :< _) :$>: x)) :<|>: (q :< _)) = Just $ CodeGen $ altNoCutCompile p q (Always . In4 . Seek) (In4 . Pop . In4 . Push (user x))
deep ((_ :< (f :<$>: (_ :< Try (p :< _)))) :<|>: (q :< _)) = Just $ CodeGen $ altNoCutCompile p q (Always . In4 . Seek) (In4 . _Fmap (user f))
deep (MetaCombinator RequiresCut (_ :< ((p :< _) :<|>: (q :< _)))) = Just $ CodeGen $ \m ->
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     qc <- freshΦ (runCodeGen q φ)
     return $! binder (In4 (Catch pc (parsecHandler qc)))
deep (MetaCombinator RequiresCut (_ :< ChainPre (op :< _) (p :< _))) = Just $ CodeGen $ chainPreCompile op p id addCoinsNeeded
deep (MetaCombinator RequiresCut (_ :< ChainPost (p :< _) (op :< _))) = Just $ CodeGen $ chainPostCompile p op id addCoinsNeeded
deep (MetaCombinator Cut (_ :< ChainPre (op :< _) (p :< _))) = Just $ CodeGen $ chainPreCompile op p addCoinsNeeded addCoinsNeeded
deep _ = Nothing

addCoinsNeeded :: Fix4 (Instr o) xs (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a
addCoinsNeeded = coinsNeeded >>= addCoins

shallow :: Combinator (CodeGen o a) x -> Fix4 (Instr o) (x : xs) (Succ n) r a -> CodeGenStack (Fix4 (Instr o) xs (Succ n) r a)
shallow (Pure x)      m = do return $! In4 (Push (user x) m)
shallow (Satisfy p)   m = do return $! In4 (Sat (userBool p) m)
shallow (pf :<*>: px) m = do pxc <- runCodeGen px (In4 (_App m)); runCodeGen pf pxc
shallow (p :*>: q)    m = do qc <- runCodeGen q m; runCodeGen p (In4 (Pop qc))
shallow (p :<*: q)    m = do qc <- runCodeGen q (In4 (Pop m)); runCodeGen p qc
shallow Empty         _ = do return $! In4 Empt
shallow (p :<|>: q)   m = do altNoCutCompile p q parsecHandler id m
shallow (Try p)       m = do fmap (In4 . flip Catch rollbackHandler) (runCodeGen p (deadCommitOptimisation m))
shallow (LookAhead p) m =
  do n <- fmap coinsNeeded (runCodeGen p (In4 Empt)) -- Dodgy hack, but oh well
     fmap (In4 . Tell) (runCodeGen p (In4 (Swap (In4 (Seek (refundCoins n m))))))
shallow (NotFollowedBy p) m =
  do pc <- runCodeGen p (In4 (Pop (In4 (Seek (In4 (Commit (In4 Empt)))))))
     let np = coinsNeeded pc
     let nm = coinsNeeded m
     return $! In4 (Catch (addCoins (maxCoins (np `minus` nm) zero) (In4 (Tell pc))) (Always (In4 (Seek (In4 (Push (user UNIT) m))))))
shallow (Branch b p q) m =
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (In4 (Swap (In4 (_App φ)))))
     qc <- freshΦ (runCodeGen q (In4 (Swap (In4 (_App φ)))))
     let minc = coinsNeeded (In4 (Case pc qc))
     let dp = maxCoins zero (coinsNeeded pc `minus` minc)
     let dq = maxCoins zero (coinsNeeded qc `minus` minc)
     fmap binder (runCodeGen b (In4 (Case (addCoins dp pc) (addCoins dq qc))))
shallow (Match p fs qs def) m =
  do (binder, φ) <- makeΦ m
     qcs <- traverse (\q -> freshΦ (runCodeGen q φ)) qs
     defc <- freshΦ (runCodeGen def φ)
     let minc = coinsNeeded (In4 (Choices (map userBool fs) qcs defc))
     let defc':qcs' = map (maxCoins zero . (`minus` minc) . coinsNeeded >>= addCoins) (defc:qcs)
     fmap binder (runCodeGen p (In4 (Choices (map user fs) qcs' defc')))
shallow (Let _ μ _)            m = do return $! tailCallOptimise μ m
shallow (ChainPre op p)        m = do chainPreCompile op p addCoinsNeeded id m
shallow (ChainPost p op)       m = do chainPostCompile p op addCoinsNeeded id m
shallow (MakeRegister σ p q)   m = do qc <- runCodeGen q m; runCodeGen p (In4 (_Make σ qc))
shallow (GetRegister σ)        m = do return $! In4 (_Get σ m)
shallow (PutRegister σ p)      m = do runCodeGen p (In4 (_Put σ (In4 (Push (user UNIT) m))))
shallow (Debug name p)         m = do fmap (In4 . LogEnter name) (runCodeGen p (In4 (Commit (In4 (LogExit name m)))))
shallow (MetaCombinator Cut p) m = do runCodeGen p (addCoins (coinsNeeded m) m)

tailCallOptimise :: MVar x -> Fix4 (Instr o) (x : xs) (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a
tailCallOptimise μ (In4 Ret) = In4 (Jump μ)
tailCallOptimise μ k         = In4 (Call μ k)

-- Thanks to the optimisation applied to the K stack, commit is deadcode before Ret
-- However, I'm not yet sure about the interactions with try yet...
deadCommitOptimisation :: Fix4 (Instr o) xs n r a -> Fix4 (Instr o) xs (Succ n) r a
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

makeΦ :: Fix4 (Instr o) (x ': xs) (Succ n) r a -> CodeGenStack (Fix4 (Instr o) xs (Succ n) r a -> Fix4 (Instr o) xs (Succ n) r a, Fix4 (Instr o) (x : xs) (Succ n) r a)
makeΦ m | elidable m = return (id, m)
  where
    elidable :: Fix4 (Instr o) (x ': xs) (Succ n) r a -> Bool
    -- This is double-φ optimisation:   If a φ-node points shallowly to another φ-node, then it can be elided
    elidable (In4 (Join _))             = True
    -- This is terminal-φ optimisation: If a φ-node points shallowly to a terminal operation, then it can be elided
    elidable (In4 Ret)                  = True
    -- This is a form of double-φ optimisation: If a φ-node points shallowly to a jump, then it can be elided and the jump used instead
    -- Note that this should NOT be done for non-tail calls, as they may generate a large continuation
    elidable (In4 (Pop (In4 (Jump _)))) = True
    elidable _                          = False
makeΦ m = let n = coinsNeeded m in fmap (\φ -> (In4 . MkJoin φ (addCoins n m), drainCoins n (In4 (Join φ)))) askΦ

freshΣ :: CodeGenStack (ΣVar a)
freshΣ = lift (lift (construct ΣVar))
