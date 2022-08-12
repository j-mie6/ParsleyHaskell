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

import Data.Set                            (Set, elems)
import Control.Monad.Trans                 (lift)
import Parsley.Internal.Backend.Machine    (user, LetBinding, makeLetBinding, newMeta, Instr(..), Handler(..),
                                            _Fmap, _App, _Get, _Put, _Make,
                                            addCoins, refundCoins, drainCoins, giveBursary, blockCoins,
                                            minus, minCoins, maxCoins, zero,
                                            IMVar, IΦVar, MVar(..), ΦVar(..), SomeΣVar)
import Parsley.Internal.Backend.Analysis   (coinsNeeded, shouldInline, reclaimable)
import Parsley.Internal.Common.Fresh       (VFreshT, VFresh, evalFreshT, evalFresh, construct, MonadFresh(..), mapVFreshT)
import Parsley.Internal.Common.Indexed     (Fix, Fix3(In3), Cofree(..), Nat(..), imap, histo, extract, (|>))
import Parsley.Internal.Core.CombinatorAST (Combinator(..), MetaCombinator(..))
import Parsley.Internal.Core.Defunc        (pattern UNIT)
import Parsley.Internal.Trace              (Trace(trace))

import Parsley.Internal.Core.Defunc as Core (Defunc)

type CodeGenStack a = VFreshT IΦVar (VFresh IMVar) a
runCodeGenStack :: CodeGenStack a -> IMVar -> IΦVar -> a
runCodeGenStack m μ0 φ0 = evalFresh (evalFreshT m φ0) μ0

newtype CodeGen o x =
  CodeGen {runCodeGen :: forall xs n r. Fix3 (Instr o) (x : xs) (Succ n) r -> CodeGenStack (Fix3 (Instr o) xs (Succ n) r)}

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
        -> LetBinding o x
codeGen letBound p rs μ0 = trace ("GENERATING " ++ name ++ ": " ++ show p ++ "\nMACHINE: " ++ show (elems rs) ++ " => " ++ show m) $ makeLetBinding m rs newMeta
  where
    name = maybe "TOP LEVEL" show letBound
    m = finalise (histo alg p)
    alg :: Combinator (Cofree Combinator (CodeGen o)) x -> CodeGen o x
    alg = deep |> (\x -> CodeGen (shallow (imap extract x)))
    -- It is never safe to add coins to the top of a binding
    -- This is because we don't know the characteristics of the caller (even the top-level!)
    finalise cg = runCodeGenStack (runCodeGen cg (In3 Ret)) μ0 0

pattern (:<$>:) :: Core.Defunc (a -> b) -> Cofree Combinator k a -> Combinator (Cofree Combinator k) b
pattern f :<$>: p <- (_ :< Pure f) :<*>: p
pattern (:$>:) :: Combinator (Cofree Combinator k) a -> Core.Defunc b -> Combinator (Cofree Combinator k) b
pattern p :$>: x <- (_ :< p) :*>: (_ :< Pure x)
pattern TryOrElse ::  k a -> k a -> Combinator (Cofree Combinator k) a
pattern TryOrElse p q <- (_ :< Try (p :< _)) :<|>: (q :< _)

-- it would be nice to generate `yesSame` handler bindings for Try, perhaps a special flag?
-- relevancy analysis might help too I guess, for a more general one?
rollbackHandler :: Handler o (Fix3 (Instr o)) (o : xs) (Succ n) r
rollbackHandler = Always False (In3 (Seek (In3 Raise)))

mergeErrors :: Handler o (Fix3 (Instr o)) (o : xs) (Succ n) r
mergeErrors = Always False (In3 MergeErrorsAndRaise)

parsecHandler :: Fix3 (Instr o) xs (Succ n) r -> Handler o (Fix3 (Instr o)) (o : xs) (Succ n) r
parsecHandler k = Same (not (shouldInline k)) k False (In3 Raise)

recoverHandler :: Fix3 (Instr o) xs n r -> Handler o (Fix3 (Instr o)) (o : xs) n r
recoverHandler = Always . not . shouldInline <*> In3 . Seek

altNoCutCompile :: Trace => CodeGen o y -> CodeGen o x
                -> (forall n xs r. Fix3 (Instr o) xs (Succ n) r -> Handler o (Fix3 (Instr o)) (o : xs) (Succ n) r)
                -> (forall n xs r. Fix3 (Instr o) (x : xs) n r  -> Fix3 (Instr o) (y : xs) n r)
                -> Fix3 (Instr o) (x : xs) (Succ n) r -> CodeGenStack (Fix3 (Instr o) xs (Succ n) r)
altNoCutCompile p q handler post m =
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation (post φ)))
     qc <- In3 . flip Catch mergeErrors <$> freshΦ (runCodeGen q (In3 (Commit φ)))
     let np = coinsNeeded pc
     let nq = coinsNeeded qc
     let dp = np `minus` minCoins np nq
     let dq = nq `minus` minCoins np nq
     return $! binder (In3 (Catch (addCoins dp pc) (handler (addCoins dq qc))))

loopCompile :: CodeGen o () -> CodeGen o x
            -> (forall n xs r. Fix3 (Instr o) xs (Succ n) r -> Fix3 (Instr o) xs (Succ n) r)
            -> (forall n xs r. Fix3 (Instr o) xs (Succ n) r -> Fix3 (Instr o) xs (Succ n) r)
            -> Fix3 (Instr o) (x : xs) (Succ n) r -> CodeGenStack (Fix3 (Instr o) xs (Succ n) r)
loopCompile body exit prebody preExit m =
  do μ <- askM
     bodyc <- freshM (runCodeGen body (In3 (Pop (In3 (Jump μ)))))
     exitc <- freshM (runCodeGen exit m)
     return $! In3 (Iter μ (prebody bodyc) (parsecHandler (preExit exitc)))

deep :: Trace => Combinator (Cofree Combinator (CodeGen o)) x -> Maybe (CodeGen o x)
deep (f :<$>: (p :< _)) = Just $ CodeGen $ \m -> runCodeGen p (In3 (_Fmap (user f) m))
deep (TryOrElse p q) = Just $ CodeGen $ altNoCutCompile p q recoverHandler id
deep ((_ :< (Try (p :< _) :$>: x)) :<|>: (q :< _)) = Just $ CodeGen $ altNoCutCompile p q recoverHandler (In3 . Pop . In3 . Push (user x))
deep ((_ :< (f :<$>: (_ :< Try (p :< _)))) :<|>: (q :< _)) = Just $ CodeGen $ altNoCutCompile p q recoverHandler (In3 . _Fmap (user f))
deep (MetaCombinator RequiresCut (_ :< ((p :< _) :<|>: (q :< _)))) = Just $ CodeGen $ \m ->
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (deadCommitOptimisation φ))
     qc <- freshΦ (runCodeGen q φ)
     return $! binder (In3 (Catch pc (parsecHandler qc)))
deep (MetaCombinator RequiresCut (_ :< Loop (body :< _) (exit :< _))) = Just $ CodeGen $ loopCompile body exit id addCoinsNeeded
deep (MetaCombinator Cut (_ :< Loop (body :< _) (exit :< _))) = Just $ CodeGen $ loopCompile body exit addCoinsNeeded addCoinsNeeded
deep _ = Nothing

addCoinsNeeded :: Fix3 (Instr o) xs (Succ n) r -> Fix3 (Instr o) xs (Succ n) r
addCoinsNeeded = coinsNeeded >>= addCoins

shallow :: Trace => Combinator (CodeGen o) x -> Fix3 (Instr o) (x : xs) (Succ n) r -> CodeGenStack (Fix3 (Instr o) xs (Succ n) r)
shallow (Pure x)      m = do return $! In3 (Push (user x) m)
shallow (Satisfy p)   m = do return $! In3 (Sat p m)
shallow (pf :<*>: px) m = do pxc <- runCodeGen px (In3 (_App m)); runCodeGen pf pxc
shallow (p :*>: q)    m = do qc <- runCodeGen q m; runCodeGen p (In3 (Pop qc))
shallow (p :<*: q)    m = do qc <- runCodeGen q (In3 (Pop m)); runCodeGen p qc
shallow Empty         _ = do return $! In3 Empt
shallow (p :<|>: q)   m = do altNoCutCompile p q parsecHandler id m
shallow (Try p)       m = do fmap (In3 . flip Catch rollbackHandler) (runCodeGen p (deadCommitOptimisation m))
shallow (LookAhead p) m =
  do n <- fmap reclaimable (runCodeGen p (In3 Ret)) -- Dodgy hack, but oh well
     fmap (In3 . Tell) (runCodeGen p (In3 (Swap (In3 (Seek (refundCoins n m))))))
shallow (NotFollowedBy p) m =
  do pc <- runCodeGen p (In3 (Pop (In3 (Seek (In3 (Commit (In3 Empt)))))))
     let np = coinsNeeded pc
     let nm = coinsNeeded m
     -- The minus here is used because the shared coins are propagated out front, neat.
     return $! In3 (Catch (addCoins (maxCoins (np `minus` nm) zero) (In3 (Tell pc))) (Always (not (shouldInline m)) (In3 (Seek (In3 (Push (user UNIT) m))))))
shallow (Branch b p q) m =
  do (binder, φ) <- makeΦ m
     pc <- freshΦ (runCodeGen p (In3 (Swap (In3 (_App φ)))))
     qc <- freshΦ (runCodeGen q (In3 (Swap (In3 (_App φ)))))
     let minc = coinsNeeded (In3 (Case pc qc))
     let dp = maxCoins zero (coinsNeeded pc `minus` minc)
     let dq = maxCoins zero (coinsNeeded qc `minus` minc)
     fmap binder (runCodeGen b (In3 (Case (addCoins dp pc) (addCoins dq qc))))
shallow (Match p fs qs def) m =
  do (binder, φ) <- makeΦ m
     qcs <- traverse (\q -> freshΦ (runCodeGen q φ)) qs
     defc <- freshΦ (runCodeGen def φ)
     let minc = coinsNeeded (In3 (Choices (map user fs) qcs defc))
     let defc':qcs' = map (maxCoins zero . (`minus` minc) . coinsNeeded >>= addCoins) (defc:qcs)
     fmap binder (runCodeGen p (In3 (Choices (map user fs) qcs' defc')))
shallow (Let _ μ)                    m = do return $! tailCallOptimise μ m
shallow (Loop body exit)             m = do loopCompile body exit addCoinsNeeded id m
shallow (MakeRegister σ p q)         m = do qc <- runCodeGen q m; runCodeGen p (In3 (_Make σ qc))
shallow (GetRegister σ)              m = do return $! In3 (_Get σ m)
shallow (PutRegister σ p)            m = do runCodeGen p (In3 (_Put σ (In3 (Push (user UNIT) m))))
shallow (Position sel)               m = do return $! In3 (SelectPos sel m)
shallow (Debug name p)               m = do fmap (In3 . LogEnter name) (runCodeGen p (In3 (Commit (In3 (LogExit name m)))))
shallow (MetaCombinator Cut p)       m = do blockCoins <$> runCodeGen p (addCoins (coinsNeeded m) m)
shallow (MetaCombinator CutImmune p) m = do addCoins . coinsNeeded <$> runCodeGen p (In3 Ret) <*> runCodeGen p m

tailCallOptimise :: MVar x -> Fix3 (Instr o) (x : xs) (Succ n) r -> Fix3 (Instr o) xs (Succ n) r
tailCallOptimise μ (In3 Ret) = In3 (Jump μ)
tailCallOptimise μ k         = In3 (Call μ k)

-- Thanks to the optimisation applied to the K stack, commit is deadcode before Ret
-- However, I'm not yet sure about the interactions with try yet...
deadCommitOptimisation :: Fix3 (Instr o) xs n r -> Fix3 (Instr o) xs (Succ n) r
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

makeΦ :: Trace => Fix3 (Instr o) (x ': xs) (Succ n) r -> CodeGenStack (Fix3 (Instr o) xs (Succ n) r -> Fix3 (Instr o) xs (Succ n) r, Fix3 (Instr o) (x : xs) (Succ n) r)
makeΦ m | shouldInline m = trace ("eliding " ++ show m) $ return (id, m)
  {-where
    elidable :: Fix3 (Instr o) (x ': xs) (Succ n) r a -> Bool
    -- This is double-φ optimisation:   If a φ-node points shallowly to another φ-node, then it can be elided
    elidable (In3 (Join _))             = True
    elidable (In3 (Pop (In3 (Join _)))) = True
    -- This is terminal-φ optimisation: If a φ-node points shallowly to a terminal operation, then it can be elided
    elidable (In3 Ret)                  = True
    elidable (In3 (Pop (In3 Ret)))      = True
    -- This is a form of double-φ optimisation: If a φ-node points shallowly to a jump, then it can be elided and the jump used instead
    -- Note that this should NOT be done for non-tail calls, as they may generate a large continuation
    elidable (In3 (Pop (In3 (Jump _)))) = True
    elidable _                          = False-}
makeΦ m = let n = coinsNeeded m in fmap (\φ -> (In3 . MkJoin φ (giveBursary n m), drainCoins n (In3 (Join φ)))) askΦ
