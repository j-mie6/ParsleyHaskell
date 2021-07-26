{-# LANGUAGE DerivingStrategies #-}
module Parsley.Internal.Frontend.Analysis.Cut (cutAnalysis, Compliance(..)) where

import Data.Coerce                         (coerce)
import Data.Kind                           (Type)
import Parsley.Internal.Common.Indexed     (Fix(..), zygo, (:*:)(..), ifst)
import Parsley.Internal.Core.CombinatorAST (Combinator(..), MetaCombinator(..))

cutAnalysis :: Bool -> Fix Combinator a -> Fix Combinator a
cutAnalysis letBound = fst . ($ letBound) . doCut . zygo (CutAnalysis . cutAlg) compliance

data Compliance (k :: Type) = DomComp | NonComp | Comp | FullPure deriving stock (Show, Eq)
newtype CutAnalysis a = CutAnalysis {doCut :: Bool -> (Fix Combinator a, Bool)}

seqCompliance :: Compliance a -> Compliance b -> Compliance c
seqCompliance c FullPure = coerce c
seqCompliance FullPure c = coerce c
seqCompliance Comp _     = Comp
seqCompliance _ _        = NonComp

caseCompliance :: Compliance a -> Compliance b -> Compliance c
caseCompliance c FullPure              = coerce c
caseCompliance FullPure c              = coerce c
caseCompliance c1 c2 | c1 == coerce c2 = coerce c1
caseCompliance _ _                     = NonComp

{-# INLINE compliance #-}
compliance :: Combinator Compliance a -> Compliance a
compliance (Pure _)                 = FullPure
compliance (Satisfy _)              = NonComp
compliance Empty                    = FullPure
compliance Let{}                    = DomComp
compliance (Try _)                  = DomComp
compliance (NonComp :<|>: FullPure) = Comp
compliance (_ :<|>: _)              = NonComp
compliance (l :<*>: r)              = seqCompliance l r
compliance (l :<*: r)               = seqCompliance l r
compliance (l :*>: r)               = seqCompliance l r
compliance (LookAhead c)            = c -- Lookahead will consume input on failure, so its compliance matches that which is beneath it
compliance (NotFollowedBy _)        = FullPure
compliance (Debug _ c)              = c
compliance (ChainPre NonComp p)     = seqCompliance Comp p
compliance (ChainPre _ p)           = seqCompliance NonComp p
compliance (ChainPost p NonComp)    = seqCompliance p Comp
compliance (ChainPost p _)          = seqCompliance p NonComp
compliance (Branch b p q)           = seqCompliance b (caseCompliance p q)
compliance (Match p _ qs def)       = seqCompliance p (foldr1 caseCompliance (def:qs))
compliance (MakeRegister _ l r)     = seqCompliance l r
compliance (GetRegister _)          = FullPure
compliance (PutRegister _ c)        = coerce c
compliance (MetaCombinator _ c)     = c

cutAlg :: Combinator (CutAnalysis :*: Compliance) a -> Bool -> (Fix Combinator a, Bool)
cutAlg (Pure x) _ = (In (Pure x), False)
cutAlg (Satisfy f) cut = (mkCut cut (In (Satisfy f)), True)
cutAlg Empty _ = (In Empty, False)
cutAlg (Let r μ p) cut = (mkCut (not cut) (In (Let r μ (fst (doCut (ifst p) True)))), False) -- If there is no cut, we generate a piggy for the continuation
cutAlg (Try p) _ = False <$ rewrap Try False (ifst p)
cutAlg ((p :*: NonComp) :<|>: (q :*: FullPure)) _ = (requiresCut (In (fst (doCut p True) :<|>: fst (doCut q False))), True)
cutAlg (p :<|>: q) cut =
  let (q', handled) = doCut (ifst q) cut
  in (In (fst (doCut (ifst p) False) :<|>: q'), handled)
cutAlg (l :<*>: r) cut = seqCutAlg (:<*>:) cut (ifst l) (ifst r)
cutAlg (l :<*: r) cut = seqCutAlg (:<*:) cut (ifst l) (ifst r)
cutAlg (l :*>: r) cut = seqCutAlg (:*>:) cut (ifst l) (ifst r)
cutAlg (LookAhead p) cut = rewrap LookAhead cut (ifst p)
cutAlg (NotFollowedBy p) _ = False <$ rewrap NotFollowedBy False (ifst p)
cutAlg (Debug msg p) cut = rewrap (Debug msg) cut (ifst p)
cutAlg (ChainPre (op :*: NonComp) p) _ =
  let (op', _) = doCut op True
      (p', _) = doCut (ifst p) False
  in (requiresCut (In (ChainPre op' p')), True)
cutAlg (ChainPre op p) cut =
  let (op', _) = doCut (ifst op) False
      (p', handled) = doCut (ifst p) cut
  in (mkCut (not cut) (In (ChainPre op' p')), handled)
cutAlg (ChainPost p (op :*: NonComp)) cut =
  let (p', _) = doCut (ifst p) cut
      (op', _) = doCut op True
  in (requiresCut (In (ChainPost p' op')), True)
cutAlg (ChainPost p op) cut =
  let (p', handled) = doCut (ifst p) cut
      (op', _) = doCut (ifst op) False
  in (mkCut (cut && handled) (In (ChainPost p' op')), handled)
cutAlg (Branch b p q) cut =
  let (b', handled) = doCut (ifst b) cut
      (p', handled') = doCut (ifst p) (cut && not handled)
      (q', handled'') = doCut (ifst q) (cut && not handled)
  in (In (Branch b' p' q'), handled || (handled' && handled''))
cutAlg (Match p f qs def) cut =
  let (p', handled) = doCut (ifst p) cut
      (def', handled') = doCut (ifst def) (cut && not handled)
      (qs', handled'') = foldr (\q -> biliftA2 (:) (&&) (doCut (ifst q) (cut && not handled))) ([], handled') qs
  in (In (Match p' f qs' def'), handled || handled'')
cutAlg (MakeRegister σ l r) cut = seqCutAlg (MakeRegister σ) cut (ifst l) (ifst r)
cutAlg (GetRegister σ) _ = (In (GetRegister σ), False)
cutAlg (PutRegister σ p) cut = rewrap (PutRegister σ) cut (ifst p)
cutAlg (MetaCombinator m p) cut = rewrap (MetaCombinator m) cut (ifst p)

mkCut :: Bool -> Fix Combinator a -> Fix Combinator a
mkCut True = In . MetaCombinator Cut
mkCut False = id

requiresCut :: Fix Combinator a -> Fix Combinator a
requiresCut = In . MetaCombinator RequiresCut

seqCutAlg :: (Fix Combinator a -> Fix Combinator b -> Combinator (Fix Combinator) c) -> Bool -> CutAnalysis a -> CutAnalysis b -> (Fix Combinator c, Bool)
seqCutAlg con cut l r =
  let (l', handled) = doCut l cut
      (r', handled') = doCut r (cut && not handled)
  in (In (con l' r'), handled || handled')

rewrap :: (Fix Combinator a -> Combinator (Fix Combinator) b) -> Bool -> CutAnalysis a -> (Fix Combinator b, Bool)
rewrap con cut p = let (p', handled) = doCut p cut in (In (con p'), handled)

biliftA2 :: (a -> b -> c) -> (x -> y -> z) -> (a, x) -> (b, y) -> (c, z)
biliftA2 f g (x1, y1) (x2, y2) = (f x1 x2, g y1 y2)
