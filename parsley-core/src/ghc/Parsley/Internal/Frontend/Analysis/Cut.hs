{-# LANGUAGE DerivingStrategies #-}
{-|
Module      : Parsley.Internal.Frontend.Analysis.Cut
Description : Marks cut points in the parser.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes a transformation that annotates the parts of the grammar where cuts occur: these are places
where backtracking is not allowed to occur. This information is used to help with correct allocation
of coins used for "Parsley.Internal.Backend.Analysis.Coins": the combinator tree has access to scoping
information lost in the machine.

@since 1.5.0.0
-}
module Parsley.Internal.Frontend.Analysis.Cut (cutAnalysis) where

import Data.Coerce                         (coerce)
import Data.Kind                           (Type)
import Parsley.Internal.Common.Indexed     (Fix(..), zygo, (:*:)(..), ifst)
import Parsley.Internal.Core.CombinatorAST (Combinator(..), MetaCombinator(..))

{-|
Annotate a tree with its cut-points. We assume a cut for let-bound parsers.

@since 1.5.0.0
-}
cutAnalysis :: Fix Combinator a -> Fix Combinator a
cutAnalysis = fst . ($ True) . doCut . zygo (CutAnalysis . cutAlg) compliance

data Compliance (k :: Type) = DomComp | NonComp | Comp | FullPure deriving stock (Show, Eq)
newtype CutAnalysis a = CutAnalysis { doCut :: Bool -> (Fix Combinator a, Bool) }

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
compliance (Loop NonComp exit)      = seqCompliance Comp exit
compliance (Loop _ exit)            = seqCompliance NonComp exit
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
cutAlg (Let r μ) cut = (mkCut (not cut) (In (Let r μ)), False) -- If there is no cut, we generate a piggy for the continuation
cutAlg (Try p) cut = (In (Try (mkImmune cut (fst (doCut (ifst p) False)))), False)
-- Special case of below, but we know immunity is useless within `q`
cutAlg ((p :*: NonComp) :<|>: (q :*: FullPure)) _ = (requiresCut (In (fst (doCut p True) :<|>: fst (doCut q False))), False)
-- both branches have to handle a cut, if `p` fails having consumed input that satisfies a cut
-- but if it doesn't, then `q` will need to handle the cut instead. When `q` has no cut to handle,
-- then that means it is immune to cuts, which is handy!
cutAlg ((p :*: NonComp) :<|>: q) cut =
  let (p', handled) = doCut p True
      (q', handled') = doCut (ifst q) cut
  in (requiresCut (In (p' :<|>: mkImmune (not cut) q')), handled && handled')
-- Why cut in both branches? Good question
-- The point here is that, even though `p` doesn't require a cut, this will enable an immunity
-- allowing for internal factoring  of input. However, if we are not under a cut requirement, we'd
-- like this input to be factored out further.
cutAlg (p :<|>: q) cut =
  let (p', handled) = doCut (ifst p) cut
      (q', handled') = doCut (ifst q) cut
  in (In (p' :<|>: q'), handled && handled')
cutAlg (l :<*>: r) cut = seqCutAlg (:<*>:) cut (ifst l) (ifst r)
cutAlg (l :<*: r) cut = seqCutAlg (:<*:) cut (ifst l) (ifst r)
cutAlg (l :*>: r) cut = seqCutAlg (:*>:) cut (ifst l) (ifst r)
cutAlg (LookAhead p) cut = rewrap LookAhead cut (ifst p)
cutAlg (NotFollowedBy p) _ = False <$ rewrap NotFollowedBy False (ifst p)
cutAlg (Debug msg p) cut = rewrap (Debug msg) cut (ifst p)
cutAlg (Loop (body :*: NonComp) exit) _ =
  let (body', _) = doCut body True
      (exit', handled) = doCut (ifst exit) False
  -- the loop could terminate having read no `body`s, so only `exit` can decide if its handled.
  in (requiresCut (In (Loop body' exit')), handled)
cutAlg (Loop body exit) cut =
  let (body', _) = doCut (ifst body) False
      (exit', handled) = doCut (ifst exit) cut
  in (mkCut (not cut) (In (Loop body' exit')), handled)
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

mkImmune :: Bool -> Fix Combinator a -> Fix Combinator a
mkImmune True = In . MetaCombinator CutImmune
mkImmune False = id

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
