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

import Data.Kind                           (Type)
import Parsley.Internal.Common.Indexed     (Fix(..), cata)
import Parsley.Internal.Core.CombinatorAST (Combinator(..), MetaCombinator(..))
import Data.Bifunctor (first)

{-|
Annotate a tree with its cut-points. We assume a cut for let-bound parsers.

@since 1.5.0.0
-}
cutAnalysis :: Fix Combinator a -> Fix Combinator a
cutAnalysis = fst . ($ True) . doCut . cata (CutAnalysis . cutAlg)

data Compliance (k :: Type) = DomComp | NonComp | Comp | FullPure deriving stock (Show, Eq)
newtype CutAnalysis a = CutAnalysis { doCut :: Bool -> (Fix Combinator a, Bool) }

mkCut :: Bool -> Fix Combinator a -> Fix Combinator a
mkCut True = In . MetaCombinator Cut
mkCut False = id

rewrap :: (Fix Combinator a -> Combinator (Fix Combinator) b) -> Bool -> CutAnalysis a -> (Fix Combinator b, Bool)
rewrap con backtracks p = first (In . con) (doCut p backtracks)

biliftA2 :: (a -> b -> c) -> (x -> y -> z) -> (a, x) -> (b, y) -> (c, z)
biliftA2 f g (x1, y1) (x2, y2) = (f x1 x2, g y1 y2)

-- TODO: comments
cutAlg :: Combinator CutAnalysis a -> Bool -> (Fix Combinator a, Bool)
cutAlg (Pure x) _ = (In (Pure x), False)
cutAlg (Satisfy f) backtracks = (mkCut (not backtracks) (In (Satisfy f)), True)
cutAlg Empty _ = (In Empty, False)
cutAlg (Let r μ) _ = (In (Let r μ), False)
cutAlg (Try p) backtracks =
  let (p', cuts) = doCut p True
  in (mkCut (cuts && not backtracks) (In (Try p')), cuts)
cutAlg (p :<|>: q) backtracks =
  let (q', qcuts) = doCut q backtracks
      (p', pcuts) = doCut p (backtracks && qcuts)
  in (In (p' :<|>: q'), pcuts && qcuts)
cutAlg (l :<*>: r) backtracks = seqCutAlg (:<*>:) backtracks l r
cutAlg (l :<*: r) backtracks = seqCutAlg (:<*:) backtracks l r
cutAlg (l :*>: r) backtracks = seqCutAlg (:*>:) backtracks l r
cutAlg (LookAhead p) backtracks = rewrap LookAhead backtracks p
cutAlg (NotFollowedBy p) _ = False <$ rewrap NotFollowedBy True p
cutAlg (Debug msg p) backtracks = rewrap (Debug msg) backtracks p
cutAlg (Loop body exit) backtracks =
  let (body', _) = doCut body False
  in rewrap (Loop body') backtracks exit
cutAlg (Branch b p q) backtracks =
  let (b', bcuts) = doCut b backtracks
      (p', pcuts) = doCut p (backtracks || bcuts)
      (q', qcuts) = doCut q (backtracks || bcuts)
  in (In (Branch b' p' q'), bcuts || (pcuts && qcuts))
cutAlg (Match p f qs def) backtracks =
  let (p', pcuts) = doCut p backtracks
      (def', defcuts) = doCut def (backtracks || pcuts)
      (qs', allcut) = foldr (\q -> biliftA2 (:) (&&) (doCut q (backtracks || pcuts))) ([], defcuts) qs
  in (In (Match p' f qs' def'), pcuts || allcut)
cutAlg (MakeRegister σ l r) backtracks = seqCutAlg (MakeRegister σ) backtracks l r
cutAlg (GetRegister σ) _ = (In (GetRegister σ), False)
cutAlg (PutRegister σ p) backtracks = rewrap (PutRegister σ) backtracks p
cutAlg (Position sel) _ = (In (Position sel), False)
cutAlg (MetaCombinator m p) backtracks = rewrap (MetaCombinator m) backtracks p

seqCutAlg :: (Fix Combinator a -> Fix Combinator b -> Combinator (Fix Combinator) c) -> Bool -> CutAnalysis a -> CutAnalysis b -> (Fix Combinator c, Bool)
seqCutAlg con backtracks l r =
  let (l', lcuts) = doCut l backtracks
      (r', rcuts) = doCut r (backtracks || lcuts)
  in (In (con l' r'), lcuts || rcuts)
