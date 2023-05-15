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

import Parsley.Internal.Common.Indexed     (Fix(..), cata)
import Parsley.Internal.Core.CombinatorAST (Combinator(..), MetaCombinator(..))
import Data.Bifunctor (first)

{-|
Annotate a tree with its cut-points. We assume a cut for let-bound parsers.

@since 1.5.0.0
-}
cutAnalysis :: Fix Combinator a -> Fix Combinator a
cutAnalysis = fst . ($ True) . doCut . cata (CutAnalysis . cutAlg)

newtype CutAnalysis a = CutAnalysis { doCut :: Bool -> (Fix Combinator a, Bool) }

cutAlg :: Combinator CutAnalysis a -> Bool -> (Fix Combinator a, Bool)
cutAlg (Pure x) _ = (In (Pure x), False)
-- if a cut is required, a `Satsify` is responsible for providing it but otherwise always handles
-- the cut: this is useful for allowing a `Try` to deal with a cut
cutAlg (Satisfy f) backtracks = (mkCut (not backtracks) (In (Satisfy f)), True)
cutAlg Empty _ = (In Empty, False)
-- all bindings must assume no backtracking, but bindings may be entirely pure
-- this means they cannot satisfy a cut themselves: basically they behave like option(item)
-- analysis could be done to prevent this though!
cutAlg (Let r μ) _ = (In (Let r μ), False)
-- obviously does not demand cuts for its children, however success of p may cause a cut
-- for the whole try - just as long as `p` itself cuts
cutAlg (Try p) backtracks =
  let (p', cuts) = doCut p True
  in (mkCut (cuts && not backtracks) (In (Try p')), cuts)
-- cannot pass `backtracks` directly to `p` because it prevents a cut being issued on the <|>
-- this has an effect if it causes an illegal backtrack that is effectful:
--     put r0 False *> try (string("abc") <|> put r0 True) <|> get
-- the problem is with non-consuming right branches: if the right branch
-- is guaranteed to consume input, then there will be a shared input factored
-- out, even if it is just one -- this means that the first input read of
-- the <|> is guarded: even if there is internal factoring, it cannot backtrack
-- to the right branch if it didn't enter the branch to begin with or didn't discharge
-- the length-check (by failing on the free read).
--
-- So, how to fix? well, only allowing this if both branches must consume input
-- seems to work ok: this can be done by using the `qcuts` flag
-- TODO: However, this rules out a fully pure branch also working: any branch without /any/ effect could be factored
cutAlg (p :<|>: q) backtracks =
  let (q', qcuts) = doCut q backtracks
      -- if the right-hand branch cuts it is guaranteed to consume input
      (p', pcuts) = doCut p ({- false -} backtracks && qcuts)
  in (In (p' :<|>: q'), pcuts && qcuts)
cutAlg (l :<*>: r) backtracks = seqCutAlg (:<*>:) backtracks l r
cutAlg (l :<*: r) backtracks = seqCutAlg (:<*:) backtracks l r
cutAlg (l :*>: r) backtracks = seqCutAlg (:*>:) backtracks l r
-- it may seems like a lookahead gaurantees the existence of some input, so can satisfy a cut
-- but this is not the case, because the consumed cutting character is rolled back: this means
-- the cut is only guaranteed to occur for a weaker predicate in whatever follows
cutAlg (LookAhead p) backtracks = False <$ rewrap LookAhead backtracks p
-- this can never satisfy a cut, because its unknown how or if it does so
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

mkCut :: Bool -> Fix Combinator a -> Fix Combinator a
mkCut True = In . MetaCombinator Cut
mkCut False = id

rewrap :: (Fix Combinator a -> Combinator (Fix Combinator) b) -> Bool -> CutAnalysis a -> (Fix Combinator b, Bool)
rewrap con backtracks p = first (In . con) (doCut p backtracks)

biliftA2 :: (a -> b -> c) -> (x -> y -> z) -> (a, x) -> (b, y) -> (c, z)
biliftA2 f g (x1, y1) (x2, y2) = (f x1 x2, g y1 y2)
