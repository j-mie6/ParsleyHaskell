{-|
Module      : Parsley.Internal.Frontend.Analysis.Inliner
Description : Decides whether to inline a let-bound parser.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes a transformation which can be used to inline let-bindings into their use-sites.

@since 1.7.0.0
-}
module Parsley.Internal.Frontend.Analysis.Inliner (inliner) where

import Data.Ratio                          ((%))
import Parsley.Internal.Common.Indexed     (Fix(..), cata)
import Parsley.Internal.Core.CombinatorAST (Combinator(..))
import Parsley.Internal.Core.Identifiers   (MVar)

inlineThreshold :: Rational
inlineThreshold = 13 % 10

{-|
Annotate a tree with its cut-points. We assume a cut for let-bound parsers.

@since 1.7.0.0
-}
inliner :: Bool -> MVar a -> Fix Combinator a -> Fix Combinator a
inliner recu _ body | not recu, shouldInline body = body
inliner recu μ _ = In (Let recu μ)

shouldInline :: Fix Combinator a -> Bool
shouldInline = (< inlineThreshold) . getWeight . cata (InlineWeight . alg)

newtype InlineWeight a = InlineWeight { getWeight :: Rational }

-- Ideally these should mirror those in the backend inliner, how can we unify them?
alg :: Combinator InlineWeight a -> Rational
alg (Pure _)             = 0
alg (Satisfy _)          = 1
alg Empty                = 0
alg Let{}                = 2 % 3
alg (Try p)              = getWeight p
alg (l :<|>: r)          = 1 % 4 + 2 % 5 + getWeight l + getWeight r
alg (l :<*>: r)          = 1 % 5 + getWeight l + getWeight r
alg (l :<*: r)           = getWeight l + getWeight r
alg (l :*>: r)           = getWeight l + getWeight r
alg (LookAhead c)        = getWeight c
alg (NotFollowedBy p)    = 1 % 4 + getWeight p
alg (Debug _ c)          = 2 % 4 + getWeight c
alg (Loop body exit)     = 2 % 3 + getWeight body + getWeight exit
alg (Branch b p q)       = 1 % 3 + 2 % 5 + getWeight b + getWeight p + getWeight q
alg (Match p _ qs def)   = fromIntegral (length qs + 1) % 3 + sum (map getWeight qs) + getWeight def + getWeight p
alg (MakeRegister _ l r) = 1 % 3 + getWeight l + getWeight r
alg (GetRegister _)      = 1 % 3
alg (PutRegister _ c)    = 1 % 3 + getWeight c
alg (Position _)         = 1 % 5
alg (MetaCombinator _ c) = getWeight c
