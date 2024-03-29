{-# LANGUAGE ImplicitParams #-}
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

import qualified Parsley.Internal.Opt   as Opt

{-|
Annotate a tree with its cut-points. We assume a cut for let-bound parsers.

@since 1.7.0.0
-}
inliner :: (?flags :: Opt.Flags) => Maybe Int -> MVar a -> Fix Combinator a -> Fix Combinator a
inliner occs _ body
  | Just n <- occs
  , Just thresh <- Opt.primaryInlineThreshold ?flags
  , shouldInline n thresh body = body
inliner _ μ _ = In (Let μ)

shouldInline :: Int -> Rational -> Fix Combinator a -> Bool
shouldInline occs inlineThreshold = (<= inlineThreshold) . (* toRational occs) . subtract callCost . getWeight . cata (InlineWeight . alg)

newtype InlineWeight a = InlineWeight { getWeight :: Rational }

callCost :: Rational
callCost = 1 % 3

handlerCost :: Rational
handlerCost = 1 % 4

registerCost :: Rational
registerCost = 1 % 3

-- Ideally these should mirror those in the backend inliner, how can we unify them?
alg :: Combinator InlineWeight a -> Rational
alg (Pure _)             = 0
alg (Satisfy _)          = 1
alg Empty                = 0
alg Let{}                = callCost
alg (Try p)              = getWeight p
alg (l :<|>: r)          = handlerCost + 1 % 5 + getWeight l + getWeight r
alg (l :<*>: r)          = 1 % 5 + getWeight l + getWeight r
alg (l :<*: r)           = getWeight l + getWeight r
alg (l :*>: r)           = getWeight l + getWeight r
alg (LookAhead c)        = getWeight c
alg (NotFollowedBy p)    = handlerCost + getWeight p
alg (Debug _ c)          = getWeight c
alg (Loop body exit)     = handlerCost + callCost + 2 % 3 + getWeight body + getWeight exit
alg (Branch b p q)       = 1 % 3 + 2 % 5 + getWeight b + getWeight p + getWeight q
alg (Match p _ qs def)   = fromIntegral (length qs + 1) % 3 + sum (map getWeight qs) + getWeight def + getWeight p
alg (MakeRegister _ l r) = registerCost + getWeight l + getWeight r
alg (GetRegister _)      = registerCost
alg (PutRegister _ c)    = registerCost + getWeight c
alg (Position _)         = 1 % 5
alg (MetaCombinator _ c) = getWeight c
