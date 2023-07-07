{-|
Module      : Parsley.Internal.Backend.Analysis.Inliner
Description : Determines whether a machine should be inlined.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes an inliner analysis that determines whether or not a given machine should be inlined
as opposed to bound in the generated code.

@since 1.7.0.0
-}
module Parsley.Internal.Backend.Analysis.Inliner (shouldInline) where

import Data.Ratio                       ((%))
import Parsley.Internal.Backend.Machine (Instr(..), Handler(..), Access(Hard, Soft))
import Parsley.Internal.Common.Indexed  (cata4, Fix4, Nat)

import qualified Parsley.Internal.Opt   as Opt

{-|
Provides a conservative estimate on whether or not each of the elements of the stack on
entry to a machine are actually used in the computation.

@since 1.7.0.0
-}
shouldInline :: Opt.Flags -> Fix4 (Instr o) xs n r a -> Bool
shouldInline flags
  | Just thresh <- Opt.inlineThreshold flags = (< thresh) . getWeight . cata4 (InlineWeight . alg)
  | otherwise                                = const False

newtype InlineWeight xs (n :: Nat) r a = InlineWeight { getWeight :: Rational }

alg :: Instr o InlineWeight xs n r a -> Rational
alg Ret                = 0
alg (Push _ k)         = 0 + getWeight k
alg (Pop k)            = 0 + getWeight k
alg (Lift2 _ k)        = 1 % 5 + getWeight k
alg (Sat _ k)          = 1 + getWeight k
alg (Call _ k)         = 2 % 3 + getWeight k
alg Empt               = 0
alg (Commit k)         = 0 + getWeight k
alg (Catch k h)        = (if handlerInlined h then 0 else 1 % 4) + getWeight k + algHandler h
alg (Tell k)           = 0 + getWeight k
alg (Seek k)           = 0 + getWeight k
alg (Case p q)         = 1 % 3 + getWeight p + getWeight q
alg (Choices _ ks def) = fromIntegral (length ks + 1) % 3 + sum (map getWeight ks) + getWeight def
alg (Iter _ b h)       = 2 % 3 + getWeight b + algHandler h
alg (Join _)           = 0
alg (MkJoin _ b k)     = 2 % 5 + getWeight b + getWeight k
alg (Swap k)           = 0 + getWeight k
alg (Dup k)            = 1 % 10 + getWeight k
alg (Make _ Hard k)    = 1 % 3 + getWeight k
alg (Get _ Hard k)     = 1 % 3 + getWeight k
alg (Put _ Hard k)     = 1 % 3 + getWeight k
alg (SelectPos _ k)    = 1 % 5 + getWeight k
alg (Make _ Soft k)    = 1 % 10 + getWeight k
alg (Get _ Soft k)     = 0 + getWeight k
alg (Put _ Soft k)     = 1 % 10 + getWeight k
alg (LogEnter _ k)     = 1 % 4 + getWeight k
alg (LogExit _ k)      = 1 % 4 + getWeight k
alg (MetaInstr _ k)    = 0 + getWeight k

algHandler :: Handler o InlineWeight xs n r a -> Rational
algHandler (Always _ h) = getWeight h
algHandler (Same _ y _ n) = getWeight y + getWeight n

handlerInlined :: Handler o k xs n r a -> Bool
handlerInlined (Always True _) = True
handlerInlined _               = False
