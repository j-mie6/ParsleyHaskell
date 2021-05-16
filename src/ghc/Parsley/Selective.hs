{-|
Module      : Parsley.Selective
Description : The @Selective@ combinators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

A version of the @Selective@ combinators as described in [/Selective Applicative Functors/
(Mokhov et al. 2019)](https://dl.acm.org/doi/10.1145/3341694).

Like the @Applicative@ and @Alternative@ combinators, these cannot be properly described by the
@Selective@ typeclass, since the API relies on Template Haskell code being used by @Applicative@.

@since 0.1.0.0
-}
module Parsley.Selective (
    module Parsley.Selective,
    module Primitives
  ) where

import Prelude hiding                (pure, (<$>))
import Data.Function                 (fix)
import Language.Haskell.TH.Syntax    (Lift(..))
import Parsley.Alternative           (empty)
import Parsley.Applicative           (pure, (<$>), liftA2, unit, constp)
import Parsley.Internal.Common.Utils (makeQ, Code)
import Parsley.Internal.Core         (Parser, Defunc(ID, EQ_H), ParserOps)

import Parsley.Internal.Core.Primitives as Primitives (conditional, branch)

select :: Parser (Either a b) -> Parser (a -> b) -> Parser b
select p q = branch p q (pure ID)

-- Filter Combinators
infixl 4 >??>
(>??>) :: Parser a -> Parser (a -> Bool) -> Parser a
px >??> pf = select (liftA2 (makeQ g qg) pf px) empty
  where
    g :: (a -> Bool) -> a -> Either () a
    g f x = if f x then Right x else Left ()
    qg :: Code ((a -> Bool) -> a -> Either () a)
    qg = [||\f x -> if f x then Right x else Left ()||]

filteredBy :: ParserOps rep => Parser a -> rep (a -> Bool) -> Parser a
filteredBy p f = p >??> pure f

infixl 4 >?>
(>?>) :: ParserOps rep => Parser a -> rep (a -> Bool) -> Parser a
(>?>) = filteredBy

-- Conditional Combinators
predicate :: ParserOps rep => rep (a -> Bool) -> Parser a -> Parser b -> Parser b -> Parser b
predicate cond p t e = conditional [(cond, t)] p e

infixl 4 <?:>
(<?:>) :: Parser Bool -> (Parser a, Parser a) -> Parser a
cond <?:> (p, q) = predicate ID cond p q

-- Match Combinators
match :: (Eq a, Lift a) => [a] -> Parser a -> (a -> Parser b) -> Parser b -> Parser b
match vs p f = conditional (map (\v -> (EQ_H (makeQ v [||v||]), f v)) vs) p

infixl 1 ||=
(||=) :: (Enum a, Bounded a, Eq a, Lift a) => Parser a -> (a -> Parser b) -> Parser b
p ||= f = match [minBound..maxBound] p f empty

-- Composite Combinators
when :: Parser Bool -> Parser () -> Parser ()
when p q = p <?:> (q, unit)

while :: Parser Bool -> Parser ()
while x = fix (when x)

fromMaybeP :: Parser (Maybe a) -> Parser a -> Parser a
fromMaybeP pm px = select (makeQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)