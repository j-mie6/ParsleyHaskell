module Parsley.Selective (
    module Parsley.Selective,
    module Primitives,
    Lift(..)
  ) where

import Prelude hiding             (pure, (<$>))
import Data.Function              (fix)
import Language.Haskell.TH.Syntax (Lift(..))
import Parsley.Alternative        (empty)
import Parsley.Applicative        (pure, (<$>), liftA2, unit, constp)
import Parsley.Common.Utils       (code, makeQ)
import Parsley.Core               (Parser, Defunc(ID, EQ_H), ParserOps)

import Parsley.Core.Primitives as Primitives (conditional, branch)

select :: Parser t (Either a b) -> Parser t (a -> b) -> Parser t b
select p q = branch p q (pure ID)

-- Filter Combinators
infixl 4 >??>
(>??>) :: Parser t a -> Parser t (a -> Bool) -> Parser t a
px >??> pf = select (liftA2 (makeQ g qg) pf px) empty
  where
    g f x = if f x then Right x else Left ()
    qg = [||\f x -> if f x then Right x else Left ()||]

filteredBy :: ParserOps rep => Parser t a -> rep (a -> Bool) -> Parser t a
filteredBy p f = p >??> pure f

infixl 4 >?>
(>?>) :: ParserOps rep => Parser t a -> rep (a -> Bool) -> Parser t a
(>?>) = filteredBy

-- Conditional Combinators
predicate :: ParserOps rep => rep (a -> Bool) -> Parser t a -> Parser t b -> Parser t b -> Parser t b
predicate cond p t e = conditional [(cond, t)] p e

infixl 4 <?:>
(<?:>) :: Parser t Bool -> (Parser t a, Parser t a) -> Parser t a
cond <?:> (p, q) = predicate ID cond p q

-- Match Combinators
match :: (Eq a, Lift a) => [a] -> Parser t a -> (a -> Parser t b) -> Parser t b -> Parser t b
match vs p f = conditional (map (\v -> (EQ_H (code v), f v)) vs) p

infixl 1 ||=
(||=) :: (Enum a, Bounded a, Eq a, Lift a) => Parser t a -> (a -> Parser t b) -> Parser t b
p ||= f = match [minBound..maxBound] p f empty

-- Composite Combinators
when :: Parser t Bool -> Parser t () -> Parser t ()
when p q = p <?:> (q, unit)

while :: Parser t Bool -> Parser t ()
while x = fix (when x)

fromMaybeP :: Parser t (Maybe a) -> Parser t a -> Parser t a
fromMaybeP pm px = select (makeQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)