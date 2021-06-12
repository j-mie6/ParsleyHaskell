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
    branch, select,
    (>??>), filteredBy, (>?>),
    predicate, (<?:>),
    conditional, match, (||=),
    when, while,
    fromMaybeP
  ) where

import Prelude hiding             (pure, (<$>))
import Data.Function              (fix)
import Language.Haskell.TH.Syntax (Lift(..))
import Parsley.Alternative        (empty)
import Parsley.Applicative        (pure, (<$>), liftA2, unit, constp)
import Parsley.Internal           (makeQ, Parser, Defunc(ID, EQ_H, IF_S, LAM_S, LET_S, APP_H), ParserOps, conditional, branch)

{-|
Similar to `branch`, except the given branch is only executed on a @Left@ returned.

> select p q = branch p q (pure id)

@since 0.1.0.0
-}
select :: Parser (Either a b) -> Parser (a -> b) -> Parser b
select p q = branch p q (pure ID)

-- Filter Combinators
{-|
This combinator is used for filtering. Given @px >??> pf@, if @px@ succeeds, then @pf@ will be
attempted too. Then the result of @px@ is given to @pf@'s. If the function returns true then the
parser succeeds and returns the result of @px@, otherwise it will fail.

@since 0.1.0.0
-}
infixl 4 >??>
(>??>) :: Parser a -> Parser (a -> Bool) -> Parser a
px >??> pf = select (liftA2 g pf px) empty
  where
    -- Not sure if I need the LET_S?
    g =
      LAM_S $ \f ->
        LAM_S $ \x ->
          LET_S x $ \x ->
            IF_S (APP_H f x)
                 (APP_H (makeQ Right [||Right||]) x)
                 (makeQ (Left ()) [||Left ()||])

{-|
An alias for @(`>?>`)@.

@since 0.1.0.0
-}
filteredBy :: ParserOps rep => Parser a -> rep (a -> Bool) -> Parser a
filteredBy p f = p >??> pure f

{-|
This combinator is used for filtering, similar to @(`>??>`)@ except the predicate is given without
parsing anything.

> px >?> f = px >??> pure f

@since 0.1.0.0
-}
infixl 4 >?>
(>?>) :: ParserOps rep => Parser a -> rep (a -> Bool) -> Parser a
(>?>) = filteredBy

-- Conditional Combinators
{-|
Similar to an @if@ statement: @predicate f p t e@ first parses @p@ and collects its result @x@.
If @f x@ is @True@ then @t@ is parsed, else @e@ is parsed.

@since 0.1.0.0
-}
predicate :: ParserOps rep => rep (a -> Bool) -> Parser a -> Parser b -> Parser b -> Parser b
predicate cond p t e = conditional [(cond, t)] p e

{-|
A \"ternary\" combinator, essentially `predicate` given the identity function.

@since 0.1.0.0
-}
infixl 4 <?:>
(<?:>) :: Parser Bool -> (Parser a, Parser a) -> Parser a
cond <?:> (p, q) = predicate ID cond p q

-- Match Combinators
{-|
The `match` combinator can be thought of as a restricted form of @(>>=)@, where there is a fixed
domain on the valid outputs of the second argument.

More concretely, @match dom p f def@ first parses @p@, and, if its result is an element of the list
@dom@, its result is applied to the function @f@ and the resulting parser is executed. If the result
was not in @dom@, then @def@ will be executed.

Note: To eliminate the dynamic nature of the operation, every possible outcome of the parser is
enumerated and tried in turn.

@since 0.1.0.0
-}
match :: (Eq a, Lift a)
      => [a]             -- ^ The domain of the function given as the third argument
      -> Parser a        -- ^ The parser whose result will be given to the function
      -> (a -> Parser b) -- ^ A function uses to generate the parser to execute
      -> Parser b        -- ^ A parser to execute if the result is not in the domain of the function
      -> Parser b
match vs p f = conditional (map (\v -> (EQ_H (makeQ v [||v||]), f v)) vs) p

{-|
This combinator, known as @sbind@ in the literature, is best avoided for efficiency sake. It is
built on `match`, but where the domain of the function is /all/ of the possible values of the
datatype. This means the type must be finite, or else this combinator would never terminate.

The problem with the combinator is not so much that it takes linear time to take the right branch
(as opposed to monadic @(>>=)@) but that it generates a /massive/ amount of code when the datatype
gets too big. For instance, using it for `Char` would generate a 66535-way case split!

The role this combinator fulfils is the branching behaviour that monadic operations can provide.
For the persistence or duplication of data that monads can provide, `Parsley.Register.bind` is a much better
alternative.

@since 0.1.0.0
-}
infixl 1 ||=
(||=) :: (Enum a, Bounded a, Eq a, Lift a) => Parser a -> (a -> Parser b) -> Parser b
p ||= f = match [minBound..maxBound] p f empty

-- Composite Combinators
{-|
This combinator will only execute its second argument if the first one returned @True@.

@since 0.1.0.0
-}
when :: Parser Bool -> Parser () -> Parser ()
when p q = p <?:> (q, unit)

{-|
The fixed-point of the `when` combinator: it will continuously parse its argument until either it
fails (in which case it fails), or until it returns @False@.

@since 0.1.0.0
-}
while :: Parser Bool -> Parser ()
while x = fix (when x)

{-|
Given @fromMaybeP p def@, if @p@ returns a @Nothing@ then @def@ is executed, otherwise the result
of @p@ will be returned with the @Just@ removed.

@since 0.1.0.0
-}
fromMaybeP :: Parser (Maybe a) -> Parser a -> Parser a
fromMaybeP pm px = select (makeQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)