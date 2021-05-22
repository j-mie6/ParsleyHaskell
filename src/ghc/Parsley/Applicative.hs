{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Parsley.Applicative
Description : The @Applicative@ combinators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This modules contains all of the @Applicative@ combinators that would normally be found in
@Data.Functor@ or @Control.Applicative@. However, since Parsley makes use of staging, the signatures
of these combinators do not correctly match the signatures of those in base Haskell.

@since 0.1.0.0
-}
module Parsley.Applicative (
    pure, (<*>), (*>), (<*),
    fmap, (<$>), void, (<$), ($>), (<&>), constp,
    unit, (<~>), (<~), (~>),
    liftA2, liftA3,
    (<:>), (<**>),
    sequence, traverse, repeat,
    between,
    (>>)
  ) where

import Prelude hiding   (pure, (<*>), (*>), (<*), (>>), (<$>), fmap, (<$), traverse, sequence, repeat)
import Parsley.Internal (makeQ, Parser, Defunc(CONS, CONST, ID, EMPTY), pattern FLIP_H, pattern UNIT, ParserOps, pure, (<*>), (*>), (<*))

-- Functor Operations
{-|
Maps a function over the result of a parser.

@since 0.1.0.0
-}
fmap :: ParserOps rep => rep (a -> b) -> Parser a -> Parser b
fmap f = (pure f <*>)

{-|
Alias of `fmap`.

@since 0.1.0.0
-}
infixl 4 <$>
(<$>) :: ParserOps rep => rep (a -> b) -> Parser a -> Parser b
(<$>) = fmap

{-|
This combinator \"forgets\" the result of a parser, and replaces it with @()@.

@since 0.1.0.0
-}
void :: Parser a -> Parser ()
void p = p $> UNIT

{-|
This combinator \"forgets\" the result of a parser, and replaces it the given value.

@since 0.1.0.0
-}
infixl 4 <$
(<$) :: ParserOps rep => rep b -> Parser a -> Parser b
x <$ p = p *> pure x

{-|
This combinator \"forgets\" the result of a parser, and replaces it the given value.

@since 0.1.0.0
-}
infixl 4 $>
($>) :: ParserOps rep => Parser a -> rep b -> Parser b
($>) = flip (<$)

{-|
Maps a function over the result of a parser.

@since 0.1.0.0
-}
infixl 4 <&>
(<&>) :: ParserOps rep => Parser a -> rep (a -> b) -> Parser b
(<&>) = flip fmap

-- | @since 0.1.0.0
constp :: Parser a -> Parser (b -> a)
constp = (CONST <$>)

-- Alias Operations
{-|
Alias of @(`*>`)@

@since 0.1.0.0
-}
infixl 1 >>
(>>) :: Parser a -> Parser b -> Parser b
(>>) = (*>)

-- Monoidal Operations
{-|
This parser always returns @()@ without consuming input.

@since 0.1.0.0
-}
unit :: Parser ()
unit = pure UNIT

{-|
Sequential zipping of one parser's result with another's. The parsers must both succeed, one after
the other to pair their results. If either parser fails then the combinator will fail.

@since 0.1.0.0
-}
infixl 4 <~>
(<~>) :: Parser a -> Parser b -> Parser (a, b)
(<~>) = liftA2 (makeQ (,) [||(,)||])

{-|
Alias of @(`<*`)@

@since 0.1.0.0
-}
infixl 4 <~
(<~) :: Parser a -> Parser b -> Parser a
(<~) = (<*)

{-|
Alias of @(`*>`)@

@since 0.1.0.0
-}
infixl 4 ~>
(~>) :: Parser a -> Parser b -> Parser b
(~>) = (*>)

-- Lift Operations
{-|
Sequential combination of two parsers results. The results are combined using the given function.

@since 0.1.0.0
-}
liftA2 :: ParserOps rep => rep (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftA2 f p q = f <$> p <*> q

{-|
Sequential combination of three parsers results. The results are combined using the given function.

@since 0.1.0.0
-}
liftA3 :: ParserOps rep => rep (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
liftA3 f p q r = f <$> p <*> q <*> r

{-|
Sequential consing of one parser's result with another's. The parsers must both succeed, one after
the other to combine their results. If either parser fails then the combinator will fail.

@since 0.1.0.0
-}
infixl 4 <:>
(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = liftA2 CONS

{-|
A variant of @(`<*>`)@ with the arguments reversed.

@since 0.1.0.0
-}
infixl 4 <**>
(<**>) :: Parser a -> Parser (a -> b) -> Parser b
(<**>) = liftA2 (FLIP_H ID)

-- Auxillary functions
{-|
Given a list of parsers, `sequence` will parse each in turn and collect all their results into a
list. All the parsers in the list must succeed.

@since 0.1.0.0
-}
sequence :: [Parser a] -> Parser [a]
sequence = foldr (<:>) (pure EMPTY)

{-|
Like `sequence`, but the parsers to sequence are generated from seed values using a given generator
function.

@since 0.1.0.0
-}
traverse :: (a -> Parser b) -> [a] -> Parser [b]
traverse f = sequence . map f

{-|
The combinator @repeat n p@ will attempt to parse @p@ exactly @n@ times. That is not to say that
the parser must fail on the @n+1@th try, but there must be @n@ successes for the combinator to
succeed. All the results generated from @p@ will be collected into a list.

@since 0.1.0.0
-}
repeat :: Int -> Parser a -> Parser [a]
repeat n = sequence . replicate n

{-|
The combinator @between open close p@ will first parse @open@ then @p@ and then @close@, yielding
the result given by @p@.

@since 0.1.0.0
-}
between :: Parser o -> Parser c -> Parser a -> Parser a
between open close p = open *> p <* close