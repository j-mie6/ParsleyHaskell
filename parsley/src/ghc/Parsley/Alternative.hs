{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Parsley.Alterative
Description : The @Alternative@ combinators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This modules contains the @Alternative@ combinators that would normally be found in
@Control.Applicative@. However, since Parsley makes use of staging, the signatures
of these combinators do not correctly match the signatures of those in base Haskell (due to a lack
of @Applicative@ constraint).

@since 0.1.0.0
-}
module Parsley.Alternative (
    (<|>), empty,
    (<+>), option, optionally, optional, choice, maybeP, manyTill
  ) where

import Prelude hiding           (pure, (<$>))
import Parsley.Applicative      (pure, (<$>), ($>), (<:>))
import Parsley.Defunctionalized (Defunc(EMPTY), pattern UNIT)
import Parsley.Internal         (makeQ, Parser)
import Parsley.ParserOps        (ParserOps)

import qualified Parsley.Internal as Internal ((<|>), empty)

{-|
This combinator always fails.

@since 0.1.0.0
-}
empty :: Parser a
empty = Internal.empty

{-|
This combinator implements branching within a parser. It is left-biased, so that if the first branch
succeeds, the second will not be attempted. In accordance with @parsec@ semantics, if the first
branch failed having consumed input the second branch cannot be taken. (see `Parsley.Combinator.try`)

@since 0.1.0.0
-}
infixr 3 <|>
(<|>) :: Parser a -> Parser a -> Parser a
(<|>) = (Internal.<|>)

{-|
This combinator is similar to @(`<|>`)@, except it allows both branches to differ in type by
producing a co-product as a result.

@since 0.1.0.0
-}
infixl 3 <+>
(<+>) :: Parser a -> Parser b -> Parser (Either a b)
p <+> q = makeQ Left [||Left||] <$> p <|> makeQ Right [||Right||] <$> q

{-|
@option x p@ first tries to parse @p@ and, if it fails without consuming input, will return
@x@ as a result.

@since 0.1.0.0
-}
option :: ParserOps rep => rep a -> Parser a -> Parser a
option x p = p <|> pure x

{-|
@optionally p x@ will try to parse @p@ and will always return @x@. If @p@ fails having consumed
input, then this combinator will fail.

@since 0.1.0.0
-}
optionally :: ParserOps rep => Parser a -> rep b -> Parser b
optionally p x = option x (p $> x)

{-|
Attempts to parse a given parser, and will always return @()@. (See `optionally`)

@since 0.1.0.0
-}
optional :: Parser a -> Parser ()
optional = flip optionally UNIT

{-|
Tries to parse each of the given parsers in turn until one of them succeeds using @(`<|>`)@. If
given the empty list, it will fail unconditionally.

@since 0.1.0.0
-}
choice :: [Parser a] -> Parser a
choice = foldr (<|>) empty

{-|
Tries to parse a given parser, returning its result in @Just@ if it succeeds and @Nothing@ if it
fails having not consumed input.

@since 0.1.0.0
-}
maybeP :: Parser a -> Parser (Maybe a)
maybeP p = option (makeQ Nothing [||Nothing||]) (makeQ Just [||Just||] <$> p)

{-|
The combinator @someTill p end@ will try and parse @p@ as many times as possible so long as @end@
cannot be successfully parsed. It will return the results from the successful parses of @p@.

@since 0.1.0.0
-}
manyTill :: Parser a -> Parser b -> Parser [a]
manyTill p end = let go = end $> EMPTY <|> p <:> go in go
