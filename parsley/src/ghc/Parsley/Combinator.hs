{-|
Module      : Parsley.Combinator
Description : The parsing combinators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains the classic parser combinator operations specific to parsers themselves, excluding
those that consume input.

@since 0.1.0.0
-}
module Parsley.Combinator (
    eof, more,
    someTill,
    try,
    lookAhead, notFollowedBy,
    line, col, pos
  ) where

import Prelude hiding           ((*>))
import Parsley.Alternative      (manyTill)
import Parsley.Applicative      (void, (<:>), (*>), (<~>))
import Parsley.Internal         (Parser)
import Parsley.Char             (item)

import qualified Parsley.Internal as Internal (try, lookAhead, notFollowedBy, line, col)

{-|
This combinator will attempt to parse a given parser. If it succeeds, the result is returned without
having consumed any input. If it fails, however, any consumed input remains consumed.

@since 0.1.0.0
-}
lookAhead :: Parser a -> Parser a
lookAhead = Internal.lookAhead

{-|
This combinator will ensure that a given parser fails. If the parser does fail, a @()@ is returned
and no input is consumed. If the parser succeeded, then this combinator will fail, however it will
not consume any input.

@since 0.1.0.0
-}
notFollowedBy :: Parser a -> Parser ()
notFollowedBy = Internal.notFollowedBy

{-|
This combinator allows a parser to backtrack on failure, which is to say that it will
not have consumed any input if it were to fail. This is important since @parsec@ semantics demand
that the second branch of @(`Parsley.Alternative.<|>`)@ can only be taken if the first did not consume input on failure.

Excessive use of `try` will reduce the efficiency of the parser and effect the generated error
messages. It should only be used in one of two circumstances:

* When two branches of a parser share a common leading prefix (in which case, it is often better
  to try and factor this out).
* When a parser needs to be executed atomically (for example, tokens).

@since 0.1.0.0
-}
try :: Parser a -> Parser a
try = Internal.try

{-|
This parser succeeds only if there is no input left to consume, and fails without consuming input
otherwise.

@since 0.1.0.0
-}
eof :: Parser ()
eof = notFollowedBy item

{-|
This parser succeeds if there is still input left to consume, and fails otherwise.

@since 0.1.0.0
-}
more :: Parser ()
more = lookAhead (void item)

-- Composite Combinators
{-|
The combinator @someTill p end@ will try and parse @p@ as many times as possible (but at least once)
so long as @end@ cannot be successfully parsed. It will return the results from the successful parses of @p@.

@since 0.1.0.0
-}
someTill :: Parser a -> Parser b -> Parser [a]
someTill p end = notFollowedBy end *> (p <:> manyTill p end)

{-|
The `line` combinator returns the current line number at this point in the parse. Line numbers
start from 1.

@since 1.0.1.0
-}
line :: Parser Int
line = Internal.line

{-|
The `col` combinator returns the current column number at this point in the parse. Column numbers
start from 1.

@since 1.0.1.0
-}
col :: Parser Int
col = Internal.col

{-|
The `pos` combinator returns the current line and column number at this point in the parse.

@since 1.0.1.0
-}
pos :: Parser (Int, Int)
pos = line <~> col
