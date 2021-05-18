{-# LANGUAGE PatternSynonyms #-}
{-|
Module      : Parsley.Combinator
Description : The parsing combinators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains the classic parser combinator operations specific to parsers themselves.
This means any combinators that deal with input consumption at a primitive level.

@since 0.1.0.0
-}
module Parsley.Combinator (
    char, item,
    string, token,
    oneOf, noneOf,
    eof, more,
    someTill,
    module Primitives
  ) where

import Prelude hiding                (traverse, (*>))
import Parsley.Alternative           (manyTill)
import Parsley.Applicative           (($>), void, traverse, (<:>), (*>))
import Parsley.Internal.Common.Utils (Code, makeQ)
import Parsley.Internal.Core         (Parser, Defunc(LIFTED, EQ_H, CONST), pattern APP_H)

import Parsley.Internal.Core.Primitives as Primitives (satisfy, lookAhead, try, notFollowedBy)

{-|
This combinator will attempt match a given string. If the parser fails midway through, this
combinator will fail having consumed input. On success, the string itself is returned and input
will be consumed.

@since 0.1.0.0
-}
string :: String -> Parser String
string = traverse char

{-|
This combinator will attempt to match any one of the provided list of characters. If one of those
characters is found, it will be returned and the input consumed. If not, the combinator will fail
having consumed no input.

@since 0.1.0.0
-}
oneOf :: [Char] -> Parser Char
oneOf cs = satisfy (makeQ (flip elem cs) [||\c -> $$(ofChars cs [||c||])||])

{-|
This combinator will attempt to not match any one of the provided list of characters. If one of those
characters is found, the combinator will fail having consumed no input. If not, it will return
the character that was not an element of the provided list.

@since 0.1.0.0
-}
noneOf :: [Char] -> Parser Char
noneOf cs = satisfy (makeQ (not . flip elem cs) [||\c -> not $$(ofChars cs [||c||])||])

ofChars :: [Char] -> Code Char -> Code Bool
ofChars = foldr (\c rest qc -> [|| c == $$qc || $$(rest qc) ||]) (const [||False||])

{-|
Like `string`, excepts parses the given string atomically using `try`. Never consumes input on
failure.

@since 0.1.0.0
-}
token :: String -> Parser String
token = try . string

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

-- Parsing Primitives
{-|
This combinator will attempt to match a given character. If that character is the next input token,
the parser succeeds and the character is returned. Otherwise, the combinator will fail having not
consumed any input.

@since 0.1.0.0
-}
char :: Char -> Parser Char
char c = satisfy (EQ_H (LIFTED c)) $> LIFTED c

{-|
Reads any single character. This combinator will only fail if there is no more input remaining.
The parsed character is returned.

@since 0.1.0.0
-}
item :: Parser Char
item = satisfy (APP_H CONST ((makeQ True [||True||])))

-- Composite Combinators
{-|
The combinator @someTill p end@ will try and parse @p@ as many times as possible (but at least once)
so long as @end@ cannot be successfully parsed. It will return the results from the successful parses of @p@.

@since 0.1.0.0
-}
someTill :: Parser a -> Parser b -> Parser [a]
someTill p end = notFollowedBy end *> (p <:> manyTill p end)