{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-|
Module      : Parsley.Char
Description : The input consuming combinators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module contains combinators that deal with input consumption..

@since 2.0.0.0
-}
module Parsley.Char (
    satisfy, char, item,
    string, token,
    oneOf, noneOf,
    digit, letter, letterOrDigit
  ) where

import Prelude hiding           (traverse)
import Data.Char                (isAlpha, isAlphaNum)
import Data.List                (sort)
import Parsley.Applicative      (($>), traverse)
import Parsley.Defunctionalized (Defunc(LIFTED, RANGES))
import Parsley.Internal         (Parser, makeQ)
import Parsley.ParserOps        (satisfy)

import qualified Parsley.Internal as Internal (try)

{-|
This combinator will attempt match a given string. If the parser fails midway through, this
combinator will fail having consumed input. On success, the string itself is returned and input
will be consumed.

@since 2.0.0.0
-}
string :: String -> Parser String
string = traverse char

{-|
This combinator will attempt to match any one of the provided list of characters. If one of those
characters is found, it will be returned and the input consumed. If not, the combinator will fail
having consumed no input.

@since 2.0.0.0
-}
oneOf :: [Char] -> Parser Char
oneOf = satisfy . RANGES True . ranges

{-|
This combinator will attempt to not match any one of the provided list of characters. If one of those
characters is found, the combinator will fail having consumed no input. If not, it will return
the character that was not an element of the provided list.

@since 2.0.0.0
-}
noneOf :: [Char] -> Parser Char
noneOf = satisfy . RANGES False . ranges

ranges :: [Char] -> [(Char, Char)]
ranges [] = []
ranges (sort -> c:cs) = go c (fromEnum c) cs
  where
    go :: Char -> Int -> [Char] -> [(Char, Char)]
    go lower prev [] = [(lower, toEnum prev)]
    go lower prev (c:cs)
      | i <- fromEnum c, i == prev + 1 = go lower i cs
      | otherwise = (lower, toEnum prev) : go c (fromEnum c) cs

{-|
Like `string`, excepts parses the given string atomically using `try`. Never consumes input on
failure.

@since 2.0.0.0
-}
token :: String -> Parser String
token = Internal.try . string

{-|
This combinator will attempt to match a given character. If that character is the next input token,
the parser succeeds and the character is returned. Otherwise, the combinator will fail having not
consumed any input.

@since 2.0.0.0
-}
char :: Char -> Parser Char
char c = satisfy (RANGES True [(c, c)]) $> LIFTED c

{-|
Reads any single character. This combinator will only fail if there is no more input remaining.
The parsed character is returned.

@since 2.0.0.0
-}
item :: Parser Char
item = satisfy (RANGES False [])

isDigit :: Defunc (Char -> Bool)
isDigit = RANGES True [('0', '9')]

{-|
Reads a digit (0 through 9).

@since 2.0.0.0
-}
digit :: Parser Char
digit = satisfy isDigit

{-|
Uses `isAlpha` to parse a letter, this includes
unicode letters.

@since 2.0.0.0
-}
letter :: Parser Char
letter = satisfy (makeQ isAlpha [||isAlpha||])

{-|
Uses `isAlphaNum` to parse a letter, this includes
unicode letters, or a digit.

@since 2.0.0.0
-}
letterOrDigit :: Parser Char
letterOrDigit = satisfy (makeQ isAlphaNum [||isAlphaNum||])
