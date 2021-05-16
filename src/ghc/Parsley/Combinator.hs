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
import Parsley.Internal.Core         (Parser, Defunc(CHAR, EQ_H, CONST), pattern APP_H)

import Parsley.Internal.Core.Primitives as Primitives (satisfy, lookAhead, try, notFollowedBy)

string :: String -> Parser String
string = traverse char

oneOf :: [Char] -> Parser Char
oneOf cs = satisfy (makeQ (flip elem cs) [||\c -> $$(ofChars cs [||c||])||])

noneOf :: [Char] -> Parser Char
noneOf cs = satisfy (makeQ (not . flip elem cs) [||\c -> not $$(ofChars cs [||c||])||])

ofChars :: [Char] -> Code Char -> Code Bool
ofChars = foldr (\c rest qc -> [|| c == $$qc || $$(rest qc) ||]) (const [||False||])

token :: String -> Parser String
token = try . string

eof :: Parser ()
eof = notFollowedBy item

more :: Parser ()
more = lookAhead (void item)

-- Parsing Primitives
char :: Char -> Parser Char
char c = satisfy (EQ_H (CHAR c)) $> CHAR c

item :: Parser Char
item = satisfy (APP_H CONST ((makeQ True [||True||])))

-- Composite Combinators
someTill :: Parser a -> Parser b -> Parser [a]
someTill p end = notFollowedBy end *> (p <:> manyTill p end)