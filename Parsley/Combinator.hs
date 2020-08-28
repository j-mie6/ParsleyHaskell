{-# LANGUAGE PatternSynonyms #-}
module Parsley.Combinator (
    char, item,
    string, token,
    oneOf, noneOf,
    eof, more,
    someTill,
    module Primitives
  ) where

import Prelude hiding       (traverse, (*>))
import Parsley.Alternative  (manyTill)
import Parsley.Applicative  (($>), void, traverse, (<:>), (*>))
import Parsley.Common.Utils (code, Code, makeQ)
import Parsley.Core         (Parser, Defunc(CHAR, EQ_H, CONST), pattern APP_H)

import Parsley.Core.Primitives as Primitives (satisfy, lookAhead, try, notFollowedBy)

string :: String -> Parser Char String
string = traverse char

oneOf :: [Char] -> Parser Char Char
oneOf cs = satisfy (makeQ (flip elem cs) [||\c -> $$(ofChars cs [||c||])||])

noneOf :: [Char] -> Parser Char Char
noneOf cs = satisfy (makeQ (not . flip elem cs) [||\c -> not $$(ofChars cs [||c||])||])

ofChars :: [Char] -> Code Char -> Code Bool
ofChars = foldr (\c rest qc -> [|| c == $$qc || $$(rest qc) ||]) (const [||False||])

token :: String -> Parser Char String
token = try . string

eof :: Parser Char ()
eof = notFollowedBy item

more :: Parser Char ()
more = lookAhead (void item)

-- Parsing Primitives
char :: Char -> Parser Char Char
char c = satisfy (EQ_H (CHAR c)) $> CHAR c

item :: Parser t t
item = satisfy (APP_H CONST (code True))

-- Composite Combinators
someTill :: Parser t a -> Parser t b -> Parser t [a]
someTill p end = notFollowedBy end *> (p <:> manyTill p end)