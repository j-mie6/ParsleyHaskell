{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE PatternSynonyms #-}
module Parsley.Combinator (
    token, char, item,
    tokens, string, atomic,
    oneOf, noneOf,
    eof, more,
    someTill,
    module Primitives
  ) where

import Prelude hiding       (traverse, (*>))
import Data.String          (IsString(fromString))
import Parsley.Alternative  (manyTill)
import Parsley.Applicative  (($>), void, traverse, (<:>), (*>))
import Parsley.Common.Utils (code, Code, makeQ)
import Parsley.Core         (Parser, Defunc(TOK, EQ_H, CONST), pattern APP_H, Token)

import Parsley.Core.Primitives as Primitives (satisfy, lookAhead, try, notFollowedBy)

instance IsString (Parser Char String) where fromString = string

string :: String -> Parser Char String
string = tokens

tokens :: Token t => [t] -> Parser t [t]
tokens = traverse token

oneOf :: [Char] -> Parser Char Char
oneOf cs = satisfy (makeQ (flip elem cs) [||\c -> $$(ofChars cs [||c||])||])

noneOf :: [Char] -> Parser Char Char
noneOf cs = satisfy (makeQ (not . flip elem cs) [||\c -> not $$(ofChars cs [||c||])||])

ofChars :: [Char] -> Code Char -> Code Bool
ofChars = foldr (\c rest qc -> [|| c == $$qc || $$(rest qc) ||]) (const [||False||])

atomic :: Token t => [t] -> Parser t [t]
atomic = try . tokens

eof :: Parser Char ()
eof = notFollowedBy item

more :: Parser Char ()
more = lookAhead (void item)

-- Parsing Primitives
token :: Token t => t -> Parser t t
token t = satisfy (EQ_H (TOK t)) $> TOK t

char :: Char -> Parser Char Char
char = token

item :: Parser t t
item = satisfy (APP_H CONST (code True))

-- Composite Combinators
someTill :: Parser t a -> Parser t b -> Parser t [a]
someTill p end = notFollowedBy end *> (p <:> manyTill p end)