{-# LANGUAGE TemplateHaskell #-}
module Primitive.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Data.Char (isDigit)
import Parsley.Internal (Parser, Defunc(EMPTY, LIFTED, RANGES, CONS), makeQ, pure, satisfy, (*>), (<*), (<|>), (<*>), satisfy, lookAhead, notFollowedBy, line, col)
import Text.ParserCombinators.ReadP (look)

char :: Char -> Parser Char
char c = satisfy (RANGES True [(c, c)])

item :: Parser Char
item = satisfy (RANGES False [])

pure7 :: Parser Int
pure7 = pure (LIFTED 7)

digit :: Parser Char
digit = satisfy (makeQ isDigit [||isDigit||])

twoDigits :: Parser Char
twoDigits = digit *> digit

abOrC :: Parser String
abOrC = (char 'a' *> char 'b' *> pure (LIFTED "ab")) <|> (char 'c' *> pure (LIFTED "c"))

abOrCThenD :: Parser String
abOrCThenD = abOrC <* char 'd'

recursive :: Parser [Char]
recursive =
  let r = pure CONS <*> item <*> r <|> pure EMPTY
  in r

lookAheadDigit :: Parser Char
lookAheadDigit = lookAhead digit *> digit

(<~>) :: Parser a -> Parser b -> Parser (a, b)
mx <~> my = pure (makeQ (,) [||(,)||]) <*> mx <*> my

pos :: Parser (Int, Int)
pos = line <~> col

posAfterA :: Parser (Int, Int)
posAfterA = char 'a' *> pos

posAfterNewline :: Parser ((Int, Int), (Int, Int))
posAfterNewline = (char 'a' *> char '\n' *> pos) <~> (char '\n' *> pos)

posAfterTab :: Parser ((Int, Int), (Int, Int))
posAfterTab = (char '\t' *> pos) <~> (char 'a' *> char '\t' *> pos)

posAfterLookahead :: Parser ((Int, Int), (Int, Int))
posAfterLookahead = lookAhead (char '\t') *> pos <~> (item *> pos)

posAfterNotFollowedBy :: Parser ((Int, Int), (Int, Int))
posAfterNotFollowedBy = notFollowedBy (char '\t') *> pos <~> (item *> pos)
