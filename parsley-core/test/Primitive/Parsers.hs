{-# LANGUAGE TemplateHaskell #-}
module Primitive.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Data.Char (isDigit)
import Parsley.Internal (Parser, Defunc(EMPTY, LIFTED, EQ_H, CONS, LAM_S), makeQ, pure, satisfy, (*>), (<*), (<|>), (<*>), satisfy, lookAhead)

pure7 :: Parser Int
pure7 = pure (LIFTED 7)

digit :: Parser Char
digit = satisfy (makeQ isDigit [||isDigit||])

twoDigits :: Parser Char
twoDigits = digit *> digit

abOrC :: Parser String
abOrC = (satisfy (EQ_H (LIFTED 'a')) *> satisfy (EQ_H (LIFTED 'b')) *> pure (LIFTED "ab")) <|> (satisfy (EQ_H (LIFTED 'c')) *> pure (LIFTED "c"))

abOrCThenD :: Parser String
abOrCThenD = abOrC <* satisfy (EQ_H (LIFTED 'd'))

recursive :: Parser [Char]
recursive =
  let r = pure CONS <*> satisfy (LAM_S (const (LIFTED True))) <*> r <|> pure EMPTY
  in r

lookAheadDigit :: Parser Char
lookAheadDigit = lookAhead digit *> digit