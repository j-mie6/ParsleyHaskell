module Parsley.Primitive.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Data.Char (isDigit)
import Parsley

pure7 :: Parser Int
pure7 = pure (code 7)

digit :: Parser Char
digit = satisfy (code isDigit)

twoDigits :: Parser Char
twoDigits = digit *> digit

abOrC :: Parser String
abOrC = string "ab" <|> string "c"

abOrCThenD :: Parser String
abOrCThenD = abOrC <* char 'd'

recursive :: Parser [Char]
recursive =
  let r = item <:> r <|> pure EMPTY
  in r