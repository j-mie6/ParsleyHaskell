{-# LANGUAGE TemplateHaskell #-}
module Parsley.Primitive.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Data.Char (isDigit)
import Parsley
import Parsley.Defunctionalized (Defunc(EMPTY))
--import Parsley.Garnish

pure7 :: Parser Int
pure7 = pure [|7|]

digit :: Parser Char
digit = satisfy [|isDigit|]

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