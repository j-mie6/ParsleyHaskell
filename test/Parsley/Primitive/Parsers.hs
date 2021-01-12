module Parsley.Primitive.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Data.Char (isDigit)
import Parsley (runParser, Parser, pure, empty, satisfy, (<*>), (*>), (<*), (<|>), code)

pure7 :: Parser Int
pure7 = pure (code 7)

digit :: Parser Char
digit = satisfy (code isDigit)

twoDigits :: Parser Char
twoDigits = digit *> digit