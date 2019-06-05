module YodaParsers where

import Text.Yoda
import CommonFunctions

manyTestYodaBad :: Parser Int
manyTestYodaBad = chainl1 (toDigit <$> satisfy (isDigit)) ((+) <$ char '+')

manyTestYodaOk :: Parser [Char]
manyTestYodaOk = cull (many (char 'a'))