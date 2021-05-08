module Parsley.Register.Parsers where

import Prelude hiding ((*>), (<*))
import Data.Char (isDigit)
import Parsley (Parser, item, char, (*>), (<*), (<|>))
import Parsley.Register
import Parsley.Garnish

getPure :: Parser Int
getPure = newRegister_ (code 8) get

getPersists :: Parser Int
getPersists = newRegister_ (code 8) (\r -> item *> get r)

getPersistsBranch :: Parser Int
getPersistsBranch = newRegister_ (code 8) (\r -> (char 'a' *> get r) <|> get r)

getNoInput :: Parser Int
getNoInput = newRegister_ (code 8) (\r -> get r <* item)

putPure :: Parser Int
putPure = newRegister_ (code 8) (\r -> put_ r (code 7) *> get r)

putSeq :: Parser Char
putSeq = newRegister_ (code 'a') (\r -> put r item *> get r)

putPut :: Parser Int
putPut = newRegister_ (code 7) (\r -> put_ r (code 5) *> put_ r (code 6) *> get r)

putCarries :: Parser Bool
putCarries = newRegister_ (code False) (\r -> (put_ r (code True) *> item *> put_ r (code False) *> get r) <|> get r)