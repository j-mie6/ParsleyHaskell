{-# LANGUAGE TemplateHaskellQuotes #-}
module Parsley.Register.Parsers where

import Prelude hiding ((*>), (<*))
import Data.Char (isDigit)
import Parsley (Parser, item, char, (*>), (<*), (<|>))
import Parsley.Register
import Parsley.Defunctionalized

getPure :: Parser Int
getPure = newRegister_ (LIFTED 8) get

getPersists :: Parser Int
getPersists = newRegister_ (LIFTED 8) (\r -> item *> get r)

getPersistsBranch :: Parser Int
getPersistsBranch = newRegister_ (LIFTED 8) (\r -> (char 'a' *> get r) <|> get r)

getNoInput :: Parser Int
getNoInput = newRegister_ (LIFTED 8) (\r -> get r <* item)

putPure :: Parser Int
putPure = newRegister_ (LIFTED 8) (\r -> put_ r (LIFTED 7) *> get r)

putSeq :: Parser Char
putSeq = newRegister_ (LIFTED 'a') (\r -> put r item *> get r)

putPut :: Parser Int
putPut = newRegister_ (LIFTED 7) (\r -> put_ r (LIFTED 5) *> put_ r (LIFTED 6) *> get r)

putCarries :: Parser Bool
putCarries = newRegister_ (LIFTED False) (\r -> (put_ r (LIFTED True) *> item *> put_ r (LIFTED False) *> get r) <|> get r)
