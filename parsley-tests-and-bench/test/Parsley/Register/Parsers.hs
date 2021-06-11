{-# LANGUAGE TemplateHaskellQuotes #-}
module Parsley.Register.Parsers where

import Prelude hiding ((*>), (<*))
import Data.Char (isDigit)
import Parsley (Parser, item, char, (*>), (<*), (<|>))
import Parsley.Register
--import Parsley.Garnish

getPure :: Parser Int
getPure = newRegister_ [|8|] get

getPersists :: Parser Int
getPersists = newRegister_ [|8|] (\r -> item *> get r)

getPersistsBranch :: Parser Int
getPersistsBranch = newRegister_ [|8|] (\r -> (char 'a' *> get r) <|> get r)

getNoInput :: Parser Int
getNoInput = newRegister_ [|8|] (\r -> get r <* item)

putPure :: Parser Int
putPure = newRegister_ [|8|] (\r -> put_ r [|7|] *> get r)

putSeq :: Parser Char
putSeq = newRegister_ [|'a'|] (\r -> put r item *> get r)

putPut :: Parser Int
putPut = newRegister_ [|7|] (\r -> put_ r [|5|] *> put_ r [|6|] *> get r)

putCarries :: Parser Bool
putCarries = newRegister_ [|False|] (\r -> (put_ r [|True|] *> item *> put_ r [|False|] *> get r) <|> get r)