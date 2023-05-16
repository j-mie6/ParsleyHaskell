{-# LANGUAGE TemplateHaskell #-}
module Regression.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Data.Char (isDigit)
import Parsley
import Parsley.Char (token)
import Parsley.Register (newRegister_, put_, get)
import Parsley.Defunctionalized (Defunc(LIFTED))

issue26_ex1 :: Parser ()
issue26_ex1 = (token "123" <|> token "") *> void (token "abc")

issue26_ex2 :: Parser ()
issue26_ex2 = (token "123" <|> token "45") *> void (token "abc")

issue41_ex1 :: Parser Bool
issue41_ex1 = newRegister_ (LIFTED False) $ \reg -> optional (try (char 'a' *> put_ reg (LIFTED True) *> char 'b')) *> get reg

issue41_ex2 :: Parser Bool
issue41_ex2 = newRegister_ (LIFTED False) $ \reg -> try ((string "abc" *> get reg) <|> (put_ reg (LIFTED True) *> get reg)) <|> get reg

issue41_ex3 :: Parser Bool
issue41_ex3 = newRegister_ (LIFTED False) $ \reg -> try ((string "abc" *> get reg) <|> (put_ reg (LIFTED True) *> item *> get reg)) <|> get reg
