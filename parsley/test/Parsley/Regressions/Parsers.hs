{-# LANGUAGE TemplateHaskell #-}
module Parsley.Regressions.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Data.Char (isDigit)
import Parsley
import Parsley.Combinator (token)
--import Parsley.Garnish

issue26_ex1 :: Parser ()
issue26_ex1 = (token "123" <|> token "") *> void (token "abc")

issue26_ex2 :: Parser ()
issue26_ex2 = (token "123" <|> token "45") *> void (token "abc")