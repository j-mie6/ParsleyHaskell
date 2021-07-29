{-# LANGUAGE TemplateHaskell #-}
module Parsley.Regressions.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*))
import Data.Char (isDigit)
import Parsley
import Parsley.Combinator (token)
--import Parsley.Garnish

issue26_ex1 :: Parser ()
issue26_ex1 = (token "123" <|> token "45") *> token "abc" *> unit