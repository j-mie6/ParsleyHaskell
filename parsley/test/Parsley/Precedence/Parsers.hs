{-# LANGUAGE TemplateHaskellQuotes #-}
module Parsley.Precedence.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*), (<$>), ($>))
import Parsley
import Parsley.Precedence
import Parsley.Fold (somel)
import Parsley.Combinator (oneOf)
import Data.Char (digitToInt)

data Expr = Add Expr Expr | Mul Expr Expr | Negate Expr | Num Int deriving (Eq, Show)

number :: Parser Int
number = somel [| \x d -> x * 10 + digitToInt d |] [|0|] (oneOf ['0'..'9'])

expr :: Parser Expr
expr = precHomo ([|Num|] <$> number)
                [ ops Prefix [string "negate" $> [|Negate|]]
                , ops InfixL [char '*' $> [|Mul|]]
                , ops InfixR [char '+' $> [|Add|]]
                ]