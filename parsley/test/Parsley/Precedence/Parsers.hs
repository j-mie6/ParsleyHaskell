{-# LANGUAGE TemplateHaskellQuotes, MultiParamTypeClasses #-}
module Parsley.Precedence.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*), (<$>), ($>), pred)
import Parsley
import Parsley.Precedence
import Parsley.Fold (somel)
import Parsley.Char (oneOf)
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

data Pred = Or Term Pred | OfTerm Term deriving (Eq, Show)
data Term = And Not Term | OfNot Not deriving (Eq, Show)
data Not = Not Not | OfAtom Atom deriving (Eq, Show)
data Atom = T | F | Parens Pred deriving (Eq, Show)

instance Subtype Atom Not where
  upcast = OfAtom
  downcast (OfAtom x) = Just x
  downcast _          = Nothing

instance Subtype Not Term where
  upcast = OfNot
  downcast (OfNot x) = Just x
  downcast _         = Nothing

pred = precedence $
  gops InfixR [char '|' $> [|Or|]] [|OfTerm|] +<
  sops InfixR [char '&' $> [|And|]]           +<
  sops Prefix [char '!' $> [|Not|]]           +<
  Atom (char 'T' $> [|T|] <|> char 'F' $> [|F|] <|> char '(' *> ([|Parens|] <$> pred) <* char ')')