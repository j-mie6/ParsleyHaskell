{-# LANGUAGE TemplateHaskellQuotes, MultiParamTypeClasses #-}
module Parsley.Precedence.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*), (<$>), ($>), pred)
import Parsley
import Parsley.Precedence
import Parsley.Fold (somel)
import Parsley.Char (oneOf)
import Data.Char (digitToInt)
import Parsley.Defunctionalized

data Expr = Add Expr Expr | Mul Expr Expr | Negate Expr | Num Int deriving (Eq, Show)

number :: Parser Int
number = somel (makeQ (\x d -> x * 10 + digitToInt d) [|| \x d -> x * 10 + digitToInt d ||]) (LIFTED 0) (oneOf ['0'..'9'])

expr :: Parser Expr
expr = precHomo (makeQ Num [||Num||] <$> number)
                [ ops Prefix [string "negate" $> makeQ Negate [||Negate||]]
                , ops InfixL [char '*' $> makeQ Mul [||Mul||]]
                , ops InfixR [char '+' $> makeQ Add [||Add||]]
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
  gops InfixR [char '|' $> makeQ Or [||Or||]] (makeQ OfTerm [||OfTerm||]) +<
  sops InfixR [char '&' $> makeQ And [||And||]]          +<
  sops Prefix [char '!' $> makeQ Not [||Not||]]          +<
  Atom (char 'T' $> makeQ T [||T||] <|> char 'F' $> makeQ F [||F||] <|> char '(' *> (makeQ Parens [||Parens||] <$> pred) <* char ')')
