{-# LANGUAGE CPP, TemplateHaskellQuotes, MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
module Parsley.Precedence.Parsers where

import Prelude hiding (pure, (<*>), (*>), (<*), (<$>), ($>), pred)
import Parsley
import Parsley.Precedence
import Parsley.Fold (somel)
import Parsley.Char (oneOf)
import Data.Char (digitToInt)
import Parsley.Defunctionalized

#define QQ(x) (makeQ (x) [|| x ||])

data Expr = Add Expr Expr | Mul Expr Expr | Negate Expr | Num Int deriving (Eq, Show)

number :: Parser Int
number = somel QQ(\x d -> x * 10 + digitToInt d) (LIFTED 0) (oneOf ['0'..'9'])

expr :: Parser Expr
expr = precHomo (QQ(Num) <$> number)
                [ ops Prefix [string "negate" $> QQ(Negate)]
                , ops InfixL [char '*' $> QQ(Mul)]
                , ops InfixR [char '+' $> QQ(Add)]
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
  gops InfixR [char '|' $> QQ(Or)] QQ(OfTerm) +<
  sops InfixR [char '&' $> QQ(And)]           +<
  sops Prefix [char '!' $> QQ(Not)]           +<
  Atom (char 'T' $> QQ(T) <|> char 'F' $> QQ(F) <|> char '(' *> (QQ(Parens) <$> pred) <* char ')')
