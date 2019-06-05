{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
module ParsleyParsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import Parsley

isDigit :: Char -> Bool
isDigit c
  |    c == '0' || c == '1' || c == '2' || c == '3'
    || c == '4' || c == '5' || c == '6' || c == '7'
    || c == '8' || c == '9' = True
  | otherwise = False

toDigit :: Char -> Int
toDigit c = fromEnum c - fromEnum '0'

digit :: Parser Int
digit = lift' toDigit <$> satisfy (lift' isDigit)

greaterThan5 :: Int -> Bool
greaterThan5 = (> 5)

plus :: Parser (Int -> Int -> Int)
plus = char '+' $> lift' (+)

selectTest :: Parser (Either Int String)
selectTest = pure (lift' (Left 10))

showi :: Int -> String
showi = show

data Pred = And Pred Pred | Not Pred | T | F deriving (Lift, Show)
pred :: Parser Pred
pred = chainr1 term (lift' And <$ token "&&")
  where
    term :: Parser Pred
    term = chainPre (lift' Not <$ token "!") atom
    atom :: Parser Pred
    atom = (lift' T <$ token "t")
       <|> (lift' F <$ token "f")