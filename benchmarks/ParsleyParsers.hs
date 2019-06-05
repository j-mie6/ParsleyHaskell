{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
module ParsleyParsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import Parsley
import CommonFunctions

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
pred = precedence [ Prefix [token "!" $> lift' Not]
                  , InfixR [token "&&" $> lift' And]] 
                  ( token "t" $> lift' T
                <|> token "f" $> lift' F )