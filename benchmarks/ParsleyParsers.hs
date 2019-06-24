{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
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

deriving instance Lift Pred

pred :: Parser Pred
pred = precedence [ Prefix [token "!" $> lift' Not]
                  , InfixR [token "&&" $> lift' And]] 
                  ( token "t" $> lift' T
                <|> token "f" $> lift' F)

phiTest :: Parser Char
--phiTest = try (char 'b') <|> char 'a' *> phiTest
phiTest = skipMany (char 'a' <* skipMany (char 'c')) *> char 'b'

-- Brainfuck benchmark
deriving instance Lift BrainFuckOp

brainfuck :: Parser [BrainFuckOp]
brainfuck = whitespace *> bf
  where
    whitespace = skipMany (noneOf "<>+-[]")
    lexeme p = p <* whitespace
    bf = many ( (lexeme (char '>' $> lift' RightPointer))
      <|> (lexeme (char '<' $> lift' LeftPointer))
      <|> (lexeme (char '+' $> lift' Increment))
      <|> (lexeme (char '-' $> lift' Decrement))
      <|> (lexeme (char '.' $> lift' Output))
      <|> (lexeme (char ',' $> lift' Input))
      <|> (between (lexeme (char '[')) (lexeme (char ']')) (lift' Loop <$> brainfuck)))
