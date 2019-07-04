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
phiTest = skipMany (char 'a') *> char 'b'

-- Brainfuck benchmark
deriving instance Lift BrainFuckOp

brainfuck :: Parser [BrainFuckOp]
brainfuck = whitespace *> bf <* eof
  where
    whitespace = skipMany (noneOf "<>+-[],.")
    lexeme p = p <* whitespace
    bf = many ( lexeme ((token ">" $> lift' RightPointer)
                    <|> (token "<" $> lift' LeftPointer)
                    <|> (token "+" $> lift' Increment)
                    <|> (token "-" $> lift' Decrement)
                    <|> (token "." $> lift' Output)
                    <|> (token "," $> lift' Input)
                    <|> (between (lexeme (token "[")) (token "]") (lift' Loop <$> bf))))

-- Regex Benchmark
regex :: Parser Bool
regex = skipMany (aStarb *> aStarb) *> char 'a' $> lift' True <|> pure (lift' False)
  where
    aStarb = aStar *> char 'b'
    aStar = skipMany (char 'a')