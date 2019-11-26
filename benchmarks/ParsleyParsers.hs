{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
module ParsleyParsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import Parsley
import CommonFunctions

digit :: Parser Int
digit = code toDigit <$> satisfy (code isDigit)

greaterThan5 :: Int -> Bool
greaterThan5 = (> 5)

plus :: Parser (Int -> Int -> Int)
plus = char '+' $> code (+)

selectTest :: Parser (Either Int String)
selectTest = pure (code (Left 10))

showi :: Int -> String
showi = show

deriving instance Lift Pred

pred :: Parser Pred
pred = precedence [ Prefix [token "!" $> code Not]
                  , InfixR [token "&&" $> code And]] 
                  ( token "t" $> code T
                <|> token "f" $> code F)

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
    {-bf = many ( lexeme ((token ">" $> code RightPointer)
                    <|> (token "<" $> code LeftPointer)
                    <|> (token "+" $> code Increment)
                    <|> (token "-" $> code Decrement)
                    <|> (token "." $> code Output)
                    <|> (token "," $> code Input)
                    <|> (between (lexeme (token "[")) (token "]") (code Loop <$> bf))))-}
    bf = many (lexeme (match "><+-.,[" (lookAhead item) op empty))
    op '>' = item $> code RightPointer
    op '<' = item $> code LeftPointer
    op '+' = item $> code Increment
    op '-' = item $> code Decrement
    op '.' = item $> code Output
    op ',' = item $> code Input
    op '[' = between (lexeme item) (try (char ']')) (code Loop <$> bf)

-- Regex Benchmark
regex :: Parser Bool
regex = skipMany (aStarb *> aStarb) *> char 'a' $> code True <|> pure (code False)
  where
    aStarb = aStar *> char 'b'
    aStar = skipMany (char 'a')