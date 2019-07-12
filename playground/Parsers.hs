{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
module Parsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import Parsley

data BrainFuckOp = RightPointer | LeftPointer | Increment | Decrement | Output | Input | Loop [BrainFuckOp] deriving Show

deriving instance Lift BrainFuckOp

brainfuck :: Parser [BrainFuckOp]
brainfuck = whitespace *> bf <* eof
  where
    whitespace = skipMany (noneOf "<>+-[],.")
    lexeme p = p <* whitespace
    {-bf = many ( lexeme ((token ">" $> lift' RightPointer)
                    <|> (token "<" $> lift' LeftPointer)
                    <|> (token "+" $> lift' Increment)
                    <|> (token "-" $> lift' Decrement)
                    <|> (token "." $> lift' Output)
                    <|> (token "," $> lift' Input)
                    <|> (between (lexeme (token "[")) (token "]") (lift' Loop <$> bf))))-}
    -- [a] -> Parser a -> (a -> Parser b) -> Parser b -> Parser b
    bf = many (lexeme (match "><+-.,[" (lookAhead item) op empty))
    op '>' = item $> lift' RightPointer
    op '<' = item $> lift' LeftPointer
    op '+' = item $> lift' Increment
    op '-' = item $> lift' Decrement
    op '.' = item $> lift' Output
    op ',' = item $> lift' Input
    op '[' = between (lexeme item) (try (char ']')) (lift' Loop <$> bf)