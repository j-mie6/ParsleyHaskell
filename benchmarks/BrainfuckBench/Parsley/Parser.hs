{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
module BrainfuckBench.Parsley.Parser where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import BrainfuckBench.Shared
import Parsley
import Parsley.Combinator (noneOf, eof)
import Parsley.Fold (skipMany)

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