{-# LANGUAGE FlexibleContexts #-}
module BrainfuckBench.Parsec.Parser where

import Shared.Parsec.Extended
import BrainfuckBench.Shared

brainfuck :: Stream s Identity Char => Parser s [BrainFuckOp]
brainfuck = whitespace *> bf <* eof
  where
    bf = many ( lexeme (char '>' $> RightPointer)
      <|> lexeme (char '<' $> LeftPointer)
      <|> lexeme (char '+' $> Increment)
      <|> lexeme (char '-' $> Decrement)
      <|> lexeme (char '.' $> Output)
      <|> lexeme (char ',' $> Input)
      <|> between (lexeme (char '[')) (lexeme (char ']')) (Loop <$> bf))
    whitespace = skipMany (noneOf "<>+-.,[]")
    lexeme p = p <* whitespace