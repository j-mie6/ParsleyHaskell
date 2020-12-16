module BrainfuckBench.Attoparsec.Parser where

import Shared.Attoparsec.Extended
import BrainfuckBench.Shared

brainfuck :: Parser [BrainFuckOp]
brainfuck = whitespace *> bf <* endOfInput
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