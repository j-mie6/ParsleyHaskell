{-# LANGUAGE ScopedTypeVariables, TypeFamilies #-}
module BrainfuckBench.Megaparsec.Parser where

import Shared.Megaparsec.Extended
import BrainfuckBench.Shared

brainfuck :: forall s. (Stream s, Token s ~ Char) => Parser s [BrainFuckOp]
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
    lexeme :: Parser s a -> Parser s a
    lexeme p = p <* whitespace