{-# LANGUAGE FlexibleContexts #-}
module ParsecParsers where
import CommonFunctions
import Text.Parsec
import Control.Monad.Identity (Identity)

type Parser s a = Parsec s () a

($>) :: Stream s Identity Char => Parser s a -> b -> Parser s b
($>) = flip (<$)

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