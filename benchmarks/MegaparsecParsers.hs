{-# LANGUAGE TypeFamilies
           , ScopedTypeVariables #-}

module MegaparsecParsers where
import CommonFunctions
import Text.Megaparsec
import Text.Megaparsec.Char

type Parser s a = Parsec () s a

($>) :: (Stream s, Token s ~ Char) => Parser s a -> b -> Parser s b
($>) = flip (<$)

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