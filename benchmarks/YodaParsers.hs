module YodaParsers where

import Text.Yoda
import CommonFunctions
import Data.Char (isDigit, digitToInt)

manyTestBad :: Parser Int
manyTestBad = chainl1 (digitToInt <$> satisfy (isDigit)) ((+) <$ char '+')

manyTestOk :: Parser [Char]
manyTestOk = cull (many (char 'a'))

($>) :: Parser a -> b -> Parser b
($>) = flip (<$)

brainfuck :: Parser [BrainFuckOp]
brainfuck = whitespace *>
  many ( lexeme (char '>' $> RightPointer)
     <|> lexeme (char '<' $> LeftPointer)
     <|> lexeme (char '+' $> Increment)
     <|> lexeme (char '-' $> Decrement)
     <|> lexeme (char '.' $> Output)
     <|> lexeme (char ',' $> Input)
     <|> between (lexeme (char '(')) (lexeme (char ')')) (Loop <$> brainfuck)) <* eof
  where
    whitespace = optional (noneOf "<>+-.,[]")
    lexeme p = p <* whitespace