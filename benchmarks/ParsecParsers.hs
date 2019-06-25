module ParsecParsers where
import CommonFunctions
import Text.Parsec

type Parser a = Parsec String () a

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