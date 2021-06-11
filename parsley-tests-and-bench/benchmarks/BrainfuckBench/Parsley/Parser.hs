{-# OPTIONS_GHC -fplugin=Parsley.OverloadedQuotesPlugin #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
module BrainfuckBench.Parsley.Parser where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import BrainfuckBench.Shared
import Parsley
import Parsley.Combinator (noneOf, eof)
import Parsley.Fold (skipMany)
--import Parsley.Garnish
import Language.Haskell.TH.Syntax (Lift(..))

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
    op '>' = item $> [|RightPointer|]
    op '<' = item $> [|LeftPointer|]
    op '+' = item $> [|Increment|]
    op '-' = item $> [|Decrement|]
    op '.' = item $> [|Output|]
    op ',' = item $> [|Input|]
    op '[' = between (lexeme item) (try (char ']')) ([|Loop|] <$> bf)