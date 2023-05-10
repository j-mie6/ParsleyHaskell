{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas -Wno-incomplete-patterns #-}
{-# HLINT ignore "Redundant bracket" #-}
module BrainfuckBench.Parsley.Parser where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import BrainfuckBench.Shared
import Parsley
import Parsley.Combinator (eof, more)
import Parsley.Char(noneOf, token)
import Parsley.Fold (skipMany)
import Language.Haskell.TH.Syntax (Lift(..))

import Parsley.Register
import Parsley.Defunctionalized

#define QQ(x) (makeQ (x) [|| x ||])

deriving instance Lift BrainFuckOp

brainfuck :: Parser [BrainFuckOp]
brainfuck = whitespace *> bf <* eof
  where
    whitespace = skipMany (noneOf "<>+-[],.")
    lexeme p = p <* whitespace
    bf = many ( lexeme ((token ">" $> QQ(RightPointer))
                            <|> (token "<" $> QQ(LeftPointer))
                            <|> (token "+" $> QQ(Increment))
                            <|> (token "-" $> QQ(Decrement))
                            <|> (token "." $> QQ(Output))
                            <|> (token "," $> QQ(Input))
                            <|> between (lexeme (token "[")) (token "]") (QQ(Loop) <$> bf)))
    {-bf = many (lexeme (match "><+-.,[" (lookAhead item) op empty))
    op '>' = item $> QQ(RightPointer)
    op '<' = item $> QQ(LeftPointer)
    op '+' = item $> QQ(Increment)
    op '-' = item $> QQ(Decrement)
    op '.' = item $> QQ(Output)
    op ',' = item $> QQ(Input)
    op '[' = between (lexeme item) (try (char ']')) (QQ(Loop) <$> bf)-}

-- This is as closed to the handrolled version as it's possible to get: it's /very/ fast
-- If register elimination can be performed, this would be equivalent to the handrolled I think
brainfuck' :: Parser [BrainFuckOp]
brainfuck' = newRegister_ EMPTY $ \acc ->
  let walk :: Parser [BrainFuckOp]
      -- This `eof` is interesting
      -- The "obvious" way of thinking about this is to just move that `gets_` clause last
      -- This works because `item` only fails if `eof` wouldn't have done.
      -- However, at the /moment/, Parsley knows that `eof`'s failure doesn't consume input, and
      -- optimises the handlers appropriately, but the scope of the failure of the match covers
      -- the cases too, and so failing there generates a length check etc. Interestingly, the fix
      -- here is to add a `try` (!!!), which improves performance considerably (but GHC then decides
      -- not to inline something to make them otherwise identical). That's wild.
      walk = eof *> gets_ acc QQ(reverse)
         <|> lookAhead (char ']') *> gets_ acc QQ(reverse)
         <|> {- try ( -}match "><+-.,[" item op walk -- )
         -- <|> gets_ acc QQ(reverse)
      op :: Char -> Parser [BrainFuckOp]
      op '>' = modify_ acc (APP_H CONS (LIFTED RightPointer)) *> walk
      op '<' = modify_ acc (APP_H CONS (LIFTED LeftPointer)) *> walk
      op '+' = modify_ acc (APP_H CONS (LIFTED Increment)) *> walk
      op '-' = modify_ acc (APP_H CONS (LIFTED Decrement)) *> walk
      op '.' = modify_ acc (APP_H CONS (LIFTED Output)) *> walk
      op ',' = modify_ acc (APP_H CONS (LIFTED Input)) *> walk
      op '[' = modify acc (CONS <$> (QQ(Loop) <$> local acc (pure EMPTY) (walk <* char ']'))) *> walk
  in walk <* eof
