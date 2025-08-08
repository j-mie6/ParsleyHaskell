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
import Parsley.Fold (skipMany, loop)
import Language.Haskell.TH.Syntax (Lift(..))
import Parsley.Register
import Parsley.Defunctionalized
import Parsley.Fold (manyl)
import Data.Maybe (catMaybes)
import Control.DeepSeq (NFData(..), deepseq)

#define QQ(x) (makeQ (x) [|| x ||])


bfLoop xs = xs `deepseq` Loop xs

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
         <|> try ( match "><+-.,[" item op walk  )
         <|> gets_ acc QQ(reverse)
      op :: Char -> Parser [BrainFuckOp]
      op '>' = modify_ acc (APP_H CONS (LIFTED RightPointer)) *> walk
      op '<' = modify_ acc (APP_H CONS (LIFTED LeftPointer)) *> walk
      op '+' = modify_ acc (APP_H CONS (LIFTED Increment)) *> walk
      op '-' = modify_ acc (APP_H CONS (LIFTED Decrement)) *> walk
      op '.' = modify_ acc (APP_H CONS (LIFTED Output)) *> walk
      op ',' = modify_ acc (APP_H CONS (LIFTED Input)) *> walk
      op '[' = modify acc (CONS <$> (QQ(Loop) <$> local acc (pure EMPTY) (walk <* char ']'))) *> walk
  in walk <* eof

many' :: Parser a -> Parser [a]
many' p = (makeQ (reverse) [|| reverse ||]) <$> manyl (FLIP_H CONS) EMPTY p

twoLoops :: Parser [BrainFuckOp]
twoLoops = whitespace *> bf <* eof
  where
    whitespace = skipMany (noneOf "<>+-[],.")
    lexeme p = p <* whitespace
    bf = many ( lexeme ((char '>' $> QQ(RightPointer))
                    <|> (char '<' $> QQ(LeftPointer))
                    <|> (char '+' $> QQ(Increment))
                    <|> (char '-' $> QQ(Decrement))
                    <|> (char '.' $> QQ(Output))
                    <|> (char ',' $> QQ(Input))
                    <|> between (lexeme (char '[')) (char ']') (QQ(bfLoop) <$> bf)))

twoLoops' :: Parser [BrainFuckOp]
twoLoops' = whitespace *> bf <* eof
  where
    whitespace = skipMany (noneOf "<>+-[],.")
    lexeme p = p <* whitespace
    bf = many (lexeme (match "><+-.,[" (lookAhead item) op empty))
    op '>' = item $> QQ(RightPointer)
    op '<' = item $> QQ(LeftPointer)
    op '+' = item $> QQ(Increment)
    op '-' = item $> QQ(Decrement)
    op '.' = item $> QQ(Output)
    op ',' = item $> QQ(Input)
    op '[' = lexeme item *> (QQ(bfLoop) <$> bf) <* char ']'

oneLoopMaybe :: Parser [BrainFuckOp]
oneLoopMaybe = bf <* eof
  where
    bf = QQ(catMaybes) <$> many (match "><+-.,[" (lookAhead item) op (noneOf "]" $> QQ(Nothing)))
    op '>' = item $> QQ(Just RightPointer)
    op '<' = item $> QQ(Just LeftPointer)
    op '+' = item $> QQ(Just Increment)
    op '-' = item $> QQ(Just Decrement)
    op '.' = item $> QQ(Just Output)
    op ',' = item $> QQ(Just Input)
    op '[' = item *> (QQ(Just) <$> (QQ(bfLoop) <$> bf)) <* char ']'

oneRecursive :: Parser [BrainFuckOp]
oneRecursive = bf <* eof
  where
    bf = match "><+-.,[" (lookAhead item) op (noneOf "]" *> bf) <|> pure EMPTY
    op '>' = item *> (QQ((RightPointer :)) <$> bf)
    op '<' = item *> (QQ((LeftPointer :)) <$> bf)
    op '+' = item *> (QQ((Increment :)) <$> bf)
    op '-' = item *> (QQ((Decrement :)) <$> bf)
    op '.' = item *> (QQ((Output :)) <$> bf)
    op ',' = item *> (QQ((Input :)) <$> bf)
    op '[' = item *> (CONS <$> (QQ(bfLoop) <$> bf)) <* char ']' <*> bf

oneLoopReg :: Parser [BrainFuckOp]
oneLoopReg = bf <* eof
  where
    bf = newRegister_ ID $ \acc ->
          loop (match "><+-.,[" (lookAhead item) (op acc) (void (noneOf "]")))
               (get acc)
          <*> pure EMPTY
    op :: Reg r ([BrainFuckOp] -> [BrainFuckOp]) -> Char -> Parser ()
    op acc '>' = snoc acc (item $> QQ(RightPointer))
    op acc '<' = snoc acc (item $> QQ(LeftPointer))
    op acc '+' = snoc acc (item $> QQ(Increment))
    op acc '-' = snoc acc (item $> QQ(Decrement))
    op acc '.' = snoc acc (item $> QQ(Output))
    op acc ',' = snoc acc (item $> QQ(Input))
    op acc '[' = snoc acc (item *> (QQ(bfLoop) <$> bf) <* char ']')

    snoc acc p = modify acc (combine <$> p)
    combine = COMPOSE_H (FLIP_H COMPOSE) CONS

oneLoopReg' :: Parser [BrainFuckOp]
oneLoopReg' = bf <* eof
  where
    bf = newRegister_ EMPTY $ \acc ->
          loop (match "><+-.,[" (lookAhead item) (op acc) (void (noneOf "]")))
               (gets_ acc QQ(reverse))
    op :: Reg r [BrainFuckOp] -> Char -> Parser ()
    op acc '>' = cons acc (item $> QQ(RightPointer))
    op acc '<' = cons acc (item $> QQ(LeftPointer))
    op acc '+' = cons acc (item $> QQ(Increment))
    op acc '-' = cons acc (item $> QQ(Decrement))
    op acc '.' = cons acc (item $> QQ(Output))
    op acc ',' = cons acc (item $> QQ(Input))
    op acc '[' = cons acc (item *> (QQ(bfLoop) <$> bf) <* char ']')

    cons acc p = modify acc (CONS <$> p)