{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
module Parsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred, repeat)
import Parsley
import Control.Monad (liftM)
import Data.Char (isAlpha, isAlphaNum, isSpace, isUpper, isDigit, digitToInt, chr, ord)
import Data.Set (fromList, member)
import Data.Maybe (catMaybes)
import Text.Read (readMaybe)

import qualified Prelude

data Expr = Var String | Num Int | Add Expr Expr deriving Show
data Asgn = Asgn String Expr deriving Show

data BrainFuckOp = RightPointer | LeftPointer | Increment | Decrement | Output | Input | Loop [BrainFuckOp] deriving (Show, Eq)
deriving instance Lift BrainFuckOp

cinput :: Parser String
cinput = m --try (string "aaa") <|> string "db" --(string "aab" <|> string "aac") --(char 'a' <|> char 'b') *> string "ab"
  where
    --m = match "ab" (lookAhead item) op empty
    --op 'a' = item $> code "aaaaa"
    --op 'b' = item $> code "bbbbb"
    m = bf <* item
    bf = match ">" item op empty
    op '>' = string ">"

regTest :: Parser Int
regTest = newRegister_ (code 7) (\r -> modify_ r (makeQ (succ @Int) [||succ @Int||]) *> (let g = get r in g *> g))

defuncTest :: Parser (Maybe Int)
defuncTest = code Just <$> (code (+) <$> (item $> code 1) <*> (item $> code 8))

manyTest :: Parser [Char]
manyTest = many (string "ab" $> (code 'c'))

nfb :: Parser ()
nfb = notFollowedBy (char 'a') <|> void (string "ab")

skipManyInspect :: Parser ()
skipManyInspect = skipMany (char 'a')

brainfuck :: Parser [BrainFuckOp]
brainfuck = whitespace *> bf
  where
    whitespace = skipMany (noneOf "<>+-[],.")
    lexeme p = p <* whitespace
    bf = many (lexeme (match "><+-.,[" (lookAhead item) op empty))
    op '>' = item $> code RightPointer
    op '<' = item $> code LeftPointer
    op '+' = item $> code Increment
    op '-' = item $> code Decrement
    op '.' = item $> code Output
    op ',' = item $> code Input
    op '[' = between (lexeme item) (char ']') (code Loop <$> bf)

data Tape = Tape [Int] Int [Int]

emptyTape :: Tape
emptyTape = Tape (Prelude.repeat 0) 0 (Prelude.repeat 0)

right :: Tape -> Tape
right (Tape ls x (r:rs)) = Tape (x:ls) r rs
left :: Tape -> Tape
left (Tape (l:ls) x rs) = Tape ls l (x:rs)
readTape :: Tape -> Int
readTape (Tape _ x _) = x
writeTape :: Int -> Tape -> Tape
writeTape x (Tape ls _ rs) = Tape ls x rs
isLoop :: BrainFuckOp -> Bool
isLoop (Loop p) = True
isLoop p        = False
getLoop :: BrainFuckOp -> [BrainFuckOp]
getLoop (Loop p) = p
inc :: Int -> Int
inc = (+ 1)
dec :: Int -> Int
dec = subtract 1
toInt :: Char -> Int
toInt = toEnum . ord
toChar :: Int -> Char
toChar = chr . fromEnum

evalBf :: Parser [BrainFuckOp] -> Parser [Char]
evalBf loader =
  -- first step is to place the program into a register and read the delimiter, then set up the state
  newRegister loader $ \instrs ->
    delim *> newRegister_ (makeQ emptyTape [||emptyTape||]) (\tape ->
      newRegister_ EMPTY $ \out ->
           eval instrs tape out
        *> gets_ out (code reverse))
  where
    delim :: Parser Char
    delim = char '$'

    eval :: Reg r1 [BrainFuckOp] -> Reg r2 Tape -> Reg r3 [Char] -> Parser ()
    eval instrs tape out =
      let go = predicate (code null) (get instrs) unit $
            bind (gets_ instrs (code head)) $ \op ->
              let evalLoop =
                    predicate (EQ_H (code 0)) read
                      unit
                      (local instrs (code getLoop <$> op) (go *> evalLoop))
              in modify_ instrs (code tail)
              *> predicate (code isLoop) op
                   evalLoop
                   (match [RightPointer, LeftPointer, Increment, Decrement, Output, Input] op evalOp' empty)
              *> go
      in go
      where
        evalOp' :: BrainFuckOp -> Parser ()
        evalOp' RightPointer = move (code right)
        evalOp' LeftPointer  = move (code left)
        evalOp' Increment    = update (code inc)
        evalOp' Decrement    = update (code dec)
        evalOp' Output       = print (code toChar <$> read)
        evalOp' Input        = write (code toInt <$> item)

        -- Operations
        move :: Defunc (Tape -> Tape) -> Parser ()
        move = modify_ tape
        print :: Parser Char -> Parser ()
        print x = modify out (CONS <$> x)
        read :: Parser Int
        read = gets_ tape (code readTape)
        write :: Parser Int -> Parser ()
        write px = modify tape (code writeTape <$> px)
        update :: Defunc (Int -> Int) -> Parser ()
        update f = write (f <$> read)
