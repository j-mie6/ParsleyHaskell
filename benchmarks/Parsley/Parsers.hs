{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE StandaloneDeriving #-}
module Parsley.Parsers where

import Prelude hiding (fmap, pure, (<*), (*>), (<*>), (<$>), (<$), pred)
import Parsley
import Parsley.Combinator (token, oneOf, noneOf, eof)
import Parsley.Fold (skipMany, skipSome, sepBy, sepBy1, pfoldl1, chainl1)
import Parsley.Precedence (precedence, monolith, prefix, postfix, infixR, infixL)
import CommonFunctions
import Data.Char (isSpace, isUpper, digitToInt, isDigit)
import Data.Maybe (catMaybes)
import Text.Read (readMaybe)
import Control.Monad (liftM)

digit :: Parser Int
digit = code digitToInt <$> satisfy (code isDigit)

plus :: Parser (Int -> Int -> Int)
plus = char '+' $> code (+)

selectTest :: Parser (Either Int String)
selectTest = pure (code (Left 10))

showi :: Int -> String
showi = show

deriving instance Lift Pred

pred :: Parser Pred
pred = precedence (monolith [ prefix [token "!" $> code Not]
                            , infixR [token "&&" $> code And]])
                  ( token "t" $> code T
                <|> token "f" $> code F)

-- Regex Benchmark
regex :: Parser Bool
regex = skipMany (aStarb *> aStarb) *> char 'a' $> code True <|> pure (code False)
  where
    aStarb = aStar *> char 'b'
    aStar = skipMany (char 'a')