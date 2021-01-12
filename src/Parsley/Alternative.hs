{-# OPTIONS_GHC -fplugin=LiftPlugin #-}
module Parsley.Alternative (
    module Parsley.Alternative,
    module Primitives
  ) where

import Prelude hiding                (pure, (<$>))
import Parsley.Applicative           (pure, (<$>), ($>), (<:>))
import Parsley.Internal.Common.Utils (code, makeQ)
import Parsley.Internal.Core         (Parser, Defunc(UNIT, EMPTY), ParserOps)

import Parsley.Internal.Core.Primitives as Primitives ((<|>), empty)

infixl 3 <+>
(<+>) :: Parser a -> Parser b -> Parser (Either a b)
p <+> q = code Left <$> p <|> code Right <$> q

option :: ParserOps rep => rep a -> Parser a -> Parser a
option x p = p <|> pure x

optionally :: ParserOps rep => Parser a -> rep b -> Parser b
optionally p x = option x (p $> x)

optional :: Parser a -> Parser ()
optional = flip optionally UNIT

choice :: [Parser a] -> Parser a
choice = foldr (<|>) empty

maybeP :: Parser a -> Parser (Maybe a)
maybeP p = option (makeQ Nothing [||Nothing||]) (code Just <$> p)

manyTill :: Parser a -> Parser b -> Parser [a]
manyTill p end = let go = end $> EMPTY <|> p <:> go in go