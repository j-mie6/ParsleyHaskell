{-# OPTIONS_GHC -fplugin=LiftPlugin #-}
module Parsley.Alternative (
    module Parsley.Alternative,
    module Primitives
  ) where

import Prelude hiding       (pure, (<$>))
import Parsley.Applicative  (pure, (<$>), ($>), (<:>))
import Parsley.Common.Utils (code, makeQ)
import Parsley.Core         (Parser, Defunc(UNIT, EMPTY), ParserOps)

import Parsley.Core.Primitives as Primitives ((<|>), empty)

infixl 3 <+>
(<+>) :: Parser t a -> Parser t b -> Parser t (Either a b)
p <+> q = code Left <$> p <|> code Right <$> q

optionally :: ParserOps rep => Parser t a -> rep b -> Parser t b
optionally p x = p $> x <|> pure x

optional :: Parser t a -> Parser t ()
optional = flip optionally UNIT

option :: ParserOps rep => rep a -> Parser t a -> Parser t a
option x p = p <|> pure x

choice :: [Parser t a] -> Parser t a
choice = foldr (<|>) empty

maybeP :: Parser t a -> Parser t (Maybe a)
maybeP p = option (makeQ Nothing [||Nothing||]) (code Just <$> p)

manyTill :: Parser t a -> Parser t b -> Parser t [a]
manyTill p end = let go = end $> EMPTY <|> p <:> go in go