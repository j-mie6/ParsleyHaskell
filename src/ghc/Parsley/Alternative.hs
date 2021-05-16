{-|
Module      : Parsley.Alterative
Description : The @Alternative@ combinators
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This modules contains the @Alternative@ combinators that would normally be found in
@Control.Applicative@. However, since Parsley makes use of staging, the signatures
of these combinators do not correctly match the signatures of those in base Haskell (due to a lack
of @Applicative@ constraint).

@since 0.1.0.0
-}
module Parsley.Alternative (
    module Parsley.Alternative,
    module Primitives
  ) where

import Prelude hiding                (pure, (<$>))
import Parsley.Applicative           (pure, (<$>), ($>), (<:>))
import Parsley.Internal.Common.Utils (makeQ)
import Parsley.Internal.Core         (Parser, Defunc(UNIT, EMPTY), ParserOps)

import Parsley.Internal.Core.Primitives as Primitives ((<|>), empty)

infixl 3 <+>
(<+>) :: Parser a -> Parser b -> Parser (Either a b)
p <+> q = makeQ Left [||Left||] <$> p <|> makeQ Right [||Right||] <$> q

option :: ParserOps rep => rep a -> Parser a -> Parser a
option x p = p <|> pure x

optionally :: ParserOps rep => Parser a -> rep b -> Parser b
optionally p x = option x (p $> x)

optional :: Parser a -> Parser ()
optional = flip optionally UNIT

choice :: [Parser a] -> Parser a
choice = foldr (<|>) empty

maybeP :: Parser a -> Parser (Maybe a)
maybeP p = option (makeQ Nothing [||Nothing||]) (makeQ Just [||Just||] <$> p)

manyTill :: Parser a -> Parser b -> Parser [a]
manyTill p end = let go = end $> EMPTY <|> p <:> go in go