{-# OPTIONS_GHC -fplugin=LiftPlugin #-}
{-# LANGUAGE PatternSynonyms #-}
module Parsley.Applicative (
    module Parsley.Applicative,
    module Primitives
  ) where

import Prelude hiding       (pure, (<*>), (*>), (<*), (>>), (<$>), fmap, (<$), traverse, sequence)
import Parsley.Common.Utils (code)
import Parsley.Core         (Parser, Defunc(UNIT, CONS, APP, CONST, EMPTY), pattern FLIP_H, ParserOps)

import Parsley.Core.Primitives as Primitives (pure, (<*>), (*>), (<*))

-- Functor Operations
fmap :: ParserOps rep => rep (a -> b) -> Parser a -> Parser b
fmap f = (pure f <*>)

infixl 4 <$>
(<$>) :: ParserOps rep => rep (a -> b) -> Parser a -> Parser b
(<$>) = fmap

void :: Parser a -> Parser ()
void p = p *> unit

infixl 4 <$
(<$) :: ParserOps rep => rep b -> Parser a -> Parser b
x <$ p = p *> pure x

infixl 4 $>
($>) :: ParserOps rep => Parser a -> rep b -> Parser b
($>) = flip (<$)

infixl 4 <&>
(<&>) :: ParserOps rep => Parser a -> rep (a -> b) -> Parser b
(<&>) = flip fmap

constp :: Parser a -> Parser (b -> a)
constp = (CONST <$>)

-- Alias Operations
infixl 1 >>
(>>) :: Parser a -> Parser b -> Parser b
(>>) = (*>)

-- Monoidal Operations
unit :: Parser ()
unit = pure UNIT

infixl 4 <~>
(<~>) :: Parser a -> Parser b -> Parser (a, b)
(<~>) = liftA2 (code (,))

infixl 4 <~
(<~) :: Parser a -> Parser b -> Parser a
(<~) = (<*)

infixl 4 ~>
(~>) :: Parser a -> Parser b -> Parser b
(~>) = (*>)

-- Lift Operations
liftA2 :: ParserOps rep => rep (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftA2 f p q = f <$> p <*> q

liftA3 :: ParserOps rep => rep (a -> b -> c -> d) -> Parser a -> Parser b -> Parser c -> Parser d
liftA3 f p q r = f <$> p <*> q <*> r

{-# INLINE (<:>) #-}
infixl 4 <:>
(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = liftA2 CONS

infixl 4 <**>
(<**>) :: Parser a -> Parser (a -> b) -> Parser b
(<**>) = liftA2 (FLIP_H APP)

-- Auxillary functions
sequence :: [Parser a] -> Parser [a]
sequence = foldr (<:>) (pure EMPTY)

traverse :: (a -> Parser b) -> [a] -> Parser [b]
traverse f = sequence . map f

repeat :: Int -> Parser a -> Parser [a]
repeat n p = traverse (const p) [1..n]

between :: Parser o -> Parser c -> Parser a -> Parser a
between open close p = open *> p <* close