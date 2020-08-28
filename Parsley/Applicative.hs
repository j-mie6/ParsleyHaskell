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
fmap :: ParserOps rep => rep (a -> b) -> Parser t a -> Parser t b
fmap f = (pure f <*>)

infixl 4 <$>
(<$>) :: ParserOps rep => rep (a -> b) -> Parser t a -> Parser t b
(<$>) = fmap

void :: Parser t a -> Parser t ()
void p = p *> unit

infixl 4 <$
(<$) :: ParserOps rep => rep b -> Parser t a -> Parser t b
x <$ p = p *> pure x

infixl 4 $>
($>) :: ParserOps rep => Parser t a -> rep b -> Parser t b
($>) = flip (<$)

infixl 4 <&>
(<&>) :: ParserOps rep => Parser t a -> rep (a -> b) -> Parser t b
(<&>) = flip fmap

constp :: Parser t a -> Parser t (b -> a)
constp = (CONST <$>)

-- Alias Operations
infixl 1 >>
(>>) :: Parser t a -> Parser t b -> Parser t b
(>>) = (*>)

-- Monoidal Operations
unit :: Parser t ()
unit = pure UNIT

infixl 4 <~>
(<~>) :: Parser t a -> Parser t b -> Parser t (a, b)
(<~>) = liftA2 (code (,))

infixl 4 <~
(<~) :: Parser t a -> Parser t b -> Parser t a
(<~) = (<*)

infixl 4 ~>
(~>) :: Parser t a -> Parser t b -> Parser t b
(~>) = (*>)

-- Lift Operations
liftA2 :: ParserOps rep => rep (a -> b -> c) -> Parser t a -> Parser t b -> Parser t c
liftA2 f p q = f <$> p <*> q

liftA3 :: ParserOps rep => rep (a -> b -> c -> d) -> Parser t a -> Parser t b -> Parser t c -> Parser t d
liftA3 f p q r = f <$> p <*> q <*> r

{-# INLINE (<:>) #-}
infixl 4 <:>
(<:>) :: Parser t a -> Parser t [a] -> Parser t [a]
(<:>) = liftA2 CONS

infixl 4 <**>
(<**>) :: Parser t a -> Parser t (a -> b) -> Parser t b
(<**>) = liftA2 (FLIP_H APP)

-- Auxillary functions
sequence :: [Parser t a] -> Parser t [a]
sequence = foldr (<:>) (pure EMPTY)

traverse :: (a -> Parser t b) -> [a] -> Parser t [b]
traverse f = sequence . map f

repeat :: Int -> Parser t a -> Parser t [a]
repeat n p = traverse (const p) [1..n]

between :: Parser t o -> Parser t c -> Parser t a -> Parser t a
between open close p = open *> p <* close