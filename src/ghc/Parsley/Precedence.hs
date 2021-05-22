{-# LANGUAGE AllowAmbiguousTypes,
             MultiParamTypeClasses #-}
{-|
Module      : Parsley.Precedence
Description : The precedence parser functionality
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : stable

This module exposes the required machinery for parsing expressions given by a precedence
table. Unlike those found in [parser-combinators](https://hackage.haskell.org/package/parser-combinators-1.3.0/docs/Control-Monad-Combinators-Expr.html)
or [parsec](https://hackage.haskell.org/package/parsec-3.1.14.0/docs/Text-Parsec-Expr.html), this
implementation allows the precedence layers to change type in the table.

@since 0.1.0.0
-}
module Parsley.Precedence (module Parsley.Precedence) where

import Prelude hiding      ((<$>))
import Parsley.Alternative (choice)
import Parsley.Applicative ((<$>))
import Parsley.Fold        (chainPre, chainPost, chainl1', chainr1')
import Parsley.Internal    (WQ, Parser, Defunc(BLACK, ID))

{-|
This combinator will construct and expression parser will provided with a table of precedence along
with a terminal atom.

@since 0.1.0.0
-}
precedence :: Prec a b -> Parser a -> Parser b
precedence NoLevel atom = atom
precedence (Level lvl lvls) atom = precedence lvls (level lvl atom)
  where
    level (InfixL ops wrap) atom  = chainl1' wrap atom (choice ops)
    level (InfixR ops wrap) atom  = chainr1' wrap atom (choice ops)
    level (Prefix ops wrap) atom  = chainPre (choice ops) (wrap <$> atom)
    level (Postfix ops wrap) atom = chainPost (wrap <$> atom) (choice ops)

{-|
A simplified version of `precedence` that does not use the heterogeneous list `Prec`, but
instead requires all layers of the table to have the same type.

@since 0.1.0.0
-}
monolith :: [Level a a] -> Prec a a
monolith = foldr Level NoLevel

{-|
A heterogeneous list that represents a precedence table so that @Prec a b@ transforms the type @a@
into @b@ via various layers of operators.

@since 0.1.0.0
-}
data Prec a b where
  NoLevel :: Prec a a
  Level :: Level a b -> Prec b c -> Prec a c

{-|
This datatype represents levels of the precedence table `Prec`, where each constructor
takes many parsers of the same level and fixity.

@since 0.1.0.0
-}
data Level a b = InfixL  [Parser (b -> a -> b)] (Defunc (a -> b)) -- ^ left-associative infix operators
               | InfixR  [Parser (a -> b -> b)] (Defunc (a -> b)) -- ^ right-associative infix operators
               | Prefix  [Parser (b -> b)]      (Defunc (a -> b)) -- ^ prefix unary operators
               | Postfix [Parser (b -> b)]      (Defunc (a -> b)) -- ^ postfix unary operators

{-|
This class provides a way of working with the `Level` datatype without needing to
provide wrappers, or not providing `Defunc` arguments.

@since 0.1.0.0
-}
class Monolith a b c where
  -- | Used to construct a precedence level of infix left-associative operators
  infixL  :: [Parser (b -> a -> b)] -> c
  -- | Used to construct a precedence level of infix right-associative operators
  infixR  :: [Parser (a -> b -> b)] -> c
  -- | Used to construct a precedence level of prefix operators
  prefix  :: [Parser (b -> b)]      -> c
  -- | Used to construct a precedence level of postfix operators
  postfix :: [Parser (b -> b)]      -> c

{-|
This instance is used to handle monolithic types where the input and output are the same,
it does not require the wrapping function to be provided.

@since 0.1.0.0
-}
instance x ~ a => Monolith x a (Level a a) where
  infixL  = flip InfixL ID
  infixR  = flip InfixR ID
  prefix  = flip Prefix ID
  postfix = flip Postfix ID

{-|
This instance is used to handle non-monolithic types: i.e. where the input and output types of
a level differ.

@since 0.1.0.0
-}
instance {-# INCOHERENT #-} x ~ (WQ (a -> b) -> Level a b) => Monolith a b x where
  infixL  ops = InfixL ops . BLACK
  infixR  ops = InfixR ops . BLACK
  prefix  ops = Prefix ops . BLACK
  postfix ops = Postfix ops . BLACK