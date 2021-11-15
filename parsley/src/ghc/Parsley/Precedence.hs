{-# LANGUAGE MultiParamTypeClasses, UndecidableInstances #-}
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
module Parsley.Precedence (
    precedence, precHomo,
    Fixity(..),
    Op,
    GOps(..), sops, ops,
    Prec(..), (>+), (+<),
    Subtype(..),
  ) where

import Prelude hiding                ((<$>), (<*>), pure)
import Data.List                     (foldl')

import Parsley.Alternative           (choice, (<|>))
import Parsley.Applicative           ((<$>), (<*>), pure, (<**>))
import Parsley.Fold                  (prefix, postfix, infixl1, infixr1)
import Parsley.Internal.Common.Utils (WQ(WQ))
import Parsley.Internal.Core         (Parser, Defunc(BLACK, ID, FLIP))

--import qualified Data.Generics.Internal.Profunctor.Prism as GLens
--import qualified Data.Generics.Sum.Internal.Subtype as GLens

{-|
This combinator will construct and expression parser will provided with a table of precedence..

@since 2.0.0.0
-}
precedence :: Prec a -> Parser a
precedence (Atom atom) = atom
precedence (Level lvls op) = level (precedence lvls) op
  where
    level :: Parser a -> Op a b -> Parser b
    level atom (Op InfixL op wrap) = infixl1 wrap atom op
    level atom (Op InfixR op wrap) = infixr1 wrap atom op
    level atom (Op InfixN op wrap) = atom <**> (FLIP <$> op <*> atom <|> pure wrap)
    level atom (Op Prefix op wrap) = prefix op (wrap <$> atom)
    level atom (Op Postfix op wrap) = postfix (wrap <$> atom) op

{-|
A simplified version of `precedence` that does not use the heterogeneous list `Prec`, but
instead requires all layers of the table to have the same type.

@since 2.0.0.0
-}
precHomo :: Parser a -> [Op a a] -> Parser a
precHomo atom = precedence . foldl' (>+) (Atom atom)

{-|
Denotes the fixity of a given level in a precedence table. The type parameter @sig@ encodes the
types of the operators on this level, in a heterogeneous fashion.

@since 2.0.0.0
-}
data Fixity a b sig where
  -- | Denotes a left-associative binary operator.
  InfixL  :: Fixity a b (b -> a -> b)
  -- | Denotes a right-associative binary operator.
  InfixR  :: Fixity a b (a -> b -> b)
  -- | Denotes a non-associative binary operator.
  InfixN  :: Fixity a b (a -> a -> b)
  -- | Denotes a prefix unary operator.
  Prefix  :: Fixity a b (b -> b)
  -- | Denotes a postfix unary operator.
  Postfix :: Fixity a b (b -> b)

{-|
Packages together a level of a precedence table, by associating a `Fixity` with the operators that
match that specific signature converting from one layer of type @a@ to a new layer of type @b@.
See `ops`, `sops`, and `gops` for how to construct them.

@since 2.0.0.0
-}
data Op a b where
  Op :: Fixity a b sig -> Parser sig -> Defunc (a -> b) -> Op a b

{-|
This typeclass is used to allow abstraction of the representation of user-level functions.
See the instances for information on what these representations are.

@since 2.0.0.0
-}
class GOps rep where
  {-|
  Sometimes, the relationship between two levels of a heterogeneous precedence hierarchy is non-trivial.
  By using `gops`, the conversion function can be used to adapt one layer into the type of the next.

  @since 2.0.0.0
  -}
  gops :: Fixity a b sig -> [Parser sig] -> rep (a -> b) -> Op a b

{-|
This is the default representation used for user-level functions and values: plain old code.

@since 2.0.0.0
-}
instance GOps WQ where
  gops fixity ps = gops fixity ps . BLACK

{-|
This is used to allow defunctionalised versions of many standard Haskell functions to be used
directly as an argument to relevant combinators.

@since 2.0.0.0
-}
instance {-# INCOHERENT #-} x ~ Defunc => GOps x where
  gops fixity ps = Op fixity (choice ps)

{-|
When two levels in a precedence hierarchy are the same type, they are trivially embedded using the
identity function.

@since 2.0.0.0
-}
ops :: Fixity a a sig -> [Parser sig] -> Op a a
ops fixity ps = Op fixity (choice ps) ID

{-|
Encodes a subtyping relationship between two types @sub@ and @sup@. This allows for the conversion
or embedding of one type into the other, as well as their extraction.

It should be the case that:

prop> fmap upcast . downcast = Just
prop> downcast . upcast = Just

@since 2.0.0.0
-}
class Subtype sub sup where
  -- | Casts a value of the subtype into one of the supertype, likely by wrapping it in some constructor
  upcast   :: sub -> sup
  -- | Attempts to extract a value of a subtype from a supertype
  downcast :: sup -> Maybe sub

{-instance GLens.Context sub sup => Subtype sub sup where
  upcast = GLens.build GLens.derived
  downcast = either (const Nothing) Just . GLens.match GLens.derived-}

{-|
When two levels of a precedence hierarchy are in a subtyping relation, the conversion between
the two can be trivially provided as the `upcast` function.

@since 2.0.0.0
-}
sops :: Subtype a b => Fixity a b sig -> [Parser sig] -> Op a b
sops fixity ps = gops fixity ps (WQ upcast [||upcast||])

{-|
A heterogeneous list that represents a precedence table so that @Prec a@ produces values of type
@a@.

@since 2.0.0.0
-}
data Prec a where
  -- | A Level of the table, containing the sub-level and the operators. See `(>+)` and `(+<)`.
  Level :: Prec a -> Op a b -> Prec b
  -- | The terminal atom in the table.
  Atom :: Parser a -> Prec a

infixl 5 >+
{-|
Sugar for the `Level` constructor, this operator - along with its sibling - is hungry and greedy: it
eats the levels with the higher precedence: in @lvls >+ lvl@, @lvl@ is lower precedence than @lvls@.

@since 2.0.0.0
-}
(>+) :: Prec a -> Op a b -> Prec b
(>+) = Level

infixr 5 +<
{-|
Sugar for the `Level` constructor, this operator - along with its sibling - is hungry and greedy: it
eats the levels with the higher precedence: in @lvl +< lvls@, @lvl@ is lower precedence than @lvls@.

@since 2.0.0.0
-}
(+<) :: Op a b -> Prec a -> Prec b
(+<) = flip (>+)