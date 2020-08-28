{-# LANGUAGE AllowAmbiguousTypes,
             MultiParamTypeClasses #-}
module Parsley.Precedence (module Parsley.Precedence) where

import Prelude hiding       ((<$>))
import Parsley.Alternative  (choice)
import Parsley.Applicative  ((<$>))
import Parsley.Common.Utils (WQ)
import Parsley.Core         (Parser, Defunc(BLACK, ID))
import Parsley.Fold         (chainPre, chainPost, chainl1', chainr1')

precedence :: Prec t a b -> Parser t a -> Parser t b
precedence NoLevel atom = atom
precedence (Level lvl lvls) atom = precedence lvls (level lvl atom)
  where
    level (InfixL ops wrap) atom  = chainl1' wrap atom (choice ops)
    level (InfixR ops wrap) atom  = chainr1' wrap atom (choice ops)
    level (Prefix ops wrap) atom  = chainPre (choice ops) (wrap <$> atom)
    level (Postfix ops wrap) atom = chainPost (wrap <$> atom) (choice ops)

data Level t a b = InfixL  [Parser t (b -> a -> b)] (Defunc (a -> b))
                 | InfixR  [Parser t (a -> b -> b)] (Defunc (a -> b))
                 | Prefix  [Parser t (b -> b)]      (Defunc (a -> b))
                 | Postfix [Parser t (b -> b)]      (Defunc (a -> b))

class Monolith t a b c where
  infixL  :: [Parser t (b -> a -> b)] -> c
  infixR  :: [Parser t (a -> b -> b)] -> c
  prefix  :: [Parser t (b -> b)]      -> c
  postfix :: [Parser t (b -> b)]      -> c

instance x ~ a => Monolith t x a (Level t a a) where
  infixL  = flip InfixL ID
  infixR  = flip InfixR ID
  prefix  = flip Prefix ID
  postfix = flip Postfix ID

instance {-# INCOHERENT #-} x ~ (WQ (a -> b) -> Level t a b) => Monolith t a b x where
  infixL  ops = InfixL ops . BLACK
  infixR  ops = InfixR ops . BLACK
  prefix  ops = Prefix ops . BLACK
  postfix ops = Postfix ops . BLACK

data Prec t a b where
  NoLevel :: Prec t a a
  Level :: Level t a b -> Prec t b c -> Prec t a c

monolith :: [Level t a a] -> Prec t a a
monolith = foldr Level NoLevel