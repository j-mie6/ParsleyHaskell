{-# LANGUAGE FlexibleContexts #-}
module Shared.Parsec.Extended (
    module Text.Parsec,
    module Data.Functor,
    module Control.Monad,
    module Control.Monad.Identity,
    module Control.Applicative,
    module Shared.Parsec.Extended
  ) where

import Text.Parsec hiding (token)
import Data.Functor (void, ($>))
import Control.Monad.Identity (Identity)
import Control.Monad (MonadPlus)
import Control.Applicative (liftA2, liftA3, empty, Alternative, (<**>))
import Data.List (foldl')

type Parser s a = Parsec s () a

token :: Stream s Identity Char => String -> Parser s String
token = try . string

match :: (Monad m, Eq a) => [a] -> m a -> (a -> m b) -> m b -> m b
match xs p f def = p >>= (\x -> if elem x xs then f x else def)

skipSome :: Stream s Identity Char => Parser s a -> Parser s ()
skipSome p = void (some p)

maybeP :: Stream s Identity Char => Parser s a -> Parser s (Maybe a)
maybeP p = option Nothing (Just <$> p)

fromMaybeP :: Monad m => m (Maybe a) -> m a -> m a
fromMaybeP mmx d = mmx >>= maybe d return

(<+>) :: Stream s Identity Char => Parser s a -> Parser s b -> Parser s (Either a b)
p <+> q = Left <$> p <|> Right <$> q

(<:>) :: Stream s Identity Char => Parser s a -> Parser s [a] -> Parser s [a]
(<:>) = liftA2 (:)

(<~>) :: Stream s Identity Char => Parser s a -> Parser s b -> Parser s (a, b)
(<~>) = liftA2 (,)

some :: Stream s Identity Char => Parser s a -> Parser s [a]
some = many1

pfoldl1 :: Stream s Identity Char => (b -> a -> b) -> b -> Parser s a -> Parser s b
pfoldl1 f k p = foldl' f k <$> some p

(>?>) :: MonadPlus m => m a -> (a -> Bool) -> m a
m >?> f = m >>= \x -> if f x then return x else empty

chainPre :: Stream s Identity Char => Parser s (a -> a) -> Parser s a -> Parser s a
chainPre op p = flip (foldr ($)) <$> many op <*> p

chainPost :: Stream s Identity Char => Parser s a -> Parser s (a -> a) -> Parser s a
chainPost p op = foldl' (flip ($)) <$> p <*> many op

data Level s a = InfixL  [Parser s (a -> a -> a)]
               | InfixR  [Parser s (a -> a -> a)]
               | Prefix  [Parser s (a -> a)]
               | Postfix [Parser s (a -> a)]

precedence :: Stream s Identity Char => [Level s a] -> Parser s a -> Parser s a
precedence levels atom = foldl' convert atom levels
  where
    convert x (InfixL ops)  = chainl1 x (choice ops)
    convert x (InfixR ops)  = chainr1 x (choice ops)
    convert x (Prefix ops)  = chainPre (choice ops) x
    convert x (Postfix ops) = chainPost x (choice ops)