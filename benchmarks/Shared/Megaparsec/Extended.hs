{-# LANGUAGE TypeFamilies #-}
module Shared.Megaparsec.Extended (
    module Text.Megaparsec,
    module Text.Megaparsec.Char,
    module Control.Monad,
    module Control.Applicative,
    module Shared.Megaparsec.Extended
  ) where
import Text.Megaparsec hiding (token, match)
import Text.Megaparsec.Char hiding (string)
import Data.List (foldl')
import Control.Monad (MonadPlus, void)
import Control.Applicative (liftA2, liftA3, empty, Alternative, (<**>))

type Parser s a = Parsec () s a

string :: (Stream s, Token s ~ Char) => String -> Parser s String
string = traverse char

token :: (Stream s, Token s ~ Char) => String -> Parser s String
token = try . string

($>) :: Functor f => f a -> b -> f b
($>) = flip (<$)

match :: (Monad m, Eq a) => [a] -> m a -> (a -> m b) -> m b -> m b
match xs p f def = p >>= (\x -> if elem x xs then f x else def)

maybeP :: (Stream s, Token s ~ Char) => Parser s a -> Parser s (Maybe a)
maybeP p = option Nothing (Just <$> p)

fromMaybeP :: Monad m => m (Maybe a) -> m a -> m a
fromMaybeP mmx d = mmx >>= maybe d return

(<+>) :: (Stream s, Token s ~ Char) => Parser s a -> Parser s b -> Parser s (Either a b)
p <+> q = Left <$> p <|> Right <$> q

(<:>) :: (Stream s, Token s ~ Char) => Parser s a -> Parser s [a] -> Parser s [a]
(<:>) = liftA2 (:)

(<~>) :: (Stream s, Token s ~ Char) => Parser s a -> Parser s b -> Parser s (a, b)
(<~>) = liftA2 (,)

pfoldl1 :: (Stream s, Token s ~ Char) => (b -> a -> b) -> b -> Parser s a -> Parser s b
pfoldl1 f k p = foldl' f k <$> some p

(>?>) :: MonadPlus m => m a -> (a -> Bool) -> m a
m >?> f = m >>= \x -> if f x then return x else empty

chainPre :: (Stream s, Token s ~ Char) => Parser s (a -> a) -> Parser s a -> Parser s a
chainPre op p = flip (foldr ($)) <$> many op <*> p

chainPost :: (Stream s, Token s ~ Char) => Parser s a -> Parser s (a -> a) -> Parser s a
chainPost p op = foldl' (flip ($)) <$> p <*> many op

chainl1 :: (Stream s, Token s ~ Char) => Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainl1 p op = chainPost p (flip <$> op <*> p)

chainr1 :: (Stream s, Token s ~ Char) => Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainr1 p op = let go = p <**> ((flip <$> op <*> go) <|> pure id) in go

data Level s a = InfixL  [Parser s (a -> a -> a)]
               | InfixR  [Parser s (a -> a -> a)]
               | Prefix  [Parser s (a -> a)]
               | Postfix [Parser s (a -> a)]

precedence :: (Stream s, Token s ~ Char) => [Level s a] -> Parser s a -> Parser s a
precedence levels atom = foldl' convert atom levels
  where
    convert x (InfixL ops)  = chainl1 x (choice ops)
    convert x (InfixR ops)  = chainr1 x (choice ops)
    convert x (Prefix ops)  = chainPre (choice ops) x
    convert x (Postfix ops) = chainPost x (choice ops)