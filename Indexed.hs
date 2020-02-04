{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Indexed where

import Control.Applicative ((<|>), liftA2)
import Data.Maybe          (fromMaybe)

class IFunctor (f :: (* -> *) -> * -> *) where
  imap :: (forall j. a j -> b j) -> f a i -> f b i

class IFunctor3 (f :: ([*] -> * -> * -> *) -> [*] -> * -> * -> *) where
  imap3 :: (forall i' j' k'. a i' j' k' -> b i' j' k') -> f a i j k -> f b i j k

newtype Fix f a = In (f (Fix f) a)
newtype Fix3 f i j k = In3 (f (Fix3 f) i j k)

inop :: Fix f a -> f (Fix f) a
inop (In x) = x

inop3 :: Fix3 f i j k -> f (Fix3 f) i j k
inop3 (In3 x) = x

cata :: IFunctor f => (forall j. f a j -> a j) -> Fix f i -> a i
cata alg (In x)  = alg (imap (cata alg) x)

cata' :: IFunctor f => (forall j. Fix f j -> f a j -> a j)
                    -> Fix f i -> a i
cata' alg i@(In x) = alg i (imap (cata' alg) x)

cata3 :: IFunctor3 f => (forall i' j' k'. f a i' j' k' -> a i' j' k') -> Fix3 f i j k -> a i j k
cata3 alg (In3 x)  = alg (imap3 (cata3 alg) x)

data Cofree f a i = a i :< f (Cofree f a) i
extract :: Cofree f a i -> a i
extract (x :< _) = x

histo :: forall f a i. IFunctor f => (forall j. f (Cofree f a) j -> a j)
                                  -> Fix f i -> a i
histo alg = extract . cata (alg >>= (:<))

data (f :**: g) i j k = f i j k :**: g i j k
(/\) :: (a -> f i j k) -> (a -> g i j k) -> (a -> (f :**: g) i j k)
(f /\ g) x = f x :**: g x
ifst3 :: (f :**: g) i j k -> f i j k
ifst3 (x :**: _) = x
isnd3 :: (f :**: g) i j k -> g i j k
isnd3 (_ :**: y) = y

class                         Chain r k         where (|>) :: (a -> Maybe r) -> (a -> k) -> a -> k
instance {-# OVERLAPPABLE #-} Chain a a         where (|>) = liftA2 (flip fromMaybe)
instance {-# OVERLAPS #-}     Chain a (Maybe a) where (|>) = liftA2 (<|>)

data Unit1 k = Unit
newtype Const1 a k = Const1 {getConst1 :: a}
data Tag t f k a = Tag {tag :: t, tagged :: f k a}

instance IFunctor f => IFunctor (Tag t f) where
  imap f (Tag t k) = Tag t (imap f k)

data Unit3 i j k = Unit3
newtype Const3 a i j k = Const3 {getConst3 :: a}


