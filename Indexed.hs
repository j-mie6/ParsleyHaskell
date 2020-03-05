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
  imap3 :: (forall i' j'. a i' j' x -> b i' j' x) -> f a i j x -> f b i j x

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

cata3 :: IFunctor3 f => (forall i' j'. f a i' j' x -> a i' j' x) -> Fix3 f i j x -> a i j x
cata3 alg (In3 x)  = alg (imap3 (cata3 alg) x)

data Cofree f a i = a i :< f (Cofree f a) i
extract :: Cofree f a i -> a i
extract (x :< _) = x

instance IFunctor f => IFunctor (Cofree f) where
  imap f (x :< xs) = f x :< imap (imap f) xs

histo :: forall f a i. IFunctor f => (forall j. f (Cofree f a) j -> a j)
                                  -> Fix f i -> a i
histo alg = extract . cata (alg >>= (:<))

data (f :*: g) i = f i :*: g i
(/\) :: (a -> f i) -> (a -> g i) -> (a -> (f :*: g) i)
(f /\ g) x = f x :*: g x
ifst :: (f :*: g) i -> f i
ifst (x :*: _) = x
isnd :: (f :*: g) i -> g i
isnd (_ :*: y) = y

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


