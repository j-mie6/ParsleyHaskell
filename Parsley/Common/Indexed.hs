{-# LANGUAGE GADTs,
             FlexibleInstances,
             RankNTypes,
             DataKinds,
             ScopedTypeVariables,
             PolyKinds,
             MultiParamTypeClasses,
             TypeOperators #-}
module Parsley.Common.Indexed (module Parsley.Common.Indexed) where

import Control.Applicative ((<|>), liftA2)
import Data.Maybe          (fromMaybe)

data Nat = Zero | Succ Nat
type One = Succ Zero

class IFunctor (f :: (* -> *) -> * -> *) where
  imap :: (forall j. a j -> b j) -> f a i -> f b i

class IFunctor4 (f :: ([*] -> Nat -> * -> * -> *) -> [*] -> Nat -> * -> * -> *) where
  imap4 :: (forall i' j' k'. a i' j' k' x -> b i' j' k' x) -> f a i j k x -> f b i j k x

newtype Fix f a = In (f (Fix f) a)
newtype Fix4 f i j k l = In4 (f (Fix4 f) i j k l)

inop :: Fix f a -> f (Fix f) a
inop (In x) = x

inop4 :: Fix4 f i j k l -> f (Fix4 f) i j k l
inop4 (In4 x) = x

cata :: IFunctor f => (forall j. f a j -> a j) -> Fix f i -> a i
cata alg (In x)  = alg (imap (cata alg) x)

cata' :: IFunctor f => (forall j. Fix f j -> f a j -> a j)
                    -> Fix f i -> a i
cata' alg i@(In x) = alg i (imap (cata' alg) x)

cata4 :: IFunctor4 f => (forall i' j' k'. f a i' j' k' x -> a i' j' k' x) -> Fix4 f i j k x -> a i j k x
cata4 alg (In4 x)  = alg (imap4 (cata4 alg) x)

data (f :+: g) k a where
  L :: f k a -> (f :+: g) k a
  R :: g k a -> (f :+: g) k a

instance (IFunctor f, IFunctor g) => IFunctor (f :+: g) where
  imap f (L x) = L (imap f x)
  imap f (R y) = R (imap f y)

(\/) :: (f a i -> b) -> (g a i -> b) -> (f :+: g) a i -> b
(f \/ g) (L x) = f x
(f \/ g) (R y) = g y

data Cofree f a i = a i :< f (Cofree f a) i
extract :: Cofree f a i -> a i
extract (x :< _) = x

instance IFunctor f => IFunctor (Cofree f) where
  imap f (x :< xs) = f x :< imap (imap f) xs

histo :: IFunctor f => (forall j. f (Cofree f a) j -> a j) -> Fix f i -> a i
histo alg = extract . cata (alg >>= (:<))

data (f :*: g) i = f i :*: g i
(/\) :: (a -> f i) -> (a -> g i) -> (a -> (f :*: g) i)
(f /\ g) x = f x :*: g x
ifst :: (f :*: g) i -> f i
ifst (x :*: _) = x
isnd :: (f :*: g) i -> g i
isnd (_ :*: y) = y

mutu :: IFunctor f => (forall j. f (a :*: b) j -> a j) -> (forall j. f (a :*: b) j -> b j) -> Fix f i -> (a :*: b) i
mutu algl algr = cata (algl /\ algr)

zygo :: IFunctor f => (forall j. f (a :*: b) j -> a j) -> (forall j. f b j -> b j) -> Fix f i -> a i
zygo alg aux = ifst . mutu alg (aux . imap isnd)

zipper :: IFunctor f => (forall j. f a j -> a j) -> (forall j. f b j -> b j) -> Fix f i -> (a :*: b) i
zipper algl algr = mutu (algl . imap ifst) (algr . imap isnd)

class                         Chain r k         where (|>) :: (a -> Maybe r) -> (a -> k) -> a -> k
instance {-# OVERLAPPABLE #-} Chain a a         where (|>) = liftA2 (flip fromMaybe)
instance {-# OVERLAPS #-}     Chain a (Maybe a) where (|>) = liftA2 (<|>)

data Unit1 k = Unit
newtype Const1 a k = Const1 {getConst1 :: a}

data Unit4 i j k l = Unit4
newtype Const4 a i j k l = Const4 {getConst4 :: a}


