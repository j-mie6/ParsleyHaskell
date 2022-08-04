{-# LANGUAGE MultiParamTypeClasses #-}
module Parsley.Internal.Common.Indexed (module Parsley.Internal.Common.Indexed) where

import Control.Applicative ((<|>), liftA2)
import Data.Kind           (Type)
import Data.Maybe          (fromMaybe)

data Nat = Zero | Succ Nat
type One = Succ Zero

class IFunctor (f :: (Type -> Type) -> Type -> Type) where
  imap :: (forall j. a j -> b j) -> f a i -> f b i

class IFunctor3 (f :: ([Type] -> Nat -> Type -> Type) -> [Type] -> Nat -> Type -> Type) where
  imap3 :: (forall i' j' k'. a i' j' k' -> b i' j' k') -> f a i j k -> f b i j k

newtype Fix f a = In (f (Fix f) a)
newtype Fix3 f i j k = In3 (f (Fix3 f) i j k)

inop :: Fix f a -> f (Fix f) a
inop (In x) = x

inop3 :: Fix3 f i j k -> f (Fix3 f) i j k
inop3 (In3 x) = x

cata :: forall f a i. IFunctor f => (forall j. f a j -> a j) -> Fix f i -> a i
cata alg = go where
  go :: Fix f j -> a j
  go (In x) = alg (imap go x)

cata' :: forall f a i. IFunctor f =>
         (forall j. Fix f j -> f a j -> a j) ->
         Fix f i -> a i
cata' alg = go where
  go :: Fix f j -> a j
  go i@(In x) = alg i (imap go x)

cata3 :: forall f a i j k. IFunctor3 f =>
         (forall i' j' k'. f a i' j' k' -> a i' j' k') ->
         Fix3 f i j k -> a i j k
cata3 alg = go where
  go :: Fix3 f i' j' k' -> a i' j' k'
  go (In3 x) = alg (imap3 go x)

data (f :+: g) k a where
  L :: f k a -> (f :+: g) k a
  R :: g k a -> (f :+: g) k a

instance (IFunctor f, IFunctor g) => IFunctor (f :+: g) where
  imap f (L x) = L (imap f x)
  imap f (R y) = R (imap f y)

(\/) :: (f a i -> b) -> (g a i -> b) -> (f :+: g) a i -> b
(f \/ _) (L x) = f x
(_ \/ g) (R y) = g y

data Cofree f a i = a i :< f (Cofree f a) i
{-# INLINE extract #-}
extract :: Cofree f a i -> a i
extract (x :< _) = x

instance IFunctor f => IFunctor (Cofree f) where
  imap f (x :< xs) = f x :< imap (imap f) xs

histo :: IFunctor f => (forall j. f (Cofree f a) j -> a j) -> Fix f i -> a i
histo alg = extract . cata (alg >>= (:<))

data (f :*: g) i = f i :*: g i

{-# INLINE (/\) #-}
(/\) :: (a -> f i) -> (a -> g i) -> (a -> (f :*: g) i)
(f /\ g) x = f x :*: g x

{-# INLINE ifst #-}
ifst :: (f :*: g) i -> f i
ifst (x :*: _) = x
{-# INLINE isnd #-}
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

data Unit3 i j k = Unit3
newtype Const3 a i j k = Const3 {getConst3 :: a}
