{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Indexed where

import Control.Applicative ((<|>), liftA2)
import Data.Maybe          (fromMaybe)

class IFunctor (f :: (* -> *) -> * -> *) where
  imap :: (forall j. a j -> b j) -> f a i -> f b i

class IFunctor3 (f :: ([*] -> * -> * -> *) -> [*] -> * -> * -> *) where
  imap3 :: (forall i' j' k'. a i' j' k' -> b i' j' k') -> f a i j k -> f b i j k
    
data Free (f :: (* -> *) -> * -> *) (a :: * -> *) (k :: *) where
  Var :: a i -> Free f a i
  Op :: f (Free f a) i -> Free f a i

data Free3 (f :: ([*] -> * -> * -> *) -> [*] -> * -> * -> *) (a :: [*] -> * -> * -> *) (i :: [*]) (j :: *) (k :: *) where
  Var3 :: a i j k -> Free3 f a i j k
  Op3 :: f (Free3 f a) i j k -> Free3 f a i j k
    
unOp :: Free f a i -> f (Free f a) i
unOp (Op op) = op

unOp3 :: Free3 f a i j k -> f (Free3 f a) i j k
unOp3 (Op3 op) = op

fold :: IFunctor f => (forall j. a j -> b j)
                   -> (forall j. f b j -> b j) -> Free f a i -> b i
fold gen alg (Var x) = gen x
fold gen alg (Op x)  = alg (imap (fold gen alg) x)

fold' :: IFunctor f => (forall j. a j -> b j)
                    -> (forall j. Free f a j -> f b j -> b j)
                    -> Free f a i -> b i
fold' gen alg (Var x)   = gen x
fold' gen alg op@(Op x) = alg op (imap (fold' gen alg) x)

fold3 :: IFunctor3 f => (forall i' j' k'. a i' j' k' -> b i' j' k')
                     -> (forall i' j' k'. f b i' j' k' -> b i' j' k') -> Free3 f a i j k -> b i j k
fold3 gen alg (Var3 x) = gen x
fold3 gen alg (Op3 x)  = alg (imap3 (fold3 gen alg) x)

fold3' :: IFunctor3 f => (forall i' j' k'. a i' j' k' -> b i' j' k')
                      -> (forall i' j' k'. Free3 f a i' j' k' -> f b i' j' k' -> b i' j' k')
                      -> Free3 f a i j k -> b i j k
fold3' gen alg (Var3 x)   = gen x
fold3' gen alg op@(Op3 x) = alg op (imap3 (fold3' gen alg) x)

(/\) :: (a -> b) -> (a -> c) -> a -> (b, c)
(f /\ g) x = (f x, g x)

data History f a i = Genesis (a i) | Era (a i) (f (History f a) i)
present :: History f a i -> a i
present (Genesis x) = x
present (Era x _)   = x

histo :: forall f a b i. IFunctor f => (forall j. a j -> b j)
                                    -> (forall j. f (History f b) j -> b j)
                                    -> Free f a i -> b i
histo gen alg = present . fold (Genesis . gen) (alg >>= Era)

{-newtype Prod f g i j k l = Prod {getProd :: (f i j k l, g i j k l)}
para :: IFunctor f => (forall i' j' k'. a i' j' k' -> b i' j' k')
                        -> (forall i' j' k'. f (Prod (Free f a) b) i' j' k' -> b i' j' k')
                        -> Free f a i j k l -> b i j k l
para gen alg (Var x) = gen x
para gen alg (Op x)  = alg (imap (Prod . (id /\ (para gen alg))) x)

parahisto :: forall f a b i j k l. IFunctor f => (forall i' j' k'. a i' j' k' -> b i' j' k')
                                              -> (forall i' j' k'. f (Prod (Free f a) (History f b)) i' j' k' -> b i' j' k')
                                              -> Free f a i j k l -> b i j k l
parahisto gen alg tree = present (go tree)
  where
    go :: forall i' j' k'. Free f a i' j' k' -> History f b i' j' k'
    go (Var x) = Genesis (gen x)
    go (Op x)  = uncurry Era ((alg /\ imap (snd . getProd)) (imap (Prod . (id /\ go)) x))-}

extract :: IFunctor f => (forall j. f a j -> a j) -> Free f a i -> a i
extract = fold id

class                         Chain r k         where (|>) :: (a -> Maybe r) -> (a -> k) -> a -> k
instance {-# OVERLAPPABLE #-} Chain a a         where (|>) = liftA2 (flip fromMaybe)
instance {-# OVERLAPS #-}     Chain a (Maybe a) where (|>) = liftA2 (<|>)

data Unit1 k = Unit
data Void1 k
data Const1 a k = Const1 {getConst1 :: a}

data Unit3 i j k = Unit3
data Void3 i j k
data Const3 a i j k = Const3 {getConst3 :: a}

class Absurd v where absurd :: v -> a
instance Absurd (Void1 k) where absurd = \case
instance Absurd (Void3 i j k) where absurd = \case


