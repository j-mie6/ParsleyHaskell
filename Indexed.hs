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

class IFunctor (f :: ([*] -> [[*]] -> * -> * -> *) -> [*] -> [[*]] -> * -> * -> *) where
  imap :: (forall i' j' k' l'. a i' j' k' l' -> b i' j' k' l') -> f a i j k l -> f b i j k l
    
data Free (f :: ([*] -> [[*]] -> * -> * -> *) -> [*] -> [[*]] -> * -> * -> *) (a :: [*] -> [[*]] -> * -> * -> *) (i :: [*]) (j :: [[*]]) (k :: *) (l :: *) where
  Var :: a i j k l -> Free f a i j k l
  Op :: f (Free f a) i j k l -> Free f a i j k l
    
unOp :: Free f a i j k l -> f (Free f a) i j k l
unOp (Op op) = op

fold :: IFunctor f => (forall i' j' k' l'. a i' j' k' l' -> b i' j' k' l')
                   -> (forall i' j' k' l'. f b i' j' k' l' -> b i' j' k' l') -> Free f a i j k l -> b i j k l
fold gen alg (Var x) = gen x
fold gen alg (Op x)  = alg (imap (fold gen alg) x)

fold' :: IFunctor f => (forall i' j' k' l'. a i' j' k' l' -> b i' j' k' l')
                    -> (forall i' j' k' l'. Free f a i' j' k' l' -> f b i' j' k' l' -> b i' j' k' l')
                    -> Free f a i j k l -> b i j k l
fold' gen alg (Var x)   = gen x
fold' gen alg op@(Op x) = alg op (imap (fold' gen alg) x)

(/\) :: (a -> b) -> (a -> c) -> a -> (b, c)
(f /\ g) x = (f x, g x)

data History f a i j k l = Genesis (a i j k l) | Era (a i j k l) (f (History f a) i j k l)
present :: History f a i j k l -> a i j k l
present (Genesis x) = x
present (Era x _)   = x

histo :: forall f a b i j k l. IFunctor f => (forall i' j' k' l'. a i' j' k' l' -> b i' j' k' l')
                                            -> (forall i' j' k' l'. f (History f b) i' j' k' l' -> b i' j' k' l')
                                            -> Free f a i j k l -> b i j k l
histo gen alg tree = present (go tree)
  where
    go :: forall i' j' k' l'. Free f a i' j' k' l' -> History f b i' j' k' l'
    go (Var x) = Genesis (gen x)
    go (Op x)  = uncurry Era ((alg /\ id) (imap go x))

{-newtype Prod f g i j k l = Prod {getProd :: (f i j k l, g i j k l)}
para :: IFunctor f => (forall i' j' k' l'. a i' j' k' l' -> b i' j' k' l')
                        -> (forall i' j' k' l'. f (Prod (Free f a) b) i' j' k' l' -> b i' j' k' l')
                        -> Free f a i j k l -> b i j k l
para gen alg (Var x) = gen x
para gen alg (Op x)  = alg (imap (Prod . (id /\ (para gen alg))) x)

parahisto :: forall f a b i j k l. IFunctor f => (forall i' j' k' l'. a i' j' k' l' -> b i' j' k' l')
                                              -> (forall i' j' k' l'. f (Prod (Free f a) (History f b)) i' j' k' l' -> b i' j' k' l')
                                              -> Free f a i j k l -> b i j k l
parahisto gen alg tree = present (go tree)
  where
    go :: forall i' j' k' l'. Free f a i' j' k' l' -> History f b i' j' k' l'
    go (Var x) = Genesis (gen x)
    go (Op x)  = uncurry Era ((alg /\ imap (snd . getProd)) (imap (Prod . (id /\ go)) x))-}

extract :: IFunctor f => (forall i' j' k' l'. f a i' j' k' l' -> a i' j' k' l') -> Free f a i j k l -> a i j k l
extract = fold id

instance IFunctor f => IFunctor (Free f) where
  imap f (Var x) = Var (f x)
  imap f (Op x) = Op (imap (imap f) x)

class                         Chain r k         where (|>) :: (a -> Maybe r) -> (a -> k) -> a -> k
instance {-# OVERLAPPABLE #-} Chain a a         where (|>) = liftA2 (flip fromMaybe)
instance {-# OVERLAPS #-}     Chain a (Maybe a) where (|>) = liftA2 (<|>)

data Unit i j k l = Unit
data Void i j k l
absurd :: Void i j k l -> b
absurd = \case
data Const a i j k l = Const {getConst :: a}