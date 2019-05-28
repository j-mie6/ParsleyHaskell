{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
module Compiler where

import Machine                    (M(..), ΣVar(..), ΣState(..), ΣVars, IMVar(..), MVar(..), ΦVar(..), fmapInstr)
import Indexed                    (IFunctor, Free(Op), History(Era), Void, Const(..), imap, fold, fold', histo, present, (|>), absurd)
import Utils                      (TExpQ, lift', (>*<), WQ(..))
import Control.Applicative        (liftA2, liftA3)
import Control.Monad              (join, (<$!>))
import Control.Monad.Reader       (ReaderT, ask, runReaderT, local, lift)
import Control.Monad.State.Strict (State, get, put, evalState, runState, MonadState)
import System.IO.Unsafe           (unsafePerformIO)
import Data.IORef                 (IORef, writeIORef, readIORef, newIORef)
import GHC.StableName             (StableName(..), makeStableName, hashStableName, eqStableName)
import Data.Hashable              (Hashable, hashWithSalt, hash)
import Data.HashMap.Lazy          (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Map.Strict            (Map)
import qualified Data.Map.Strict as Map
import Data.Set                   (Set)
import qualified Data.Set as Set
import GHC.Prim                   (StableName#)
import Safe.Coerce                (coerce)
import Data.Maybe                 (isJust, fromJust)
import Debug.Trace                (traceShow)

newtype Parser a = Parser {unParser :: Free Parser' Void '[] '[] a ()}
data Parser' (k :: [*] -> [[*]] -> * -> * -> *) (xs :: [*]) (ks :: [[*]]) (a :: *) (i :: *) where
  Pure          :: WQ a -> Parser' k xs ks a i
  Satisfy       :: WQ (Char -> Bool) -> Parser' k xs ks Char i
  (:<*>:)       :: k xs ks (a -> b) i -> k xs ks a i -> Parser' k xs ks b i
  (:*>:)        :: k xs ks a i -> k xs ks b i -> Parser' k xs ks b i
  (:<*:)        :: k xs ks a i -> k xs ks b i -> Parser' k xs ks a i
  (:<|>:)       :: k xs ks a i -> k xs ks a i -> Parser' k xs ks a i
  Empty         :: Parser' k xs ks a i
  Try           :: Maybe Int -> k xs ks a i -> Parser' k xs ks a i
  LookAhead     :: k xs ks a i -> Parser' k xs ks a i
  Rec           :: IMVar -> k xs ks a i -> Parser' k xs ks a i
  NotFollowedBy :: k xs ks a i -> Parser' k xs ks () i
  Branch        :: k xs ks (Either a b) i -> k xs ks (a -> c) i -> k xs ks (b -> c) i -> Parser' k xs ks c i
  Match         :: k xs ks a i -> [WQ (a -> Bool)] -> [k xs ks b i] -> Parser' k xs ks b i
  ChainPre      :: k xs ks (a -> a) i -> k xs ks a i -> Parser' k xs ks a i
  ChainPost     :: k xs ks a i -> k xs ks (a -> a) i -> Parser' k xs ks a i
  Debug         :: String -> k xs ks a i -> Parser' k xs ks a i

instance IFunctor Parser' where
  imap _ (Pure x) = Pure x
  imap _ (Satisfy p) = Satisfy p
  imap f (p :<*>: q) = f p :<*>: f q
  imap f (p :*>: q) = f p :*>: f q
  imap f (p :<*: q) = f p :<*: f q
  imap f (p :<|>: q) = f p :<|>: f q
  imap _ Empty = Empty
  imap f (Try n p) = Try n (f p)
  imap f (LookAhead p) = LookAhead (f p)
  imap f (Rec p q) = Rec p (f q)
  imap f (NotFollowedBy p) = NotFollowedBy (f p)
  imap f (Branch b p q) = Branch (f b) (f p) (f q)
  imap f (Match p fs qs) = Match (f p) fs (map f qs)
  imap f (ChainPre op p) = ChainPre (f op) (f p)
  imap f (ChainPost p op) = ChainPost (f p) (f op)
  imap f (Debug name p) = Debug name (f p)

instance Show (Free Parser' f '[] '[] a i) where
  show = getConst . fold (const (Const "")) (Const . alg)
    where
      alg :: forall xs ks a i. Parser' (Const String) xs ks a i -> String
      alg (Pure x) = "(pure x)"
      alg (Satisfy _) = "(satisfy f)"
      alg (Const pf :<*>: Const px) = concat ["(", pf, " <*> ",  px, ")"]
      alg (Const p :*>: Const q) = concat ["(", p, " *> ", q, ")"]
      alg (Const p :<*: Const q) = concat ["(", p, " <* ", q, ")"]
      alg (Const p :<|>: Const q) = concat ["(", p, " <|> ", q, ")"]
      alg Empty = "empty"
      alg (Try Nothing (Const p)) = concat ["(try ? ", p, ")"]
      alg (Try (Just n) (Const p)) = concat ["(try ", show n, " ", p, ")"]
      alg (LookAhead (Const p)) = concat ["(lookAhead ", p, ")"]
      alg (Rec _ _) = "recursion point!"
      alg (NotFollowedBy (Const p)) = concat ["(notFollowedBy ", p, ")"]
      alg (Branch (Const b) (Const p) (Const q)) = concat ["(branch ", b, " ", p, " ", q, ")"]
      alg (Match (Const p) fs qs) = concat ["(match ", p, " ", show (map getConst qs), ")"]
      alg (ChainPre (Const op) (Const p)) = concat ["(chainPre ", op, " ", p, ")"]
      alg (ChainPost (Const p) (Const op)) = concat ["(chainPost ", p, " ", op, ")"]
      alg (Debug _ (Const p)) = p

data StableParserName xs ks i = forall a. StableParserName (StableName# (Free Parser' Void xs ks a i))
data GenParser xs ks i = forall a. GenParser (Free Parser' Void xs ks a i)
instance Eq (StableParserName xs ks i) where (StableParserName n) == (StableParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable (StableParserName xs ks i) where
  hash (StableParserName n) = hashStableName (StableName n)
  hashWithSalt salt (StableParserName n) = hashWithSalt salt (StableName n)

newtype Carrier xs ks a i = Carrier {unCarrier :: ReaderT (HashMap (StableParserName xs ks i) (IMVar, GenParser xs ks i, IORef Bool), IMVar) IO (Free Parser' Void xs ks a i)}
preprocess :: Free Parser' Void '[] '[] a i -> Free Parser' Void '[] '[] a i
preprocess !p = unsafePerformIO (runReaderT (unCarrier (fold' absurd alg p)) (HashMap.empty, 0))
  where
    alg :: Free Parser' Void xs ks a i -> Parser' Carrier xs ks a i -> Carrier xs ks a i
    -- Force evaluation of p to ensure that the stableName is correct first time
    alg !p q = Carrier $ do
      !(seen, v) <- ask
      (StableName _name) <- lift (makeStableName p)
      let !name = StableParserName _name
      case HashMap.lookup name seen of
        Just (v', GenParser q, used) -> do lift (writeIORef used True)
                                           return $! (Op (Rec v' (coerce q)))
        Nothing -> mdo usedVar <- lift (newIORef False)
                       q' <- local (HashMap.insert name (v, GenParser q', usedVar) >< (+1)) (unCarrier $ subalg q)
                       used <- lift (readIORef usedVar)
                       if used then return $! (Op (Rec v q'))
                       else         return $! q'
    subalg :: Parser' Carrier xs ks a i -> Carrier xs ks a i
    subalg !(pf :<*>: px)     = Carrier (fmap optimise (liftA2 (:<*>:) (unCarrier pf) (unCarrier px)))
    subalg !(p :*>: q)        = Carrier (fmap optimise (liftA2 (:*>:)  (unCarrier p)  (unCarrier q)))
    subalg !(p :<*: q)        = Carrier (fmap optimise (liftA2 (:<*:)  (unCarrier p)  (unCarrier q)))
    subalg !(p :<|>: q)       = Carrier (fmap optimise (liftA2 (:<|>:) (unCarrier p)  (unCarrier q)))
    subalg !Empty             = Carrier (return (Op Empty))
    subalg !(Try n p)         = Carrier (fmap optimise (fmap (Try n) (unCarrier p)))
    subalg !(LookAhead p)     = Carrier (fmap optimise (fmap LookAhead (unCarrier p)))
    subalg !(NotFollowedBy p) = Carrier (fmap optimise (fmap NotFollowedBy (unCarrier p)))
    subalg !(Branch b p q)    = Carrier (fmap optimise (liftA3 Branch (unCarrier b) (unCarrier p) (unCarrier q)))
    subalg !(Match p fs qs)   = Carrier (fmap optimise (liftA3 Match (unCarrier p) (return fs) (traverse unCarrier qs)))
    subalg !(ChainPre op p)   = Carrier (liftA2 (\op p -> Op (ChainPre op p)) (unCarrier op) (unCarrier p))
    subalg !(ChainPost p op)  = Carrier (liftA2 (\p op -> Op (ChainPost p op)) (unCarrier p) (unCarrier op))
    subalg !(Debug name p)    = Carrier (fmap (Op . Debug name) (unCarrier p))
    subalg !(Pure x)          = Carrier (return (Op (Pure x)))
    subalg !(Satisfy f)       = Carrier (return (Op (Satisfy f)))

    (><) :: (a -> x) -> (b -> y) -> (a, b) -> (x, y)
    (f >< g) (x, y) = (f x, g y)

optimise :: Parser' (Free Parser' f) xs ks a i -> Free Parser' f xs ks a i
-- DESTRUCTIVE OPTIMISATION
-- Right Absorption Law: empty <*> u = empty
optimise (Op Empty :<*>: _)                           = Op Empty
-- Failure Weakening Law: u <*> empty = u *> empty
optimise (u :<*>: Op Empty)                           = Op (u :*>: Op Empty)
-- Right Absorption Law: empty *> u = empty
optimise (Op Empty :*>: _)                            = Op Empty
-- Right Absorption Law: empty <* u = empty
optimise (Op Empty :<*: _)                            = Op Empty
-- Failure Weakening Law: u <* empty = u *> empty
optimise (u :<*: Op Empty)                            = Op (u :*>: Op Empty)
-- APPLICATIVE OPTIMISATION
-- Homomorphism Law: pure f <*> pure x = pure (f x)
optimise (Op (Pure f) :<*>: Op (Pure x))              = Op (Pure (f >*< x))
-- NOTE: This is basically a shortcut, it can be caught by the Composition Law and Homomorphism law
-- Functor Composition Law: f <$> (g <$> p) = (f . g) <$> p
optimise (Op (Pure f) :<*>: Op (Op (Pure g) :<*>: p)) = optimise (Op (Pure (lift' (.) >*< f >*< g)) :<*>: p)
-- Composition Law: u <*> (v <*> w) = pure (.) <*> u <*> v <*> w
optimise (u :<*>: Op (v :<*>: w))                     = optimise (optimise (optimise (Op (Pure (lift' (.))) :<*>: u) :<*>: v) :<*>: w)
-- Reassociation Law 1: (u *> v) <*> w = u *> (v <*> w)
optimise (Op (u :*>: v) :<*>: w)                      = optimise (u :*>: (optimise (v :<*>: w)))
-- Interchange Law: u <*> pure x = pure ($ x) <*> u
optimise (u :<*>: Op (Pure x))                        = optimise (Op (Pure (lift' flip >*< lift' ($) >*< x)) :<*>: u)
-- Right Absorption Law: (f <$> p) *> q = p *> q
optimise (Op (Op (Pure f) :<*>: p) :*>: q)            = Op (p :*>: q)
-- Left Absorption Law: p <* (f <$> q) = p <* q
optimise (p :<*: (Op (Op (Pure f) :<*>: q)))          = Op (p :<*: q)
-- Reassociation Law 2: u <*> (v <* w) = (u <*> v) <* w
optimise (u :<*>: Op (v :<*: w))                      = optimise (optimise (u :<*>: v) :<*: w)
-- Reassociation Law 3: u <*> (v *> pure x) = (u <*> pure x) <* v
optimise (u :<*>: Op (v :*>: Op (Pure x)))            = optimise (optimise (u :<*>: Op (Pure x)) :<*: v)
-- ALTERNATIVE OPTIMISATION
-- Left Catch Law: pure x <|> u = pure x
optimise (p@(Op (Pure x)) :<|>: _)                    = p
-- Left Neutral Law: empty <|> u = u
optimise (Op Empty :<|>: u)                           = u
-- Right Neutral Law: u <|> empty = u
optimise (u :<|>: Op Empty)                           = u
-- Associativity Law: (u <|> v) <|> w = u <|> (v <|> w)
optimise (Op (u :<|>: v) :<|>: w)                     = Op (u :<|>: optimise (v :<|>: w))
-- SEQUENCING OPTIMISATION
-- Identity law: pure x *> u = u
optimise (Op (Pure _) :*>: u)                         = u
-- Identity law: (u *> pure x) *> v = u *> v
optimise (Op (u :*>: Op (Pure _)) :*>: v)             = Op (u :*>: v)
-- Associativity Law: u *> (v *> w) = (u *> v) *> w
optimise (u :*>: Op (v :*>: w))                       = optimise (optimise (u :*>: v) :*>: w)
-- Identity law: u <* pure x = u
optimise (u :<*: Op (Pure _))                         = u
-- Identity law: u <* (v *> pure x) = u <* v
optimise (u :<*: Op (v :*>: Op (Pure _)))             = optimise (u :<*: v)
-- Commutativity Law: pure x <* u = u *> pure x
optimise (Op (Pure x) :<*: u)                         = optimise (u :*>: Op (Pure x))
-- Associativity Law (u <* v) <* w = u <* (v <* w)
optimise (Op (u :<*: v) :<*: w)                       = optimise (u :<*: optimise (v :<*: w))
-- Pure lookahead: lookAhead (pure x) = pure x
optimise (LookAhead p@(Op (Pure x)))                  = p
-- Dead lookahead: lookAhead empty = empty
optimise (LookAhead p@(Op Empty))                     = p
-- Pure negative-lookahead: notFollowedBy (pure x) = empty
optimise (NotFollowedBy (Op (Pure _)))                = Op Empty
-- Dead negative-lookahead: notFollowedBy empty = unit
optimise (NotFollowedBy (Op Empty))                   = Op (Pure (lift' ()))
-- Double Negation Law: notFollowedBy . notFollowedBy = lookAhead . try . void
optimise (NotFollowedBy (Op (NotFollowedBy p)))       = optimise (LookAhead (Op (Op (Try (constantInput p) p) :*>: Op (Pure (lift' ())))))
-- Zero Consumption Law: notFollowedBy (try p) = notFollowedBy p
optimise (NotFollowedBy (Op (Try _ p)))               = optimise (NotFollowedBy p)
-- Idempotence Law: lookAhead . lookAhead = lookAhead
optimise (LookAhead (Op (LookAhead p)))               = Op (LookAhead p)
-- Right Identity Law: notFollowedBy . lookAhead = notFollowedBy
optimise (NotFollowedBy (Op (LookAhead p)))           = optimise (NotFollowedBy p)
-- Left Identity Law: lookAhead . notFollowedBy = notFollowedBy
optimise (LookAhead (Op (NotFollowedBy p)))           = Op (NotFollowedBy p)
-- Transparency Law: notFollowedBy (try p <|> q) = notFollowedBy p *> notFollowedBy q
optimise (NotFollowedBy (Op (Op (Try _ p) :<|>: q)))  = optimise (optimise (NotFollowedBy p) :*>: optimise (NotFollowedBy q))
-- Distributivity Law: lookAhead p <|> lookAhead q = lookAhead (p <|> q)
optimise (Op (LookAhead p) :<|>: Op (LookAhead q))    = optimise (LookAhead (optimise (p :<|>: q)))
-- Interchange Law: lookAhead (p *> pure x) = lookAhead p *> pure x
optimise (LookAhead (Op (p :*>: Op (Pure x))))        = optimise (optimise (LookAhead p) :*>: Op (Pure x))
-- Interchange law: lookAhead (f <$> p) = f <$> lookAhead p
optimise (LookAhead (Op (Op (Pure f) :<*>: p)))       = optimise (Op (Pure f) :<*>: optimise (LookAhead p))
-- Absorption Law: p <*> notFollowedBy q = (p <*> unit) <* notFollowedBy q
optimise (p :<*>: Op (NotFollowedBy q))               = optimise (optimise (p :<*>: Op (Pure (lift' ()))) :<*: Op (NotFollowedBy q))
-- Idempotence Law: notFollowedBy (p *> pure x) = notFollowedBy p
optimise (NotFollowedBy (Op (p :*>: Op (Pure _))))    = optimise (NotFollowedBy p)
-- Idempotence Law: notFollowedBy (f <$> p) = notFollowedBy p
optimise (NotFollowedBy (Op (Op (Pure _) :<*>: p)))   = optimise (NotFollowedBy p)
-- Interchange Law: try (p *> pure x) = try p *> pure x
optimise (Try n (Op (p :*>: Op (Pure x))))            = optimise (optimise (Try n p) :*>: Op (Pure x))
-- Interchange law: try (f <$> p) = f <$> try p
optimise (Try n (Op (Op (Pure f) :<*>: p)))           = optimise (Op (Pure f) :<*>: optimise (Try n p))
optimise (Try Nothing p)                              = case constantInput p of
                                                          Just 0 -> p
                                                          Just 1 -> p
                                                          ci -> Op (Try ci p)
-- pure Left law: branch (pure (Left x)) p q = p <*> pure x
optimise (Branch (Op (Pure (WQ (Left x) ql))) p _)    = optimise (p :<*>: Op (Pure (WQ x qx))) where qx = [||case $$ql of Left x -> x||]
-- pure Right law: branch (pure (Right x)) p q = q <*> pure x
optimise (Branch (Op (Pure (WQ (Right x) ql))) _ q)   = optimise (q :<*>: Op (Pure (WQ x qx))) where qx = [||case $$ql of Right x -> x||]
-- Generalised Identity law: branch b (pure f) (pure g) = either f g <$> b
optimise (Branch b (Op (Pure f)) (Op (Pure g)))       = optimise (Op (Pure (lift' either >*< f >*< g)) :<*>: b)
-- Interchange law: branch (x *> y) p q = x *> branch y p q
optimise (Branch (Op (x :*>: y)) p q)                 = optimise (x :*>: optimise (Branch y p q))
-- Negated Branch law: branch b p empty = branch (swapEither <$> b) empty p
optimise (Branch b p (Op Empty))                      = Op (Branch (Op (Op (Pure (WQ (either Right Left) [||either Right Left||])) :<*>: b)) (Op Empty) p)
-- Branch Fusion law: branch (branch b empty (pure f)) empty k = branch (g <$> b) empty k where g is a monad transforming (>>= f)
optimise (Branch (Op (Branch b (Op Empty) (Op (Pure (WQ f qf))))) (Op Empty) k) = optimise (Branch (optimise (Op (Pure (WQ g qg)) :<*>: b)) (Op Empty) k)
  where
    g (Left _) = Left ()
    g (Right x) = case f x of
      Left _ -> Left ()
      Right x -> Right x
    qg = [||\case Left _ -> Left ()
                  Right x -> case $$qf x of
                               Left _ -> Left ()
                               Right y -> Right y||]
-- Distributivity Law: f <$> branch b p q = branch b ((f .) <$> p) ((f .) <$> q)
optimise (Op (Pure f) :<*>: Op (Branch b p q))   = optimise (Branch b (optimise (Op (Pure (lift' (.) >*< f)) :<*>: p)) (optimise (Op (Pure (lift' (.) >*< f)) :<*>: q)))
-- pure Match law: match vs (pure x) f = if elem x vs then f x else empty
optimise (Match (Op (Pure (WQ x _))) fs qs) = foldr (\(f, q) k -> if _val f x then q else k) (Op Empty) (zip fs qs)
-- Generalised Identity Match law: match vs p (pure . f) = f <$> (p >?> flip elem vs)
optimise (Match p fs qs)
  | all (\case {Op (Pure _) -> True; _ -> False}) qs = optimise (Op (Pure (WQ apply qapply)) :<*>: (p >?> (WQ validate qvalidate)))
    where apply x    = foldr (\(f, Op (Pure y)) k -> if _val f x then _val y else k) (error "whoopsie") (zip fs qs)
          qapply     = foldr (\(f, Op (Pure y)) k -> [||\x -> if $$(_code f) x then $$(_code y) else $$k x||]) ([||const (error "whoopsie")||]) (zip fs qs)
          validate x = foldr (\f b -> _val f x || b) False fs
          qvalidate  = foldr (\f k -> [||\x -> $$(_code f) x || $$k x||]) [||const False||] fs
          (>?>) :: Free Parser' f xs ks a i -> WQ (a -> Bool) -> Free Parser' f xs ks a i
          p >?> (WQ f qf) = Op (Branch (Op (Op (Pure (WQ g qg)) :<*>: p)) (Op Empty) (Op (Pure (lift' id))))
            where
              g x = if f x then Right x else Left ()
              qg = [||\x -> if $$qf x then Right x else Left ()||]
-- Distributivity Law: f <$> match vs p g = match vs p ((f <$>) . g)
optimise (Op (Pure f) :<*>: (Op (Match p fs qs))) = Op (Match p fs (map (optimise . (Op (Pure f) :<*>:)) qs))
optimise p                                        = Op p

constantInput :: Free Parser' f xs ks a i -> Maybe Int
constantInput = getConst . histo (const (Const Nothing)) (alg1 |> (Const . alg2 . imap present))
  where
    alg1 :: Parser' (History Parser' (Const (Maybe Int))) xs ks a i -> Maybe (Const (Maybe Int) xs ks a i)
    alg1 (Era (Const n) (Try _ _) :<|>: Era (Const q) _) = Just (Const (n <==> q))
    alg1 _ = Nothing
    alg2 :: Parser' (Const (Maybe Int)) xs ks a i -> Maybe Int
    alg2 (Pure _)                               = Just 0
    alg2 (Satisfy _)                            = Just 1
    alg2 (Const p :<*>: Const q)                = p <+> q
    alg2 (Const p :*>: Const q)                 = p <+> q
    alg2 (Const p :<*: Const q)                 = p <+> q
    alg2 Empty                                  = Just 0
    alg2 (Try n _)                              = n
    alg2 (LookAhead (Const p))                  = p
    alg2 (NotFollowedBy (Const p))              = p
    alg2 (Branch (Const b) (Const p) (Const q)) = b <+> (p <==> q)
    alg2 (Match (Const p) _ qs)                 = p <+> (foldr1 (<==>) (map getConst qs))
    alg2 (Debug _ (Const p))                    = p
    alg2 _                                      = Nothing

(<+>) :: (Num a, Monad m) => m a -> m a -> m a
(<+>) = liftA2 (+)
(<==>) :: Eq a => Maybe a -> Maybe a -> Maybe a
(Just x) <==> (Just y)
  | x == y    = Just x
  | otherwise = Nothing
_ <==> _ = Nothing

data Consumption = Some | None | Never
data Prop = Prop {success :: Consumption, fails :: Consumption, indisputable :: Bool} | Unknown
--data InferredTerm = Loops | Safe | Undecidable
newtype Termination xs ks a i = Termination {runTerm :: ReaderT (Set IMVar) (State (Map IMVar Prop)) Prop}
terminationAnalysis :: Free Parser' Void '[] '[] a i -> Free Parser' Void '[] '[] a i
terminationAnalysis p = if not (looping (evalState (runReaderT (runTerm (fold absurd (Termination . alg) p)) Set.empty) Map.empty)) then p
                        else error "Parser will loop indefinitely: either it is left-recursive or iterates over pure computations"
  where
    looping (Prop Never Never _)          = True
    looping _                             = False
    strongLooping (Prop Never Never True) = True
    strongLooping _                       = False
    neverSucceeds (Prop Never _ _)        = True
    neverSucceeds _                       = False
    neverFails (Prop _ Never _)           = True
    neverFails _                          = False

    Never ||| _     = Never
    _     ||| Never = Never
    Some  ||| _     = Some
    None  ||| p     = p

    Some  &&& _    = Some
    _     &&& Some = Some
    None  &&& _    = None
    Never &&& p    = p

    Never ^^^ _     = Never
    _     ^^^ Never = Never
    None  ^^^ _     = None
    Some  ^^^ p     = p

    (==>) :: Prop -> Prop -> Prop
    p ==> _ | neverSucceeds p            = p
    _ ==> Prop Never Never True          = Prop Never Never True
    Prop None _ _ ==> Prop Never Never _ = Prop Never Never False
    Prop s1 f1 b1 ==> Prop s2 f2 b2      = Prop (s1 ||| s2) (f1 &&& (s1 ||| f2)) (b1 && b2)

    branching :: Prop -> [Prop] -> Prop
    branching b ps
      | neverSucceeds b = b
      | any strongLooping ps = Prop Never Never True
    branching (Prop None f _) ps
      | any looping ps = Prop Never Never False
      | otherwise      = Prop (foldr1 (|||) (map success ps)) (f &&& (foldr1 (^^^) (map fails ps))) False
    branching (Prop Some f _) ps = Prop (foldr (|||) Some (map success ps)) f False

    alg :: Parser' Termination ks xs a i -> ReaderT (Set IMVar) (State (Map IMVar Prop)) Prop
    alg (Satisfy _)                          = return $! Prop Some None True
    alg (Pure _)                             = return $! Prop None Never True
    alg Empty                                = return $! Prop Never None True
    alg (Try _ p)                            =
      do x <- runTerm p
         return $! if looping x then x
                   else Prop (success x) None (indisputable x)
    alg (LookAhead p)                        =
      do x <- runTerm p
         return $! if looping x then x
                   else Prop None (fails x) (indisputable x)
    alg (NotFollowedBy p)                    =
      do x <- runTerm p
         return $! if looping x then x
                   else Prop None None True
    alg (p :<*>: q)                          = liftA2 (==>) (runTerm p) (runTerm q)
    alg (p :*>: q)                           = liftA2 (==>) (runTerm p) (runTerm q)
    alg (p :<*: q)                           = liftA2 (==>) (runTerm p) (runTerm q)
    alg (p :<|>: q)                          =
      do x <- runTerm p; case x of
           -- If we fail without consuming input then q governs behaviour
           Prop _ None _       -> runTerm q
           -- If p never fails then q is irrelevant
           x | neverFails x    -> return $! x
           -- If p never succeeds then q governs
           x | neverSucceeds x -> runTerm q
           Prop s1 Some i1     -> do ~(Prop s2 f i2) <- runTerm q; return $! Prop (s1 &&& s2) (Some ||| f) (i1 && i2)
    alg (Branch b p q)                       = liftA2 branching (runTerm b) (sequence [runTerm p, runTerm q])
    alg (Match p _ qs)                       = liftA2 branching (runTerm p) (traverse runTerm qs)
    alg (ChainPre op p)                      =
      do x <- runTerm op; case x of
           -- Never failing implies you must either loop or not consume input
           Prop _ Never _ -> return $! Prop Never Never True
           -- Reaching p can take a route that consumes no input, if op failed
           _ -> do y <- runTerm p
                   return $! if looping y then y
                             else y -- TODO Verify!
    alg (ChainPost p op)                     =
      do y <- runTerm op; case y of
           Prop None _ _ -> return $! Prop Never Never True
           y -> do x <- runTerm p; case (x, y) of
                     (Prop Some f _, Prop _ Never _) -> return $! Prop Some f False
                     (x, y)                          -> return $! Prop (success x) (fails x &&& fails y) False -- TODO Verify
    alg (Rec v p)                            =
      do props <- get
         seen <- ask
         case Map.lookup v props of
           Just prop -> return $! prop
           Nothing | Set.member v seen -> return $! Prop Never Never False
           Nothing -> do prop <- local (Set.insert v) (runTerm p)
                         let prop' = if looping prop then Prop Never Never True else prop
                         put (Map.insert v prop' props)
                         return $! prop'
    alg (Debug _ p)                          = runTerm p
    --alg _                                    = return $! Unknown

type IΦVar = Int
newtype CodeGen b xs ks a i = CodeGen {runCodeGen :: forall xs' ks'. Free M Void (a ': xs') ks' b i
                                                  -> ReaderT (Map IMVar IMVar, IMVar, IΦVar) (State ΣVars) (Free M Void xs' ks' b i)}

compile :: Free Parser' Void '[] '[] a i -> (Free M Void '[] '[] a i, ΣVars)
compile p = let (m, vs) = runState (runReaderT (runCodeGen (histo absurd alg (traceShow p p)) (Op Halt)) (Map.empty, 0, 0)) []
            in traceShow m (m, vs)
  where
    alg = peephole |> (direct . imap present)
    peephole :: Parser' (History Parser' (CodeGen b)) xs ks a i -> Maybe (CodeGen b xs ks a i)
    peephole !(Era _ (Pure f) :<*>: Era p _) = Just $ CodeGen $ \(!m) -> runCodeGen p (fmapInstr f m)
    peephole !(Era _ (Era _ (Pure f) :<*>: Era p _) :<*>: Era q _) = Just $ CodeGen $ \(!m) ->
      do qc <- runCodeGen q (Op (Lift2 f m))
         runCodeGen p qc
    peephole !(Era _ (Try n (Era p _)) :<|>: Era q _) = Just $ CodeGen $ \(!m) ->
      do (_, _, i) <- ask
         let (reg, φ) = case m of
               Op (Join _) -> (Nothing, m)
               m           -> (Just (ΦVar i, m), Op (Join (ΦVar i)))
         pc <- local (trimap id id (+1)) (runCodeGen p (Op (Commit (isJust n) φ)))
         qc <- local (trimap id id (+1)) (runCodeGen q φ)
         return $! Op (SoftFork n pc qc reg)
    peephole !(Era _ (Era _ (Try n (Era p _)) :*>: Era _ (Pure x)) :<|>: Era q _) = Just $ CodeGen $ \(!m) ->
      do (_, _, i) <- ask
         let (reg, φ) = case m of
               Op (Join _) -> (Nothing, m)
               m           -> (Just (ΦVar i, m), Op (Join (ΦVar i)))
         pc <- local (trimap id id (+1)) (runCodeGen p (Op (Commit (isJust n) (Op (Pop (Op (Push x φ)))))))
         qc <- local (trimap id id (+1)) (runCodeGen q φ)
         return $! Op (SoftFork n pc qc reg)
    -- TODO: One more for fmap try
    peephole !(ChainPost (Era _ (Pure x)) (Era op _)) = Just $ CodeGen $ \(!m) ->
      do (_, v, _) <- ask
         σ <- freshΣ (_val x) (_code x)
         opc <- local (trimap id (+1) id) (runCodeGen op (Op (ChainIter σ (MVar v))))
         return $! Op (Push x (Op (ChainInit x σ opc (MVar v) m)))
    peephole _ = Nothing
    direct :: Parser' (CodeGen b) xs ks a i -> CodeGen b xs ks a i
    direct !(Pure x)          = CodeGen $ \(!m) -> do return $! (Op (Push x m))
    direct !(Satisfy p)       = CodeGen $ \(!m) -> do return $! (Op (Sat p m))
    direct !(pf :<*>: px)     = CodeGen $ \(!m) -> do !pxc <- runCodeGen px (Op (Lift2 (lift' ($)) m)); runCodeGen pf pxc
    direct !(p :*>: q)        = CodeGen $ \(!m) -> do !qc <- runCodeGen q m; runCodeGen p (Op (Pop qc))
    direct !(p :<*: q)        = CodeGen $ \(!m) -> do !qc <- runCodeGen q (Op (Pop m)); runCodeGen p qc
    direct !Empty             = CodeGen $ \(!m) -> do return $! Op Empt
    direct !(p :<|>: q)       = CodeGen $ \(!m) ->
      do (_, _, i) <- ask
         let (reg, φ) = case m of
               Op (Join _) -> (Nothing, m)
               m           -> (Just (ΦVar i, m), Op (Join (ΦVar i)))
         pc <- local (trimap id id (+1)) (runCodeGen p (Op (Commit False φ)))
         qc <- local (trimap id id (+1)) (runCodeGen q φ)
         return $! Op (HardFork pc qc reg)
    direct !(Try n p)         = CodeGen $ \(!m) -> do fmap (Op . Attempt n) (runCodeGen p (Op (Commit (isJust n) m)))
    direct !(LookAhead p)     = CodeGen $ \(!m) -> do fmap (Op . Look) (runCodeGen p (Op (Restore m)))
    direct !(NotFollowedBy p) = CodeGen $ \(!m) -> do liftA2 (\p q -> Op (NegLook p q)) (runCodeGen p (Op (Restore (Op Empt)))) (return (Op (Push (lift' ()) m)))
    direct !(Branch b p q)    = CodeGen $ \(!m) -> do !pc <- runCodeGen p (Op (Lift2 (WQ (flip ($)) [||flip ($)||]) m))
                                                      !qc <- runCodeGen q (Op (Lift2 (WQ (flip ($)) [||flip ($)||]) m))
                                                      runCodeGen b (Op (Case pc qc))
    direct !(Match p fs qs)   = CodeGen $ \(!m) -> do !qcs <- traverse (flip runCodeGen m) qs
                                                      runCodeGen p (Op (Choices fs qcs))
    -- NOTE: It is necessary to rename the MVars produced by preprocess
    direct !(Rec !old !q)     = CodeGen $ \(!m) ->
      do (seen, v, _) <- ask
         case Map.lookup old seen of
           Just new -> do return $! Op (MuCall (MVar new) m)
           Nothing  -> do n <- local (trimap (Map.insert old v) (const (v+1)) id) (runCodeGen q (Op Ret))
                          return $! Op (Call n (MVar v) m)
    direct !(ChainPre op p) = CodeGen $ \(!m) ->
      do (_, v, _) <- ask
         σ <- freshΣ id [||id||]
         opc <- local (trimap id (+1) id) (runCodeGen op (fmapInstr (lift' flip >*< lift' (.)) (Op (ChainIter σ (MVar v)))))
         pc <- local (trimap id (+1) id) (runCodeGen p (Op (Lift2 (lift' ($)) m)))
         return $! Op (Push (lift' id) (Op (ChainInit (lift' id) σ opc (MVar v) pc)))
    direct !(ChainPost p op) = CodeGen $ \(!m) ->
      do (_, v, _) <- ask
         σ <- freshΣ Nothing [||Nothing||]
         opc <- local (trimap id (+1) id) (runCodeGen op (fmapInstr (lift' (<$!>)) (Op (ChainIter σ (MVar v)))))
         let m' = Op (ChainInit (WQ Nothing [||Nothing||]) σ opc (MVar v) (fmapInstr (lift' fromJust) m))
         local (trimap id (+1) id) (runCodeGen p (fmapInstr (lift' Just) m'))
    direct !(Debug name p) = CodeGen $ \(!m) -> fmap (Op . LogEnter name) (runCodeGen p (Op (LogExit name m)))

    trimap :: (a -> x) -> (b -> y) -> (c -> z) -> (a, b, c) -> (x, y, z)
    trimap f g h (x, y, z) = (f x, g y, h z)

    freshΣ :: MonadState ΣVars m => a -> TExpQ a -> m (ΣVar a)
    freshΣ x qx = do σs <- get
                     let σ = nextΣ σs
                     put (State x qx σ:σs)
                     return $! σ
      where
        nextΣ []                     = ΣVar 0
        nextΣ (State _ _ (ΣVar x):_) = ΣVar (x+1)

pipeline :: Parser a -> (Free M Void '[] '[] a (), ΣVars)
pipeline = compile . terminationAnalysis . preprocess . unParser