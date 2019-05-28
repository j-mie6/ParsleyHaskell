{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MagicHash, UnboxedTuples #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor, DeriveLift #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase, MultiWayIf #-}
{-# LANGUAGE EmptyCase #-}
module Parsley {-( Parser--, CompiledParser
               , runParser--, mkParser, runCompiledParser
               -- Functor
               , fmap, (<$>), (<$), ($>), (<&>), void
               -- Applicative
               , pure, (<*>), (*>), (<*), (<**>), (<:>), liftA2
               -- Alternative
               , empty, (<|>), some, many, optional, choice
               -- Monoidal
               , {-Monoidal,-} unit, (<~>), (<~), (~>)
               -- Monadic
               , return, (>>=), (>>), mzero, mplus, join
               -- Primitives
               , satisfy, item
               , lookAhead, {-notFollowedBy,-} try
               -- Composites
               , char, {-eof,-} more
               --, traverse, sequence, string--, manyUnrolled
               , eval, runST, compile, preprocess
               )-} where

import Prelude hiding             (fmap, pure, (<*), (*>), (<*>), (<$>), (<$))
import qualified Data.Functor as Functor
import qualified Control.Applicative as Applicative
import Control.Monad              (MonadPlus, mzero, mplus, liftM, liftM2, liftM3, join, (<$!>), forM)
import GHC.ST                     (ST(..), runST)
import Control.Monad.ST.Unsafe    (unsafeIOToST)
import Control.Monad.Reader       (ReaderT, ask, runReaderT, Reader, runReader, local)
import Control.Monad.State.Strict (State, get, put, runState, evalState, MonadState)
import qualified Control.Monad.Reader as Reader
import Data.STRef                 (STRef, writeSTRef, readSTRef, modifySTRef', newSTRef)
import System.IO.Unsafe           (unsafePerformIO)
import Data.IORef                 (IORef, writeIORef, readIORef, newIORef)
import Data.Array                 (Array, array)
import GHC.StableName             (StableName(..), makeStableName, hashStableName, eqStableName)
import Data.Hashable              (Hashable, hashWithSalt, hash)
import Data.HashMap.Lazy          (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Map.Strict            (Map)
import qualified Data.Map.Strict as Map
import Data.Set                   (Set)
import qualified Data.Set as Set
import Data.Dependent.Map         (DMap)
import Data.GADT.Compare          (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))
import qualified Data.Dependent.Map as DMap
import Data.Array.Unboxed         (listArray)
import Data.Array.Base            (STUArray(..), UArray(..), unsafeAt, newArray_, unsafeRead, unsafeWrite, MArray, getNumElements, numElements, ixmap, elems)
import GHC.Prim                   (Int#, Char#, StableName#, newByteArray#, indexWideCharArray#)
import GHC.Exts                   (Int(..), Char(..), (-#), (+#), (*#))
import Unsafe.Coerce              (unsafeCoerce)
import Safe.Coerce                (coerce)
import Data.Maybe                 (isJust, fromMaybe, fromJust)
import Data.List                  (foldl')
import Language.Haskell.TH hiding (Match, match)
import Language.Haskell.TH.Syntax hiding (Match, match)
import Debug.Trace
import System.Console.Pretty      (color, Color(Green, White, Red, Blue))
import LiftPlugin

isDigit :: Char -> Bool
isDigit c
  |    c == '0' || c == '1' || c == '2' || c == '3'
    || c == '4' || c == '5' || c == '6' || c == '7'
    || c == '8' || c == '9' = True
  | otherwise = False

toDigit :: Char -> Int
toDigit c = fromEnum c - fromEnum '0'

digit :: Parser Int
digit = lift' toDigit <$> satisfy (lift' isDigit)

greaterThan5 :: Int -> Bool
greaterThan5 = (> 5)

plus :: Parser (Int -> Int -> Int)
plus = char '+' $> lift' (+)

selectTest :: Parser (Either Int String)
selectTest = Parsley.pure (lift' (Left 10))

showi :: Int -> String
showi = show

data Pred' = And Pred' Pred' | Not Pred' | T | F deriving Lift
pred :: Parser Pred'
pred = chainr1 term (lift' And <$ token "&&")
  where
    term :: Parser Pred'
    term = chainPre (lift' Not <$ token "!") atom
    atom :: Parser Pred'
    atom = (lift' T <$ token "t")
       <|> (lift' F <$ token "f")

instance Pure WQ where lift' x = WQ x [||x||]

-- AST
newtype Parser a = Parser {unParser :: Free Parser' Void '[] '[] a ()}
data WQ a = WQ { _val :: a, _code :: TExpQ a }
type IMVar = Int
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
instance {-# OVERLAPPABLE #-} Chain a a         where (|>) = liftM2 (flip fromMaybe)
instance {-# OVERLAPS #-}     Chain a (Maybe a) where (|>) = liftM2 (Applicative.<|>)

data Unit i j k l = Unit
data Void i j k l
absurd :: Void i j k l -> b
absurd = \case
data Const a i j k l = Const {getConst :: a}

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

fmap :: WQ (a -> b) -> Parser a -> Parser b
fmap f = (pure f <*>)

(<$>) :: WQ (a -> b) -> Parser a -> Parser b
(<$>) = fmap

void :: Parser a -> Parser ()
void p = p *> unit

(<$) :: WQ b -> Parser a -> Parser b
x <$ p = p *> pure x

($>) :: Parser a -> WQ b -> Parser b
($>) = flip (<$)

(<&>) :: Parser a -> WQ (a -> b) -> Parser b
(<&>) = flip fmap

pure :: WQ a -> Parser a
pure = Parser . Op . Pure

(<*>) :: Parser (a -> b) -> Parser a -> Parser b
Parser p <*> Parser q = Parser (Op (p :<*>: q))

(<*) :: Parser a -> Parser b -> Parser a
Parser p <* Parser q = Parser (Op (p :<*: q))

(*>) :: Parser a -> Parser b -> Parser b
Parser p *> Parser q = Parser (Op (p :*>: q))

liftA2 :: WQ (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftA2 f p q = f <$> p <*> q

empty :: Parser a
empty = Parser (Op Empty)

(<|>) :: Parser a -> Parser a -> Parser a
Parser p <|> Parser q = Parser (Op (p :<|>: q))

many :: Parser a -> Parser [a]
many p = pfoldr (lift' (:)) (WQ [] [||[]||]) p

some :: Parser a -> Parser [a]
some p = p <:> many p

skipMany :: Parser a -> Parser ()
skipMany = pfoldr (lift' const >*< lift' id) (lift' ())

-- Additional Combinators
(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = liftA2 (lift' (:))

(<**>) :: Parser a -> Parser (a -> b) -> Parser b
(<**>) = liftA2 (WQ (flip ($)) [|| (flip ($)) ||])

unit :: Parser ()
unit = pure (lift' ())

(<~>) :: Parser a -> Parser b -> Parser (a, b)
(<~>) = liftA2 (lift' (,))

(<~) :: Parser a -> Parser b -> Parser a
(<~) = (<*)

(~>) :: Parser a -> Parser b -> Parser b
(~>) = (*>)

  -- Auxillary functions
string :: String -> Parser String
string = foldr (<:>) (pure (lift' [])) . map char

token :: String -> Parser String
token = try . string

eof :: Parser ()
eof = notFollowedBy item

more :: Parser ()
more = lookAhead (void item)

-- Parsing Primitives
satisfy :: WQ (Char -> Bool) -> Parser Char
satisfy = Parser . Op . Satisfy

lookAhead :: Parser a -> Parser a
lookAhead = Parser . Op . LookAhead . unParser

notFollowedBy :: Parser a -> Parser ()
notFollowedBy = Parser . Op . NotFollowedBy . unParser

try :: Parser a -> Parser a
try = Parser . Op . Try Nothing . unParser

char :: Char -> Parser Char
char c = lift' c <$ satisfy (WQ (== c) [||(== c)||])

item :: Parser Char
item = satisfy (WQ (const True) [|| const True ||])

optional :: Parser a -> Parser ()
optional p = void p <|> unit

choice :: [Parser a] -> Parser a
choice = foldr (<|>) empty

bool :: a -> a -> Bool -> a
bool x y True  = x
bool x y False = y

constp :: Parser a -> Parser (b -> a)
constp = (lift' const <$>)

(<?|>) :: Parser Bool -> (Parser a, Parser a) -> Parser a
cond <?|> (p, q) = branch (WQ (bool (Left ()) (Right ())) [||bool (Left ()) (Right ())||] <$> cond) (constp p) (constp q)

(>?>) :: Parser a -> WQ (a -> Bool) -> Parser a
p >?> (WQ f qf) = select (WQ g qg <$> p) empty
  where
    g x = if f x then Right x else Left ()
    qg = [||\x -> if $$qf x then Right x else Left ()||]

match :: (Eq a, Lift a) => [a] -> Parser a -> (a -> Parser b) -> Parser b
match vs (Parser p) f = Parser (Op (Match p (map (\v -> WQ (== v) [||(== v)||]) vs) (map (unParser . f) vs)))

(||=) :: forall a b. (Enum a, Bounded a, Eq a, Lift a) => Parser a -> (a -> Parser b) -> Parser b
p ||= f = match [minBound..maxBound] p f

branch :: Parser (Either a b) -> Parser (a -> c) -> Parser (b -> c) -> Parser c
branch (Parser c) (Parser p) (Parser q) = Parser (Op (Branch c p q))

when :: Parser Bool -> Parser () -> Parser ()
when p q = p <?|> (q, unit)

while :: Parser Bool -> Parser ()
while x = fix (when x)

select :: Parser (Either a b) -> Parser (a -> b) -> Parser b
select p q = branch p q (pure (lift' id))

fromMaybeP :: Parser (Maybe a) -> Parser a -> Parser a
fromMaybeP pm px = select (WQ (maybe (Left ()) Right) [||maybe (Left ()) Right||] <$> pm) (constp px)

chainl1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainl1 p op = chainPost p (lift' flip <$> op <*> p)

chainr1 :: Parser a -> Parser (a -> a -> a) -> Parser a
chainr1 p op = let go = p <**> ((lift' flip <$> op <*> go) <|> pure (lift' id)) in go

pfoldr :: WQ (a -> b -> b) -> WQ b -> Parser a -> Parser b
pfoldr f k p = chainPre (f <$> p) (pure k)

pfoldl :: WQ (b -> a -> b) -> WQ b -> Parser a -> Parser b
pfoldl f k p = chainPost (pure k) (lift' flip >*< f <$> p)

chainPre :: Parser (a -> a) -> Parser a -> Parser a
chainPre (Parser op) (Parser p) = Parser (Op (ChainPre op p))

chainPost :: Parser a -> Parser (a -> a) -> Parser a
chainPost (Parser p) (Parser op) = Parser (Op (ChainPost p op))

debug :: String -> Parser a -> Parser a
debug name (Parser p) = Parser (Op (Debug name p))

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
      (StableName _name) <- Reader.lift (makeStableName p)
      let !name = StableParserName _name
      case HashMap.lookup name seen of
        Just (v', GenParser q, used) -> do Reader.lift (writeIORef used True)
                                           return $! (Op (Rec v' (coerce q)))
        Nothing -> mdo usedVar <- Reader.lift (newIORef False)
                       q' <- local (HashMap.insert name (v, GenParser q', usedVar) >< (+1)) (unCarrier $ subalg q)
                       used <- Reader.lift (readIORef usedVar)
                       if used then return $! (Op (Rec v q'))
                       else         return $! q'
    subalg :: Parser' Carrier xs ks a i -> Carrier xs ks a i
    subalg !(pf :<*>: px)     = Carrier (liftM optimise (liftM2 (:<*>:) (unCarrier pf) (unCarrier px)))
    subalg !(p :*>: q)        = Carrier (liftM optimise (liftM2 (:*>:)  (unCarrier p)  (unCarrier q)))
    subalg !(p :<*: q)        = Carrier (liftM optimise (liftM2 (:<*:)  (unCarrier p)  (unCarrier q)))
    subalg !(p :<|>: q)       = Carrier (liftM optimise (liftM2 (:<|>:) (unCarrier p)  (unCarrier q)))
    subalg !Empty             = Carrier (return (Op Empty))
    subalg !(Try n p)         = Carrier (liftM optimise (liftM (Try n) (unCarrier p)))
    subalg !(LookAhead p)     = Carrier (liftM optimise (liftM LookAhead (unCarrier p)))
    subalg !(NotFollowedBy p) = Carrier (liftM optimise (liftM NotFollowedBy (unCarrier p)))
    subalg !(Branch b p q)    = Carrier (liftM optimise (liftM3 Branch (unCarrier b) (unCarrier p) (unCarrier q)))
    subalg !(Match p fs qs)   = Carrier (liftM optimise (liftM3 Match (unCarrier p) (return fs) (traverse unCarrier qs)))
    subalg !(ChainPre op p)   = Carrier (liftM2 (\op p -> Op (ChainPre op p)) (unCarrier op) (unCarrier p))
    subalg !(ChainPost p op)  = Carrier (liftM2 (\p op -> Op (ChainPost p op)) (unCarrier p) (unCarrier op))
    subalg !(Debug name p)    = Carrier (liftM (Op . Debug name) (unCarrier p))
    subalg !(Pure x)          = Carrier (return (Op (Pure x)))
    subalg !(Satisfy f)       = Carrier (return (Op (Satisfy f)))

    (><) :: (a -> x) -> (b -> y) -> (a, b) -> (x, y)
    (f >< g) (x, y) = (f x, g y)

-- pronounced quapp
(>*<) :: WQ (a -> b) -> WQ a -> WQ b
WQ f qf >*< WQ x qx = WQ (f x) [||$$qf $$qx||]
infixl 9 >*<

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
(<+>) = liftM2 (+)
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
    alg (p :<*>: q)                          = liftM2 (==>) (runTerm p) (runTerm q)
    alg (p :*>: q)                           = liftM2 (==>) (runTerm p) (runTerm q)
    alg (p :<*: q)                           = liftM2 (==>) (runTerm p) (runTerm q)
    alg (p :<|>: q)                          =
      do x <- runTerm p; case x of
           -- If we fail without consuming input then q governs behaviour
           Prop _ None _       -> runTerm q
           -- If p never fails then q is irrelevant
           x | neverFails x    -> return $! x
           -- If p never succeeds then q governs
           x | neverSucceeds x -> runTerm q
           Prop s1 Some i1     -> do ~(Prop s2 f i2) <- runTerm q; return $! Prop (s1 &&& s2) (Some ||| f) (i1 && i2)
    alg (Branch b p q)                       = liftM2 branching (runTerm b) (sequence [runTerm p, runTerm q])
    alg (Match p _ qs)                       = liftM2 branching (runTerm p) (traverse runTerm qs)
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

newtype ΣVar a = ΣVar Int
newtype MVar xs ks a = MVar Int
newtype ΦVar a = ΦVar Int
data M k xs ks a i where
  Halt      :: M k '[a] ks a i
  Ret       :: M k (b ': xs) ((b ': xs) ': ks) a i
  Push      :: WQ x -> !(k (x ': xs) ks a i) -> M k xs ks a i
  Pop       :: !(k xs ks a i) -> M k (b ': xs) ks a i
  Lift2     :: !(WQ (x -> y -> z)) -> !(k (z ': xs) ks a i) -> M k (y ': x ': xs) ks a i
  Sat       :: WQ (Char -> Bool) -> !(k (Char ': xs) ks a i) -> M k xs ks a i
  Call      :: k xs ((b ': xs) ': ks) a i -> MVar xs ((b ': xs) ': ks) a -> !(k (b ': xs) ks a i) -> M k xs ks a i
  MuCall    :: MVar xs ((b ': xs) ': ks) a -> !(k (b ': xs) ks a i) -> M k xs ks a i
  Empt      :: M k xs ks a i
  Commit    :: !Bool -> !(k xs ks a i) -> M k xs ks a i
  HardFork  :: !(k xs ks a i) -> !(k xs ks a i) -> !(Maybe (ΦVar x, k (x ': xs) ks a i)) -> M k xs ks a i
  SoftFork  :: !(Maybe Int) -> !(k xs ks a i) -> !(k xs ks a i) -> !(Maybe (ΦVar x, k (x ': xs) ks a i)) -> M k xs ks a i
  Join      :: !(ΦVar x) -> M k (x ': xs) ks a i
  Attempt   :: !(Maybe Int) -> !(k xs ks a i) -> M k xs ks a i
  Look      :: !(k xs ks a i) -> M k xs ks a i
  NegLook   :: !(k xs ks a i) -> !(k xs ks a i) -> M k xs ks a i
  Restore   :: !(k xs ks a i) -> M k xs ks a i
  Case      :: !(k (x ': xs) ks a i) -> !(k (y ': xs) ks a i) -> M k (Either x y ': xs) ks a i
  Choices   :: ![WQ (x -> Bool)] -> ![k xs ks a i] -> M k (x ': xs) ks a i
  ChainIter :: !(ΣVar x) -> !(MVar xs ks a) -> M k ((x -> x) ': xs) ks a i
  ChainInit :: !(WQ x) -> !(ΣVar x) -> !(k xs ks a i) -> !(MVar xs ks a) -> k (x ': xs) ks a i -> M k (x ': xs) ks a i
  LogEnter  :: String -> !(k xs ks a i) -> M k xs ks a i
  LogExit   :: String -> !(k xs ks a i) -> M k xs ks a i

fmapInstr :: WQ (x -> y) -> Free M f (y ': xs) ks a i -> Free M f (x ': xs) ks a i
fmapInstr !f !m = Op (Push f (Op (Lift2 (lift' flip >*< lift' ($)) m)))

instance IFunctor M where
  imap f Halt = Halt
  imap f Ret = Ret
  imap f (Push x k) = Push x (f k)
  imap f (Pop k) = Pop (f k)
  imap f (Lift2 g k) = Lift2 g (f k)
  imap f (Sat g k) = Sat g (f k)
  imap f (Call m v k) = Call (f m) v (f k)
  imap f (MuCall v k) = MuCall v (f k)
  imap f Empt = Empt
  imap f (Commit exit k) = Commit exit (f k)
  imap f (SoftFork n p q (Just (φ, k))) = SoftFork n (f p) (f q) (Just (φ, f k))
  imap f (SoftFork n p q Nothing) = SoftFork n (f p) (f q) Nothing
  imap f (HardFork p q (Just (φ, k))) = HardFork (f p) (f q) (Just (φ, f k))
  imap f (HardFork p q Nothing) = HardFork (f p) (f q) Nothing
  imap f (Join φ) = Join φ
  imap f (Attempt n k) = Attempt n (f k)
  imap f (Look k) = Look (f k)
  imap f (NegLook m k) = NegLook (f m) (f k)
  imap f (Restore k) = Restore (f k)
  imap f (Case p q) = Case (f p) (f q)
  imap f (Choices fs ks) = Choices fs (map f ks)
  imap f (ChainIter σ v) = ChainIter σ v
  imap f (ChainInit x σ l v k) = ChainInit x σ (f l) v (f k)
  imap f (LogEnter name k) = LogEnter name (f k)
  imap f (LogExit name k) = LogExit name (f k)

instance Show (Free M f xs ks a i) where
  show = getConst . fold (const (Const "")) (Const . alg) where
    alg :: forall i j k l. M (Const String) i j k l -> String
    alg Halt = "Halt"
    alg Ret = "Ret"
    alg (Call m (MVar v) k) = "{Call μ" ++ show v ++ " " ++ getConst m ++ " " ++ getConst k ++ "}"
    alg (MuCall (MVar v) k) = "(μCall μ" ++ show v ++ " " ++ getConst k ++ ")"
    alg (Push _ k) = "(Push x " ++ getConst k ++ ")"
    alg (Pop k) = "(Pop " ++ getConst k ++ ")"
    alg (Lift2 _ k) = "(Lift2 f " ++ getConst k ++ ")"
    alg (Sat _ k) = "(Sat f " ++ getConst k ++ ")"
    alg Empt = "Empt"
    alg (Commit True k) = "(Commit end " ++ getConst k ++ ")"
    alg (Commit False k) = "(Commit " ++ getConst k ++ ")"
    alg (SoftFork Nothing p q Nothing) = "(SoftFork " ++ getConst p ++ " " ++ getConst q ++ ")"
    alg (SoftFork (Just n) p q Nothing) = "(SoftFork " ++ show n ++ " " ++ getConst p ++ " " ++ getConst q ++ ")"
    alg (SoftFork Nothing p q (Just (ΦVar φ, k))) = "(SoftFork " ++ getConst p ++ " " ++ getConst q ++ " (φ" ++ show φ ++ " = " ++ getConst k ++ "))"
    alg (SoftFork (Just n) p q (Just (ΦVar φ, k))) = "(SoftFork " ++ show n ++ " " ++ getConst p ++ " " ++ getConst q ++ " (φ" ++ show φ ++ " = " ++ getConst k ++ "))"
    alg (HardFork p q Nothing) = "(HardFork " ++ getConst p ++ " " ++ getConst q ++ ")"
    alg (HardFork p q (Just (ΦVar φ, k))) = "(HardFork " ++ getConst p ++ " " ++ getConst q ++ " (φ" ++ show φ ++ " = " ++ getConst k ++ "))"
    alg (Join (ΦVar φ)) = "φ" ++ show φ
    alg (Attempt Nothing k) = "(Try " ++ getConst k ++ ")"
    alg (Attempt (Just n) k) = "(Try " ++ show n ++ " " ++ getConst k ++ ")"
    alg (Look k) = "(Look " ++ getConst k ++ ")"
    alg (NegLook m k) = "(NegLook " ++ getConst m ++ " " ++ getConst k ++ ")"
    alg (Restore k) = "(Restore " ++ getConst k ++ ")"
    alg (Case m k) = "(Case " ++ getConst m ++ " " ++ getConst k ++ ")"
    alg (Choices _ ks) = "(Choices " ++ show (map getConst ks) ++ ")"
    alg (ChainIter (ΣVar σ) (MVar v)) = "(ChainIter σ" ++ show σ ++ " μ" ++ show v ++ ")"
    alg (ChainInit _ (ΣVar σ) m (MVar v) k) = "{ChainInit σ" ++ show σ ++ " μ" ++ show v ++ " " ++ getConst m ++ " " ++ getConst k ++ "}"
    alg (LogEnter _ k) = getConst k
    alg (LogExit _ k) = getConst k

data ΣState = forall a. State !a !(TExpQ a) !(ΣVar a)
type ΣVars = [ΣState]
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
    direct !(Try n p)         = CodeGen $ \(!m) -> do liftM (Op . Attempt n) (runCodeGen p (Op (Commit (isJust n) m)))
    direct !(LookAhead p)     = CodeGen $ \(!m) -> do liftM (Op . Look) (runCodeGen p (Op (Restore m)))
    direct !(NotFollowedBy p) = CodeGen $ \(!m) -> do liftM2 (\p q -> Op (NegLook p q)) (runCodeGen p (Op (Restore (Op Empt)))) (return (Op (Push (lift' ()) m)))
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
    direct !(Debug name p) = CodeGen $ \(!m) -> liftM (Op . LogEnter name) (runCodeGen p (Op (LogExit name m)))

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

data SList a = !a ::: !(SList a) | SNil
data HList xs where
  HNil :: HList '[]
  HCons :: a -> !(HList as) -> HList (a ': as)
data K s ks a where
  KNil :: K s '[] a
  KCons :: !(X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)) -> !(K s ks a) -> K s (xs ': ks) a

instance Show (K s ks a) where
  show KNil = "KNil"
  show (KCons _ ks) = "(KCons " ++ show ks ++ ")"

newtype H s a = H (SList (O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)))
type QH s a = TExpQ (H s a)
type X = HList
type QX xs = TExpQ (X xs)
type QK s ks a = TExpQ (K s ks a)
type CIdx = Int
type CIdx# = Int#
type QCIdx = TExpQ CIdx
type C s = STUArray s Int Int
type QC s = TExpQ (C s)
type O = Int
type O# = Int#
type QO = TExpQ O
type D = Int
type D# = Int#
type QD = TExpQ D
type QST s a = TExpQ (ST s a)
newtype QSTRef s a = QSTRef (TExpQ (STRef s (SList a)))

data Γ s xs ks a = Γ { xs    :: QX xs
                     , ks    :: QK s ks a
                     , o     :: QO
                     , hs    :: QH s a
                     , cidx  :: QCIdx
                     , cs    :: QC s
                     , d     :: QD }

bug :: a -> b
bug = coerce

double :: STUArray s Int Int -> ST s (STUArray s Int Int)
double !arr =
  do !sz <- getNumElements arr
     resize arr sz (sz * 2)

resize :: STUArray s Int Int -> Int -> Int -> ST s (STUArray s Int Int)
resize arr old (I# new) =
  do !arr' <- ST (\s -> case newByteArray# (new *# 8#) s of (# s', arr'# #) -> (# s', STUArray 0 ((I# new)-1) (I# new) arr'# #))
     let copy !from !to !n = do !x <- unsafeRead from n
                                unsafeWrite to n x
                                if n == 0 then return $! ()
                                else copy from to $! (n-1)
                             in copy arr arr' $! (old-1)
     return $! arr'

makeX :: ST s (X '[])
makeX = return $! HNil
{-# INLINE pushX #-}
pushX :: a -> X xs -> X (a ': xs)
pushX = HCons
{-# INLINE popX #-}
popX :: X (a ': xs) -> (a, X xs)
popX (HCons x xs) = (x, xs)
{-# INLINE popX_ #-}
popX_ :: X (a ': xs) -> X xs
popX_ (HCons x xs) = xs
{-# INLINE pokeX #-}
pokeX :: a -> X (a ': xs) -> X (a ': xs)
pokeX y (HCons x xs) = HCons y xs
{-# INLINE modX #-}
modX :: (a -> b) -> X (a ': xs) -> X (b ': xs)
modX f (HCons x xs) = HCons (f x) xs
{-# INLINE peekX #-}
peekX :: X (a ': xs) -> a
peekX (HCons x xs) = x

makeK :: ST s (K s '[] a)
makeK = return $! KNil
suspend :: Exec s xs ks a i -> Ctx s a -> QK s ks a -> QK s (xs ': ks) a
suspend m ctx ks =
  [|| KCons (\xs ks o hs cidx cs d ->
    $$(run m (Γ[||xs||] [||ks||] [||I# o||] [||hs||] [||I# cidx||] [||cs||] [||I# d||]) ctx)) $$ks ||]
resume :: Γ s xs (xs ': ks) a -> QST s (Maybe a)
resume (Γ xs ks o hs cidx cs d) =
  [|| let ks' = bug ($$ks) :: K s (xs ': ks) a
          I# o# = $$o
          I# cidx# = $$cidx
          I# d# = $$d
      in
        case ks' of
          (KCons k ks) -> k $$(bug xs) ks o# $$hs cidx# $$cs d#
  ||]

makeH :: ST s (H s a)
makeH = return $! (H SNil)
pushH :: (O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)) -> H s a -> H s a
pushH !h !(H hs) = H (h:::hs)
{-# INLINE popH_ #-}
popH_ :: H s a -> H s a
popH_ !(H (_:::hs)) = H hs

makeC :: ST s (CIdx, C s)
makeC = do cs <- newArray_ (0, 3)
           return $! (-1, cs)
{-# INLINE pushC #-}
pushC :: O -> CIdx -> C s -> ST s (CIdx, C s)
pushC c i !cs = let !j = i + 1 in
  do sz <- getNumElements cs
     if j == sz then do !cs' <- double cs
                        unsafeWrite cs' j c
                        return $! (j, cs')
     else do unsafeWrite cs j c; return $! (j, cs)
popC :: CIdx -> C s -> ST s (O, CIdx)
popC !i !cs = do !c <- unsafeRead cs i; return $! (c, i - 1)
{-# INLINE popC_ #-}
popC_ :: CIdx -> CIdx
popC_ !i = i - 1
pokeC :: O -> CIdx -> C s -> ST s ()
pokeC !c !i !cs = unsafeWrite cs i c

-- TODO Convert Input into a pair of getChar and inputSize, stored statically in the context
nextSafe :: Bool -> Input -> QO -> TExpQ (Char -> Bool) -> (QO -> TExpQ Char -> QST s (Maybe a)) -> QST s (Maybe a) -> QST s (Maybe a)
nextSafe True input o p good bad = [|| let !c = $$(charAt input) $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else $$bad ||]
nextSafe False input o p good bad = [||
    let bad' = $$bad in
      if  $$(size input) > $$o then let !c = $$(charAt input) $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else bad'
      else bad'
  ||]

instance GEq ΣVar where
  geq (ΣVar u) (ΣVar v)
    | u == v    = Just (coerce Refl)
    | otherwise = Nothing

instance GCompare ΣVar where
  gcompare (ΣVar u) (ΣVar v) = case compare u v of
    LT -> coerce GLT
    EQ -> coerce GEQ
    GT -> coerce GGT

instance GEq ΦVar where
  geq (ΦVar u) (ΦVar v)
    | u == v    = Just (coerce Refl)
    | otherwise = Nothing

instance GCompare ΦVar where
  gcompare (ΦVar u) (ΦVar v) = case compare u v of
    LT -> coerce GLT
    EQ -> coerce GEQ
    GT -> coerce GGT

makeΣ :: ΣVars -> (DMap ΣVar (QSTRef s) -> Σ s -> QST s r) -> QST s r
makeΣ ps = makeΣ' ps (DMap.empty) [|| return () ||] [|| return () ||] [|| const (return ()) ||]
  where
    makeΣ' :: ΣVars -> DMap ΣVar (QSTRef s) -> QST s () -> QST s () -> TExpQ (D -> ST s ()) -> (DMap ΣVar (QSTRef s) -> Σ s -> QST s r) -> QST s r
    makeΣ' [] m save restore rollback k =
      [|| let save' = $$save
              restore' = $$restore
              rollback' n = if n == 0 then return () else $$rollback n
          in $$(let !σs = Σ [||save'||] [||restore'||] [||rollback'||] in k m σs) ||]
    makeΣ' (State x qx (ΣVar v):ps) m save restore rollback k = [||
      do σ <- newSTRef ($$qx:::SNil)
         $$(let save' = [|| do modifySTRef' σ ($$qx:::); $$save ||]
                restore' = [|| do modifySTRef' σ (\(_:::xs) -> xs); $$restore ||]
                rollback' = [||\n -> do modifySTRef' σ (sdrop n); $$rollback n ||]
                m' = DMap.insert (ΣVar v) (QSTRef [|| σ ||]) m
            in makeΣ' ps m' save' restore' rollback' k)
      ||]

modifyΣ :: STRef s (SList a) -> (a -> a) -> ST s ()
modifyΣ σ f =
  do (x:::xs) <- readSTRef σ
     writeSTRef σ ((f $! x) ::: xs)

writeΣ :: STRef s (SList a) -> a -> ST s ()
writeΣ σ = modifyΣ σ . const

readΣ :: STRef s (SList a) -> ST s a
readΣ σ =
  do (x:::_) <- readSTRef σ
     return $! x

pokeΣ :: STRef s (SList a) -> a -> ST s a
pokeΣ σ y =
  do (x:::xs) <- readSTRef σ
     writeSTRef σ (y:::xs)
     return $! x

sdrop :: Int -> SList a -> SList a
sdrop 0 xs = xs
sdrop n (_ ::: xs) = sdrop (n-1) xs

data GenExec s a = forall xs ks. GenExec (TExpQ (X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)))
newtype GenJoin s a x = GenJoin (TExpQ (x -> O# -> ST s (Maybe a)))
data Input = Input {charAt :: TExpQ (Int -> Char), size :: TExpQ Int, substr :: TExpQ (Int -> Int -> UArray Int Char)}
data Σ s = Σ { save :: QST s (), restore :: QST s (), rollback :: TExpQ (D -> ST s ()) }
data Ctx s a = Ctx {μs         :: Map IMVar (GenExec s a),
                    φs         :: DMap ΦVar (GenJoin s a),
                    σm         :: DMap ΣVar (QSTRef s),
                    σs         :: {-# UNPACK #-} !(Σ s),
                    input      :: {-# UNPACK #-} !Input,
                    constCount :: Int,
                    debugLevel :: Int}

addConstCount :: Int -> Ctx s a -> Ctx s a
addConstCount x ctx = ctx {constCount = constCount ctx + x}

skipBounds :: Ctx s a -> Bool
skipBounds ctx = constCount ctx > 0

debugUp :: Ctx s a -> Ctx s a
debugUp ctx = ctx {debugLevel = debugLevel ctx + 1}

debugDown :: Ctx s a -> Ctx s a
debugDown ctx = ctx {debugLevel = debugLevel ctx - 1}


newtype Exec s xs ks a i = Exec (Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a)))
run :: Exec s xs ks a i -> Γ s xs ks a -> (Ctx s a) -> QST s (Maybe a)
run (Exec m) γ ctx = runReader (m γ) ctx

exec :: TExpQ String -> (Free M Void '[] '[] a i, ΣVars) -> QST s (Maybe a)
exec input (!m, vss) = [||
  do xs <- makeX
     ks <- makeK
     hs <- makeH
     !(cidx, cs) <- makeC
     let !(UArray _ _ size input#) = $$(toArray input)
     let charAt (I# i#) = C# (indexWideCharArray# input# i#)
     let substr i j = ixmap (i, j) id (UArray 0 (size - 1) size input#) :: UArray Int Char
     $$(makeΣ vss (\σm σs ->
       run (fold absurd alg m) (Γ [||xs||] [||ks||] [||0||] [||hs||] [||cidx||] [||cs||] [||0||])
                               (Ctx Map.empty DMap.empty σm 0 0 σs (Input [||charAt||] [||size||] [||substr||]))))
  ||]
  where
    toArray :: TExpQ String -> TExpQ (UArray Int Char)
    toArray input = [|| listArray (0, length $$input-1) $$input ||]

    alg :: M (Exec s) xs ks a i -> Exec s xs ks a i
    alg Halt                  = Exec $ execHalt
    alg Ret                   = Exec $ execRet
    alg (Call m v k)          = Exec $ execCall m v k
    alg (MuCall v k)          = Exec $ execMuCall v k
    alg (Push x k)            = Exec $ execPush x k
    alg (Pop k)               = Exec $ execPop k
    alg (Lift2 f k)           = Exec $ execLift2 f k
    alg (Sat p k)             = Exec $ execSat p k
    alg Empt                  = Exec $ execEmpt
    alg (Commit exit k)       = Exec $ execCommit exit k
    alg (HardFork p q φ)      = Exec $ execHardFork p q φ
    alg (SoftFork n p q φ)    = Exec $ execSoftFork n p q φ
    alg (Join φ)              = Exec $ execJoin φ
    alg (Attempt n k)         = Exec $ execAttempt n k
    alg (Look k)              = Exec $ execLook k
    alg (NegLook m k)         = Exec $ execNegLook m k
    alg (Restore k)           = Exec $ execRestore k
    alg (Case p q)            = Exec $ execCase p q
    alg (Choices fs ks)       = Exec $ execChoices fs ks
    alg (ChainIter σ v)       = Exec $ execChainIter σ v
    alg (ChainInit x σ l v k) = Exec $ execChainInit x σ l v k
    alg (LogEnter name k)     = Exec $ execLogEnter name k
    alg (LogExit name k)      = Exec $ execLogExit name k

{-# INLINE setupHandlerΓ #-}
setupHandlerΓ :: Γ s xs ks a -> TExpQ (O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)) ->
                                (Γ s xs ks a -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandlerΓ γ !h !k = setupHandler (hs γ) (cidx γ) (cs γ) (o γ) h (\hs cidx cs -> k (γ {hs = hs, cidx = cidx, cs = cs}))

{-# INLINE setupHandler #-}
setupHandler :: QH s a -> QCIdx -> QC s -> QO -> TExpQ (O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)) ->
                                                 (QH s a -> QCIdx -> QC s -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandler !hs !cidx !cs !o !h !k = [||
  do !(cidx', cs') <- pushC $$o $$cidx $$cs
     $$(k [|| pushH $$h $$hs ||] [|| cidx' ||] [|| cs' ||])
  ||]

raiseΓ :: Γ s xs ks a -> QST s (Maybe a)
raiseΓ γ = [|| raise $$(hs γ) $$(cidx γ) $$(cs γ) $$(o γ) $$(d γ) ||]

{-# INLINE raise #-}
raise :: H s a -> CIdx -> C s -> O -> D -> ST s (Maybe a)
raise (H SNil) !_ !_ !_ !_                           = return Nothing
raise (H (h:::hs')) !(I# cidx) !cs !(I# o) !(I# d)   = h o (H hs') cidx cs d

execHalt :: Γ s (a ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execHalt γ = return $! [|| case $$(xs γ) of HCons x _ -> return (Just x) ||]

execRet :: Γ s (b ': xs) ((b ': xs) ': ks) a -> Reader (Ctx s a) (QST s (Maybe a))
execRet γ = do ctx <- ask; return $! [|| do $$(restore (σs ctx)); $$(resume γ) ||]

fix :: (a -> a) -> a
fix f = let x = f x in x

execCall :: Exec s xs ((b ': xs) ': ks) a i -> MVar xs ((b ': xs) ': ks) a -> Exec s (b ': xs) ks a i
         -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execCall m (MVar μ) k γ@(Γ !xs ks o hs cidx cs d) =
  do ctx <- ask
     return $! [|| let !(I# o#) = $$o
                       !(I# cidx#) = $$cidx
                       !(I# d#) = $$d + 1
                   in fix (\r xs ks o# hs cidx# cs d# ->
       do $$(save (σs ctx))
          $$(let μs' = Map.insert μ (GenExec [||r||]) (μs ctx)
             in run m (Γ [||bug xs||] [||bug ks||] [||I# o#||] [||hs||] [||I# cidx#||] [||cs||] [||I# d#||]) (ctx {μs = μs'})
           )) (bug $$xs) $$(suspend k ctx ks) o# $$hs cidx# $$cs d# ||]

execMuCall :: MVar xs ((b ': xs) ': ks) a -> Exec s (b ': xs) ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execMuCall (MVar μ) k γ@(Γ !xs ks o hs cidx cs d) =
  do ctx <- ask
     case (μs ctx) Map.! μ of
       GenExec m -> return $! [|| let !(I# o#) = $$o
                                      !(I# cidx#) = $$cidx
                                      !(I# d#) = $$d + 1
                                  in $$(coerce m) $$xs $$(suspend k ctx ks) o# $$hs cidx# $$cs d#||]

execPush :: WQ x -> Exec s (x ': xs) ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execPush x (Exec k) γ = k (γ {xs = [|| pushX $$(_code x) $$(xs γ) ||]})

execPop :: Exec s xs ks a i -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execPop (Exec k) γ = k (γ {xs = [|| popX_ $$(xs γ) ||]})

execLift2 :: WQ (x -> y -> z) -> Exec s (z ': xs) ks a i -> Γ s (y ': x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLift2 f (Exec k) γ = k (γ {xs = [|| let !(y, xs') = popX $$(xs γ); !(x, xs'') = popX xs' in pushX ($$(_code f) x y) xs'' ||]})

execSat :: WQ (Char -> Bool) -> Exec s (Char ': xs) ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execSat p k γ =
  do ctx <- ask
     return $! (nextSafe (skipBounds ctx) (input ctx) (o γ) (_code p) (\o c -> run k (γ {xs = [|| pushX $$c $$(xs γ) ||], o = o}) ctx) (raiseΓ γ))

execEmpt :: Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execEmpt γ = return (raiseΓ γ)

execCommit :: Bool -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execCommit exit (Exec k) γ = local (\ctx -> if exit then addConstCount (-1) ctx else ctx)
                            (k (γ {hs = [|| popH_ $$(hs γ) ||], cidx = [|| popC_ $$(cidx γ) ||]}))

execHardFork :: Exec s xs ks a i -> Exec s xs ks a i -> Maybe (ΦVar x, Exec s (x ': xs) ks a i) -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execHardFork p q (Just (φ, k)) γ =
  do ctx <- ask
     return $! [||
       let join x (o# :: O#) = $$(run k (γ {xs = [||HCons x $$(xs γ)||], o = [||I# o#||]}) ctx)
       in $$(let ctx' = ctx {φs = DMap.insert φ (GenJoin [||join||]) (φs ctx)}
                 handler = [||\o# hs cidx# cs d'# ->
                   do (c, cidx') <- popC (I# cidx#) cs
                      if c == (I# o#) then do $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
                                              $$(run q (γ {o = [||I# o#||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx')
                      else raise hs cidx' cs (I# o#) (I# d'#)
                   ||]
             in setupHandlerΓ γ handler (\γ' -> run p γ' ctx'))
       ||]
execHardFork p q Nothing γ =
  do ctx <- ask
     let handler = [||\o# hs cidx# cs d'# ->
           do (c, cidx') <- popC (I# cidx#) cs
              if c == (I# o#) then do $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
                                      $$(run q (γ {o = [||I# o#||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx)
              else raise hs cidx' cs (I# o#) (I# d'#)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' -> run p γ' ctx))

execSoftFork :: Maybe Int -> Exec s xs ks a i -> Exec s xs ks a i -> Maybe (ΦVar x, Exec s (x ': xs) ks a i) -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execSoftFork constantInput p q (Just (φ, k)) γ =
  do ctx <- ask
     return $! [||
       let join x (o# :: O#) = $$(run k (γ {xs = [||HCons x $$(xs γ)||], o = [||I# o#||]}) ctx)
       in $$(let ctx' = ctx {φs = DMap.insert φ (GenJoin [||join||]) (φs ctx)}
                 handler = [||\_ hs cidx# cs d'# ->
                   do !(o, cidx') <- popC (I# cidx#) cs
                      $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
                      $$(run q (γ {o = [||o||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx')
                   ||]
             in setupHandlerΓ γ handler (\γ' ->
               case constantInput of
                 Nothing -> run p γ' ctx
                 Just _ | skipBounds ctx -> run p γ' (addConstCount 1 ctx)
                 Just n -> [||
                     if $$(size (input ctx)) > (n + $$(o γ) - 1) then $$(run p γ' (addConstCount 1 ctx'))
                     else $$(raiseΓ γ')
                   ||]))
       ||]
execSoftFork constantInput p q Nothing γ =
  do ctx <- ask
     let handler = [||\_ hs cidx# cs d'# ->
           do !(o, cidx') <- popC (I# cidx#) cs
              $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
              $$(run q (γ {o = [||o||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' ->
       case constantInput of
         Nothing -> run p γ' ctx
         Just _ | skipBounds ctx -> run p γ' (addConstCount 1 ctx)
         Just n -> [||
             if $$(size (input ctx)) > (n + $$(o γ) - 1) then $$(run p γ' (addConstCount 1 ctx))
             else $$(raiseΓ γ')
           ||]
       ))

execJoin :: ΦVar x -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execJoin φ γ = liftM (\(GenJoin k) -> [|| let !(I# o#) = $$(o γ) in $$k (peekX $$(xs γ)) o# ||]) (liftM ((DMap.! φ) . φs) ask)

execAttempt :: Maybe Int -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execAttempt constantInput k γ =
  do ctx <- ask
     let handler = [||\(_ :: O#) hs cidx# cs d'# ->
           do !(o, cidx') <- popC (I# cidx#) cs
              raise hs cidx' cs o (I# d'#)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' ->
       case constantInput of
         Nothing -> run k γ' ctx
         Just _ | skipBounds ctx -> run k γ' (addConstCount 1 ctx)
         Just n -> [||
             if $$(size (input ctx)) > (n + $$(o γ) - 1) then $$(run k γ' (addConstCount 1 ctx))
             else $$(raiseΓ γ')
           ||]
       ))

execLook :: Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLook k γ =
  do ctx <- ask
     let handler = [||\o# hs cidx# cs d'# -> raise hs (popC_ (I# cidx#)) cs (I# o#) (I# d'#)||]
     return $! (setupHandlerΓ γ handler (\γ' -> run k γ' ctx))

execNegLook :: Exec s xs ks a i -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execNegLook m k γ =
  do ctx <- ask
     let handler = [||\_ hs cidx# cs d'# ->
           do (o, cidx') <- popC (I# cidx#) cs
              $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
              $$(run k (γ {o = [||o||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' -> run m γ' ctx))

execRestore :: Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execRestore k γ =
  do ctx <- ask
     return $! [||
       do (o, cidx') <- popC $$(cidx γ) $$(cs γ)
          $$(run k (γ {o = [||o||], hs = [|| popH_ $$(hs γ) ||], cidx = [||cidx'||]}) ctx)
       ||]

execCase :: Exec s (x ': xs) ks a i -> Exec s (y ': xs) ks a i -> Γ s (Either x y ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execCase p q γ =
  do ctx <- ask
     return $! [||
         let !(e, xs') = popX $$(xs γ)
         in case e of
           Left x -> $$(run p (γ {xs = [||pushX x xs'||]}) ctx)
           Right y  -> $$(run q (γ {xs = [||pushX y xs'||]}) ctx)
       ||]

execChoices :: forall x xs ks a s i. [WQ (x -> Bool)] -> [Exec s xs ks a i] -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execChoices fs ks γ = do ctx <- ask; return [|| let (x, xs') = popX $$(xs γ) in $$(go [||x||] fs ks (γ {xs = [||xs'||]}) ctx) ||]
  where
    go :: TExpQ x -> [WQ (x -> Bool)] -> [Exec s xs ks a i] -> Γ s xs ks a -> Ctx s a -> QST s (Maybe a)
    go _ [] [] γ _ = raiseΓ γ
    go x (f:fs) (k:ks) γ ctx = [||
        if $$(_code f) $$x then $$(run k γ ctx)
        else $$(go x fs ks γ ctx)
      ||]


execChainIter :: ΣVar x -> MVar xs ks a -> Γ s ((x -> x) ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execChainIter u (MVar μ) γ@(Γ !xs ks o hs cidx cs d) =
  do ctx <- ask
     let !(QSTRef σ) = (σm ctx) DMap.! u
     case (μs ctx) Map.! μ of
       GenExec k -> return [||
         do let !(g, xs') = popX $$xs
            modifyΣ $$σ g
            pokeC $$o $$cidx $$cs
            let I# o# = $$o
            let I# cidx# = $$cidx
            let I# d# = $$d
            $$(coerce k) xs' $$ks o# $$hs cidx# $$cs d#
         ||]

execChainInit :: WQ x -> ΣVar x -> Exec s xs ks a i -> MVar xs ks a -> Exec s (x ': xs) ks a i
                  -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execChainInit deflt u l (MVar μ) k γ@(Γ !xs ks o _ _ _ d) =
  do ctx <- ask
     let !(QSTRef σ) = (σm ctx) DMap.! u
     let xs' = [|| popX $$xs ||]
     let handler = [||\o# hs cidx# cs d'# ->
          do $$(rollback (σs ctx)) ((I# d'#) - $$d)
             (c, cidx') <- popC (I# cidx#) cs
             if c == (I# o#) then do y <- pokeΣ $$σ $$(_code deflt)
                                     $$(run k (γ {xs = [|| pushX y (snd $$xs') ||],
                                                  o = [||I# o#||],
                                                  hs = [||hs||],
                                                  cidx = [||cidx'||],
                                                  cs = [||cs||]}) ctx)
             else do writeΣ $$σ $$(_code deflt); raise hs cidx' cs (I# o#) $$d
          ||]
     return $! (setupHandlerΓ γ handler (\γ' -> [||
       -- NOTE: Only the offset and the cs array can change between interations of a chainPre
       do writeΣ $$σ (fst $$xs')
          let I# o# = $$o
          fix (\r o# cs ->
            $$(let μs' = Map.insert μ (GenExec [|| \_ _ o# _ _ cs _ -> r o# cs ||]) (μs ctx)
               in run l (Γ [||snd $$xs'||] ks [||I# o#||] (hs γ') (cidx γ') [||cs||] d) (ctx {μs = μs'})))
            o# $$(cs γ')||]))

runParser :: Parser a -> TExpQ (String -> Maybe a)
runParser (Parser p) = [||\input -> runST $$(exec [||input||] (compile (terminationAnalysis (preprocess p))))||]

showM :: Parser a -> String
showM (Parser p) = show (fst (compile (preprocess p)))

preludeString :: String -> Char -> Γ s xs ks a -> Ctx s a -> String -> TExpQ String
preludeString name dir γ ctx ends = [|| concat [$$prelude, $$eof, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    offset       = o γ
    indent       = replicate (debugLevel ctx * 2) ' '
    start        = [|| max ($$offset - 5) 0 ||]
    end          = [|| min ($$offset + 6) $$(size (input ctx)) ||]
    sub          = [|| $$(substr (input ctx)) $$start ($$end - 1) ||]
    inputTrace   = [|| let replace '\n' = color Green "↙"
                           replace ' '  = color White "·"
                           replace c    = return c
                       in concatMap replace (elems $$sub) ||]
    eof          = [|| if $$end == $$(size (input ctx)) then $$inputTrace ++ color Red "•" else $$inputTrace ||]
    prelude      = [|| concat [indent, dir : name, dir : " (", show $$offset, "): "] ||]
    caretSpace   = [|| replicate (length $$prelude + $$offset - $$start) ' ' ||]


execLogEnter :: String -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLogEnter name k γ =
  do ctx <- ask
     let handler = [||\o hs cidx cs d' -> trace $$(preludeString name '<' (γ {o = [||I# o||]}) ctx (color Red " Fail")) (raise hs (I# cidx) cs (I# o) (I# d')) ||]
     return $! (setupHandlerΓ γ handler (\γ' -> [|| trace $$(preludeString name '>' γ ctx "") $$(run k γ' (debugUp ctx))||]))


execLogExit :: String -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLogExit name k γ =
  do ctx <- ask
     return $! [|| trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(run k γ (debugDown ctx)) ||]
