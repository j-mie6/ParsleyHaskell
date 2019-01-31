{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
import Prelude hiding ((*>), (<*), (>>))
import Control.Applicative hiding ((<*), (*>), many, some)
import Control.Monad hiding ((>>))
import Control.Monad.ST
import Control.Monad.Reader
import Data.STRef
import System.IO.Unsafe
import Data.IORef
import System.Mem.StableName
import Data.Hashable
import Data.HashSet hiding (empty, null)
import qualified Data.HashSet as HashSet
import Data.HList.HList

-- AST
data Parser a where
  Pure    :: a -> Parser a
  (:<*>:) :: Parser (a -> b) -> Parser a -> Parser b
  (:*>:)  :: Parser a -> Parser b -> Parser b
  (:<*:)  :: Parser a -> Parser b -> Parser a
  (:>>=:) :: Parser a -> (a -> Parser b) -> Parser b
  (:<|>:) :: Parser a -> Parser a -> Parser a
  Empty   :: Parser a
  Fix     :: Parser a -> Parser a
  Many    :: Parser a -> Parser [a]

instance Show (Parser a) where
  show (Pure _) = "pure x"
  show (pf :<*>: px) = concat ["(", show pf, " <*> ", show px, ")"]
  show (p :*>: q) = concat ["(", show p, " *> ", show q, ")"]
  show (p :<*: q) = concat ["(", show p, " <* ", show q, ")"]
  show (p :>>=: f) = concat ["(", show p, " >>= f)"]
  show (p :<|>: q) = concat ["(", show p, " <|> ", show q, ")"]
  show Empty = "empty"
  show (Fix _) = "fix!"
  show (Many p) = concat ["(many ", show p, "]"]

-- Smart Constructors
instance Functor Parser where fmap = liftA
instance Applicative Parser where
  pure = Pure
  (<*>) = (:<*>:)
(<*) :: Parser a -> Parser b -> Parser a
(<*) = (:<*:)
(*>) :: Parser a -> Parser b -> Parser b
(*>) = (:*>:)
instance Monad Parser where
  return = Pure
  (>>=) = (:>>=:)
(>>) :: Parser a -> Parser b -> Parser b
(>>) = (*>)
instance Alternative Parser where
  empty = Empty
  (<|>) = (:<|>:)
instance MonadPlus Parser where
  mzero = empty
  mplus = (<|>)

-- Additional Combinators
many :: Parser a -> Parser [a]
many p = let manyp = (p <:> manyp) <|> pure [] in manyp --Many p

some :: Parser a -> Parser [a]
some p = p <:> many p

(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = liftA2 (:)

data StableParserName = forall a. StableParserName (StableName (Parser a))
instance Eq StableParserName where (StableParserName n) == (StableParserName m) = eqStableName n m
instance Hashable StableParserName where
  hash (StableParserName n) = hashStableName n
  hashWithSalt salt (StableParserName n) = hashWithSalt salt n

preprocess :: Parser a -> Parser a
preprocess p = unsafePerformIO ((newIORef HashSet.empty) >>= runReaderT (preprocess' p))
  where
    preprocess' :: Parser a -> ReaderT (IORef (HashSet StableParserName)) IO (Parser a)
    preprocess' p = fix p >>= preprocess''
    preprocess'' :: Parser a -> ReaderT (IORef (HashSet StableParserName)) IO (Parser a)
    preprocess'' (pf :<*>: px) = fmap optimise (liftM2 (:<*>:)  (preprocess' pf) (preprocess' px))
    preprocess'' (p :*>: q)    = fmap optimise (liftM2 (:*>:)   (preprocess' p)  (preprocess' q))
    preprocess'' (p :<*: q)    = fmap optimise (liftM2 (:<*:)   (preprocess' p)  (preprocess' q))
    preprocess'' (p :>>=: f)   = fmap optimise (liftM (:>>=: f) (preprocess' p))
    preprocess'' (p :<|>: q)   = fmap optimise (liftM2 (:<|>:)  (preprocess' p)  (preprocess' q))
    preprocess'' Empty         = return Empty
    preprocess'' (Many p)      = liftM Many (preprocess' p)
    preprocess'' p             = return p

    fix :: Parser a -> ReaderT (IORef (HashSet StableParserName)) IO (Parser a)
    -- Force evaluation of p to ensure that the stableName is correct first time
    fix !p =
      do seenRef <- ask
         seen <- lift (readIORef seenRef)
         name <- StableParserName <$> lift (makeStableName p)
         if member name seen then return (Fix p)
         else do lift (writeIORef seenRef (insert name seen))
                 return p

optimise :: Parser a -> Parser a
-- Applicative Optimisation
optimise (Pure f :<*>: Pure x)            = pure (f x)
optimise (Pure f :<*>: (Pure g :<*>: px)) = (f . g) <$> px
optimise (Empty :<*>: _)                  = Empty
optimise ((q :*>: pf) :<*>: px)           = q *> (optimise (pf <*> px))
optimise (pf :<*>: (px :<*: q))           = optimise (optimise (pf <*> px) <* q)
optimise (pf :<*>: (q :*>: Pure x))       = optimise (optimise (pf <*> pure x) <* q)
optimise (pf :<*>: Empty)                 = pf *> empty
optimise (pf :<*>: Pure x)                = ($x) <$> pf
-- Alternative Optimisation
optimise (Pure x :<|>: _)                 = pure x
optimise (Empty :<|>: p)                  = p
optimise (p :<|>: Empty)                  = p
optimise ((u :<|>: v) :<|>: w)            = u <|> optimise (v <|> w)
-- Monadic Optimisation
optimise (Pure x :>>=: f)                 = f x
optimise ((q :*>: p) :>>=: f)             = q *> optimise (p >>= f)
optimise (Empty :>>=: f)                  = Empty
-- Sequential Optimisation
optimise (Pure _ :*>: p)                  = p
optimise ((p :*>: Pure _) :*>: q)         = p *> q
-- TODO Character and string fusion optimisation
optimise (Empty :*>: _)                   = Empty
optimise (p :*>: (q :*>: r))              = optimise (optimise (p *> q) *> r)
optimise (p :<*: Pure _) = p
optimise (p :<*: (q :*>: Pure _))         = optimise (p <* q)
-- TODO Character and string fusion optimisation
optimise (p :<*: Empty)                   = p *> empty
optimise (Pure x :<*: p)                  = optimise (p *> pure x)
optimise (Empty :<*: _)                   = Empty
optimise ((p :<*: q) :<*: r)              = optimise (p <* optimise (q <* r))
optimise p                                = p

data M state input output where
  Halt        :: M s '[a] '[a]
  Push        :: a -> M s (a ': xs) ys -> M s xs ys
  Pop         :: M s xs ys -> M s (a ': xs) ys
  App         :: M s (b ': xs) ys -> M s (a ': (a -> b) ': xs) ys
  Bind        :: (a -> ST s (M s xs ys)) -> M s (a ': xs) ys
  Empt        :: M s xs ys
  Cut         :: M s xs ys -> M s xs ys
  Try         :: M s xs ys -> M s xs ys -> M s xs ys
  TryCut      :: M s xs ys -> M s xs ys -> M s xs ys
  ManyIter    :: STRef s [a] -> M s xs (a ': xs) -> M s (a ': xs) (a ': xs)
  ManyInit    :: STRef s [a] -> M s xs (a ': xs) -> M s ([a] ': xs) ys -> M s xs ys
  ManyInitCut :: STRef s [a] -> M s xs (a ': xs) -> M s ([a] ': xs) ys -> M s xs ys

-- ts ++ ts' == ts''
class Append (ts :: [*]) (ts' :: [*]) (ts'' :: [*]) | ts ts' -> ts''
instance ts ~ ts' => Append '[] ts ts'
instance {-# OVERLAPPABLE #-} (Append ts ts' ts'', xs ~ (t ': ts), ys ~ (t ': ts'')) => Append xs ts' ys

compile :: Parser a -> ST s (M s '[] '[a])
compile = flip (compile' @'[]) Halt

compile' :: forall xs ys xys a b s. Append xs ys xys => Parser a -> M s (a ': xys) (b ': ys) -> ST s (M s xys (b ': ys))
compile' (Pure x) m      = do return (Push x m)
compile' (pf :<*>: px) m = do pxc <- compile' @(_ ': xs) px (App m); compile' @xs pf pxc
compile' (p :*>: q) m    = do qc <- compile' @xs q m; compile' @xs p (Pop qc)
compile' (p :<*: q) m    = do qc <- compile' @(a ': xs) q (Pop m); compile' @xs p qc
compile' Empty m         = do return Empt
compile' (p :<|>: q) m   = do TryCut <$> compile' @xs p (Cut m) <*> compile' @xs q m
compile' (p :>>=: f) m   = do compile' @xs p (Bind (flip (compile' @xs) m . preprocess . f))
compile' (Fix p) m       = do compile' @xs p m
compile' (Many p) m      =
  mdo st <- newSTRef []
      manyp <- compile' @'[] p (ManyIter st manyp)
      return (ManyInitCut st manyp m)

type H s a = STRef s [ST s (Maybe a)]
type X = HList
type C s = STRef s [Int]
data Status = Good | Bad deriving (Show, Eq)
type S s = STRef s Status

makeX :: ST s (X '[])
makeX = return HNil
pushX :: a -> X xs -> X (a ': xs)
pushX = HCons
popX :: X (a ': xs) -> (a, X xs)
popX (HCons x xs) = (x, xs)
pokeX :: a -> X (a ': xs) -> X (a ': xs)
pokeX = undefined

makeH :: ST s (H s a)
makeH = newSTRef []
emptyH :: H s a -> ST s Bool
emptyH = fmap null . readSTRef
pushH :: X xs -> C s -> S s -> String -> M s xs '[a] -> H s a -> ST s ()
pushH xs cs s input m hs = modifySTRef' hs (eval' xs hs cs s input m :)
popH :: H s a -> ST s (Maybe a)
popH href =
  do (h:hs) <- readSTRef href
     writeSTRef href hs
     h

makeC :: ST s (C s)
makeC = newSTRef []
pushC :: Int -> C s -> ST s ()
pushC c cs = modifySTRef' cs (c:)
popC :: C s -> ST s Int
popC ref = do (c:cs) <- readSTRef ref; writeSTRef ref cs; return c

makeS :: ST s (S s)
makeS = newSTRef Good
status :: S s -> ST s a -> ST s a -> ST s a
status ref good bad =
  do s <- readSTRef ref
     case s of
       Good -> good
       Bad -> bad
oops :: S s -> ST s ()
oops ref = writeSTRef ref Bad
ok :: S s -> ST s ()
ok ref = writeSTRef ref Good

eval :: String -> M s '[] '[a] -> ST s (Maybe a)
eval input m =
  do xs <- makeX
     hs <- makeH
     cs <- makeC
     s <- makeS
     eval' xs hs cs s input m

-- TODO Implement semantics of the machine
eval' :: X xs -> H s a -> C s -> S s -> String -> M s xs '[a] -> ST s (Maybe a)
eval' xs hs cs s input Halt       = status s (return (Just (fst (popX xs)))) (return Nothing)
eval' xs hs cs s input (Push x k) = eval' (pushX x xs) hs cs s input k
eval' xs hs cs s input (Pop k)    = eval' (snd (popX xs)) hs cs s input k
eval' xs hs cs s input (App k)    = let (x, xs') = popX xs
                                        (f, xs'') = popX xs'
                                    in eval' (pushX (f x) xs'') hs cs s input k
eval' xs hs cs s input (Bind f)   = do let (x, xs') = popX xs
                                       k <- f x
                                       eval' xs' hs cs s input k
eval' xs hs cs s input Empt =
  do noHandler <- emptyH hs
     if noHandler then return Nothing
     else do oops s; popH hs
eval' xs hs cs s input _ = return Nothing

runParser :: Parser a -> String -> Maybe a
runParser p input = runST (compile (preprocess p) >>= eval input)
