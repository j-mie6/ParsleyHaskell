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
import Prelude hiding ((*>), (<*), (>>))
import Control.Applicative hiding ((<*), (*>), many, some)
import Control.Monad hiding ((>>))
import Control.Monad.ST
import Data.STRef
import System.IO.Unsafe

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

-- TODO: Stable name and unsafePerformIO!
--       we have to find recursion points and perform optimisation in here, aux required
preprocess :: Parser a -> Parser a
preprocess = unsafePerformIO . preprocess'
  where
    preprocess' :: Parser a -> IO (Parser a)
    preprocess' = return

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
--optimise ((m :>>=: g) :>>=: f)            = m >>= (\x -> optimise (g x >>= f)) -- Compiler does this for us?
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
  --Ret         :: M s (a ': xs) (a ': xs)
  Halt        :: M s '[a] '[a]
  Push        :: a -> M s (a ': xs) ys -> M s xs ys
  Pop         :: M s xs ys -> M s (a ': xs) ys
  App         :: M s (b ': xs) ys -> M s (a ': (a -> b) ': xs) ys
  Bind        :: (a -> ST s (M s xs ys)) -> M s (a ': xs) ys
  Empt        :: M s xs ys
  Cut         :: M s xs ys -> M s xs ys
  Try         :: M s xs ys -> M s xs ys -> M s xs ys
  TryCut      :: M s xs ys -> M s xs ys -> M s xs ys
  --Many'    :: STRef s [a] -> M s xs (a ': xs) -> M s ([a] ': xs) ys -> M s xs ys
  --ManyCut' :: STRef s [a] -> M s xs (a ': xs) -> M s ([a] ': xs) ys -> M s xs ys
  ManyIter    :: STRef s [a] -> M s xs (a ': xs) -> M s ([a] ': xs) ys -> M s (a ': xs) (a ': xs)
  ManyIterCut :: STRef s [a] -> M s xs (a ': xs) -> M s ([a] ': xs) ys -> M s (a ': xs) (a ': xs)
  ManyInit    :: STRef s [a] -> M s (a ': xs) (a ': xs) -> M s xs (a ': xs) -> M s ([a] ': xs) ys -> M s xs ys

halt :: M s '[a] '[a]
halt = Halt

-- ts ++ ts' == ts''
class Append (ts :: [*]) (ts' :: [*]) (ts'' :: [*]) | ts ts' -> ts''
instance ts ~ ts' => Append '[] ts ts'
instance {-# OVERLAPPABLE #-} (Append ts ts' ts'', xs ~ (t ': ts), ys ~ (t ': ts'')) => Append xs ts' ys

compile :: Parser a -> ST s (M s '[] '[a])
compile = flip (compile' @'[]) halt

compile' :: forall xs ys xys a b s. Append xs ys xys => Parser a -> M s (a ': xys) (b ': ys) -> ST s (M s xys (b ': ys))
compile' (Pure x) m      = do return (Push x m)
compile' (pf :<*>: px) m = do pxc <- compile' @(_ ': xs) px (App m); compile' @xs pf pxc
compile' (p :*>: q) m    = do qc <- compile' @xs q m; compile' @xs p (Pop qc)
compile' (p :<*: q) m    = do qc <- compile' @(a ': xs) q (Pop m); compile' @xs p qc
compile' Empty m         = do return Empt
compile' (p :<|>: q) m   = do TryCut <$> compile' @xs p (Cut m) <*> compile' @xs q m
compile' (p :>>=: f) m   = do compile' @xs p (Bind (flip (compile' @xs) m . f))
compile' (Fix p) m       = do compile' @xs p m
--compile' (Many p) m      = do Many' <$> newSTRef [] <*> compile' @'[] p Ret <*> pure m
compile' (Many p) m      =
  mdo st <- newSTRef []
      manyp <- compile' @'[] p manyp'
      let manyp' = (ManyIterCut st manyp m)
      return (ManyInit st manyp' manyp m)

-- Obviously, this will have setup code for the stack etc
eval :: String -> M s '[] '[a] -> ST s (Maybe a)
eval = eval'

-- This is the operational semantics of the instruction set!
eval' :: String -> M s '[] '[a] -> ST s (Maybe a)
eval' _ _ = return Nothing

runParser :: Parser a -> String -> Maybe a
runParser p input = runST (compile (preprocess p) >>= eval input)
