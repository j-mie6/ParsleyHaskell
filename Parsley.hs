{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MagicHash, UnboxedTuples #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
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

import Prelude hiding          (fmap, pure, (<*), (*>), (<*>), (<$>), (<$))
--import Control.Applicative     (Alternative, (<|>), empty, liftA2, liftA, (<**>), many, some)
import Control.Monad           (MonadPlus, mzero, mplus, liftM, liftM2, join, (<$!>), forM)
--import Data.Functor            ((<$>), (<$), ($>), (<&>), void)
import GHC.ST                  (ST(..), runST)
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Control.Monad.Reader    (ReaderT, ask, runReaderT, Reader, runReader, local)
import qualified Control.Monad.Reader as Reader
import Data.STRef              (STRef, writeSTRef, readSTRef, modifySTRef', newSTRef)
import System.IO.Unsafe        (unsafePerformIO)
import Data.IORef              (IORef, writeIORef, readIORef, newIORef)
import Data.Array              (Array, array)
import GHC.StableName          (StableName(..), makeStableName, hashStableName, eqStableName)
import Data.Hashable           (Hashable, hashWithSalt, hash)
import Data.HashMap.Lazy       (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Map.Strict         (Map)
import qualified Data.Map.Strict as Map
import Data.Dependent.Map      (DMap)
import Data.GADT.Compare       (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))
import qualified Data.Dependent.Map as DMap
import Data.Array.Unboxed      (UArray, listArray)
--import Data.Array.ST           (STArray)
import Data.Array.Base         (STUArray(..), unsafeAt, newArray_, unsafeRead, unsafeWrite, MArray, getNumElements, numElements)
import GHC.Prim                (Int#, Char#, StableName#, newByteArray#)
import GHC.Exts                (Int(..), Char(..), (-#), (+#), (*#))
import Unsafe.Coerce           (unsafeCoerce)
import Safe.Coerce             (coerce)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Debug.Trace

-- AST
data WQ a = WQ { _val :: a, _code :: TExpQ a }
data Parser a where
  Pure      :: WQ a -> Parser a
  Char      :: Char -> Parser Char
  Satisfy   :: WQ (Char -> Bool) -> Parser Char
  (:<*>:)   :: Parser (a -> b) -> Parser a -> Parser b
  (:*>:)    :: Parser a -> Parser b -> Parser b
  (:<*:)    :: Parser a -> Parser b -> Parser a
  --(:>>=:)   :: Parser a -> (a -> Parser b) -> Parser b
  (:<|>:)   :: Parser a -> Parser a -> Parser a
  Empty     :: Parser a
  Try       :: Parser a -> Parser a
  LookAhead :: Parser a -> Parser a
  Rec       :: Parser a -> Parser a
  Many      :: Parser a -> Parser [a]

showAST :: Parser a -> String
showAST (Pure _) = "(pure x)"
showAST (Char c) = "(char " ++ show c ++ ")"
showAST (Satisfy _) = "(satisfy f)"
showAST (pf :<*>: px) = concat ["(", showAST pf, " <*> ", showAST px, ")"]
showAST (p :*>: q) = concat ["(", showAST p, " *> ", showAST q, ")"]
showAST (p :<*: q) = concat ["(", showAST p, " <* ", showAST q, ")"]
--showAST (p :>>=: f) = concat ["(", showAST p, " >>= f)"]
showAST (p :<|>: q) = concat ["(", showAST p, " <|> ", showAST q, ")"]
showAST Empty = "empty"
showAST (Try p) = concat ["(try ", showAST p, ")"]
showAST (LookAhead p) = concat ["(lookAhead ", showAST p, ")"]
showAST (Rec _) = "recursion point!"
showAST (Many p) = concat ["(many ", showAST p, ")"]

-- Smart Constructors
{-instance Functor Parser where
  fmap = liftA
  x <$ p = p *> pure x
instance Applicative Parser where
  pure = Pure
  (<*>) = (:<*>:)
  (<*) = (:<*:)
  (*>) = (:*>:)
instance Monad Parser where
  return = Pure
  (>>=) = (:>>=:)
  (>>) = (*>)
instance Alternative Parser where
  empty = Empty
  (<|>) = (:<|>:)
  --many = Many
  some p = p <:> many p
instance MonadPlus Parser-}

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
pure = Pure

(<*>) :: Parser (a -> b) -> Parser a -> Parser b
(<*>) = (:<*>:)

(<*) :: Parser a -> Parser b -> Parser a
(<*) = (:<*:)

(*>) :: Parser a -> Parser b -> Parser b
(*>) = (:*>:)

liftA2 :: WQ (a -> b -> c) -> Parser a -> Parser b -> Parser c
liftA2 f p q = f <$> p <*> q

empty :: Parser a
empty = Empty

(<|>) :: Parser a -> Parser a -> Parser a
(<|>) = (:<|>:)

many :: Parser a -> Parser [a]
many p = {-let manyp = p <:> manyp <|> pure (WQ [] [|| [] ||]) in manyp--}Many p

some :: Parser a -> Parser [a]
some p = p <:> many p

skipMany :: Parser a -> Parser ()
skipMany p = let skipp = p *> skipp <|> unit in skipp

-- Additional Combinators
(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = liftA2 (WQ (:) [|| (:) ||])

(<**>) :: Parser a -> Parser (a -> b) -> Parser b
(<**>) = liftA2 (WQ (flip ($)) [|| (flip ($)) ||])

{-class Functor f => Monoidal f where
  unit :: f ()
  (<~>) :: f a -> f b -> f (a, b)
  (<~) :: f a -> f b -> f a
  p <~ q = fst <$> (p <~> q)
  (~>) :: f a -> f b -> f b
  p ~> q = snd <$> (p <~> q)-}

{-instance (Functor f, Applicative f) => Monoidal f where
  unit = pure ()
  (<~>) = liftA2 (,)
  (<~) = (<*)
  (~>) = (*>)-}

unit :: Parser ()
unit = pure (WQ () [|| () ||])

(<~>) :: Parser a -> Parser b -> Parser (a, b)
(<~>) = liftA2 (WQ (,) [|| (,) ||])

(<~) :: Parser a -> Parser b -> Parser a
(<~) = (<*)

(~>) :: Parser a -> Parser b -> Parser b
(~>) = (*>)

--class (Monad p, Alternative p) => MonadParser p where
--  {-# MINIMAL (satisfy | item), notFollowedBy, lookAhead #-}
satisfy :: WQ (Char -> Bool) -> Parser Char
--satisfy p = item >>= (\x -> if p x then return x else empty)
item :: Parser Char
item = satisfy (WQ (const True) [|| const True ||])

  {-
  These combinators should adhere to the following laws:
    double negation: notFollowedBy . notFollowedBy         = lookAhead . void
    idempotence:     lookAhead . lookAhead                 = lookAhead
    right-identity:  notFollowedBy . lookAhead             = notFollowedBy
    left-identity:   lookAhead . notFollowedBy             = notFollowedBy
    transparency:    notFollowedBy p *>/<* notFollowedBy p = notFollowedBy p

  As a consequence of these laws:
    notFollowedBy eof = more
    notFollowedBy more = eof
  -}
lookAhead :: Parser a -> Parser a
--notFollowedBy :: p a -> p ()

  -- Auxillary functions
char :: Char -> Parser Char
--char c = satisfy (== c)
string :: String -> Parser String
--string = traverse char
string = foldr (<:>) (pure (WQ [] [|| [] ||])) . map char
--eof :: Parser ()
--eof = notFollowedBy item
more :: Parser ()
more = lookAhead (void item)

--instance MonadParser Parser where
satisfy = Satisfy
char = Char
lookAhead = LookAhead
---notFollowedBy p = try (join ((try p *> return empty) <|> return unit))

try :: Parser a -> Parser a
try = Try

optional :: Parser a -> Parser ()
optional p = void p <|> unit

choice :: [Parser a] -> Parser a
choice = foldr (<|>) empty

data StableParserName = forall a. StableParserName (StableName# (Parser a))
data GenParser = forall a. GenParser (Parser a)
instance Eq StableParserName where (StableParserName n) == (StableParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable StableParserName where
  hash (StableParserName n) = hashStableName (StableName n)
  hashWithSalt salt (StableParserName n) = hashWithSalt salt (StableName n)

preprocess :: Parser a -> Parser a
preprocess !p = trace "preprocessing" $ unsafePerformIO (runReaderT (preprocess' p) (HashMap.empty))
  where
    preprocess' :: Parser a -> ReaderT (HashMap StableParserName GenParser) IO (Parser a)
    -- Force evaluation of p to ensure that the stableName is correct first time
    preprocess' !p =
      do !seen <- ask
         (StableName _name) <- Reader.lift (makeStableName p)
         let !name = StableParserName _name
         case HashMap.lookup name seen of
           Just (GenParser q) -> return $! (Rec (coerce q))
           Nothing -> mdo q <- local (HashMap.insert name (GenParser q)) (preprocess'' p)
                          return $! q
    preprocess'' :: Parser a -> ReaderT (HashMap StableParserName GenParser) IO (Parser a)
    preprocess'' !(pf :<*>: px) = liftM optimise (liftM2 (:<*>:)  (preprocess' pf) (preprocess' px))
    preprocess'' !(p :*>: q)    = liftM optimise (liftM2 (:*>:)   (preprocess' p)  (preprocess' q))
    preprocess'' !(p :<*: q)    = liftM optimise (liftM2 (:<*:)   (preprocess' p)  (preprocess' q))
    --preprocess'' !(p :>>=: f)   = fmap optimise (liftM (:>>=: f) (preprocess' p))
    preprocess'' !(p :<|>: q)   = liftM optimise (liftM2 (:<|>:)  (preprocess' p)  (preprocess' q))
    preprocess'' !Empty         = return Empty
    preprocess'' !(Try p)       = liftM Try (preprocess' p)
    preprocess'' !(LookAhead p) = liftM LookAhead (preprocess' p)
    preprocess'' !(Many p)      = liftM Many (preprocess' p)
    preprocess'' !p             = return p

optimise :: Parser a -> Parser a
-- Applicative Optimisation
optimise (Pure (WQ f qf) :<*>: Pure (WQ x qx)) = pure (WQ (f x) [|| $$qf $$qx ||])
optimise (Pure (WQ f qf) :<*>: (Pure (WQ g qg) :<*>: px)) = WQ (f . g) [|| $$qf . $$qg ||] <$> px
optimise (Empty :<*>: _)                  = Empty
optimise ((q :*>: pf) :<*>: px)           = q *> (optimise (pf <*> px))
optimise (pf :<*>: (px :<*: q))           = optimise (optimise (pf <*> px) <* q)
optimise (pf :<*>: (q :*>: Pure x))       = optimise (optimise (pf <*> pure x) <* q)
optimise (pf :<*>: Empty)                 = pf *> empty
optimise (pf :<*>: Pure (WQ x qx))        = WQ ($ x) [|| \f -> f $$qx ||] <$> pf
-- Alternative Optimisation
optimise (Pure x :<|>: _)                 = pure x
optimise (Empty :<|>: p)                  = p
optimise (p :<|>: Empty)                  = p
optimise ((u :<|>: v) :<|>: w)            = u <|> optimise (v <|> w)
-- Monadic Optimisation
--optimise (Pure x :>>=: f)                 = f x
--optimise ((q :*>: p) :>>=: f)             = q *> optimise (p >>= f)
--optimise (Empty :>>=: f)                  = Empty
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
-- TODO There are a few more laws to address when the instrinsics come in:
-- notFollowedBy . notFollowedBy = lookAhead
-- eof *> eof | eof <* eof = eof
-- p <*> eof = (p <*> unit) <* eof
-- notFollowedBy eof = lookAhead (void item)
optimise p                                = p

newtype ΣVar a = ΣVar Int deriving Show
newtype MVar xs ks a = MVar Int deriving Show
data M xs ks a where
  Halt         :: M '[a] ks a
  Ret          :: M (b ': xs) ((b ': xs) ': ks) a
  Push         :: WQ x -> !(M (x ': xs) ks a) -> M xs ks a
  Pop          :: !(M xs ks a) -> M (b ': xs) ks a
  App          :: !(M (y ': xs) ks a) -> M (x ': (x -> y) ': xs) ks a
  Chr          :: !Char -> !(M (Char ': xs) ks a) -> M xs ks a
  Sat          :: WQ (Char -> Bool) -> !(M (Char ': xs) ks a) -> M xs ks a
  Call         :: M xs ((b ': xs) ': ks) a -> MVar xs ((b ': xs) ': ks) a -> !(M (b ': xs) ks a) -> M xs ks a
  MuCall       :: MVar xs ((b ': xs) ': ks) a -> !(M (b ': xs) ks a) -> M xs ks a
  --Bind         :: !(x -> M xs ks a) -> M (x ': xs) ks a
  Empt         :: M xs ks a
  Commit       :: !(M xs ks a) -> M xs ks a
  SoftFork     :: !(M xs ks a) -> M xs ks a -> M xs ks a
  HardFork     :: !(M xs ks a) -> M xs ks a -> M xs ks a
  Attempt      :: !(M xs ks a) -> M xs ks a
  Look         :: !(M xs ks a) -> M xs ks a
  Restore      :: !(M xs ks a) -> M xs ks a
  ManyIter     :: !(ΣVar ([x] -> [x])) -> !(MVar xs ks a) -> M (x ': xs) ks a
  ManyInitSoft :: !(ΣVar ([x] -> [x])) -> !(M xs ks a) -> !(MVar xs ks a) -> !(M ([x] ': xs) ks a) -> M xs ks a
  ManyInitHard :: !(ΣVar ([x] -> [x])) -> !(M xs ks a) -> !(MVar xs ks a) -> !(M ([x] ': xs) ks a) -> M xs ks a

instance Show (M xs ks a) where
  show Halt = "Halt"
  show Ret = "Ret"
  show (Call m v k) = "{Call (" ++ show v ++ ") " ++ show m ++ " " ++ show k ++ "}"
  show (MuCall v k) = "(μCall (" ++ show v ++ ") " ++ show k ++ ")"
  show (Push _ k) = "(Push x " ++ show k ++ ")"
  show (Pop k) = "(Pop " ++ show k ++ ")"
  show (App k) = "(App " ++ show k ++ ")"
  show (Chr c k) = "(Chr " ++ show c ++ " " ++ show k ++ ")"
  show (Sat _ k) = "(Sat f " ++ show k ++ ")"
  --show (Bind _) = "(Bind ?)"
  show Empt = "Empt"
  show (Commit k) = "(Commit " ++ show k ++ ")"
  show (SoftFork p q) = "(SoftFork " ++ show p ++ " " ++ show q ++ ")"
  show (HardFork p q) = "(HardFork " ++ show p ++ " " ++ show q ++ ")"
  show (Attempt k) = "(Try " ++ show k ++ ")"
  show (Look k) = "(Look " ++ show k ++ ")"
  show (Restore k) = "(Restore " ++ show k ++ ")"
  show (ManyIter σ v) = "(ManyIter (" ++ show σ ++ ") (" ++ show v ++ "))"
  show (ManyInitSoft σ m v k) = "{ManyInitSoft (" ++ show σ ++ ") (" ++ show v ++ ") " ++ show m ++ " " ++ show k ++ "}"
  show (ManyInitHard σ m v k) = "{ManyInitHard (" ++ show σ ++ ") (" ++ show v ++ ") " ++ show m ++ " " ++ show k ++ "}"

--data GenM s a = forall xs ks. GenM (M xs ks a)
compile :: Parser a -> (M '[] '[] a, [PState])
compile !p = trace (show m) (m, vss)
  where (m, vss) = unsafePerformIO (do σs <- newIORef []
                                       m <- runReaderT (compile' (trace (showAST p) p) Halt) (HashMap.empty, 0, σs)
                                       vss <- readIORef σs
                                       return $! (m, vss))

(><) :: (a -> c) -> (b -> d) -> (a, b, x) -> (c, d, x)
(f >< g) (x, y, z) = (f x, g y, z)

type IMVar = Int
data PState = forall a. PState a (TExpQ a) (ΣVar a)
type ΣVars = IORef [PState]
compile' :: Parser a -> M (a ': xs) ks b -> ReaderT (HashMap StableParserName IMVar, IMVar, ΣVars) IO (M xs ks b)
compile' !(Pure x) !m        = do return $! (Push x m)
compile' !(Char c) !m        = do return $! (Chr c m)
compile' !(Satisfy p) !m     = do return $! (Sat p m)
compile' !(pf :<*>: px) !m   = do !pxc <- compile' px (App m); compile' pf pxc
compile' !(p :*>: q) !m      = do !qc <- compile' q m; compile' p (Pop qc)
compile' !(p :<*: q) !m      = do !qc <- compile' q (Pop m); compile' p qc
compile' !Empty !m           = do return $! Empt
compile' !(Try p :<|>: q) !m = do liftM2 SoftFork (compile' p (Commit m)) (compile' q m)
compile' !(p :<|>: q) !m     = do liftM2 HardFork (compile' p (Commit m)) (compile' q m)
--compile' !(p :>>=: f) !m     = do compile' p (Bind f')
--  where f' x = runST $ (newSTRef HashMap.empty) >>= runReaderT (compile' (preprocess (f x)) m)
compile' !(Try p) !m         = do liftM Attempt (compile' p (Commit m))
compile' !(LookAhead p) !m   = do liftM Look (compile' p (Restore m))
compile' !(Rec !p) !m        =
  do (StableName _name) <- Reader.lift (makeStableName p)
     (seen, v, _) <- ask
     let !name = StableParserName _name
     case HashMap.lookup name seen of
       Just v' -> do return $! MuCall (MVar v') m
       Nothing -> do n <- local (HashMap.insert name v >< (+1)) (compile' p Ret)
                     return $! Call n (MVar v) m
compile' (Many p) m =
  do (_, v, rσs) <- ask
     σs <- Reader.lift (readIORef rσs)
     let u = case σs of
               [] -> ΣVar 0
               (PState _ _ (ΣVar x)):_ -> ΣVar (x+1)
     Reader.lift (writeIORef rσs (PState id [|| id ||] u:σs))
     n <- local (id >< (+1)) (compile' p (ManyIter u (MVar v)))
     return $! (ManyInitHard u n (MVar v) m)
{-compile' (Many (Try p)) m  =
  do σ <- lift (newSTRef id)
     rec manyp <- compile' p (ManyIter σ manyp)
     return $! (ManyInitSoft σ manyp m)
compile' !(Many p) !m        =
  do σ <- lift (newSTRef id)
     rec manyp <- compile' p (ManyIter σ manyp)
     return $! ManyInitHard σ manyp m-}

data SList a = !a ::: !(SList a) | SNil
data HList xs where
  HNil :: HList '[]
  HCons :: a -> !(HList as) -> HList (a ': as)
data K s ks a where
  KNil :: K s '[] a
  KCons :: !(Input -> X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> Σ s -> D# -> ST s (Maybe a)) -> !(K s ks a) -> K s (xs ': ks) a

instance Show (K s ks a) where
  show KNil = "KNil"
  show (KCons _ ks) = "(KCons " ++ show ks ++ ")"

type Input = UArray Int Char
type QInput = TExpQ Input
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
data State s = forall a. State a (STRef s (SList a))
type QState s = TExpQ (State s)
type Σ s = SList (State s)--Array Int (State s)
type D = Int
type D# = Int#
type QD = TExpQ D
type QΣ s = TExpQ (Σ s)
type QST s a = TExpQ (ST s a)
newtype QSTRef s a = QSTRef (TExpQ (STRef s (SList a)))

data Γ s xs ks a = Γ { input :: QInput
                     , xs    :: QX xs
                     , ks    :: QK s ks a
                     , o     :: QO
                     , hs    :: QH s a
                     , cidx  :: QCIdx
                     , cs    :: QC s
                     , σs    :: QΣ s
                     , d     :: QD }

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
suspend :: M xs ks a -> FixMap s a -> DMap ΣVar (QSTRef s) -> QK s ks a -> QK s (xs ': ks) a
suspend m μ σm ks =
  [|| KCons (\input xs ks o hs cidx cs σs d ->
    $$(runReader (eval' m (Γ [|| input ||] [|| xs ||] [||ks||] [||I# o||] [||hs||] [||I# cidx||] [||cs||] [||σs||] [||I# d||])) (μ, σm))) $$ks ||]
resume :: Γ s xs (xs ': ks) a -> QST s (Maybe a)
resume (Γ input xs ks o hs cidx cs σs d) =
  [|| let ks' = bug ($$ks) :: forall s xs ks a. K s (xs ': ks) a in
        case ks' of
          (KCons k ks) -> (bug k) $$input $$(bug xs) (bug ks) $$o $$hs $$cidx $$cs $$σs $$d
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

nextSafe :: QInput -> QO -> TExpQ (Char -> Bool) -> (QO -> TExpQ Char -> QST s (Maybe a)) -> QST s (Maybe a) -> QST s (Maybe a)
nextSafe input o p good bad = [||
    let bad' = $$bad in
      if  numElements $$input > $$o then let !c = unsafeAt $$input $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else bad'
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

makeΣ :: [PState] -> (DMap ΣVar (QSTRef s) -> QΣ s -> QST s r) -> QST s r
makeΣ []                            = makeΣ' [] (-1) (DMap.empty) []
makeΣ (p@(PState x qx (ΣVar v)):ps) = makeΣ' (p:ps) v (DMap.empty) []

-- TODO It would be better to have Σ be a pair of functions, that way we can statically create them...
--      It might also allow us to optimise them away or in?
makeΣ' :: [PState] -> Int -> DMap ΣVar (QSTRef s) -> [(Int, QState s)] -> (DMap ΣVar (QSTRef s) -> QΣ s -> QST s r) -> QST s r
makeΣ' [] v m vss k = [|| let !σs = $$(weaken vss) in $$(k m [|| σs ||]) ||]
  where
    weaken :: [(Int, QState s)] -> TExpQ (SList (State s))
    weaken []           = [|| SNil ||]
    weaken ((_, s):vss) = [|| $$s:::($$(weaken vss)) ||]
makeΣ' (PState x qx (ΣVar u):ps) v m vss k = [||
  do σ <- newSTRef ($$qx:::SNil)
     let s = State $$qx σ
     $$(let vss' = (u, [|| s ||]):vss
            m' = DMap.insert (ΣVar u) (QSTRef [|| σ ||]) m
        in makeΣ' ps v m' vss' k)
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

sfor_ :: Σ s -> (State s -> ST s ()) -> ST s ()
sfor_ !xs !f = go xs
  where
    go !SNil = return $! ()
    go ((!x):::(!xs)) = do f $! x; go xs

save :: Σ s -> ST s ()
save σs = sfor_ σs up where up (State x σ) = modifySTRef' σ (x:::)

sdrop :: Int -> SList a -> SList a
sdrop 0 xs = xs
sdrop n (_ ::: xs) = sdrop (n-1) xs

rollback :: Σ s -> D -> ST s ()
rollback _ 0 = return $! ()
rollback σs n = sfor_ σs down where down (State x σ) = modifySTRef' σ (sdrop n)

data GenMVar a = forall xs ks. GenMVar (MVar xs ks a)
instance Ord (GenMVar a) where compare (GenMVar (MVar u)) (GenMVar (MVar v)) = compare u v
instance Eq (GenMVar a) where (GenMVar (MVar u)) == (GenMVar (MVar v)) = u == v

data GenEval s a = forall xs ks. GenEval (TExpQ (Input -> X xs -> K s ks a -> O -> H s a -> CIdx -> C s -> Σ s -> D -> ST s (Maybe a)))
type FixMap s a = Map (GenMVar a) (GenEval s a)
type Ctx s a = (FixMap s a, DMap ΣVar (QSTRef s))
eval :: TExpQ String -> (M '[] '[] a, [PState]) -> QST s (Maybe a)
eval input (!m, vss) = [||
  do xs <- makeX
     ks <- makeK
     hs <- makeH
     !(cidx, cs) <- makeC
     let input' = $$(toArray input) :: Input
     $$(makeΣ vss (\σm σs -> runReader (eval' m (Γ [||input'||] [||xs||] [||ks||] [||0||] [||hs||] [||cidx||] [||cs||] σs [||0||])) (Map.empty, σm)))
  ||]
  where
    toArray :: TExpQ String -> QInput
    toArray input = [|| listArray (0, length $$input-1) $$input ||]

{-# INLINE setupHandlerΓ #-}
setupHandlerΓ :: Γ s xs ks a -> TExpQ (O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)) ->
                                (QH s a -> QCIdx -> QC s -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandlerΓ γ !h !k = setupHandler (hs γ) (cidx γ) (cs γ) (o γ) h k

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

evalHalt :: Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalHalt γ = return [|| case $$(xs γ) of HCons x _ -> return (Just (bug x)) ||]

-- TODO: This will require a state restore later down the line
evalRet :: Γ s (b ': xs) ((b ': xs) ': ks) a -> Reader (Ctx s a) (QST s (Maybe a))
evalRet γ = return (resume γ)

fix :: (a -> a) -> a
fix f = let x = f x in x

bug :: a -> b
bug = coerce

evalCall :: M xs ((b ': xs) ': ks) a -> MVar xs ((b ': xs) ': ks) a -> M (b ': xs) ks a
         -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalCall m v k γ@(Γ input !xs ks o hs cidx cs σs d) =
  do (μ, σm) <- ask
     return [|| fix (\r input xs ks o hs cidx cs σs d ->
       do save σs
          $$(let μ' = Map.insert (GenMVar v) (GenEval [||r||]) μ
             in runReader (eval' m (Γ [||input||] [|| bug xs ||] [|| bug ks ||] [||o||] [||hs||] [||cidx||] [||cs||] [||σs||] [||d||])) (μ', σm)
           )) $$input $$xs $$(suspend k μ σm ks) $$o $$hs $$cidx $$cs $$σs ($$d + 1) ||]

evalMuCall :: MVar xs ((b ': xs) ': ks) a -> M (b ': xs) ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalMuCall v k γ@(Γ input !xs ks o hs cidx cs σs d) =
  do (μ, σm) <- ask
     case μ Map.! (GenMVar v) of
       GenEval m -> return [|| $$(coerce m) $$input $$xs $$(suspend k μ σm ks) $$o $$hs $$cidx $$cs $$σs ($$d + 1)||]

evalPush :: WQ x -> M (x ': xs) ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalPush x k γ = eval' k (γ {xs = [|| pushX $$(_code x) $$(bug (xs γ)) ||]})

evalPop :: M xs ks a -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalPop k γ = eval' k (γ {xs = [|| popX_ $$(bug (xs γ)) ||]})

evalApp :: M (y ': xs) ks a -> Γ s (x ': (x -> y) ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalApp k γ = eval' k (γ {xs = [|| let !(x, xs') = popX $$(bug (xs γ)); !(f, xs'') = popX xs' in pushX (f x) xs'' ||]})

evalSat :: WQ (Char -> Bool) -> M (Char ': xs) ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalSat p k γ =
  do μ <- ask
     return (nextSafe (input γ) (o γ) (_code p) (\o c -> runReader (eval' k (γ {xs = [|| pushX $$c $$(bug (xs γ)) ||], o = o})) μ) (raiseΓ γ))

evalChr :: Char -> M (Char ': xs) ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalChr c k γ =
  do μ <- ask
     return (nextSafe (input γ) (o γ) [|| (== c) ||] (\o c -> runReader (eval' k (γ {xs = [|| pushX $$c $$(bug (xs γ)) ||], o = o})) μ) (raiseΓ γ))

--evalBind :: (x -> {-ST s-} (M xs ks a)) -> QInput -> QX (x ': xs) -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
--evalBind f input !xs ks o hs cidx cs =
--  do let !(x, xs') = popX xs
     --k <- f x
--     eval' (f x) input xs' ks o hs cidx cs

evalEmpt :: Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalEmpt γ = return (raiseΓ γ)

evalCommit :: M xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalCommit k γ = eval' k (γ {hs = [|| popH_ $$(hs γ) ||], cidx = [|| popC_ $$(cidx γ) ||]})

evalHardFork :: M xs ks a -> M xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalHardFork p q γ =
  do μ <- ask
     let handler = [||\o hs cidx cs d' ->
           do (c, cidx') <- popC (I# cidx) cs
              if c == (I# o) then do rollback $$(σs γ) ((I# d') - $$(d γ))
                                     $$(runReader (eval' q (γ {o = [||I# o||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]})) μ)
              else raise hs cidx' cs (I# o) (I# d')
           ||]
     return (setupHandlerΓ γ handler (\hs cidx cs -> runReader (eval' p (γ {hs = hs, cidx = cidx, cs = cs})) μ))

evalSoftFork :: M xs ks a -> M xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalSoftFork p q γ =
  do μ <- ask
     let handler = [||\_ hs cidx cs d' ->
           do !(o', cidx') <- popC (I# cidx) cs
              rollback $$(σs γ) ((I# d') - $$(d γ))
              $$(runReader (eval' q (γ {o = [||o'||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]})) μ)
           ||]
     return (setupHandlerΓ γ handler (\hs cidx cs -> runReader (eval' p (γ {hs = hs, cidx = cidx, cs = cs})) μ))

evalAttempt :: M xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalAttempt k γ =
  do μ <- ask
     let handler = [||\(_ :: O#) hs cidx cs d' ->
           do !(o, cidx') <- popC (I# cidx) cs
              raise hs cidx' cs o (I# d')
           ||]
     return (setupHandlerΓ γ handler (\hs cidx cs -> runReader (eval' k (γ {hs = hs, cidx = cidx, cs = cs})) μ))


evalLook :: M xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalLook k γ =
  do μ <- ask
     let handler = [||\o hs cidx cs d' -> raise hs (popC_ (I# cidx)) cs (I# o) (I# d')||]
     return (setupHandlerΓ γ handler (\hs cidx cs -> runReader (eval' k (γ {hs = hs, cidx = cidx, cs = cs})) μ))

evalRestore :: M xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalRestore k γ =
  do μ <- ask
     return [||
       do (o, cidx') <- popC $$(cidx γ) $$(cs γ)
          $$(runReader (eval' k (γ {o = [||o||], hs = [|| popH_ $$(hs γ) ||], cidx = [||cidx'||]})) μ)
       ||]

evalManyIter :: ΣVar ([x] -> [x]) -> MVar xs ks a -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalManyIter u v γ@(Γ input !xs ks o hs cidx cs σs d) =
  do (μ, σm) <- ask
     let !(QSTRef σ) = σm DMap.! u
     case μ Map.! (GenMVar v) of
       GenEval k -> return [||
         do let !(x, xs') = popX $$(bug xs)
            modifyΣ $$σ ((\x f xs -> f (x:xs)) $! x)
            pokeC $$o $$cidx $$cs
            $$(coerce k) $$input xs' $$ks $$o $$hs $$cidx $$cs $$σs $$d
         ||]

evalManyInitHard :: ΣVar ([x] -> [x]) -> M xs ks a -> MVar xs ks a -> M ([x] ': xs) ks a
                 -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
evalManyInitHard u l v k γ@(Γ input !xs ks o _ _ _ σs d) =
  do (μ, σm) <- ask
     let !(QSTRef σ) = σm DMap.! u
     let handler = [||\o hs cidx cs d' ->
          do rollback $$σs ((I# d') - $$d)
             (c, cidx') <- popC (I# cidx) cs
             if c == (I# o) then do ys <- pokeΣ $$σ id
                                    $$(runReader (eval' k (γ {xs = [|| pushX (ys []) (bug $$xs) ||],
                                                              o = [||I# o||],
                                                              hs = [||hs||],
                                                              cidx = [||cidx'||],
                                                              cs = [||cs||]})) (μ, σm))
             else do writeΣ $$σ id; raise hs cidx' cs (I# o) $$d
          ||]
     return (setupHandlerΓ γ handler (\hs cidx cs -> [||
       -- NOTE: Only the offset and the cs array can change between interations of a many
       fix (\r o cs ->
         $$(let μ' = Map.insert (GenMVar v) (GenEval [|| \_ _ _ o _ _ cs _ _ -> r o cs ||]) μ
            in runReader (eval' l (Γ input (bug xs) (bug ks) [||o||] hs cidx [||cs||] σs d)) (μ', σm)))
       $$o $$cs||]))

{-
evalManyInitSoft :: STRef s ([x] -> [x]) -> M xs ks a -> M ([x] ': xs) ks a -> Input -> X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> QST s (Maybe a)
evalManyInitSoft σ l k input !xs ks o hs cidx cs = setupHandler hs cidx cs o handler (eval' l input xs ks o)
  where
    handler _ hs cidx cs =
      do !(I# o, I# cidx') <- popC cidx cs
         ys <- readSTRef σ
         writeSTRef σ id
         eval' k input (pushX (ys []) xs) ks o hs cidx' cs
         -}

eval' :: M xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
eval' Halt γ                   = trace "HALT" $ evalHalt γ
eval' Ret γ                    = trace "RET" $ evalRet γ
eval' (Call m v k) γ           = trace "CALL" $ evalCall m v k γ
eval' (MuCall v k) γ           = trace "MUCALL" $ evalMuCall v k γ
eval' (Push x k) γ             = trace "PUSH" $ evalPush x k γ
eval' (Pop k) γ                = trace "POP" $ evalPop k γ
eval' (App k) γ                = trace "APP" $ evalApp k γ
eval' (Sat p k) γ              = trace "SAT" $ evalSat p k γ
eval' (Chr c k) γ              = trace "CHR" $ evalChr c k γ
--eval' (Bind f) γ               = trace "" $ evalBind f γ
eval' Empt γ                   = trace "EMPT" $ evalEmpt γ
eval' (Commit k) γ             = trace "COMMIT" $ evalCommit k γ
eval' (HardFork p q) γ         = trace "HARDFORK" $ evalHardFork p q γ
eval' (SoftFork p q) γ         = trace "SOFTFORK" $ evalSoftFork p q γ
eval' (Attempt k) γ            = trace "ATTEMPT" $ evalAttempt k γ
eval' (Look k) γ               = trace "LOOK" $ evalLook k γ
eval' (Restore k) γ            = trace "RESTORE" $ evalRestore k γ
eval' (ManyIter σ v) γ         = trace "MANYITER" $ evalManyIter σ v γ
eval' (ManyInitHard σ l v k) γ = trace "MANYINITHARD" $ evalManyInitHard σ l v k γ
--eval' (ManyInitSoft σ l k) γ = trace "MANYINITSOFT" $ evalManyInitSoft σ l k γ

{-
manyUnrolled :: String -> Maybe [Char]
manyUnrolled input = runST $
  do xs <- makeX
     hs <- makeH
     (I# cidx, cs) <- makeC
     I# o <- makeO
     σ <- newSTRef id
     manyUnrolled' σ (listArray (0, length input-1) input) xs o hs cidx cs
  where
    manyUnrolled' :: STRef s ([Char] -> [Char]) -> Input -> X '[] -> O# -> H s [Char] -> CIdx# -> C s -> ST s (Maybe [Char])
    manyUnrolled' σ input xs o hs cidx cs =
      let
        --sat :: forall s. (Char -> Bool) -> Input -> X '[] -> O# -> H s [Char] -> CIdx# -> C s -> ST s (Maybe [Char])
        sat p input !xs o hs cidx cs = nextSafe input o p (\o c -> loop input (pushX c xs) o hs cidx cs) (raise hs cidx cs)
        --loop :: forall s. Input -> X '[Char] -> O# -> H s [Char] -> CIdx# -> C s -> ST s (Maybe [Char])
        loop input !xs o hs cidx cs =
          do let !(x, xs') = popX xs
             modifySTRef' σ ((x :) .)
             pokeC o cidx cs
             sat (== 'a') input xs' o hs cidx cs
      in
      setupHandler hs cidx cs o handler (sat (== 'a') input xs o)
        where
          handler o hs cidx cs =
            do !(c, I# cidx') <- popC cidx cs
               if c == (I# o) then do ys <- readSTRef σ
                                      writeSTRef σ id
                                      evalHalt input (pushX (ys []) xs) o hs cidx' cs
               else do writeSTRef σ id; raise hs cidx' cs o
-}

runParser :: Parsley.Parser a -> TExpQ (String -> Maybe a)
runParser p = --runST (compile (preprocess p) >>= eval input)
  [||\input -> runST $$(eval [|| input ||] (compile (preprocess p)))||]

{-data CompiledParser a = Compiled (forall s. M '[] '[] a)

mkParser :: Parser a -> CompiledParser a
mkParser p = Compiled (runST (slightyUnsafeLeak (compile (preprocess p))))
  where
    slightyUnsafeLeak :: (forall s. ST s (M s '[] '[] a)) -> (forall s. ST s (M s' '[] '[] a))
    slightyUnsafeLeak = unsafeCoerce

runCompiledParser :: CompiledParser a -> String -> Maybe a
runCompiledParser (Compiled p) input = runST (eval input p)-}

showM :: Parser a -> String
showM p = show (fst (compile (preprocess p)))
