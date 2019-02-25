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
data HKList s ks a where
  KNil :: HKList s '[] a
  KCons :: !(Input -> X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)) -> !(HKList s ks a) -> HKList s (xs ': ks) a

instance Show (HKList s ks a) where
  show KNil = "KNil"
  show (KCons _ ks) = "(KCons " ++ show ks ++ ")"

type Input = UArray Int Char
type QInput = TExpQ Input
newtype H s a = H (SList (O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)))
type QH s a = TExpQ (H s a)
type X = HList
type QX xs = TExpQ (X xs)
type K = HKList
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
type Σ s = Array Int (State s)
type QΣ s = TExpQ (Σ s)
type QST s a = TExpQ (ST s a)
newtype QSTRef s a = QSTRef (TExpQ (STRef s (SList a)))

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
suspend m μ σm ks = [|| KCons (\input xs ks o hs cidx cs ->
                          $$(runReader (eval' m [|| input ||] [|| xs ||] [||ks||] [||I# o||] [||hs||] [||I# cidx||] [||cs||]) (μ, σm))) $$ks ||]
-- NOTE: coerce here is needed because of TTH bug!
resume :: QInput -> QX xs -> QK s (xs ': ks) a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
resume input xs ks o hs cidx cs =
  [|| let ks' = bug ($$ks) :: forall s xs ks a. K s (xs ': ks) a in
        case ks' of
          (KCons k ks) -> (bug k) $$input $$(bug xs) (bug ks) $$o $$hs $$cidx $$cs
  ||]

makeH :: ST s (H s a)
makeH = return $! (H SNil)
pushH :: (O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)) -> H s a -> H s a
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

makeO :: ST s O
makeO = return 0
nextSafe :: QInput -> QO -> TExpQ (Char -> Bool) -> (QO -> TExpQ Char -> QST s (Maybe a)) -> TExpQ (O -> ST s (Maybe a)) -> QST s (Maybe a)
nextSafe input o p good bad = [||
    let bad' = $$bad $$o in
      if  numElements $$input > $$o then let !c = unsafeAt $$input $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else bad'
      else bad'
  ||]

forArray_ :: Σ s -> (State s -> ST s ()) -> ST s ()
forArray_ arr f =
  let go !n = do f (unsafeAt arr n)
                 if n == 0 then return $! ()
                 else go $! (n-1)
  in go (numElements arr-1)

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

makeΣ' :: [PState] -> Int -> DMap ΣVar (QSTRef s) -> [(Int, QState s)] -> (DMap ΣVar (QSTRef s) -> QΣ s -> QST s r) -> QST s r
makeΣ' [] v m vss k = [|| let σs = array (0, v) $$(weaken vss) in $$(k m [|| σs ||]) ||]
  where
    weaken :: [(Int, QState s)] -> TExpQ [(Int, State s)]
    weaken []           = [|| [] ||]
    weaken ((v, s):vss) = [|| (v, $$s):($$(weaken vss)) ||]
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

save :: Σ s -> ST s ()
save σs = forArray_ σs up where up (State x σ) = modifySTRef' σ (x:::)

restore :: Σ s -> ST s ()
restore σs = forArray_ σs down where down (State x σ) = modifySTRef' σ (\(_:::xs) -> xs)

data GenMVar a = forall xs ks. GenMVar (MVar xs ks a)
instance Ord (GenMVar a) where compare (GenMVar (MVar u)) (GenMVar (MVar v)) = compare u v
instance Eq (GenMVar a) where (GenMVar (MVar u)) == (GenMVar (MVar v)) = u == v

data GenEval s a = forall xs ks. GenEval (TExpQ (Input -> X xs -> K s ks a -> O -> H s a -> CIdx -> C s -> ST s (Maybe a)))
type FixMap s a = Map (GenMVar a) (GenEval s a)
type Ctx s a = (FixMap s a, DMap ΣVar (QSTRef s))
eval :: TExpQ String -> (M '[] '[] a, [PState]) -> QST s (Maybe a)
eval input (!m, vss) = [||
  do xs <- makeX
     ks <- makeK
     hs <- makeH
     !(cidx, cs) <- makeC
     o <- makeO
     let input' = $$(toArray input) :: Input
     $$(makeΣ vss (\σm σs -> runReader (eval' m [||input'||] [||xs||] [||ks||] [||o||] [||hs||] [||cidx||] [||cs||]) (Map.empty, σm)))
  ||]
  where
    toArray :: TExpQ String -> QInput
    toArray input = [|| listArray (0, length $$input-1) $$input ||]

{-# INLINE setupHandler #-}
setupHandler :: QH s a -> QCIdx -> QC s -> QO -> TExpQ (O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)) ->
                                                 (QH s a -> QCIdx -> QC s -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandler !hs !cidx !cs !o !h !k = [||
  do !(cidx', cs') <- pushC $$o $$cidx $$cs
     $$(k [|| pushH $$h $$hs ||] [|| cidx' ||] [|| cs' ||])
  ||]

{-# INLINE raise #-}
raise :: H s a -> CIdx -> C s -> O -> ST s (Maybe a)
raise (H SNil) !_ !_ !_                    = return Nothing
raise (H (h:::hs')) !(I# cidx) !cs !(I# o) = h o (H hs') cidx cs

evalHalt :: QInput -> QX '[a] -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalHalt _ xs _ _ _ _ _ = return [|| case $$xs of HCons x _ -> return (Just (bug x)) ||]

-- TODO: This will require a state restore later down the line
evalRet :: QInput -> QX (b ': xs) -> QK s ((b ': xs) ': ks) a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalRet input xs ks o hs cidx cs = return (resume input xs ks o hs cidx cs)

fix :: (a -> a) -> a
fix f = let x = f x in x

bug :: a -> b
bug = coerce

evalCall :: M xs ((b ': xs) ': ks) a -> MVar xs ((b ': xs) ': ks) a -> M (b ': xs) ks a
         -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalCall m v k input xs ks o hs cidx cs =
  do (μ, σm) <- ask
     return [|| fix (\r input xs ks o hs cidx cs -> $$(
         let μ' = Map.insert (GenMVar v) (GenEval [|| r ||]) μ
         in runReader (eval' m [|| input ||] [|| bug xs ||] [|| bug ks ||] [||o||] [||hs||] [||cidx||] [||cs||]) (μ', σm)
       )) $$input $$xs $$(suspend k μ σm ks) $$o $$hs $$cidx $$cs ||]

evalMuCall :: MVar xs ((b ': xs) ': ks) a -> M (b ': xs) ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalMuCall v k input xs ks o hs cidx cs =
  do (μ, σm) <- ask
     case μ Map.! (GenMVar v) of
       GenEval m -> return [|| $$(coerce m) $$input $$xs $$(suspend k μ σm ks) $$o $$hs $$cidx $$cs ||]

evalPush :: WQ x -> M (x ': xs) ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalPush x k input !xs ks o hs cidx cs = eval' k input [|| pushX $$(_code x) $$(bug xs) ||] ks o hs cidx cs

evalPop :: M xs ks a -> QInput -> QX (x ': xs) -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalPop k input !xs ks o hs cidx cs = eval' k input [|| popX_ $$(bug xs) ||] ks o hs cidx cs

evalApp :: M (y ': xs) ks a -> QInput -> QX (x ': (x -> y) ': xs) -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalApp k input !xs ks o hs cidx cs = eval' k input [|| let !(x, xs') = popX $$(bug xs); !(f, xs'') = popX xs' in pushX (f x) xs'' ||] ks o hs cidx cs

evalSat :: WQ (Char -> Bool) -> M (Char ': xs) ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalSat p k input !xs ks o hs cidx cs =
  do μ <- ask
     return (nextSafe input o (_code p) (\o c -> runReader (eval' k input [|| pushX $$c $$(bug xs) ||] ks o hs cidx cs) μ) [|| raise $$hs $$cidx $$cs ||])

evalChr :: Char -> M (Char ': xs) ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalChr c k input !xs ks o hs cidx cs =
  do μ <- ask
     return (nextSafe input o [|| (== c) ||] (\o c -> runReader (eval' k input [|| pushX $$c $$(bug xs) ||] ks o hs cidx cs) μ) [|| raise $$hs $$cidx $$cs ||])

--evalBind :: (x -> {-ST s-} (M xs ks a)) -> QInput -> QX (x ': xs) -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
--evalBind f input !xs ks o hs cidx cs =
--  do let !(x, xs') = popX xs
     --k <- f x
--     eval' (f x) input xs' ks o hs cidx cs

evalEmpt :: QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalEmpt _ !_ _ o hs cidx cs = return [|| raise $$hs $$cidx $$cs $$o ||]

evalCommit :: M xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalCommit k input !xs ks o hs cidx cs = eval' k input xs ks o [|| popH_ $$hs ||] [|| popC_ $$cidx ||] cs

evalHardFork :: M xs ks a -> M xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalHardFork p q input !xs ks o hs cidx cs =
  do μ <- ask
     let handler = [||\o hs cidx cs ->
           do !(c, cidx') <- popC (I# cidx) cs
              if c == (I# o) then $$(runReader (eval' q input xs ks [|| (I# o) ||] [|| hs ||] [|| cidx' ||] [|| cs ||]) μ)
              else raise hs cidx' cs (I# o)
           ||]
     return (setupHandler hs cidx cs o handler (\hs cidx cs -> runReader (eval' p input xs ks o hs cidx cs) μ))

evalSoftFork :: M xs ks a -> M xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalSoftFork p q input !xs ks o hs cidx cs =
  do μ <- ask
     let handler = [||\_ hs cidx cs ->
           do !(o', cidx') <- popC (I# cidx) cs
              $$(runReader (eval' q input xs ks [|| o' ||] [|| hs ||] [|| cidx' ||] [|| cs ||]) μ)
           ||]
     return (setupHandler hs cidx cs o handler (\hs cidx cs -> runReader (eval' p input xs ks o hs cidx cs) μ))

evalAttempt :: M xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalAttempt k input !xs ks o hs cidx cs =
  do μ <- ask
     let handler = [||\(_ :: O#) hs cidx cs ->
           do !(o, cidx') <- popC (I# cidx) cs
              raise hs cidx' cs o
           ||]
     return (setupHandler hs cidx cs o handler (\hs cidx cs -> runReader (eval' k input xs ks o hs cidx cs) μ))


evalLook :: M xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalLook k input !xs ks o hs cidx cs =
  do μ <- ask
     let handler = [||\o hs cidx cs -> raise hs (popC_ (I# cidx)) cs (I# o)||]
     return (setupHandler hs cidx cs o handler (\hs cidx cs -> runReader (eval' k input xs ks o hs cidx cs) μ))

evalRestore :: M xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalRestore k input !xs ks _ hs cidx cs =
  do μ <- ask
     return [||
       do (o, cidx') <- popC $$cidx $$cs
          $$(runReader (eval' k input xs ks [|| o ||] [|| popH_ $$hs ||] [|| cidx' ||] cs) μ)
       ||]

evalManyIter :: ΣVar ([x] -> [x]) -> MVar xs ks a -> QInput -> QX (x ': xs) -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalManyIter u v input !xs ks o hs cidx cs =
  do (μ, σm) <- ask
     let !(QSTRef σ) = σm DMap.! u
     case μ Map.! (GenMVar v) of
       GenEval k -> return [||
         do let !(x, xs') = popX $$(bug xs)
            modifyΣ $$σ ((\x f xs -> f (x:xs)) $! x)
            pokeC $$o $$cidx $$cs
            $$(coerce k) $$input xs' $$ks $$o $$hs $$cidx $$cs
         ||]

evalManyInitHard :: ΣVar ([x] -> [x]) -> M xs ks a -> MVar xs ks a -> M ([x] ': xs) ks a
                 -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> Reader (Ctx s a) (QST s (Maybe a))
evalManyInitHard u l v k input !xs ks o hs cidx cs =
  do (μ, σm) <- ask
     let !(QSTRef σ) = σm DMap.! u
     let handler = [||\o hs cidx cs ->
          do !(c, cidx') <- popC (I# cidx) cs
             if c == (I# o) then do ys <- pokeΣ $$σ id
                                    $$(runReader (eval' k input [|| pushX (ys []) (bug $$xs) ||] ks [|| I# o ||] [|| hs ||] [|| cidx' ||] [|| cs ||]) (μ, σm))
             else do writeΣ $$σ id; raise hs cidx' cs (I# o)
          ||]
     return (setupHandler hs cidx cs o handler (\hs cidx cs -> [||
       fix (\r input xs ks o cs ->
         $$(let μ' = Map.insert (GenMVar v) (GenEval [|| \input xs ks o _ _ cs -> r input xs ks o cs ||]) μ
            in runReader (eval' l [|| input ||] [|| bug xs ||] [|| bug ks ||] [||o||] hs cidx [||cs||]) (μ', σm)))
       $$input $$xs $$ks $$o $$cs ||]))

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

eval' :: M xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s{- -> QΣ s-} -> Reader (Ctx s a) (QST s (Maybe a))
eval' Halt input xs ks o hs cidx cs                   = trace "HALT" $ evalHalt input xs ks o hs cidx cs
eval' Ret input xs ks o hs cidx cs                    = trace "RET" $ evalRet input xs ks o hs cidx cs
eval' (Call m v k) input xs ks o hs cidx cs           = trace "CALL" $ evalCall m v k input xs ks o hs cidx cs
eval' (MuCall v k) input xs ks o hs cidx cs           = trace "MUCALL" $ evalMuCall v k input xs ks o hs cidx cs
eval' (Push x k) input xs ks o hs cidx cs             = trace "PUSH" $ evalPush x k input xs ks o hs cidx cs
eval' (Pop k) input xs ks o hs cidx cs                = trace "POP" $ evalPop k input xs ks o hs cidx cs
eval' (App k) input xs ks o hs cidx cs                = trace "APP" $ evalApp k input xs ks o hs cidx cs
eval' (Sat p k) input xs ks o hs cidx cs              = trace "SAT" $ evalSat p k input xs ks o hs cidx cs
eval' (Chr c k) input xs ks o hs cidx cs              = trace "CHR" $ evalChr c k input xs ks o hs cidx cs
--eval' (Bind f) input xs ks o hs cidx cs               = trace "" $ evalBind f input xs ks o hs cidx cs
eval' Empt input xs ks o hs cidx cs                   = trace "EMPT" $ evalEmpt input xs ks o hs cidx cs
eval' (Commit k) input xs ks o hs cidx cs             = trace "COMMIT" $ evalCommit k input xs ks o hs cidx cs
eval' (HardFork p q) input xs ks o hs cidx cs         = trace "HARDFORK" $ evalHardFork p q input xs ks o hs cidx cs
eval' (SoftFork p q) input xs ks o hs cidx cs         = trace "SOFTFORK" $ evalSoftFork p q input xs ks o hs cidx cs
eval' (Attempt k) input xs ks o hs cidx cs            = trace "ATTEMPT" $ evalAttempt k input xs ks o hs cidx cs
eval' (Look k) input xs ks o hs cidx cs               = trace "LOOK" $ evalLook k input xs ks o hs cidx cs
eval' (Restore k) input xs ks o hs cidx cs            = trace "RESTORE" $ evalRestore k input xs ks o hs cidx cs
eval' (ManyIter σ v) input xs ks o hs cidx cs         = trace "MANYITER" $ evalManyIter σ v input xs ks o hs cidx cs
eval' (ManyInitHard σ l v k) input xs ks o hs cidx cs = trace "MANYINITHARD" $ evalManyInitHard σ l v k input xs ks o hs cidx cs
--eval' (ManyInitSoft σ l k) input xs ks o hs cidx cs = trace "MANYINITSOFT" $ evalManyInitSoft σ l k input xs ks o hs cidx cs

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
