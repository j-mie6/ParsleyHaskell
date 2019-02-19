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
import Control.Monad           (MonadPlus, mzero, mplus, liftM, liftM2, join, (<$!>))
--import Data.Functor            ((<$>), (<$), ($>), (<&>), void)
import GHC.ST                  (ST(..), runST)
import Control.Monad.ST.Unsafe (unsafeIOToST)
import Control.Monad.Reader    (ReaderT, ask, runReaderT)
import qualified Control.Monad.Reader as Reader
import Data.STRef              (STRef, writeSTRef, readSTRef, modifySTRef', newSTRef)
import System.IO.Unsafe        (unsafePerformIO)
import Data.IORef              (IORef, writeIORef, readIORef, newIORef)
import GHC.StableName          (StableName(..), makeStableName, hashStableName, eqStableName)
import Data.Hashable           (Hashable, hashWithSalt, hash)
import Data.HashMap.Lazy       (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Array.Unboxed      (UArray, listArray)
import Data.Array.ST           (STArray, Ix)
import Data.Array.Base         (STUArray(..), unsafeAt, newArray_, unsafeRead, unsafeWrite, MArray, getNumElements, numElements)
import GHC.Prim                (Int#, Char#, StableName#, newByteArray#)
import GHC.Exts                (Int(..), Char(..), (-#), (+#), (*#))
import Unsafe.Coerce           (unsafeCoerce)
import Safe.Coerce             (coerce)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Debug.Trace

abc :: Char -> Bool
abc 'a' = True
abc 'b' = True
abc 'c' = True
abc _   = False

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
  --Many      :: Parser a -> Parser [a]

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
--showAST (Many p) = concat ["(many ", showAST p, "]"]

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
many p = let manyp = p <:> manyp <|> pure (WQ [] [|| [] ||]) in manyp

some :: Parser a -> Parser [a]
some p = p <:> many p

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
preprocess !p = trace "preprocessing" $ unsafePerformIO ((newIORef HashMap.empty) >>= runReaderT (preprocess' p))
  where
    preprocess' :: Parser a -> ReaderT (IORef (HashMap StableParserName GenParser)) IO (Parser a)
    -- Force evaluation of p to ensure that the stableName is correct first time
    preprocess' !p =
      do !seenRef <- ask
         !seen <- Reader.lift (readIORef seenRef)
         (StableName _name) <- Reader.lift (makeStableName p)
         let !name = StableParserName _name
         case HashMap.lookup name seen of
           Just (GenParser q) -> return $! (Rec (coerce q))
           Nothing -> mdo Reader.lift (writeIORef seenRef (HashMap.insert name (GenParser q) seen))
                          q <- preprocess'' p
                          return $! q
    preprocess'' :: Parser a -> ReaderT (IORef (HashMap StableParserName GenParser)) IO (Parser a)
    preprocess'' !(pf :<*>: px) = liftM optimise (liftM2 (:<*>:)  (preprocess' pf) (preprocess' px))
    preprocess'' !(p :*>: q)    = liftM optimise (liftM2 (:*>:)   (preprocess' p)  (preprocess' q))
    preprocess'' !(p :<*: q)    = liftM optimise (liftM2 (:<*:)   (preprocess' p)  (preprocess' q))
    --preprocess'' !(p :>>=: f)   = fmap optimise (liftM (:>>=: f) (preprocess' p))
    preprocess'' !(p :<|>: q)   = liftM optimise (liftM2 (:<|>:)  (preprocess' p)  (preprocess' q))
    preprocess'' !Empty         = return Empty
    preprocess'' !(Try p)       = liftM Try (preprocess' p)
    preprocess'' !(LookAhead p) = liftM LookAhead (preprocess' p)
    --preprocess'' !(Many p)      = liftM Many (preprocess' p)
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

newtype IRef = IRef Int deriving (Num, Eq, Ord, Ix)
data M {-s-} xs ks a where
  Halt         :: M {-s-} '[a] ks a
  Ret          :: M {-s-} (b ': xs) ((b ': xs) ': ks) a
  Push         :: WQ x -> !(M {-s-} (x ': xs) ks a) -> M {-s-} xs ks a
  Pop          :: !(M {-s-} xs ks a) -> M {-s-} (b ': xs) ks a
  App          :: !(M {-s-} (y ': xs) ks a) -> M {-s-} (x ': (x -> y) ': xs) ks a
  Chr          :: !Char -> !(M {-s-} (Char ': xs) ks a) -> M {-s-} xs ks a
  Sat          :: WQ (Char -> Bool) -> !(M {-s-} (Char ': xs) ks a) -> M {-s-} xs ks a
  Call         :: M {-s-} xs ((b ': xs) ': ks) a -> !(M {-s-} (b ': xs) ks a) -> M {-s-} xs ks a
  --Bind         :: !(x -> {-ST s-} (M {-s-} xs ks a)) -> M {-s-} (x ': xs) ks a
  Empt         :: M {-s-} xs ks a
  Commit       :: !(M {-s-} xs ks a) -> M {-s-} xs ks a
  SoftFork     :: !(M {-s-} xs ks a) -> M {-s-} xs ks a -> M {-s-} xs ks a
  HardFork     :: !(M {-s-} xs ks a) -> M {-s-} xs ks a -> M {-s-} xs ks a
  Attempt      :: !(M {-s-} xs ks a) -> M {-s-} xs ks a
  Look         :: !(M {-s-} xs ks a) -> M {-s-} xs ks a
  Restore      :: !(M {-s-} xs ks a) -> M {-s-} xs ks a
  --ManyIter     :: !(STRef s ([x] -> [x])) -> (M s xs ks a) -> M s (x ': xs) ks a
  --ManyInitSoft :: !(STRef s ([x] -> [x])) -> !(M s xs ks a) -> !(M s ([x] ': xs) ks a) -> M s xs ks a
  --ManyInitHard :: !(STRef s ([x] -> [x])) -> !(M s xs ks a) -> !(M s ([x] ': xs) ks a) -> M s xs ks a

instance Show (M {-s-} xs ks a) where
  show Halt = "Halt"
  show Ret = "Ret"
  show (Call _ k) = "(Call ? " ++ show k ++ ")"
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
  --show (ManyIter _ k) = "(ManyIter " ++ show k ++ ")"
  --show (ManyInitSoft _ l k) = "(ManyInitSoft " ++ show l ++ " " ++ show k ++ ")"
  --show (ManyInitHard _ l k) = "(ManyInitHard " ++ show l ++ " " ++ show k ++ ")"

data GenM s a = forall xs ks. GenM (M {-s-} xs ks a)
compile :: Parser a -> M {-s-} '[] '[] a
compile p = trace "compiling" $ runST $ (newSTRef HashMap.empty) >>= runReaderT (compile' p Halt)

compile' :: Parser a -> M {-s-} (a ': xs) ks b -> ReaderT (STRef s (HashMap StableParserName (GenM s b))) (ST s) (M {-s-} xs ks b)
compile' !(Pure x) !m        = trace "pure" $ do return $! (Push x m)
compile' !(Char c) !m        = trace "char" $ do return $! (Chr c m)
compile' !(Satisfy p) !m     = trace "satisfy" $ do return $! (Sat p m)
compile' !(pf :<*>: px) !m   = trace "<*>" $ do !pxc <- compile' px (App m); compile' pf pxc
compile' !(p :*>: q) !m      = trace "*>" $ do !qc <- compile' q m; compile' p (Pop qc)
compile' !(p :<*: q) !m      = trace "<*" $ do !qc <- compile' q (Pop m); compile' p qc
compile' !Empty !m           = trace "empty" $ do return $! Empt
--compile' !(Try p :<|>: q) !m = do liftM2 SoftFork (compile' p (Commit m)) (compile' q m)
compile' !(p :<|>: q) !m     = trace "<|>" $ do liftM2 HardFork (compile' p (Commit m)) (compile' q m)
--compile' !(p :>>=: f) !m     = do compile' p (Bind f')
--  where f' x = runST $ (newSTRef HashMap.empty) >>= runReaderT (compile' (preprocess (f x)) m)
compile' !(Try p) !m         = trace "try" $ do liftM Attempt (compile' p (Commit m))
compile' !(LookAhead p) !m   = trace "lookAhead" $ do liftM Look (compile' p (Restore m))
compile' !(Rec !p) !m        =
  do (StableName _name) <- Reader.lift (unsafeIOToST (makeStableName p))
     !ref <- ask
     seen <- Reader.lift (readSTRef ref)
     let !name = StableParserName _name
     case HashMap.lookup name seen of
       Just (GenM n) -> trace "fixpoint found" $ return $! Call (coerce n) m
       Nothing -> trace "fixpoint missing" $ mdo Reader.lift (writeSTRef ref (HashMap.insert name (GenM n) seen))
                                                 n <- compile' p Ret
                                                 return $! Call n m
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
  --KCons :: !(M {-s-} xs ks a) -> !(HKList s ks a) -> HKList s (xs ': ks) a
  KCons :: !(Input -> X xs -> K s ks a -> O -> H s a -> CIdx -> C s -> ST s (Maybe a)) -> !(HKList s ks a) -> HKList s (xs ': ks) a

type Input = UArray Int Char
type QInput = TExpQ Input
newtype H s a = H (SList (O -> H s a -> CIdx -> C s -> ST s (Maybe a)))
type QH s a = TExpQ (H s a)
type X = HList
type QX xs = TExpQ (X xs)
type K = HKList
type QK s ks a = TExpQ (K s ks a)
type CIdx = Int
type QCIdx = TExpQ CIdx
type C s = STUArray s Int Int
type QC s = TExpQ (C s)
type O = Int
type QO = TExpQ O
data State s = forall a. State a (STRef s [a])
type Σ s = STArray s IRef (State s)
type QST s a = TExpQ (ST s a)

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
suspend :: M {-s-} xs ks a -> QK s ks a -> QK s (xs ': ks) a
suspend m ks = [|| KCons (\input xs ks o hs cidx cs ->
                          $$(eval' m [|| input ||] [|| xs ||] [||ks||] [||o||] [||hs||] [||cidx||] [||cs||])) $$ks ||]
-- NOTE: coerce here is needed because of TTH bug!
resume :: QInput -> QX xs -> QK s (xs ': ks) a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
resume input xs ks o hs cidx cs = [|| case $$ks of (KCons k ks) -> k $$input $$(coerce xs) ks $$o $$hs $$cidx $$cs ||]

makeH :: ST s (H s a)
makeH = return $! (H SNil)
pushH :: (O -> H s a -> CIdx -> C s -> ST s (Maybe a)) -> H s a -> H s a
pushH !h !(H hs) = H (h:::hs)
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
popC_ :: CIdx -> CIdx
popC_ !i = i - 1
pokeC :: O -> CIdx -> C s -> ST s ()
pokeC !c !i !cs = unsafeWrite cs i c

makeO :: ST s O
makeO = return 0
nextSafe :: QInput -> QO -> TExpQ (Char -> Bool) -> (QO -> TExpQ Char -> QST s (Maybe a)) -> TExpQ (O -> ST s (Maybe a)) -> QST s (Maybe a)
nextSafe input o p good bad = [||
    if  numElements $$input > $$o then let !c = unsafeAt $$input $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else $$bad $$o
    else $$bad $$o
  ||]

forArray_ :: Σ s -> (State s -> ST s ()) -> ST s ()
forArray_ arr f =
  do sz <- getNumElements arr
     let go !n = do !x <- unsafeRead arr n
                    f x
                    if n == 0 then return $! ()
                    else go $! (n-1)
     go (sz-1)

--makeΣ :: [State s] -> ST s (Σ s)
--makeΣ σs =

save :: Σ s -> ST s ()
save σs = forArray_ σs up where up (State x σ) = modifySTRef' σ (x:)

restore :: Σ s -> ST s ()
restore σs = forArray_ σs down where down (State x σ) = modifySTRef' σ (\(_:xs) -> xs)

eval :: TExpQ String -> M {-s-} '[] '[] a -> QST s (Maybe a)
eval input !m = trace "eval" $ [||
  do xs <- makeX
     ks <- makeK
     hs <- makeH
     !(cidx, cs) <- makeC
     o <- makeO
     let input' = $$(toArray input)
     $$(eval' m [||input'||] [||xs||] [||ks||] [||o||] [||hs||] [||cidx||] [||cs||])
  ||]
  where
    toArray :: TExpQ String -> QInput
    toArray input = [|| listArray (0, length $$input-1) $$input ||]

{-# INLINE setupHandler #-}
setupHandler :: QH s a -> QCIdx -> QC s -> QO -> TExpQ (O -> H s a -> CIdx -> C s -> ST s (Maybe a)) ->
                                                 (QH s a -> QCIdx -> QC s -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandler !hs !cidx !cs !o !h !k = [||
  do !(cidx', cs') <- pushC $$o $$cidx $$cs
     $$(k [|| pushH $$h $$hs ||] [|| cidx' ||] [|| cs' ||])
  ||]

{-# INLINE raise #-}
raise :: H s a -> CIdx -> C s -> O -> ST s (Maybe a)
raise (H SNil) !_ !_ !_          = return Nothing
raise (H (h:::hs')) !cidx !cs !o = h o (H hs') cidx cs

evalHalt :: QInput -> QX '[a] -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalHalt _ xs _ _ _ _ _ = [|| case $$xs of HCons x _ -> return (Just x) ||]

-- TODO: This will require a state restore later down the line
evalRet :: QInput -> QX (b ': xs) -> QK s ((b ': xs) ': ks) a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalRet input xs ks o hs cidx cs = resume input xs ks o hs cidx cs

evalCall :: M {-s-} xs ((b ': xs) ': ks) a -> M {-s-} (b ': xs) ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalCall m k input xs ks o hs cidx cs = let !ks' = suspend k ks in eval' m input xs ks' o hs cidx cs

evalPush :: WQ x -> M {-s-} (x ': xs) ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalPush x k input !xs ks o hs cidx cs = eval' k input [|| pushX $$(_code x) $$xs ||] ks o hs cidx cs

evalPop :: M {-s-} xs ks a -> QInput -> QX (x ': xs) -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalPop k input !xs ks o hs cidx cs = eval' k input [|| popX_ $$xs ||] ks o hs cidx cs

evalApp :: M {-s-} (y ': xs) ks a -> QInput -> QX (x ': (x -> y) ': xs) -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalApp k input !xs ks o hs cidx cs = eval' k input [|| let !(x, xs') = popX $$xs; !(f, xs'') = popX xs' in pushX (f x) xs'' ||] ks o hs cidx cs

evalSat :: WQ (Char -> Bool) -> M {-s-} (Char ': xs) ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalSat p k input !xs ks o hs cidx cs = nextSafe input o (_code p) (\o c -> eval' k input [|| pushX $$c $$xs ||] ks o hs cidx cs) [|| raise $$hs $$cidx $$cs ||]

evalChr :: Char -> M {-s-} (Char ': xs) ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalChr c k input !xs ks o hs cidx cs = nextSafe input o [|| (== c) ||] (\o c -> eval' k input [|| pushX $$c $$xs ||] ks o hs cidx cs) [|| raise $$hs $$cidx $$cs ||]

--evalBind :: (x -> {-ST s-} (M {-s-} xs ks a)) -> QInput -> QX (x ': xs) -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
--evalBind f input !xs ks o hs cidx cs =
--  do let !(x, xs') = popX xs
     --k <- f x
--     eval' (f x) input xs' ks o hs cidx cs

evalEmpt :: QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalEmpt _ !_ _ o hs cidx cs = [|| raise $$hs $$cidx $$cs $$o ||]

evalCommit :: M {-s-} xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalCommit k input !xs ks o hs cidx cs = eval' k input xs ks o [|| popH_ $$hs ||] [|| popC_ $$cidx ||] cs

evalHardFork :: M {-s-} xs ks a -> M {-s-} xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalHardFork p q input !xs ks o hs cidx cs = setupHandler hs cidx cs o handler (eval' p input xs ks o)
  where
    handler = [||\o hs cidx cs ->
      do !(c, cidx') <- popC cidx cs
         if c == o then $$(eval' q input xs ks [|| o ||] [|| hs ||] [|| cidx' ||] [|| cs ||])
         else raise hs cidx' cs o
      ||]

evalSoftFork :: M {-s-} xs ks a -> M {-s-} xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalSoftFork p q input !xs ks o hs cidx cs = setupHandler hs cidx cs o handler (eval' p input xs ks o)
  where
    handler = [||\_ hs cidx cs ->
      do !(o', cidx') <- popC cidx cs
         $$(eval' q input xs ks [|| o' ||] [|| hs ||] [|| cidx' ||] [|| cs ||])
      ||]

evalAttempt :: M {-s-} xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalAttempt k input !xs ks o hs cidx cs = setupHandler hs cidx cs o handler (eval' k input xs ks o)
  where
    handler = [||\_ hs cidx cs ->
      do !(o, cidx') <- popC cidx cs
         raise hs cidx' cs o
      ||]

evalLook :: M {-s-} xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalLook k input !xs ks o hs cidx cs = setupHandler hs cidx cs o handler (eval' k input xs ks o)
  where handler = [||\o hs cidx cs -> raise hs (popC_ cidx) cs o||]

evalRestore :: M {-s-} xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
evalRestore k input !xs ks _ hs cidx cs = [||
  do (o, cidx') <- popC $$cidx $$cs
     $$(eval' k input xs ks [|| o ||] [|| popH_ $$hs ||] [|| cidx' ||] cs)
  ||]

{-evalManyIter :: STRef s ([x] -> [x]) -> M {-s-} xs ks a -> Input -> X (x ': xs) -> K s ks a -> O# -> H s a -> CIdx# -> C s -> QST s (Maybe a)
evalManyIter σ k input !xs ks o hs cidx cs =
  do let !(x, xs') = popX xs
     modifySTRef' σ ((\x f xs -> f (x:xs)) $! x)
     pokeC o cidx cs
     eval' k input xs' ks o hs cidx cs

evalManyInitHard :: STRef s ([x] -> [x]) -> M {-s-} xs ks a -> M {-s-} ([x] ': xs) ks a -> Input -> X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> QST s (Maybe a)
evalManyInitHard σ l k input !xs ks o hs cidx cs = setupHandler hs cidx cs o handler (eval' l input xs ks o)
  where
    handler o hs cidx cs =
      do !(c, I# cidx') <- popC cidx cs
         if c == (I# o) then do ys <- readSTRef σ
                                writeSTRef σ id
                                eval' k input (pushX (ys []) xs) ks o hs cidx' cs
         else do writeSTRef σ id; raise hs cidx' cs o

evalManyInitSoft :: STRef s ([x] -> [x]) -> M {-s-} xs ks a -> M {-s-} ([x] ': xs) ks a -> Input -> X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> QST s (Maybe a)
evalManyInitSoft σ l k input !xs ks o hs cidx cs = setupHandler hs cidx cs o handler (eval' l input xs ks o)
  where
    handler _ hs cidx cs =
      do !(I# o, I# cidx') <- popC cidx cs
         ys <- readSTRef σ
         writeSTRef σ id
         eval' k input (pushX (ys []) xs) ks o hs cidx' cs-}

eval' :: M {-s-} xs ks a -> QInput -> QX xs -> QK s ks a -> QO -> QH s a -> QCIdx -> QC s -> QST s (Maybe a)
eval' Halt input xs ks o hs cidx cs                 = trace "HALT" $ evalHalt input xs ks o hs cidx cs
eval' Ret input xs ks o hs cidx cs                  = trace "RET" $ evalRet input xs ks o hs cidx cs
eval' (Call m k) input xs ks o hs cidx cs           = trace "CALL" $ evalCall m k input xs ks o hs cidx cs
eval' (Push x k) input xs ks o hs cidx cs           = trace "PUSH" $ evalPush x k input xs ks o hs cidx cs
eval' (Pop k) input xs ks o hs cidx cs              = trace "POP" $ evalPop k input xs ks o hs cidx cs
eval' (App k) input xs ks o hs cidx cs              = trace "APP" $ evalApp k input xs ks o hs cidx cs
eval' (Sat p k) input xs ks o hs cidx cs            = trace "SAT" $ evalSat p k input xs ks o hs cidx cs
eval' (Chr c k) input xs ks o hs cidx cs            = trace "CHR" $ evalChr c k input xs ks o hs cidx cs
--eval' (Bind f) input xs ks o hs cidx cs             = trace "" $ evalBind f input xs ks o hs cidx cs
eval' Empt input xs ks o hs cidx cs                 = trace "EMPT" $ evalEmpt input xs ks o hs cidx cs
eval' (Commit k) input xs ks o hs cidx cs           = trace "COMMIT" $ evalCommit k input xs ks o hs cidx cs
eval' (HardFork p q) input xs ks o hs cidx cs       = trace "HARDFORK" $ evalHardFork p q input xs ks o hs cidx cs
eval' (SoftFork p q) input xs ks o hs cidx cs       = trace "SOFTFORK" $ evalSoftFork p q input xs ks o hs cidx cs
eval' (Attempt k) input xs ks o hs cidx cs          = trace "ATTEMPT" $ evalAttempt k input xs ks o hs cidx cs
eval' (Look k) input xs ks o hs cidx cs             = trace "LOOK" $ evalLook k input xs ks o hs cidx cs
eval' (Restore k) input xs ks o hs cidx cs          = trace "RESTORE" $ evalRestore k input xs ks o hs cidx cs
--eval' (ManyIter σ k) input xs ks o hs cidx cs       = trace "" $ evalManyIter σ k input xs ks o hs cidx cs
--eval' (ManyInitHard σ l k) input xs ks o hs cidx cs = trace "" $ evalManyInitHard σ l k input xs ks o hs cidx cs
--eval' (ManyInitSoft σ l k) input xs ks o hs cidx cs = trace "" $ evalManyInitSoft σ l k input xs ks o hs cidx cs

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

{-data CompiledParser a = Compiled (forall s. M {-s-} '[] '[] a)

mkParser :: Parser a -> CompiledParser a
mkParser p = Compiled (runST (slightyUnsafeLeak (compile (preprocess p))))
  where
    slightyUnsafeLeak :: (forall s. ST s (M s '[] '[] a)) -> (forall s. ST s (M s' '[] '[] a))
    slightyUnsafeLeak = unsafeCoerce

runCompiledParser :: CompiledParser a -> String -> Maybe a
runCompiledParser (Compiled p) input = runST (eval input p)-}

showM :: Parser a -> String
showM p = show (compile (preprocess p))
