{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MagicHash, UnboxedTuples #-}
module Parsley ( Parser, CompiledParser(..)
               , runParser, mkParser, runCompiledParser
               -- Functor
               , fmap, (<$>), (<$), void
               -- Applicative
               , pure, (<*>), (*>), (<*), (<**>), (<:>), liftA2
               -- Alternative
               , empty, (<|>), some, many, optional, choice
               -- Monoidal
               , Monoidal, unit, (<~>), (<~), (~>)
               -- Monadic
               , return, (>>=), (>>), mzero, mplus, join
               -- Primitives
               , satisfy, item, char
               , lookAhead, try
               -- Composites
               , eof, notFollowedBy
               , traverse, sequence, string--, manyUnrolled
               ) where

import Prelude hiding          ((*>), (<*), (>>), traverse, sequence, (<$), (<**>))
import Control.Applicative     (Alternative, (<|>), empty, liftA2, liftA)
import Control.Monad           (MonadPlus, mzero, mplus, liftM, liftM2, join, (<$!>))
import Control.Monad.ST        (ST, runST)
import Control.Monad.ST.Unsafe (unsafeInterleaveST)
import Control.Monad.Reader    (ReaderT, lift, ask, runReaderT)
import Data.STRef              (STRef, writeSTRef, readSTRef, modifySTRef', newSTRef)
import System.IO.Unsafe        (unsafePerformIO)
import Data.IORef              (IORef, writeIORef, readIORef, newIORef)
import GHC.StableName          (StableName(..), makeStableName, hashStableName, eqStableName)
import Data.Hashable           (Hashable, hashWithSalt, hash)
import Data.HashSet            (HashSet)
import qualified Data.HashSet as HashSet
import Data.Array.Unboxed      (UArray, listArray)
import Data.Array.ST           (STArray, STUArray)
import Data.Array.Base         (unsafeAt, newArray_, unsafeNewArray_, unsafeRead, unsafeWrite, MArray, getNumElements, numElements)
import GHC.Prim                (Int#, Char#, StableName#)
import GHC.Exts                (Int(..), Char(..), (-#), (+#))
import Unsafe.Coerce           (unsafeCoerce)

data HList xs where
  HNil :: HList '[]
  HCons :: !a -> !(HList as) -> HList (a ': as)

-- AST
data Parser a where
  Pure      :: a -> Parser a
  Char      :: Char -> Parser Char
  Satisfy   :: (Char -> Bool) -> Parser Char
  (:<*>:)   :: Parser (a -> b) -> Parser a -> Parser b
  (:*>:)    :: Parser a -> Parser b -> Parser b
  (:<*:)    :: Parser a -> Parser b -> Parser a
  (:>>=:)   :: Parser a -> (a -> Parser b) -> Parser b
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
showAST (p :>>=: f) = concat ["(", showAST p, " >>= f)"]
showAST (p :<|>: q) = concat ["(", showAST p, " <|> ", showAST q, ")"]
showAST Empty = "empty"
showAST (Try p) = concat ["(try ", showAST p, ")"]
showAST (LookAhead p) = concat ["(lookAhead ", showAST p, ")"]
showAST (Rec _) = "recursion point!"
showAST (Many p) = concat ["(many ", showAST p, "]"]

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
many p = {-let manyp = p <:> manyp <|> pure [] in manyp--}Many p

some :: Parser a -> Parser [a]
some p = p <:> many p

(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = liftA2 (:)

(<**>) :: Parser a -> Parser (a -> b) -> Parser b
(<**>) = liftA2 (flip ($))

class Functor f => Monoidal f where
  unit :: f ()
  (<~>) :: f a -> f b -> f (a, b)

(<~) :: Monoidal f => f a -> f b -> f a
p <~ q = fst <$> (p <~> q)

(~>) :: Monoidal f => f a -> f b -> f b
p ~> q = snd <$> (p <~> q)

instance (Functor f, Applicative f) => Monoidal f where
  unit = pure ()
  (<~>) = liftA2 (,)

(<$) :: a -> Parser b -> Parser a
x <$ p = p *> pure x

satisfy :: (Char -> Bool) -> Parser Char
satisfy = Satisfy

char :: Char -> Parser Char
char = Char--satisfy (== c)

item :: Parser Char
item = satisfy (const True)

try :: Parser a -> Parser a
try = Try

lookAhead :: Parser a -> Parser a
lookAhead = LookAhead

sequence :: [Parser a] -> Parser [a]
sequence = foldr (<:>) (pure [])

traverse :: (a -> Parser b) -> [a] -> Parser [b]
traverse f = sequence . map f

string :: String -> Parser String
string = traverse char

void :: Parser a -> Parser ()
void = (() <$)

optional :: Parser a -> Parser ()
optional p = void p <|> unit

choice :: [Parser a] -> Parser a
choice = foldr (<|>) empty

-- NOTE: When the intrinsic is introduced to fix this properly, prove the law:
--   notFollowedBy . notFollowedBy = lookAhead
notFollowedBy :: Parser a -> Parser ()
notFollowedBy p = try (join ((try p *> return empty) <|> return unit))
                  --try ((try p *> empty) <|> unit)

eof :: Parser ()
eof = notFollowedBy item

data StableParserName = forall a. StableParserName (StableName# (Parser a))
instance Eq StableParserName where (StableParserName n) == (StableParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable StableParserName where
  hash (StableParserName n) = hashStableName (StableName n)
  hashWithSalt salt (StableParserName n) = hashWithSalt salt (StableName n)

preprocess :: Parser a -> Parser a
preprocess !p = unsafePerformIO ((newIORef HashSet.empty) >>= runReaderT (preprocess' p))
  where
    preprocess' :: Parser a -> ReaderT (IORef (HashSet StableParserName)) IO (Parser a)
    preprocess' !p = fix p >>= preprocess''
    preprocess'' :: Parser a -> ReaderT (IORef (HashSet StableParserName)) IO (Parser a)
    preprocess'' !(pf :<*>: px) = fmap optimise (liftM2 (:<*>:)  (preprocess' pf) (preprocess' px))
    preprocess'' !(p :*>: q)    = fmap optimise (liftM2 (:*>:)   (preprocess' p)  (preprocess' q))
    preprocess'' !(p :<*: q)    = fmap optimise (liftM2 (:<*:)   (preprocess' p)  (preprocess' q))
    preprocess'' !(p :>>=: f)   = fmap optimise (liftM (:>>=: f) (preprocess' p))
    preprocess'' !(p :<|>: q)   = fmap optimise (liftM2 (:<|>:)  (preprocess' p)  (preprocess' q))
    preprocess'' !Empty         = return Empty
    preprocess'' !(Try p)       = liftM Try (preprocess' p)
    preprocess'' !(LookAhead p) = liftM LookAhead (preprocess' p)
    preprocess'' !(Many p)      = liftM Many (preprocess' p)
    preprocess'' !p             = return p

    fix :: Parser a -> ReaderT (IORef (HashSet StableParserName)) IO (Parser a)
    -- Force evaluation of p to ensure that the stableName is correct first time
    fix !p =
      do !seenRef <- ask
         !seen <- lift (readIORef seenRef)
         !(StableName _name) <- lift (makeStableName p)
         let !name = StableParserName _name
         if (HashSet.member name) seen
           then return $! (Rec p)
           else do lift (writeIORef seenRef ((HashSet.insert $! name) seen))
                   return $! p

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

data M s xs a where
  Halt         :: M s '[a] a
  Push         :: !x -> M s (x ': xs) a -> M s xs a
  Pop          :: M s xs a -> M s (b ': xs) a
  App          :: M s (y ': xs) a -> M s (x ': (x -> y) ': xs) a
  Chr          :: Char# -> M s (Char ': xs) a -> M s xs a
  Sat          :: (Char -> Bool) -> M s (Char ': xs) a -> M s xs a
  Bind         :: (x -> ST s (M s xs a)) -> M s (x ': xs) a
  Empt         :: M s xs a
  Commit       :: M s xs a -> M s xs a
  SoftFork     :: M s xs a -> M s xs a -> M s xs a
  HardFork     :: M s xs a -> M s xs a -> M s xs a
  Attempt      :: M s xs a -> M s xs a
  Look         :: M s xs a -> M s xs a
  Restore      :: M s xs a -> M s xs a
  ManyIter     :: STRef s ([x] -> [x]) -> M s xs a -> M s (x ': xs) a
  ManyInitSoft :: STRef s ([x] -> [x]) -> M s xs a -> M s ([x] ': xs) a -> M s xs a
  ManyInitHard :: STRef s ([x] -> [x]) -> M s xs a -> M s ([x] ': xs) a -> M s xs a

instance Show (M ss xs a) where
  show Halt = "Halt"
  show (Push _ k) = "(Push x " ++ show k ++ ")"
  show (Pop k) = "(Pop " ++ show k ++ ")"
  show (App k) = "(App " ++ show k ++ ")"
  show (Chr c k) = "(Chr " ++ show (C# c) ++ " " ++ show k ++ ")"
  show (Sat _ k) = "(Sat f " ++ show k ++ ")"
  show (Bind _) = "(Bind ?)"
  show Empt = "Empt"
  show (Commit k) = "(Commit " ++ show k ++ ")"
  show (SoftFork p q) = "(SoftFork " ++ show p ++ " " ++ show q ++ ")"
  show (HardFork p q) = "(HardFork " ++ show p ++ " " ++ show q ++ ")"
  show (Attempt k) = "(Try " ++ show k ++ ")"
  show (Look k) = "(Look " ++ show k ++ ")"
  show (Restore k) = "(Restore " ++ show k ++ ")"
  show (ManyIter _ k) = "(ManyIter " ++ show k ++ ")"
  show (ManyInitSoft _ l k) = "(ManyInitSoft " ++ show l ++ " " ++ show k ++ ")"
  show (ManyInitHard _ l k) = "(ManyInitHard " ++ show l ++ " " ++ show k ++ ")"

compile :: Parser a -> ST s (M s '[] a)
compile = flip compile' Halt

compile' :: Parser a -> M s (a ': xs) b -> ST s (M s xs b)
compile' (Pure x) m        = do return (Push x m)
compile' (Char (C# c)) m   = do return (Chr c m)
compile' (Satisfy p) m     = do return (Sat p m)
compile' (pf :<*>: px) m   = do pxc <- compile' px (App m); compile' pf pxc
compile' (p :*>: q) m      = do qc <- compile' q m; compile' p (Pop qc)
compile' (p :<*: q) m      = do qc <- compile' q (Pop m); compile' p qc
compile' Empty m           = do return Empt
--compile' (Try p :<|>: q) m = do SoftFork <$> compile' p (Commit m) <*> compile' q m
compile' (p :<|>: q) m     = do HardFork <$> compile' p (Commit m) <*> compile' q m
compile' (p :>>=: f) m     = do compile' p (Bind (flip compile' m . preprocess . f))
compile' (Try p) m         = do Attempt <$> compile' p (Commit m)
compile' (LookAhead p) m   = do Look <$> compile' p (Restore m)
--                              Using unsafeInterleaveST prevents this code from being compiled until it is asked for!
compile' (Rec p) m         = do unsafeInterleaveST (compile' (preprocess p) m)
{-compile' (Many (Try p)) m  =
  do σ <- newSTRef []
     rec manyp <- compile' p (ManyIter σ manyp)
     return (ManyInitSoft σ manyp m)-}
compile' (Many p) m        =
  do σ <- newSTRef id
     rec manyp <- compile' p (ManyIter σ manyp)
     return (ManyInitHard σ manyp m)

data SList a = !a ::: !(SList a) | SNil
type Input = UArray Int Char
newtype H s a = H (SList (O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)))
type X = HList
type CIdx = Int
type CIdx# = Int#
type C s = STUArray s Int Int
type O = Int
type O# = Int#

double :: (Monad m, MArray a e m) => a Int e -> m (a Int e)
double arr =
  do sz <- getNumElements arr
     resize arr sz (sz * 2)

resize :: (Monad m, MArray a e m) => a Int e -> Int -> Int -> m (a Int e)
resize arr old new =
  do arr' <- unsafeNewArray_ (0, new-1)
     let copy from to n = do x <- unsafeRead from n
                             unsafeWrite to n x
                             if n == 0 then return ()
                             else copy from to $! (n-1)
                          in copy arr arr' (old-1)
     return $! arr'

makeX :: ST s (X '[])
makeX = return HNil
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

makeH :: ST s (H s a)
makeH = return $! (H SNil)
pushH :: (O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)) -> H s a -> H s a
pushH !h !(H hs) = H (h:::hs)
--popH :: H s a -> CIdx -> C s -> O -> ST s (Maybe a)
--popH !(H (h:::hs)) cidx !cs o = h o (H hs) cidx cs
popH_ :: H s a -> H s a
popH_ !(H (_:::hs)) = H hs

makeC :: ST s (CIdx, C s)
makeC = do cs <- newArray_ (0, 3)
           return $! (-1, cs)
pushC :: O# -> CIdx# -> C s -> ST s (CIdx, C s)
pushC c i !cs = let !j = (I# i) + 1 in
  do sz <- getNumElements cs
     if j == sz then do cs' <- double cs
                        unsafeWrite cs' j (I# c)
                        return $! (j, cs')
     else do unsafeWrite cs j (I# c); return $! (j, cs)
popC :: CIdx# -> C s -> ST s (O, CIdx)
popC !i !cs = do !c <- unsafeRead cs (I# i); return $! (c, I# (i -# 1#))
popC_ :: CIdx# -> CIdx#
popC_ !i = i -# 1#
pokeC :: O# -> CIdx# -> C s -> ST s ()
pokeC !c !i !cs = unsafeWrite cs (I# i) (I# c)

makeO :: ST s O
makeO = return 0
--more :: UArray Int Char -> O s -> ST s Bool
--more input o = (size input >) <$!> readSTRefU o
--next :: UArray Int Char -> O s -> ST s Char
--next input o = (unsafeAt input) <$!> readSTRefU o
{-# INLINE nextSafe #-}
nextSafe :: Input -> O# -> (Char -> Bool) -> (O# -> Char -> ST s (Maybe a)) -> (O# -> ST s (Maybe a)) -> ST s (Maybe a)
nextSafe !input !o !p !good !bad =
  if  numElements input > (I# o) then let !c = unsafeAt input (I# o) in if p c then good (o +# 1#) c else bad o
  else bad o

eval :: String -> M s '[] a -> ST s (Maybe a)
eval input m =
  do xs <- makeX
     hs <- makeH
     !(I# cidx, cs) <- makeC
     I# o <- makeO
     eval' m (listArray (0, length input-1) input) xs o hs cidx cs

{-# INLINE setupHandler #-}
setupHandler :: H s a -> CIdx# -> C s -> O# -> (O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)) ->
                                               (H s a -> CIdx# -> C s -> ST s (Maybe a)) -> ST s (Maybe a)
setupHandler !hs !cidx !cs !o !h !k =
  do let !hs' = pushH h hs
     !(I# cidx', cs') <- pushC o cidx cs
     k hs' cidx' cs'

{-# INLINE raise #-}
raise :: H s a -> CIdx# -> C s -> O# -> ST s (Maybe a)
raise (H SNil) !_ !_ !_          = return Nothing
raise (H (h:::hs')) !cidx !cs !o = h o (H hs') cidx cs

evalHalt :: Input -> X (a ': xs) -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalHalt _ !(HCons x _) _ _ _ _ = return (Just x)

evalPush :: x -> M s (x ': xs) a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalPush x k input !xs o hs cidx cs = eval' k input (pushX x xs) o hs cidx cs

evalPop :: M s xs a -> Input -> X (x ': xs) -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalPop k input !xs o hs cidx cs = eval' k input (popX_ xs) o hs cidx cs

evalApp :: M s (y ': xs) a -> Input -> X (x ': (x -> y) ': xs) -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalApp k input !xs o hs cidx cs =
  let !(x, xs') = popX xs
      !(f, xs'') = popX xs'
  in eval' k input (pushX (f x) xs'') o hs cidx cs

evalSat :: (Char -> Bool) -> M s (Char ': xs) a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalSat p k input !xs o hs cidx cs = nextSafe input o p (\o c -> eval' k input (pushX c xs) o hs cidx cs) (raise hs cidx cs)

evalChr :: Char# -> M s (Char ': xs) a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalChr c k input !xs o hs cidx cs = nextSafe input o (== (C# c)) (\o c -> eval' k input (pushX c xs) o hs cidx cs) (raise hs cidx cs)

evalBind :: (x -> ST s (M s xs a)) -> Input -> X (x ': xs) -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalBind f input !xs o hs cidx cs =
  do let !(x, xs') = popX xs
     k <- f x
     eval' k input xs' o hs cidx cs

evalEmpt :: Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalEmpt _ !_ o hs cidx cs = raise hs cidx cs o

evalCommit :: M s xs a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalCommit k input !xs o hs cidx cs = eval' k input xs o (popH_ hs) (popC_ cidx) cs

evalHardFork :: M s xs a -> M s xs a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalHardFork p q input !xs o hs cidx cs = setupHandler hs cidx cs o handler (eval' p input xs o)
  where
    handler o hs cidx cs =
      do !(c, I# cidx') <- popC cidx cs
         if c == (I# o) then eval' q input xs o hs cidx' cs
         else raise hs cidx' cs o

evalSoftFork :: M s xs a -> M s xs a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalSoftFork p q input !xs o hs cidx cs = setupHandler hs cidx cs o handler (eval' p input xs o)
  where
    handler _ hs cidx cs =
      do !(I# o', I# cidx') <- popC cidx cs
         eval' q input xs o' hs cidx' cs

evalAttempt :: M s xs a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalAttempt k input !xs o hs cidx cs = setupHandler hs cidx cs o handler (eval' k input xs o)
  where
    handler :: O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
    handler _ hs cidx cs =
      do !(I# o, I# cidx') <- popC cidx cs
         raise hs cidx' cs o

evalLook :: M s xs a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalLook k input !xs o hs cidx cs = setupHandler hs cidx cs o handler (eval' k input xs o)
  where handler o hs cidx cs = raise hs (popC_ cidx) cs o

evalRestore :: M s xs a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalRestore k input !xs _ hs cidx cs = do (I# o, I# cidx') <- popC cidx cs; eval' k input xs o (popH_ hs) cidx' cs

evalManyIter :: STRef s ([x] -> [x]) -> M s xs a -> Input -> X (x ': xs) -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalManyIter σ k input !xs o hs cidx cs =
  do let !(x, xs') = popX xs
     modifySTRef' σ ((\x f xs -> f (x:xs)) $! x)
     pokeC o cidx cs
     eval' k input xs' o hs cidx cs

evalManyInitHard :: STRef s ([x] -> [x]) -> M s xs a -> M s ([x] ': xs) a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalManyInitHard σ l k input !xs o hs cidx cs = setupHandler hs cidx cs o handler (eval' l input xs o)
  where
    handler o hs cidx cs =
      do !(c, I# cidx') <- popC cidx cs
         if c == (I# o) then do ys <- readSTRef σ
                                writeSTRef σ id
                                eval' k input (pushX (ys []) xs) o hs cidx' cs
         else do writeSTRef σ id; raise hs cidx' cs o

evalManyInitSoft :: STRef s ([x] -> [x]) -> M s xs a -> M s ([x] ': xs) a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
evalManyInitSoft σ l k input !xs o hs cidx cs = setupHandler hs cidx cs o handler (eval' l input xs o)
  where
    handler _ hs cidx cs =
      do !(I# o, I# cidx') <- popC cidx cs
         ys <- readSTRef σ
         writeSTRef σ id
         eval' k input (pushX (ys []) xs) o hs cidx' cs

eval' :: M s xs a -> Input -> X xs -> O# -> H s a -> CIdx# -> C s -> ST s (Maybe a)
eval' Halt input xs o hs cidx cs                 = evalHalt input xs o hs cidx cs
eval' (Push x k) input xs o hs cidx cs           = evalPush x k input xs o hs cidx cs
eval' (Pop k) input xs o hs cidx cs              = evalPop k input xs o hs cidx cs
eval' (App k) input xs o hs cidx cs              = evalApp k input xs o hs cidx cs
eval' (Sat p k) input xs o hs cidx cs            = evalSat p k input xs o hs cidx cs
eval' (Chr c k) input xs o hs cidx cs            = evalChr c k input xs o hs cidx cs
eval' (Bind f) input xs o hs cidx cs             = evalBind f input xs o hs cidx cs
eval' Empt input xs o hs cidx cs                 = evalEmpt input xs o hs cidx cs
eval' (Commit k) input xs o hs cidx cs           = evalCommit k input xs o hs cidx cs
eval' (HardFork p q) input xs o hs cidx cs       = evalHardFork p q input xs o hs cidx cs
eval' (SoftFork p q) input xs o hs cidx cs       = evalSoftFork p q input xs o hs cidx cs
eval' (Attempt k) input xs o hs cidx cs          = evalAttempt k input xs o hs cidx cs
eval' (Look k) input xs o hs cidx cs             = evalLook k input xs o hs cidx cs
eval' (Restore k) input xs o hs cidx cs          = evalRestore k input xs o hs cidx cs
eval' (ManyIter σ k) input xs o hs cidx cs       = evalManyIter σ k input xs o hs cidx cs
eval' (ManyInitHard σ l k) input xs o hs cidx cs = evalManyInitHard σ l k input xs o hs cidx cs
eval' (ManyInitSoft σ l k) input xs o hs cidx cs = evalManyInitSoft σ l k input xs o hs cidx cs

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

runParser :: Parser a -> String -> Maybe a
runParser p input = runST (compile (preprocess p) >>= eval input)

data CompiledParser a = Compiled (forall s. M s '[] a)

mkParser :: Parser a -> CompiledParser a
mkParser p = Compiled (runST (slightyUnsafeLeak (compile (preprocess p))))
  where
    slightyUnsafeLeak :: (forall s. ST s (M s '[] a)) -> (forall s. ST s (M s' '[] a))
    slightyUnsafeLeak = unsafeCoerce

runCompiledParser :: CompiledParser a -> String -> Maybe a
runCompiledParser (Compiled p) input = runST (eval input p)
