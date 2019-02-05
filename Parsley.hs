{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
import Prelude hiding ((*>), (<*), (>>), traverse, sequence, (<$))
import Control.Applicative hiding ((<*), (*>), many, some, (<$))
import Control.Monad hiding ((>>), sequence)
import Control.Monad.ST
import Control.Monad.ST.Unsafe
import Control.Monad.Reader hiding (sequence, (>>))
import Data.STRef
import System.IO.Unsafe
import Data.IORef
import System.Mem.StableName
import Data.Hashable
import Data.HashSet hiding (empty, null, size, map, foldr)
import qualified Data.HashSet as HashSet
import Data.HList.HList
import Data.Array.Unboxed
import Debug.Trace
import Unsafe.Coerce

-- AST
data Parser a where
  Pure      :: a -> Parser a
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

instance Show (Parser a) where
  show (Pure _) = "pure x"
  show (pf :<*>: px) = concat ["(", show pf, " <*> ", show px, ")"]
  show (p :*>: q) = concat ["(", show p, " *> ", show q, ")"]
  show (p :<*: q) = concat ["(", show p, " <* ", show q, ")"]
  show (p :>>=: f) = concat ["(", show p, " >>= f)"]
  show (p :<|>: q) = concat ["(", show p, " <|> ", show q, ")"]
  show Empty = "empty"
  show (Try p) = concat ["(try ", show p, ")"]
  show (LookAhead p) = concat ["(lookAhead ", show p, ")"]
  show (Rec _) = "recursion point!"
  show (Many p) = concat ["(many ", show p, "]"]
  show (Satisfy _) = "satisfy f"

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
many p = let manyp = p <:> manyp <|> pure [] in manyp--Many p

some :: Parser a -> Parser [a]
some p = p <:> many p

(<:>) :: Parser a -> Parser [a] -> Parser [a]
(<:>) = liftA2 (:)

(<$) :: a -> Parser b -> Parser a
x <$ p = p *> pure x

satisfy :: (Char -> Bool) -> Parser Char
satisfy = Satisfy

char :: Char -> Parser Char
char c = satisfy (== c)

item :: Parser Char
item = satisfy (const True)

sequence :: [Parser a] -> Parser [a]
sequence = foldr (<:>) (pure [])

traverse :: (a -> Parser b) -> [a] -> Parser [b]
traverse f = sequence . map f

string :: String -> Parser String
string = traverse char

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
    preprocess'' (Try p)       = liftM Try (preprocess' p)
    preprocess'' (LookAhead p) = liftM LookAhead (preprocess' p)
    preprocess'' (Many p)      = liftM Many (preprocess' p)
    preprocess'' p             = return p

    fix :: Parser a -> ReaderT (IORef (HashSet StableParserName)) IO (Parser a)
    -- Force evaluation of p to ensure that the stableName is correct first time
    fix !p =
      do seenRef <- ask
         seen <- lift (readIORef seenRef)
         name <- StableParserName <$> lift (makeStableName p)
         if member name seen
           then return (Rec p)
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

data M s xs a where
  Halt         :: M s '[a] a
  Push         :: x -> M s (x ': xs) a -> M s xs a
  Pop          :: M s xs a -> M s (b ': xs) a
  App          :: M s (y ': xs) a -> M s (x ': (x -> y) ': xs) a
  Sat          :: (Char -> Bool) -> M s (Char ': xs) a -> M s xs a
  Bind         :: (x -> ST s (M s xs a)) -> M s (x ': xs) a
  Empt         :: M s xs a
  Commit       :: M s xs a -> M s xs a
  SoftFork     :: M s xs a -> M s xs a -> M s xs a
  HardFork     :: M s xs a -> M s xs a -> M s xs a
  Attempt      :: M s xs a -> M s xs a
  Look         :: M s xs a -> M s xs a
  Restore      :: M s xs a -> M s xs a
  ManyIter     :: STRef s [x] -> M s xs a -> M s (x ': xs) a
  ManyInitSoft :: STRef s [x] -> M s xs a -> M s ([x] ': xs) a -> M s xs a
  ManyInitHard :: STRef s [x] -> M s xs a -> M s ([x] ': xs) a -> M s xs a

compile :: Parser a -> ST s (M s '[] a)
compile = flip compile' Halt

compile' :: Parser a -> M s (a ': xs) b -> ST s (M s xs b)
compile' (Pure x) m        = do return (Push x m)
compile' (Satisfy p) m     = do return (Sat p m)
compile' (pf :<*>: px) m   = do pxc <- compile' px (App m); compile' pf pxc
compile' (p :*>: q) m      = do qc <- compile' q m; compile' p (Pop qc)
compile' (p :<*: q) m      = do qc <- compile' q (Pop m); compile' p qc
compile' Empty m           = do return Empt
compile' (Try p :<|>: q) m = do SoftFork <$> compile' p (Commit m) <*> compile' q m
compile' (p :<|>: q) m     = do HardFork <$> compile' p (Commit m) <*> compile' q m
compile' (p :>>=: f) m     = do compile' p (Bind (flip compile' m . preprocess . f))
compile' (Try p) m         = do Attempt <$> compile' p (Commit m)
compile' (LookAhead p) m   = do Look <$> compile' p (Restore m)
--                              Using unsafeInterleaveST prevents this code from being compiled until it is asked for!
compile' (Rec p) m         = do unsafeInterleaveST (compile' (preprocess p) m)
compile' (Many (Try p)) m  =
  mdo σ <- newSTRef []
      manyp <- compile' p (ManyIter σ manyp)
      return (ManyInitSoft σ manyp m)
compile' (Many p) m        =
  mdo σ <- newSTRef []
      manyp <- compile' p (ManyIter σ manyp)
      return (ManyInitHard σ manyp m)


type H s a = STRef s [ST s (Maybe a)]
type X = HList
type C s = STRef s [Int]
data Status = Good | Bad deriving (Show, Eq)
type S s = STRef s Status
type O s = STRef s Int

makeX :: ST s (X '[])
makeX = return HNil
pushX :: a -> X xs -> X (a ': xs)
pushX = HCons
popX :: X (a ': xs) -> (a, X xs)
popX (HCons x xs) = (x, xs)
pokeX :: a -> X (a ': xs) -> X (a ': xs)
pokeX y (HCons x xs) = HCons y xs
modX :: (a -> b) -> X (a ': xs) -> X (b ': xs)
modX f (HCons x xs) = HCons (f x) xs
peekX :: X (a ': xs) -> a
peekX (HCons x xs) = x

makeH :: ST s (H s a)
makeH = newSTRef []
emptyH :: H s a -> ST s Bool
emptyH = fmap null . readSTRef
pushH :: X xs -> C s -> S s -> O s -> UArray Int Char -> M s xs a -> H s a -> ST s ()
pushH xs cs s o input m hs = modifySTRef' hs (eval' xs hs cs s o input m :)
popH :: H s a -> ST s ()
popH href = modifySTRef' href tail
handle :: H s a -> ST s (Maybe a)
handle href =
  do (h:hs) <- readSTRef href
     writeSTRef href hs
     h

makeC :: ST s (C s)
makeC = newSTRef []
pushC :: Int -> C s -> ST s ()
pushC c cs = modifySTRef' cs (c:)
popC :: C s -> ST s Int
popC ref = do (c:cs) <- readSTRef ref; writeSTRef ref cs; return c
pokeC :: Int -> C s -> ST s ()
pokeC c cs = modifySTRef' cs ((c:) . tail)

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

makeO :: ST s (O s)
makeO = newSTRef 0
incO :: O s -> ST s ()
incO o = modifySTRef' o (+1)
getO :: O s -> ST s Int
getO = readSTRef
setO :: Int -> O s -> ST s ()
setO = flip writeSTRef
more :: UArray Int Char -> O s -> ST s Bool
more input = fmap (size input >) . readSTRef
next :: UArray Int Char -> O s -> ST s Char
next input o = fmap (input !) (readSTRef o)
nextSafe :: UArray Int Char -> O s -> (Char -> Bool) -> (Char -> ST s (Maybe a)) -> ST s (Maybe a) -> ST s (Maybe a)
nextSafe input o p good bad =
  do b <- more input o
     if b then do c <- next input o; if p c then do incO o; good c else bad
     else bad
size :: UArray Int Char -> Int
size = snd . bounds

eval :: String -> M s '[] a -> ST s (Maybe a)
eval input m =
  do xs <- makeX
     hs <- makeH
     cs <- makeC
     s <- makeS
     o <- makeO
     eval' xs hs cs s o (listArray (0, length input) input) m

setupHandler :: X xs -> H s a -> C s -> S s -> O s -> UArray Int Char -> M s xs a -> M s xs a -> ST s (Maybe a)
setupHandler xs hs cs s o input self k =
  do pushH xs cs s o input self hs
     o' <- getO o
     pushC o' cs
     eval' xs hs cs s o input k

-- TODO Implement semantics of the machine
eval' :: X xs -> H s a -> C s -> S s -> O s -> UArray Int Char -> M s xs a -> ST s (Maybe a)
eval' xs hs cs s o input Halt = status s (return (Just (fst (popX xs)))) (return Nothing)
eval' xs hs cs s o input (Push x k) = eval' (pushX x xs) hs cs s o input k
eval' xs hs cs s o input (Pop k) = eval' (snd (popX xs)) hs cs s o input k
eval' xs hs cs s o input (App k) = --let (x, xs') = popX xs in eval' (modX ($ x) xs') hs cs s o input k
  let (x, xs') = popX xs
      (f, xs'') = popX xs'
  in eval' (pushX (f x) xs'') hs cs s o input k
eval' xs hs cs s o input (Sat p k) = nextSafe input o p (\c -> eval' (pushX c xs) hs cs s o input k) (eval' xs hs cs s o input Empt)
eval' xs hs cs s o input (Bind f) =
  do let (x, xs') = popX xs
     k <- f x
     eval' xs' hs cs s o input k
eval' xs hs cs s o input Empt =
  do noHandler <- emptyH hs
     if noHandler then return Nothing
     else do oops s; handle hs
eval' xs hs cs s o input (Commit k) = do popH hs; popC cs; eval' xs hs cs s o input k
eval' xs hs cs s o input self@(SoftFork p q) =
  status s (setupHandler xs hs cs s o input self p)
           (do o' <- popC cs
               setO o' o
               ok s
               eval' xs hs cs s o input q)
eval' xs hs cs s o input self@(HardFork p q) =
  status s (setupHandler xs hs cs s o input self p)
           (do o' <- getO o
               c <- popC cs
               if c == o' then do ok s; eval' xs hs cs s o input q
               else eval' xs hs cs s o input Empt)
eval' xs hs cs s o input self@(Attempt k) =
  status s (setupHandler xs hs cs s o input self k)
           (do o' <- popC cs
               setO o' o
               eval' xs hs cs s o input Empt)
eval' xs hs cs s o input self@(Look k) =
  status s (setupHandler xs hs cs s o input self k)
           (do popC cs
               eval' xs hs cs s o input Empt)
eval' xs hs cs s o input (Restore k) = do popH hs; o' <- popC cs; setO o' o; eval' xs hs cs s o input k
eval' xs hs cs s o input (ManyIter σ k) =
  do let (x, xs') = popX xs
     modifySTRef' σ (x:)
     o' <- getO o
     pokeC o' cs
     eval' xs' hs cs s o input k
eval' xs hs cs s o input self@(ManyInitHard σ l k) =
  status s (setupHandler xs hs cs s o input self l)
           (do o' <- getO o
               c <- popC cs
               if c == o' then do ok s
                                  ys <- readSTRef σ
                                  writeSTRef σ []
                                  eval' (pushX (reverse ys) xs) hs cs s o input k
               else do writeSTRef σ []; eval' xs hs cs s o input Empt)
eval' xs hs cs s o input self@(ManyInitSoft σ l k) =
  status s (setupHandler xs hs cs s o input self l)
           (do o' <-popC cs
               setO o' o
               ok s
               ys <- readSTRef σ
               writeSTRef σ []
               eval' (pushX (reverse ys) xs) hs cs s o input k)
--eval' xs hs cs s o input _ = undefined

runParser :: Parser a -> String -> Maybe a
runParser p input = runST (compile (preprocess p) >>= eval input)
{-
data CompiledParser a = Compiled (forall s. M s '[] a)

mkParser :: Parser a -> CompiledParser a
mkParser p = Compiled (runST (slightyUnsafeLeak (compile (preprocess p))))
  where
    slightyUnsafeLeak :: (forall s. ST s (M s '[] a)) -> (forall s. ST s (M s' '[] a))
    slightyUnsafeLeak = unsafeCoerce

runCompiledParser :: CompiledParser a -> String -> Maybe a
runCompiledParser (Compiled p) input = runST (eval input p)
-}
