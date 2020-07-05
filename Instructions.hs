{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             FlexibleInstances,
             TemplateHaskell,
             PolyKinds,
             KindSignatures,
             PatternSynonyms #-}
module Instructions where

import Indexed     (IFunctor4, Fix4(In4), Const4(..), imap4, cata4, Nat(..))
import Utils       (WQ(..))
import Defunc      (DefuncUser(APP, ID), Defunc(USER), pattern FLIP_H)
import Data.Void   (Void)
import Data.List   (intercalate)
import Identifiers (IMVar, MVar, IΣVar)

type One = Succ Zero
newtype Program o a = Program { getProgram :: Fix4 (Instr WQ o) '[] One a a }
newtype LetBinding q o a x = LetBinding (Fix4 (Instr q o) '[] One x a)
instance Show (LetBinding q o a x) where show (LetBinding m) = show m

data Instr q o (k :: [*] -> Nat -> * -> * -> *) (xs :: [*]) (n :: Nat) (r :: *) (a :: *) where
  Ret       :: Instr q o k '[x] n x a
  Push      :: Defunc q o x -> k (x : xs) n r a -> Instr q o k xs n r a
  Pop       :: k xs n r a -> Instr q o k (x : xs) n r a
  Lift2     :: Defunc q o (x -> y -> z) -> k (z : xs) n r a -> Instr q o k (y : x : xs) n r a
  Sat       :: Defunc q o (Char -> Bool) -> k (Char : xs) (Succ n) r a -> Instr q o k xs (Succ n) r a
  Call      :: MVar x -> k (x : xs) (Succ n) r a -> Instr q o k xs (Succ n) r a
  Jump      :: MVar x -> Instr q o k '[] (Succ n) x a
  Empt      :: Instr q o k xs (Succ n) r a
  Commit    :: k xs n r a -> Instr q o k xs (Succ n) r a
  Catch     :: k xs (Succ n) r a -> k (o : xs) n r a -> Instr q o k xs n r a
  Tell      :: k (o : xs) n r a -> Instr q o k xs n r a
  Seek      :: k xs n r a -> Instr q o k (o : xs) n r a
  Case      :: k (x : xs) n r a -> k (y : xs) n r a -> Instr q o k (Either x y : xs) n r a
  Choices   :: [Defunc q o (x -> Bool)] -> [k xs n r a] -> k xs n r a -> Instr q o k (x : xs) n r a
  Iter      :: MVar Void -> k '[] One Void a -> k (o : xs) n r a -> Instr q o k xs n r a
  Join      :: ΦVar x -> Instr q o k (x : xs) n r a
  MkJoin    :: ΦVar x -> k (x : xs) n r a -> k xs n r a -> Instr q o k xs n r a
  Swap      :: k (x : y : xs) n r a -> Instr q o k (y : x : xs) n r a
  Make      :: ΣVar x -> k xs n r a -> Instr q o k (x : xs) n r a
  Get       :: ΣVar x -> k (x : xs) n r a -> Instr q o k xs n r a
  Put       :: ΣVar x -> k xs n r a -> Instr q o k (x : xs) n r a
  LogEnter  :: String -> k xs (Succ (Succ n)) r a -> Instr q o k xs (Succ n) r a
  LogExit   :: String -> k xs n r a -> Instr q o k xs n r a
  MetaInstr :: MetaInstr n -> k xs n r a -> Instr q o k xs n r a

data MetaInstr (n :: Nat) where
  AddCoins    :: Int -> MetaInstr (Succ n)
  FreeCoins   :: Int -> MetaInstr n
  RefundCoins :: Int -> MetaInstr n
  DrainCoins  :: Int -> MetaInstr (Succ n)

mkCoin :: (Int -> MetaInstr n) -> Int -> Fix4 (Instr q o) xs n r a -> Fix4 (Instr q o) xs n r a
mkCoin meta 0 = id
mkCoin meta n = In4 . MetaInstr (meta n)

addCoins = mkCoin AddCoins
freeCoins = mkCoin FreeCoins
refundCoins = mkCoin RefundCoins
drainCoins = mkCoin DrainCoins

_App :: Fix4 (Instr q o) (y : xs) n r a -> Instr q o (Fix4 (Instr q o)) (x : (x -> y) : xs) n r a
_App m = Lift2 (USER APP) m

_Fmap :: Defunc q o (x -> y) -> Fix4 (Instr q o) (y : xs) n r a -> Instr q o (Fix4 (Instr q o)) (x : xs) n r a
_Fmap f m = Push f (In4 (Lift2 (USER (FLIP_H APP)) m))

_Modify :: ΣVar x -> Fix4 (Instr q o) xs n r a -> Instr q o (Fix4 (Instr q o)) ((x -> x) : xs) n r a
_Modify σ m = Get σ (In4 (_App (In4 (Put σ m))))

-- This this is a nice little trick to get this instruction to generate optimised code
_If :: Fix4 (Instr q o) xs n r a -> Fix4 (Instr q o) xs n r a -> Instr q o (Fix4 (Instr q o)) (Bool : xs) n r a
_If t e = Choices [USER ID] [t] e

instance IFunctor4 (Instr q o) where
  imap4 f Ret                 = Ret
  imap4 f (Push x k)          = Push x (f k)
  imap4 f (Pop k)             = Pop (f k)
  imap4 f (Lift2 g k)         = Lift2 g (f k)
  imap4 f (Sat g k)           = Sat g (f k)
  imap4 f (Call μ k)          = Call μ (f k)
  imap4 f (Jump μ)            = Jump μ
  imap4 f Empt                = Empt
  imap4 f (Commit k)          = Commit (f k)
  imap4 f (Catch p h)         = Catch (f p) (f h)
  imap4 f (Tell k)            = Tell (f k)
  imap4 f (Seek k)            = Seek (f k)
  imap4 f (Case p q)          = Case (f p) (f q)
  imap4 f (Choices fs ks def) = Choices fs (map f ks) (f def)
  imap4 f (Iter μ l h)        = Iter μ (f l) (f h)
  imap4 f (Join φ)            = Join φ
  imap4 f (MkJoin φ p k)      = MkJoin φ (f p) (f k)
  imap4 f (Swap k)            = Swap (f k)
  imap4 f (Make σ k)          = Make σ (f k)
  imap4 f (Get σ k)           = Get σ (f k)
  imap4 f (Put σ k)           = Put σ (f k)
  imap4 f (LogEnter name k)   = LogEnter name (f k)
  imap4 f (LogExit name k)    = LogExit name (f k)
  imap4 f (MetaInstr m k)     = MetaInstr m (f k)

instance Show (Program o a) where show = show . getProgram
instance Show (Fix4 (Instr q o) xs n r a) where
  show x = let Const4 s = cata4 alg x in s where
    alg :: forall i j k. Instr q o (Const4 String) i j k a -> Const4 String i j k a
    alg Ret                 = Const4 $ "Ret"
    alg (Call μ k)          = Const4 $ "(Call " ++ show μ ++ " " ++ show k ++ ")"
    alg (Jump μ)            = Const4 $ "(Jump " ++ show μ ++ ")"
    alg (Push x k)          = Const4 $ "(Push " ++ show x ++ " " ++ show k ++ ")"
    alg (Pop k)             = Const4 $ "(Pop " ++ show k ++ ")"
    alg (Lift2 f k)         = Const4 $ "(Lift2 " ++ show f ++ " " ++ show k ++ ")"
    alg (Sat f k)           = Const4 $ "(Sat " ++ show f ++ " " ++ show k ++ ")"
    alg Empt                = Const4 $ "Empt"
    alg (Commit k)          = Const4 $ "(Commit " ++ show k ++ ")"
    alg (Catch p h)         = Const4 $ "(Catch " ++ show p ++ " " ++ show h ++ ")"
    alg (Tell k)            = Const4 $ "(Tell " ++ show k ++ ")"
    alg (Seek k)            = Const4 $ "(Seek " ++ show k ++ ")"
    alg (Case p q)          = Const4 $ "(Case " ++ show p ++ " " ++ show q ++ ")"
    alg (Choices fs ks def) = Const4 $ "(Choices " ++ show fs ++ " [" ++ intercalate ", " (map show ks) ++ "] " ++ show def ++ ")"
    alg (Iter μ l h)        = Const4 $ "{Iter " ++ show μ ++ " " ++ show l ++ " " ++ show h ++ "}"
    alg (Join φ)            = Const4 $ show φ
    alg (MkJoin φ p k)      = Const4 $ "(let " ++ show φ ++ " = " ++ show p ++ " in " ++ show k ++ ")"
    alg (Swap k)            = Const4 $ "(Swap " ++ show k ++ ")"
    alg (Make σ k)          = Const4 $ "(Make " ++ show σ ++ " " ++ show k ++ ")"
    alg (Get σ k)           = Const4 $ "(Get " ++ show σ ++ " " ++ show k ++ ")"
    alg (Put σ k)           = Const4 $ "(Put " ++ show σ ++ " " ++ show k ++ ")"
    alg (LogEnter _ k)      = Const4 $ show k
    alg (LogExit _ k)       = Const4 $ show k
    alg (MetaInstr m k)         = Const4 $ "[" ++ show m ++ "] " ++ show k

instance Show (Const4 String xs n r a) where show = getConst4

instance Show (MetaInstr n) where
  show (AddCoins n)    = "Add " ++ show n ++ " coins"
  show (RefundCoins n) = "Refund " ++ show n ++ " coins"
  show (DrainCoins n)    = "Using " ++ show n ++ " coins"
