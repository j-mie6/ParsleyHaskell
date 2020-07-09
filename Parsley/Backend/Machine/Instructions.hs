{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             FlexibleInstances,
             PolyKinds,
             KindSignatures,
             PatternSynonyms,
             ScopedTypeVariables,
             DerivingStrategies,
             GeneralizedNewtypeDeriving,
             OverloadedStrings #-}
module Parsley.Backend.Machine.Instructions where

import Parsley.Common.Indexed     (IFunctor4, Fix4(In4), Const4(..), imap4, cata4, Nat(..), One)
import Parsley.Common.Utils       (WQ(..), intercalateDiff)
import Parsley.Core.Defunc as Core (Defunc(APP, ID), pattern FLIP_H)
import Parsley.Backend.Machine.Defunc as Machine (Defunc(USER))
import Data.Void                  (Void)
import Parsley.Backend.Machine.Identifiers (MVar, ΦVar, ΣVar)
import Data.GADT.Compare          (geq, (:~:)(Refl))

newtype LetBinding o a x = LetBinding (Fix4 (Instr o) '[] One x a) deriving newtype Show

data Instr o (k :: [*] -> Nat -> * -> * -> *) (xs :: [*]) (n :: Nat) (r :: *) (a :: *) where
  Ret       :: Instr o k '[x] n x a
  Push      :: Machine.Defunc x -> k (x : xs) n r a -> Instr o k xs n r a
  Pop       :: k xs n r a -> Instr o k (x : xs) n r a
  Lift2     :: Machine.Defunc (x -> y -> z) -> k (z : xs) n r a -> Instr o k (y : x : xs) n r a
  Sat       :: Machine.Defunc (Char -> Bool) -> k (Char : xs) (Succ n) r a -> Instr o k xs (Succ n) r a
  Call      :: MVar x -> k (x : xs) (Succ n) r a -> Instr o k xs (Succ n) r a
  Jump      :: MVar x -> Instr o k '[] (Succ n) x a
  Empt      :: Instr o k xs (Succ n) r a
  Commit    :: k xs n r a -> Instr o k xs (Succ n) r a
  Catch     :: k xs (Succ n) r a -> k (o : xs) n r a -> Instr o k xs n r a
  Tell      :: k (o : xs) n r a -> Instr o k xs n r a
  Seek      :: k xs n r a -> Instr o k (o : xs) n r a
  Case      :: k (x : xs) n r a -> k (y : xs) n r a -> Instr o k (Either x y : xs) n r a
  Choices   :: [Machine.Defunc (x -> Bool)] -> [k xs n r a] -> k xs n r a -> Instr o k (x : xs) n r a
  Iter      :: MVar Void -> k '[] One Void a -> k (o : xs) n r a -> Instr o k xs n r a
  Join      :: ΦVar x -> Instr o k (x : xs) n r a
  MkJoin    :: ΦVar x -> k (x : xs) n r a -> k xs n r a -> Instr o k xs n r a
  Swap      :: k (x : y : xs) n r a -> Instr o k (y : x : xs) n r a
  Dup       :: k (x : x : xs) n r a -> Instr o k (x : xs) n r a
  Make      :: ΣVar x -> k xs n r a -> Instr o k (x : xs) n r a
  Get       :: ΣVar x -> k (x : xs) n r a -> Instr o k xs n r a
  Put       :: ΣVar x -> k xs n r a -> Instr o k (x : xs) n r a
  LogEnter  :: String -> k xs (Succ (Succ n)) r a -> Instr o k xs (Succ n) r a
  LogExit   :: String -> k xs n r a -> Instr o k xs n r a
  MetaInstr :: MetaInstr n -> k xs n r a -> Instr o k xs n r a

data MetaInstr (n :: Nat) where
  AddCoins    :: Int -> MetaInstr (Succ n)
  FreeCoins   :: Int -> MetaInstr n
  RefundCoins :: Int -> MetaInstr n
  DrainCoins  :: Int -> MetaInstr (Succ n)

mkCoin :: (Int -> MetaInstr n) -> Int -> Fix4 (Instr o) xs n r a -> Fix4 (Instr o) xs n r a
mkCoin meta 0 = id
mkCoin meta n = In4 . MetaInstr (meta n)

addCoins = mkCoin AddCoins
freeCoins = mkCoin FreeCoins
refundCoins = mkCoin RefundCoins
drainCoins = mkCoin DrainCoins

pattern App :: Fix4 (Instr o) (y : xs) n r a -> Instr o (Fix4 (Instr o)) (x : (x -> y) : xs) n r a
pattern App k = Lift2 (USER APP) k

pattern Fmap :: Machine.Defunc (x -> y) -> Fix4 (Instr o) (y : xs) n r a -> Instr o (Fix4 (Instr o)) (x : xs) n r a
pattern Fmap f k = Push f (In4 (Lift2 (USER (FLIP_H APP)) k))

_Modify :: ΣVar x -> Fix4 (Instr o) xs n r a -> Instr o (Fix4 (Instr o)) ((x -> x) : xs) n r a
_Modify σ = Get σ . In4 . App . In4 . Put σ

-- This this is a nice little trick to get this instruction to generate optimised code
pattern If :: Fix4 (Instr o) xs n r a -> Fix4 (Instr o) xs n r a -> Instr o (Fix4 (Instr o)) (Bool : xs) n r a
pattern If t e = Choices [USER ID] [t] e

instance IFunctor4 (Instr o) where
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
  imap4 f (Dup k)             = Dup (f k)
  imap4 f (Make σ k)          = Make σ (f k)
  imap4 f (Get σ k)           = Get σ (f k)
  imap4 f (Put σ k)           = Put σ (f k)
  imap4 f (LogEnter name k)   = LogEnter name (f k)
  imap4 f (LogExit name k)    = LogExit name (f k)
  imap4 f (MetaInstr m k)     = MetaInstr m (f k)

instance Show (Fix4 (Instr o) xs n r a) where
  show = ($ "") . getConst4 . cata4 (Const4 . alg)
    where
      alg :: forall xs n r a. Instr o (Const4 (String -> String)) xs n r a -> String -> String
      alg Ret                 = "Ret"
      alg (Call μ k)          = "(Call " . shows μ . " " . getConst4 k . ")"
      alg (Jump μ)            = "(Jump " . shows μ . ")"
      alg (Push x k)          = "(Push " . shows x . " " . getConst4 k . ")"
      alg (Pop k)             = "(Pop " . getConst4 k . ")"
      alg (Lift2 f k)         = "(Lift2 " . shows f . " " . getConst4 k . ")"
      alg (Sat f k)           = "(Sat " . shows f . " " . getConst4 k . ")"
      alg Empt                = "Empt"
      alg (Commit k)          = "(Commit " . getConst4 k . ")"
      alg (Catch p h)         = "(Catch " . getConst4 p . " " . getConst4 h . ")"
      alg (Tell k)            = "(Tell " . getConst4 k . ")"
      alg (Seek k)            = "(Seek " . getConst4 k . ")"
      alg (Case p q)          = "(Case " . getConst4 p . " " . getConst4 q . ")"
      alg (Choices fs ks def) = "(Choices " . shows fs . " [" . intercalateDiff (", ") (map getConst4 ks) . "] " . getConst4 def . ")"
      alg (Iter μ l h)        = "{Iter " . shows μ . " " . getConst4 l . " " . getConst4 h . "}"
      alg (Join φ)            = shows φ
      alg (MkJoin φ p k)      = "(let " . shows φ . " = " . getConst4 p . " in " . getConst4 k . ")"
      alg (Swap k)            = "(Swap " . getConst4 k . ")"
      alg (Dup k)             = "(Dup " . getConst4 k . ")"
      alg (Make σ k)          = "(Make " . shows σ . " " . getConst4 k . ")"
      alg (Get σ k)           = "(Get " . shows σ . " " . getConst4 k . ")"
      alg (Put σ k)           = "(Put " . shows σ . " " . getConst4 k . ")"
      alg (LogEnter _ k)      = getConst4 k
      alg (LogExit _ k)       = getConst4 k
      alg (MetaInstr m k)     = "[" . shows m . "] " . getConst4 k

instance Show (MetaInstr n) where
  show (AddCoins n)    = "Add " ++ show n ++ " coins"
  show (RefundCoins n) = "Refund " ++ show n ++ " coins"
  show (DrainCoins n)  = "Using " ++ show n ++ " coins"
