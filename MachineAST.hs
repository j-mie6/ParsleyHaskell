{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             FlexibleInstances,
             TemplateHaskell,
             PolyKinds,
             KindSignatures,
             ScopedTypeVariables,
             GeneralizedNewtypeDeriving,
             PatternSynonyms #-}
module MachineAST where

import Indexed           (IFunctor3, Fix3(In3), Const3(..), imap3, cata3)
import Utils             (WQ(..))
import Defunc            (Defunc(APP), pattern FLIP_H)
import Data.Word         (Word64)
import Safe.Coerce       (coerce)
import Data.List         (intercalate)
import Data.GADT.Compare (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))

newtype Machine o a = Machine { getMachine :: Fix3 (M o) '[] a a }
newtype ΣVar (a :: *) = ΣVar IΣVar
newtype MVar (a :: *) = MVar IMVar
newtype ΦVar (a :: *) = ΦVar IΦVar
newtype IMVar = IMVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype IΦVar = IΦVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype IΣVar = IΣVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype LetBinding o a x = LetBinding (Fix3 (M o) '[] x a)
instance Show (LetBinding o a x) where show (LetBinding m) = show m

data M o (k :: [*] -> * -> * -> *) (xs :: [*]) (r :: *) (a :: *) where
  Ret       :: M o k '[x] x a
  Push      :: WQ x -> k (x ': xs) r a -> M o k xs r a
  Pop       :: k xs r a -> M o k (x ': xs) r a
  Lift2     :: Defunc (x -> y -> z) -> k (z ': xs) r a -> M o k (y ': x ': xs) r a
  Sat       :: WQ (Char -> Bool) -> k (Char ': xs) r a -> M o k xs r a
  Call      :: MVar x -> k (x ': xs) r a -> M o k xs r a
  Jump      :: MVar x -> M o k '[] x a
  Empt      :: M o k xs r a
  Commit    :: k xs r a -> M o k xs r a
  HardFork  :: k xs r a -> k xs r a -> M o k xs r a --TODO: Deprecate
  SoftFork  :: k xs r a -> k xs r a -> M o k xs r a --TODO: Deprecate
  Attempt   :: k xs r a -> M o k xs r a             --TODO: Deprecate
  Tell      :: k (o ': xs) r a -> M o k xs r a
  Seek      :: k xs r a -> M o k (o ': xs) r a
  Case      :: k (x ': xs) r a -> k (y ': xs) r a -> M o k (Either x y ': xs) r a
  Choices   :: [WQ (x -> Bool)] -> [k xs r a] -> k xs r a -> M o k (x ': xs) r a
  ChainIter :: ΣVar x -> MVar x -> M o k '[] x a
  ChainInit :: ΣVar x -> k '[] x a -> MVar x -> k xs r a -> M o k xs r a
  Join      :: ΦVar x -> M o k (x ': xs) r a
  MkJoin    :: ΦVar x -> k (x ': xs) r a -> k xs r a -> M o k xs r a
  Swap      :: k (x ': y ': xs) r a -> M o k (y ': x ': xs) r a
  Make      :: ΣVar x -> k xs r a -> M o k (x ': xs) r a
  Get       :: ΣVar x -> k (x ': xs) r a -> M o k xs r a
  Put       :: ΣVar x -> k xs r a -> M o k (x ': xs) r a
  LogEnter  :: String -> k xs r a -> M o k xs r a
  LogExit   :: String -> k xs r a -> M o k xs r a
  MetaM     :: MetaM -> k xs r a -> M o k xs r a

data MetaM where
  AddCoins    :: Int -> MetaM
  FreeCoins   :: Int -> MetaM
  RefundCoins :: Int -> MetaM
  DrainCoins  :: Int -> MetaM

mkCoin :: (Int -> MetaM) -> Int -> Fix3 (M o) xs r a -> Fix3 (M o) xs r a
mkCoin meta 0 = id
mkCoin meta n = In3 . MetaM (meta n)

addCoins = mkCoin AddCoins
freeCoins = mkCoin FreeCoins
refundCoins = mkCoin RefundCoins
drainCoins = mkCoin DrainCoins

_App :: Fix3 (M o) (y ': xs) r a -> M o (Fix3 (M o)) (x ': (x -> y) ': xs) r a
_App m = Lift2 APP m

_Fmap :: WQ (x -> y) -> Fix3 (M o) (y ': xs) r a -> M o (Fix3 (M o)) (x ': xs) r a
_Fmap f m = Push f (In3 (Lift2 (FLIP_H APP) m))

_Modify :: ΣVar x -> Fix3 (M o) xs r a -> M o (Fix3 (M o)) ((x -> x) ': xs) r a
_Modify σ m = Get σ (In3 (_App (In3 (Put σ m))))

instance IFunctor3 (M o) where
  imap3 f Ret                 = Ret
  imap3 f (Push x k)          = Push x (f k)
  imap3 f (Pop k)             = Pop (f k)
  imap3 f (Lift2 g k)         = Lift2 g (f k)
  imap3 f (Sat g k)           = Sat g (f k)
  imap3 f (Call μ k)          = Call μ (f k)
  imap3 f (Jump μ)            = Jump μ
  imap3 f Empt                = Empt
  imap3 f (Commit k)          = Commit (f k)
  imap3 f (SoftFork p q)      = SoftFork (f p) (f q)
  imap3 f (HardFork p q)      = HardFork (f p) (f q)
  imap3 f (Attempt k)         = Attempt (f k)
  imap3 f (Tell k)            = Tell (f k)
  imap3 f (Seek k)            = Seek (f k)
  imap3 f (Case p q)          = Case (f p) (f q)
  imap3 f (Choices fs ks def) = Choices fs (map f ks) (f def)
  imap3 f (ChainIter σ μ)     = ChainIter σ μ
  imap3 f (ChainInit σ l μ k) = ChainInit σ (f l) μ (f k)
  imap3 f (Join φ)            = Join φ
  imap3 f (MkJoin φ p k)      = MkJoin φ (f p) (f k)
  imap3 f (Swap k)            = Swap (f k)
  imap3 f (Make σ k)          = Make σ (f k)
  imap3 f (Get σ k)           = Get σ (f k)
  imap3 f (Put σ k)           = Put σ (f k)
  imap3 f (LogEnter name k)   = LogEnter name (f k)
  imap3 f (LogExit name k)    = LogExit name (f k)
  imap3 f (MetaM m k)         = MetaM m (f k)

instance Show (Machine o a) where show = show . getMachine
instance Show (Fix3 (M o) xs r a) where
  show x = let Const3 s = cata3 alg x in s where
    alg :: forall i j. M o (Const3 String) i j a -> Const3 String i j a
    alg Ret                 = Const3 $ "Ret"
    alg (Call μ k)          = Const3 $ "(Call " ++ show μ ++ " " ++ getConst3 k ++ ")"
    alg (Jump μ)            = Const3 $ "(Jump " ++ show μ ++ ")"
    alg (Push _ k)          = Const3 $ "(Push x " ++ getConst3 k ++ ")"
    alg (Pop k)             = Const3 $ "(Pop " ++ getConst3 k ++ ")"
    alg (Lift2 f k)         = Const3 $ "(Lift2 " ++ show f ++ " " ++ getConst3 k ++ ")"
    alg (Sat _ k)           = Const3 $ "(Sat f " ++ getConst3 k ++ ")"
    alg Empt                = Const3 $ "Empt"
    alg (Commit k)          = Const3 $ "(Commit " ++ getConst3 k ++ ")"
    alg (SoftFork p q)      = Const3 $ "(SoftFork " ++ getConst3 p ++ " " ++ getConst3 q ++ ")"
    alg (HardFork p q)      = Const3 $ "(HardFork " ++ getConst3 p ++ " " ++ getConst3 q ++ ")"
    alg (Attempt k)         = Const3 $ "(Try " ++ getConst3 k ++ ")"
    alg (Tell k)            = Const3 $ "(Tell " ++ getConst3 k ++ ")"
    alg (Seek k)            = Const3 $ "(Seek " ++ getConst3 k ++ ")"
    alg (Case p q)          = Const3 $ "(Case " ++ getConst3 p ++ " " ++ getConst3 q ++ ")"
    alg (Choices _ ks def)  = Const3 $ "(Choices [" ++ intercalate ", " (map getConst3 ks) ++ "] " ++ getConst3 def ++ ")"
    alg (ChainIter σ μ)     = Const3 $ "(ChainIter " ++ show σ ++ " " ++ show μ ++ ")"
    alg (ChainInit σ m μ k) = Const3 $ "{ChainInit " ++ show σ ++ " " ++ show μ ++ " " ++ getConst3 m ++ " " ++ getConst3 k ++ "}"
    alg (Join φ)            = Const3 $ show φ
    alg (MkJoin φ p k)      = Const3 $ "(let " ++ show φ ++ " = " ++ getConst3 p ++ " in " ++ getConst3 k ++ ")"
    alg (Swap k)            = Const3 $ "(Swap " ++ getConst3 k ++ ")"
    alg (Make σ k)          = Const3 $ "(Make " ++ show σ ++ " " ++ getConst3 k ++ ")"
    alg (Get σ k)           = Const3 $ "(Get " ++ show σ ++ " " ++ getConst3 k ++ ")"
    alg (Put σ k)           = Const3 $ "(Put " ++ show σ ++ " " ++ getConst3 k ++ ")"
    alg (LogEnter _ k)      = Const3 $ getConst3 k
    alg (LogExit _ k)       = Const3 $ getConst3 k
    alg (MetaM m k)         = Const3 $ "[" ++ show m ++ "] " ++ getConst3 k

instance Show (MVar a) where show (MVar (IMVar μ)) = "μ" ++ show μ
instance Show (ΦVar a) where show (ΦVar (IΦVar φ)) = "φ" ++ show φ
instance Show (ΣVar a) where show (ΣVar (IΣVar σ)) = "σ" ++ show σ

instance Show MetaM where
  show (AddCoins n)    = "Add " ++ show n ++ " coins"
  show (RefundCoins n) = "Refund " ++ show n ++ " coins"
  show (DrainCoins n)    = "Using " ++ show n ++ " coins"

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

instance GEq MVar where
  geq (MVar u) (MVar v)
    | u == v    = Just (coerce Refl)
    | otherwise = Nothing

instance GCompare MVar where
  gcompare (MVar u) (MVar v) = case compare u v of
    LT -> coerce GLT
    EQ -> coerce GEQ
    GT -> coerce GGT