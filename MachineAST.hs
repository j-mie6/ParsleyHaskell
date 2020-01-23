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
  
import Indexed           (IFunctor3, Free3(Op3), Void3, Const3(..), imap3, fold3)
import Utils             (WQ(..))
import Defunc            (Defunc(APP), pattern FLIP_H)
import Data.Word         (Word64)
import Data.Void         (Void)
import Safe.Coerce       (coerce)
import Data.List         (intercalate)
import Data.GADT.Compare (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))

newtype Machine o a = Machine { getMachine :: Free3 (M o) Void3 '[] Void a }
newtype ΣVar (a :: *) = ΣVar IΣVar
newtype MVar (a :: *) = MVar IMVar
newtype ΦVar (a :: *) = ΦVar IΦVar
newtype IMVar = IMVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype IΦVar = IΦVar Word64 deriving (Ord, Eq, Num, Enum, Show)
newtype IΣVar = IΣVar Word64 deriving (Ord, Eq, Num, Enum, Show)
type ΦDecl k x xs r a = (ΦVar x, k (x ': xs) r a)
newtype LetBinding o a x = LetBinding (Free3 (M o) Void3 '[] x a)
instance Show (LetBinding o a x) where show (LetBinding m) = show m

data M o k xs r a where
  Halt      :: M o k '[a] Void a
  Ret       :: M o k '[x] x a
  Push      :: WQ x -> k (x ': xs) r a -> M o k xs r a
  Pop       :: k xs r a -> M o k (x ': xs) r a
  Lift2     :: Defunc (x -> y -> z) -> k (z ': xs) r a -> M o k (y ': x ': xs) r a
  Sat       :: WQ (Char -> Bool) -> k (Char ': xs) r a -> M o k xs r a
  Call      :: MVar x -> k (x ': xs) r a -> M o k xs r a
  Jump      :: MVar x -> M o k '[] x a
  Empt      :: M o k xs r a
  Commit    :: Bool -> k xs r a -> M o k xs r a
  HardFork  :: k xs r a -> k xs r a -> Maybe (ΦDecl k x xs r a) -> M o k xs r a              --TODO: Deprecate
  SoftFork  :: Maybe Int -> k xs r a -> k xs r a -> Maybe (ΦDecl k x xs r a) -> M o k xs r a --TODO: Deprecate
  Join      :: ΦVar x -> M o k (x ': xs) r a
  Attempt   :: Maybe Int -> k xs r a -> M o k xs r a                                         --TODO: Deprecate
  Tell      :: k (o ': xs) r a -> M o k xs r a
  Seek      :: k xs r a -> M o k (o ': xs) r a
  Case      :: k (x ': xs) r a -> k (y ': xs) r a -> Maybe (ΦDecl k z xs r a) -> M o k (Either x y ': xs) r a
  Choices   :: [WQ (x -> Bool)] -> [k xs r a] -> k xs r a -> Maybe (ΦDecl k y xs r a) -> M o k (x ': xs) r a
  ChainIter :: ΣVar x -> MVar x -> M o k '[] x a
  ChainInit :: ΣVar x -> k '[] x a -> MVar x -> k xs r a -> M o k xs r a
  Swap      :: k (x ': y ': xs) r a -> M o k (y ': x ': xs) r a
  Make      :: ΣVar x -> k xs r a -> M o k (x ': xs) r a
  Get       :: ΣVar x -> k (x ': xs) r a -> M o k xs r a
  Put       :: ΣVar x -> k xs r a -> M o k (x ': xs) r a
  LogEnter  :: String -> k xs r a -> M o k xs r a
  LogExit   :: String -> k xs r a -> M o k xs r a
  MetaM     :: MetaM -> k xs r a -> M o k xs r a

data MetaM

_App :: Free3 (M o) f (y ': xs) r a -> M o (Free3 (M o) f) (x ': (x -> y) ': xs) r a
_App m = Lift2 APP m

_Fmap :: WQ (x -> y) -> Free3 (M o) f (y ': xs) r a -> M o (Free3 (M o) f) (x ': xs) r a
_Fmap f m = Push f (Op3 (Lift2 (FLIP_H APP) m))

_Modify :: ΣVar x -> Free3 (M o) f xs r a -> M o (Free3 (M o) f) ((x -> x) ': xs) r a
_Modify σ m = Get σ (Op3 (_App (Op3 (Put σ m))))

instance IFunctor3 (M o) where
  imap3 f Halt                              = Halt
  imap3 f Ret                               = Ret
  imap3 f (Push x k)                        = Push x (f k)
  imap3 f (Pop k)                           = Pop (f k)
  imap3 f (Lift2 g k)                       = Lift2 g (f k)
  imap3 f (Sat g k)                         = Sat g (f k)
  imap3 f (Call μ k)                        = Call μ (f k)
  imap3 f (Jump μ)                          = Jump μ
  imap3 f Empt                              = Empt
  imap3 f (Commit exit k)                   = Commit exit (f k)
  imap3 f (SoftFork n p q (Just (φ, k)))    = SoftFork n (f p) (f q) (Just (φ, f k))
  imap3 f (SoftFork n p q Nothing)          = SoftFork n (f p) (f q) Nothing
  imap3 f (HardFork p q (Just (φ, k)))      = HardFork (f p) (f q) (Just (φ, f k))
  imap3 f (HardFork p q Nothing)            = HardFork (f p) (f q) Nothing
  imap3 f (Join φ)                          = Join φ
  imap3 f (Attempt n k)                     = Attempt n (f k)
  imap3 f (Tell k)                          = Tell (f k)
  imap3 f (Seek k)                          = Seek (f k)
  imap3 f (Case p q (Just (φ, k)))          = Case (f p) (f q) (Just (φ, f k))
  imap3 f (Case p q Nothing)                = Case (f p) (f q) Nothing
  imap3 f (Choices fs ks def (Just (φ, k))) = Choices fs (map f ks) (f def) (Just (φ, f k))
  imap3 f (Choices fs ks def Nothing)       = Choices fs (map f ks) (f def) Nothing
  imap3 f (ChainIter σ μ)                   = ChainIter σ μ
  imap3 f (ChainInit σ l μ k)               = ChainInit σ (f l) μ (f k)
  imap3 f (Swap k)                          = Swap (f k)
  imap3 f (Make σ k)                        = Make σ (f k)
  imap3 f (Get σ k)                         = Get σ (f k)
  imap3 f (Put σ k)                         = Put σ (f k)
  imap3 f (LogEnter name k)                 = LogEnter name (f k)
  imap3 f (LogExit name k)                  = LogExit name (f k)

instance Show (Machine o a) where show = show . getMachine
instance Show (Free3 (M o) f xs ks a) where
  show = getConst3 . fold3 (const (Const3 "")) (Const3 . alg) where
    alg :: forall i j k. M o (Const3 String) i j k -> String
    alg Halt                                  = "Halt"
    alg Ret                                   = "Ret"
    alg (Call μ k)                            = "(Call " ++ show μ ++ " " ++ getConst3 k ++ ")"
    alg (Jump μ)                              = "(Jump " ++ show μ ++ ")"
    alg (Push _ k)                            = "(Push x " ++ getConst3 k ++ ")"
    alg (Pop k)                               = "(Pop " ++ getConst3 k ++ ")"
    alg (Lift2 f k)                           = "(Lift2 " ++ show f ++ " " ++ getConst3 k ++ ")"
    alg (Sat _ k)                             = "(Sat f " ++ getConst3 k ++ ")"
    alg Empt                                  = "Empt"
    alg (Commit True k)                       = "(Commit end " ++ getConst3 k ++ ")"
    alg (Commit False k)                      = "(Commit " ++ getConst3 k ++ ")"
    alg (SoftFork Nothing p q Nothing)        = "(SoftFork " ++ getConst3 p ++ " " ++ getConst3 q ++ ")"
    alg (SoftFork (Just n) p q Nothing)       = "(SoftFork " ++ show n ++ " " ++ getConst3 p ++ " " ++ getConst3 q ++ ")"
    alg (SoftFork Nothing p q (Just (φ, k)))  = "(SoftFork " ++ getConst3 p ++ " " ++ getConst3 q ++ " (" ++ show φ ++ " = " ++ getConst3 k ++ "))"
    alg (SoftFork (Just n) p q (Just (φ, k))) = "(SoftFork " ++ show n ++ " " ++ getConst3 p ++ " " ++ getConst3 q ++ " (" ++ show φ ++ " = " ++ getConst3 k ++ "))"
    alg (HardFork p q Nothing)                = "(HardFork " ++ getConst3 p ++ " " ++ getConst3 q ++ ")"
    alg (HardFork p q (Just (φ, k)))          = "(HardFork " ++ getConst3 p ++ " " ++ getConst3 q ++ " (" ++ show φ ++ " = " ++ getConst3 k ++ "))"
    alg (Join φ)                              = show φ
    alg (Attempt Nothing k)                   = "(Try " ++ getConst3 k ++ ")"
    alg (Attempt (Just n) k)                  = "(Try " ++ show n ++ " " ++ getConst3 k ++ ")"
    alg (Tell k)                              = "(Tell " ++ getConst3 k ++ ")"
    alg (Seek k)                              = "(Seek " ++ getConst3 k ++ ")"
    alg (Case p q Nothing)                    = "(Case " ++ getConst3 p ++ " " ++ getConst3 q ++ ")"
    alg (Case p q (Just (φ, k)))              = "(Case " ++ getConst3 p ++ " " ++ getConst3 q ++ " (" ++ show φ ++ " = " ++ getConst3 k ++ "))"
    alg (Choices _ ks def Nothing)            = "(Choices [" ++ intercalate ", " (map getConst3 ks) ++ "] " ++ getConst3 def ++ ")"
    alg (Choices _ ks def (Just (φ, k)))      = "(Choices [" ++ intercalate ", " (map getConst3 ks) ++ "] " ++ getConst3 def ++ " (" ++ show φ ++ " = " ++ getConst3 k ++ "))"
    alg (ChainIter σ μ)                       = "(ChainIter " ++ show σ ++ " " ++ show μ ++ ")"
    alg (ChainInit σ m μ k)                   = "{ChainInit " ++ show σ ++ " " ++ show μ ++ " " ++ getConst3 m ++ " " ++ getConst3 k ++ "}"
    alg (Swap k)                              = "(Swap " ++ getConst3 k ++ ")"
    alg (Make σ k)                            = "(Make " ++ show σ ++ " " ++ getConst3 k ++ ")"
    alg (Get σ k)                             = "(Get " ++ show σ ++ " " ++ getConst3 k ++ ")"
    alg (Put σ k)                             = "(Put " ++ show σ ++ " " ++ getConst3 k ++ ")"
    alg (LogEnter _ k)                        = getConst3 k
    alg (LogExit _ k)                         = getConst3 k

instance Show (MVar a) where show (MVar (IMVar μ)) = "μ" ++ show μ
instance Show (ΦVar a) where show (ΦVar (IΦVar φ)) = "φ" ++ show φ
instance Show (ΣVar a) where show (ΣVar (IΣVar σ)) = "σ" ++ show σ

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