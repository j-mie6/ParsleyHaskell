{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE UnboxedTuples #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Machine where

import Indexed                    (IFunctor, Free(Op), Void, Const(..), imap, absurd, fold, getConst)
import Utils                      (bug, WQ(..), lift', (>*<))
import Data.Function              (fix)
import GHC.ST                     (ST(..))
import Control.Monad.Reader       (ask, Reader, runReader, local)
import Data.STRef                 (STRef, writeSTRef, readSTRef, modifySTRef', newSTRef)
import Data.Map.Strict            (Map)
import qualified Data.Map.Strict as Map
import Data.Dependent.Map         (DMap)
import Data.GADT.Compare          (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))
import qualified Data.Dependent.Map as DMap
import Data.Array.Unboxed         (listArray)
import Data.Array.Base            (STUArray(..), UArray(..), unsafeAt, newArray_, unsafeRead, unsafeWrite, MArray, getNumElements, numElements, ixmap, elems)
import GHC.Prim                   (Int#, Char#, newByteArray#, indexWideCharArray#)
import GHC.Exts                   (Int(..), Char(..), (-#), (+#), (*#))
import Safe.Coerce                (coerce)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Debug.Trace                (trace)
import System.Console.Pretty      (color, Color(Green, White, Red, Blue))

data ΣState = forall a. State !a !(TExpQ a) !(ΣVar a)
type ΣVars = [ΣState]
type IMVar = Int

newtype ΣVar a = ΣVar Int
newtype MVar xs ks a = MVar Int
newtype ΦVar a = ΦVar Int
data M k xs ks a i where
  Halt      :: M k '[a] ks a i
  Ret       :: M k (b ': xs) ((b ': xs) ': ks) a i
  Push      :: WQ x -> !(k (x ': xs) ks a i) -> M k xs ks a i
  Pop       :: !(k xs ks a i) -> M k (b ': xs) ks a i
  Lift2     :: !(WQ (x -> y -> z)) -> !(k (z ': xs) ks a i) -> M k (y ': x ': xs) ks a i
  Sat       :: WQ (Char -> Bool) -> !(k (Char ': xs) ks a i) -> M k xs ks a i
  Call      :: k xs ((b ': xs) ': ks) a i -> MVar xs ((b ': xs) ': ks) a -> !(k (b ': xs) ks a i) -> M k xs ks a i
  MuCall    :: MVar xs ((b ': xs) ': ks) a -> !(k (b ': xs) ks a i) -> M k xs ks a i
  Empt      :: M k xs ks a i
  Commit    :: !Bool -> !(k xs ks a i) -> M k xs ks a i
  HardFork  :: !(k xs ks a i) -> !(k xs ks a i) -> !(Maybe (ΦVar x, k (x ': xs) ks a i)) -> M k xs ks a i
  SoftFork  :: !(Maybe Int) -> !(k xs ks a i) -> !(k xs ks a i) -> !(Maybe (ΦVar x, k (x ': xs) ks a i)) -> M k xs ks a i
  Join      :: !(ΦVar x) -> M k (x ': xs) ks a i
  Attempt   :: !(Maybe Int) -> !(k xs ks a i) -> M k xs ks a i
  Look      :: !(k xs ks a i) -> M k xs ks a i
  NegLook   :: !(k xs ks a i) -> !(k xs ks a i) -> M k xs ks a i
  Restore   :: !(k xs ks a i) -> M k xs ks a i
  Case      :: !(k (x ': xs) ks a i) -> !(k (y ': xs) ks a i) -> M k (Either x y ': xs) ks a i
  Choices   :: ![WQ (x -> Bool)] -> ![k xs ks a i] -> M k (x ': xs) ks a i
  ChainIter :: !(ΣVar x) -> !(MVar xs ks a) -> M k ((x -> x) ': xs) ks a i
  ChainInit :: !(WQ x) -> !(ΣVar x) -> !(k xs ks a i) -> !(MVar xs ks a) -> k (x ': xs) ks a i -> M k (x ': xs) ks a i
  LogEnter  :: String -> !(k xs ks a i) -> M k xs ks a i
  LogExit   :: String -> !(k xs ks a i) -> M k xs ks a i

fmapInstr :: WQ (x -> y) -> Free M f (y ': xs) ks a i -> Free M f (x ': xs) ks a i
fmapInstr !f !m = Op (Push f (Op (Lift2 (lift' flip >*< lift' ($)) m)))

instance IFunctor M where
  imap f Halt = Halt
  imap f Ret = Ret
  imap f (Push x k) = Push x (f k)
  imap f (Pop k) = Pop (f k)
  imap f (Lift2 g k) = Lift2 g (f k)
  imap f (Sat g k) = Sat g (f k)
  imap f (Call m v k) = Call (f m) v (f k)
  imap f (MuCall v k) = MuCall v (f k)
  imap f Empt = Empt
  imap f (Commit exit k) = Commit exit (f k)
  imap f (SoftFork n p q (Just (φ, k))) = SoftFork n (f p) (f q) (Just (φ, f k))
  imap f (SoftFork n p q Nothing) = SoftFork n (f p) (f q) Nothing
  imap f (HardFork p q (Just (φ, k))) = HardFork (f p) (f q) (Just (φ, f k))
  imap f (HardFork p q Nothing) = HardFork (f p) (f q) Nothing
  imap f (Join φ) = Join φ
  imap f (Attempt n k) = Attempt n (f k)
  imap f (Look k) = Look (f k)
  imap f (NegLook m k) = NegLook (f m) (f k)
  imap f (Restore k) = Restore (f k)
  imap f (Case p q) = Case (f p) (f q)
  imap f (Choices fs ks) = Choices fs (map f ks)
  imap f (ChainIter σ v) = ChainIter σ v
  imap f (ChainInit x σ l v k) = ChainInit x σ (f l) v (f k)
  imap f (LogEnter name k) = LogEnter name (f k)
  imap f (LogExit name k) = LogExit name (f k)

instance Show (Free M f xs ks a i) where
  show = getConst . fold (const (Const "")) (Const . alg) where
    alg :: forall i j k l. M (Const String) i j k l -> String
    alg Halt = "Halt"
    alg Ret = "Ret"
    alg (Call m (MVar v) k) = "{Call μ" ++ show v ++ " " ++ getConst m ++ " " ++ getConst k ++ "}"
    alg (MuCall (MVar v) k) = "(μCall μ" ++ show v ++ " " ++ getConst k ++ ")"
    alg (Push _ k) = "(Push x " ++ getConst k ++ ")"
    alg (Pop k) = "(Pop " ++ getConst k ++ ")"
    alg (Lift2 _ k) = "(Lift2 f " ++ getConst k ++ ")"
    alg (Sat _ k) = "(Sat f " ++ getConst k ++ ")"
    alg Empt = "Empt"
    alg (Commit True k) = "(Commit end " ++ getConst k ++ ")"
    alg (Commit False k) = "(Commit " ++ getConst k ++ ")"
    alg (SoftFork Nothing p q Nothing) = "(SoftFork " ++ getConst p ++ " " ++ getConst q ++ ")"
    alg (SoftFork (Just n) p q Nothing) = "(SoftFork " ++ show n ++ " " ++ getConst p ++ " " ++ getConst q ++ ")"
    alg (SoftFork Nothing p q (Just (ΦVar φ, k))) = "(SoftFork " ++ getConst p ++ " " ++ getConst q ++ " (φ" ++ show φ ++ " = " ++ getConst k ++ "))"
    alg (SoftFork (Just n) p q (Just (ΦVar φ, k))) = "(SoftFork " ++ show n ++ " " ++ getConst p ++ " " ++ getConst q ++ " (φ" ++ show φ ++ " = " ++ getConst k ++ "))"
    alg (HardFork p q Nothing) = "(HardFork " ++ getConst p ++ " " ++ getConst q ++ ")"
    alg (HardFork p q (Just (ΦVar φ, k))) = "(HardFork " ++ getConst p ++ " " ++ getConst q ++ " (φ" ++ show φ ++ " = " ++ getConst k ++ "))"
    alg (Join (ΦVar φ)) = "φ" ++ show φ
    alg (Attempt Nothing k) = "(Try " ++ getConst k ++ ")"
    alg (Attempt (Just n) k) = "(Try " ++ show n ++ " " ++ getConst k ++ ")"
    alg (Look k) = "(Look " ++ getConst k ++ ")"
    alg (NegLook m k) = "(NegLook " ++ getConst m ++ " " ++ getConst k ++ ")"
    alg (Restore k) = "(Restore " ++ getConst k ++ ")"
    alg (Case m k) = "(Case " ++ getConst m ++ " " ++ getConst k ++ ")"
    alg (Choices _ ks) = "(Choices " ++ show (map getConst ks) ++ ")"
    alg (ChainIter (ΣVar σ) (MVar v)) = "(ChainIter σ" ++ show σ ++ " μ" ++ show v ++ ")"
    alg (ChainInit _ (ΣVar σ) m (MVar v) k) = "{ChainInit σ" ++ show σ ++ " μ" ++ show v ++ " " ++ getConst m ++ " " ++ getConst k ++ "}"
    alg (LogEnter _ k) = getConst k
    alg (LogExit _ k) = getConst k

data SList a = !a ::: !(SList a) | SNil
data HList xs where
  HNil :: HList '[]
  HCons :: a -> !(HList as) -> HList (a ': as)
data K s ks a where
  KNil :: K s '[] a
  KCons :: !(X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)) -> !(K s ks a) -> K s (xs ': ks) a

instance Show (K s ks a) where
  show KNil = "KNil"
  show (KCons _ ks) = "(KCons " ++ show ks ++ ")"

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
type D = Int
type D# = Int#
type QD = TExpQ D
type QST s a = TExpQ (ST s a)
newtype QSTRef s a = QSTRef (TExpQ (STRef s (SList a)))

data Γ s xs ks a = Γ { xs    :: QX xs
                     , ks    :: QK s ks a
                     , o     :: QO
                     , hs    :: QH s a
                     , cidx  :: QCIdx
                     , cs    :: QC s
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
suspend :: Exec s xs ks a i -> Ctx s a -> QK s ks a -> QK s (xs ': ks) a
suspend m ctx ks =
  [|| KCons (\xs ks o hs cidx cs d ->
    $$(run m (Γ[||xs||] [||ks||] [||I# o||] [||hs||] [||I# cidx||] [||cs||] [||I# d||]) ctx)) $$ks ||]
resume :: Γ s xs (xs ': ks) a -> QST s (Maybe a)
resume (Γ xs ks o hs cidx cs d) =
  [|| let ks' = bug ($$ks) :: K s (xs ': ks) a
          I# o# = $$o
          I# cidx# = $$cidx
          I# d# = $$d
      in
        case ks' of
          (KCons k ks) -> k $$(bug xs) ks o# $$hs cidx# $$cs d#
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

-- TODO Convert Input into a pair of getChar and inputSize, stored statically in the context
nextSafe :: Bool -> Input -> QO -> TExpQ (Char -> Bool) -> (QO -> TExpQ Char -> QST s (Maybe a)) -> QST s (Maybe a) -> QST s (Maybe a)
nextSafe True input o p good bad = [|| let !c = $$(charAt input) $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else $$bad ||]
nextSafe False input o p good bad = [||
    let bad' = $$bad in
      if  $$(size input) > $$o then let !c = $$(charAt input) $$o in if $$p c then $$(good [|| $$o + 1 ||] [|| c ||]) else bad'
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

instance GEq ΦVar where
  geq (ΦVar u) (ΦVar v)
    | u == v    = Just (coerce Refl)
    | otherwise = Nothing

instance GCompare ΦVar where
  gcompare (ΦVar u) (ΦVar v) = case compare u v of
    LT -> coerce GLT
    EQ -> coerce GEQ
    GT -> coerce GGT

makeΣ :: ΣVars -> (DMap ΣVar (QSTRef s) -> Σ s -> QST s r) -> QST s r
makeΣ ps = makeΣ' ps (DMap.empty) [|| return () ||] [|| return () ||] [|| const (return ()) ||]
  where
    makeΣ' :: ΣVars -> DMap ΣVar (QSTRef s) -> QST s () -> QST s () -> TExpQ (D -> ST s ()) -> (DMap ΣVar (QSTRef s) -> Σ s -> QST s r) -> QST s r
    makeΣ' [] m save restore rollback k =
      [|| let save' = $$save
              restore' = $$restore
              rollback' n = if n == 0 then return () else $$rollback n
          in $$(let !σs = Σ [||save'||] [||restore'||] [||rollback'||] in k m σs) ||]
    makeΣ' (State x qx (ΣVar v):ps) m save restore rollback k = [||
      do σ <- newSTRef ($$qx:::SNil)
         $$(let save' = [|| do modifySTRef' σ ($$qx:::); $$save ||]
                restore' = [|| do modifySTRef' σ (\(_:::xs) -> xs); $$restore ||]
                rollback' = [||\n -> do modifySTRef' σ (sdrop n); $$rollback n ||]
                m' = DMap.insert (ΣVar v) (QSTRef [|| σ ||]) m
            in makeΣ' ps m' save' restore' rollback' k)
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

sdrop :: Int -> SList a -> SList a
sdrop 0 xs = xs
sdrop n (_ ::: xs) = sdrop (n-1) xs

data GenExec s a = forall xs ks. GenExec (TExpQ (X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)))
newtype GenJoin s a x = GenJoin (TExpQ (x -> O# -> ST s (Maybe a)))
data Input = Input {charAt :: TExpQ (Int -> Char), size :: TExpQ Int, substr :: TExpQ (Int -> Int -> UArray Int Char)}
data Σ s = Σ { save :: QST s (), restore :: QST s (), rollback :: TExpQ (D -> ST s ()) }
data Ctx s a = Ctx {μs         :: Map IMVar (GenExec s a),
                    φs         :: DMap ΦVar (GenJoin s a),
                    σm         :: DMap ΣVar (QSTRef s),
                    σs         :: {-# UNPACK #-} !(Σ s),
                    input      :: {-# UNPACK #-} !Input,
                    constCount :: Int,
                    debugLevel :: Int}

addConstCount :: Int -> Ctx s a -> Ctx s a
addConstCount x ctx = ctx {constCount = constCount ctx + x}

skipBounds :: Ctx s a -> Bool
skipBounds ctx = constCount ctx > 0

debugUp :: Ctx s a -> Ctx s a
debugUp ctx = ctx {debugLevel = debugLevel ctx + 1}

debugDown :: Ctx s a -> Ctx s a
debugDown ctx = ctx {debugLevel = debugLevel ctx - 1}


newtype Exec s xs ks a i = Exec (Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a)))
run :: Exec s xs ks a i -> Γ s xs ks a -> (Ctx s a) -> QST s (Maybe a)
run (Exec m) γ ctx = runReader (m γ) ctx

exec :: TExpQ String -> (Free M Void '[] '[] a i, ΣVars) -> QST s (Maybe a)
exec input (!m, vss) = [||
  do xs <- makeX
     ks <- makeK
     hs <- makeH
     !(cidx, cs) <- makeC
     let !(UArray _ _ size input#) = $$(toArray input)
     let charAt (I# i#) = C# (indexWideCharArray# input# i#)
     let substr i j = ixmap (i, j) id (UArray 0 (size - 1) size input#) :: UArray Int Char
     $$(makeΣ vss (\σm σs ->
       run (fold absurd alg m) (Γ [||xs||] [||ks||] [||0||] [||hs||] [||cidx||] [||cs||] [||0||])
                               (Ctx Map.empty DMap.empty σm σs (Input [||charAt||] [||size||] [||substr||]) 0 0)))
  ||]
  where
    toArray :: TExpQ String -> TExpQ (UArray Int Char)
    toArray input = [|| listArray (0, length $$input-1) $$input ||]

    alg :: M (Exec s) xs ks a i -> Exec s xs ks a i
    alg Halt                  = Exec $ execHalt
    alg Ret                   = Exec $ execRet
    alg (Call m v k)          = Exec $ execCall m v k
    alg (MuCall v k)          = Exec $ execMuCall v k
    alg (Push x k)            = Exec $ execPush x k
    alg (Pop k)               = Exec $ execPop k
    alg (Lift2 f k)           = Exec $ execLift2 f k
    alg (Sat p k)             = Exec $ execSat p k
    alg Empt                  = Exec $ execEmpt
    alg (Commit exit k)       = Exec $ execCommit exit k
    alg (HardFork p q φ)      = Exec $ execHardFork p q φ
    alg (SoftFork n p q φ)    = Exec $ execSoftFork n p q φ
    alg (Join φ)              = Exec $ execJoin φ
    alg (Attempt n k)         = Exec $ execAttempt n k
    alg (Look k)              = Exec $ execLook k
    alg (NegLook m k)         = Exec $ execNegLook m k
    alg (Restore k)           = Exec $ execRestore k
    alg (Case p q)            = Exec $ execCase p q
    alg (Choices fs ks)       = Exec $ execChoices fs ks
    alg (ChainIter σ v)       = Exec $ execChainIter σ v
    alg (ChainInit x σ l v k) = Exec $ execChainInit x σ l v k
    alg (LogEnter name k)     = Exec $ execLogEnter name k
    alg (LogExit name k)      = Exec $ execLogExit name k

{-# INLINE setupHandlerΓ #-}
setupHandlerΓ :: Γ s xs ks a -> TExpQ (O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)) ->
                                (Γ s xs ks a -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandlerΓ γ !h !k = setupHandler (hs γ) (cidx γ) (cs γ) (o γ) h (\hs cidx cs -> k (γ {hs = hs, cidx = cidx, cs = cs}))

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

execHalt :: Γ s (a ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execHalt γ = return $! [|| case $$(xs γ) of HCons x _ -> return (Just x) ||]

execRet :: Γ s (b ': xs) ((b ': xs) ': ks) a -> Reader (Ctx s a) (QST s (Maybe a))
execRet γ = do ctx <- ask; return $! [|| do $$(restore (σs ctx)); $$(resume γ) ||]

execCall :: Exec s xs ((b ': xs) ': ks) a i -> MVar xs ((b ': xs) ': ks) a -> Exec s (b ': xs) ks a i
         -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execCall m (MVar μ) k γ@(Γ !xs ks o hs cidx cs d) =
  do ctx <- ask
     return $! [|| let !(I# o#) = $$o
                       !(I# cidx#) = $$cidx
                       !(I# d#) = $$d + 1
                   in fix (\r xs ks o# hs cidx# cs d# ->
       do $$(save (σs ctx))
          $$(let μs' = Map.insert μ (GenExec [||r||]) (μs ctx)
             in run m (Γ [||bug xs||] [||bug ks||] [||I# o#||] [||hs||] [||I# cidx#||] [||cs||] [||I# d#||]) (ctx {μs = μs'})
           )) (bug $$xs) $$(suspend k ctx ks) o# $$hs cidx# $$cs d# ||]

execMuCall :: MVar xs ((b ': xs) ': ks) a -> Exec s (b ': xs) ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execMuCall (MVar μ) k γ@(Γ !xs ks o hs cidx cs d) =
  do ctx <- ask
     case (μs ctx) Map.! μ of
       GenExec m -> return $! [|| let !(I# o#) = $$o
                                      !(I# cidx#) = $$cidx
                                      !(I# d#) = $$d + 1
                                  in $$(coerce m) $$xs $$(suspend k ctx ks) o# $$hs cidx# $$cs d#||]

execPush :: WQ x -> Exec s (x ': xs) ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execPush x (Exec k) γ = k (γ {xs = [|| pushX $$(_code x) $$(xs γ) ||]})

execPop :: Exec s xs ks a i -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execPop (Exec k) γ = k (γ {xs = [|| popX_ $$(xs γ) ||]})

execLift2 :: WQ (x -> y -> z) -> Exec s (z ': xs) ks a i -> Γ s (y ': x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLift2 f (Exec k) γ = k (γ {xs = [|| let !(y, xs') = popX $$(xs γ); !(x, xs'') = popX xs' in pushX ($$(_code f) x y) xs'' ||]})

execSat :: WQ (Char -> Bool) -> Exec s (Char ': xs) ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execSat p k γ =
  do ctx <- ask
     return $! (nextSafe (skipBounds ctx) (input ctx) (o γ) (_code p) (\o c -> run k (γ {xs = [|| pushX $$c $$(xs γ) ||], o = o}) ctx) (raiseΓ γ))

execEmpt :: Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execEmpt γ = return (raiseΓ γ)

execCommit :: Bool -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execCommit exit (Exec k) γ = local (\ctx -> if exit then addConstCount (-1) ctx else ctx)
                            (k (γ {hs = [|| popH_ $$(hs γ) ||], cidx = [|| popC_ $$(cidx γ) ||]}))

execHardFork :: Exec s xs ks a i -> Exec s xs ks a i -> Maybe (ΦVar x, Exec s (x ': xs) ks a i) -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execHardFork p q (Just (φ, k)) γ =
  do ctx <- ask
     return $! [||
       let join x (o# :: O#) = $$(run k (γ {xs = [||HCons x $$(xs γ)||], o = [||I# o#||]}) ctx)
       in $$(let ctx' = ctx {φs = DMap.insert φ (GenJoin [||join||]) (φs ctx)}
                 handler = [||\o# hs cidx# cs d'# ->
                   do (c, cidx') <- popC (I# cidx#) cs
                      if c == (I# o#) then do $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
                                              $$(run q (γ {o = [||I# o#||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx')
                      else raise hs cidx' cs (I# o#) (I# d'#)
                   ||]
             in setupHandlerΓ γ handler (\γ' -> run p γ' ctx'))
       ||]
execHardFork p q Nothing γ =
  do ctx <- ask
     let handler = [||\o# hs cidx# cs d'# ->
           do (c, cidx') <- popC (I# cidx#) cs
              if c == (I# o#) then do $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
                                      $$(run q (γ {o = [||I# o#||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx)
              else raise hs cidx' cs (I# o#) (I# d'#)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' -> run p γ' ctx))

execSoftFork :: Maybe Int -> Exec s xs ks a i -> Exec s xs ks a i -> Maybe (ΦVar x, Exec s (x ': xs) ks a i) -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execSoftFork constantInput p q (Just (φ, k)) γ =
  do ctx <- ask
     return $! [||
       let join x (o# :: O#) = $$(run k (γ {xs = [||HCons x $$(xs γ)||], o = [||I# o#||]}) ctx)
       in $$(let ctx' = ctx {φs = DMap.insert φ (GenJoin [||join||]) (φs ctx)}
                 handler = [||\_ hs cidx# cs d'# ->
                   do !(o, cidx') <- popC (I# cidx#) cs
                      $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
                      $$(run q (γ {o = [||o||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx')
                   ||]
             in setupHandlerΓ γ handler (\γ' ->
               case constantInput of
                 Nothing -> run p γ' ctx
                 Just _ | skipBounds ctx -> run p γ' (addConstCount 1 ctx)
                 Just n -> [||
                     if $$(size (input ctx)) > (n + $$(o γ) - 1) then $$(run p γ' (addConstCount 1 ctx'))
                     else $$(raiseΓ γ')
                   ||]))
       ||]
execSoftFork constantInput p q Nothing γ =
  do ctx <- ask
     let handler = [||\_ hs cidx# cs d'# ->
           do !(o, cidx') <- popC (I# cidx#) cs
              $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
              $$(run q (γ {o = [||o||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' ->
       case constantInput of
         Nothing -> run p γ' ctx
         Just _ | skipBounds ctx -> run p γ' (addConstCount 1 ctx)
         Just n -> [||
             if $$(size (input ctx)) > (n + $$(o γ) - 1) then $$(run p γ' (addConstCount 1 ctx))
             else $$(raiseΓ γ')
           ||]
       ))

execJoin :: ΦVar x -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execJoin φ γ = fmap (\(GenJoin k) -> [|| let !(I# o#) = $$(o γ) in $$k (peekX $$(xs γ)) o# ||]) (fmap ((DMap.! φ) . φs) ask)

execAttempt :: Maybe Int -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execAttempt constantInput k γ =
  do ctx <- ask
     let handler = [||\(_ :: O#) hs cidx# cs d'# ->
           do !(o, cidx') <- popC (I# cidx#) cs
              raise hs cidx' cs o (I# d'#)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' ->
       case constantInput of
         Nothing -> run k γ' ctx
         Just _ | skipBounds ctx -> run k γ' (addConstCount 1 ctx)
         Just n -> [||
             if $$(size (input ctx)) > (n + $$(o γ) - 1) then $$(run k γ' (addConstCount 1 ctx))
             else $$(raiseΓ γ')
           ||]
       ))

execLook :: Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLook k γ =
  do ctx <- ask
     let handler = [||\o# hs cidx# cs d'# -> raise hs (popC_ (I# cidx#)) cs (I# o#) (I# d'#)||]
     return $! (setupHandlerΓ γ handler (\γ' -> run k γ' ctx))

execNegLook :: Exec s xs ks a i -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execNegLook m k γ =
  do ctx <- ask
     let handler = [||\_ hs cidx# cs d'# ->
           do (o, cidx') <- popC (I# cidx#) cs
              $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
              $$(run k (γ {o = [||o||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' -> run m γ' ctx))

execRestore :: Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execRestore k γ =
  do ctx <- ask
     return $! [||
       do (o, cidx') <- popC $$(cidx γ) $$(cs γ)
          $$(run k (γ {o = [||o||], hs = [|| popH_ $$(hs γ) ||], cidx = [||cidx'||]}) ctx)
       ||]

execCase :: Exec s (x ': xs) ks a i -> Exec s (y ': xs) ks a i -> Γ s (Either x y ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execCase p q γ =
  do ctx <- ask
     return $! [||
         let !(e, xs') = popX $$(xs γ)
         in case e of
           Left x -> $$(run p (γ {xs = [||pushX x xs'||]}) ctx)
           Right y  -> $$(run q (γ {xs = [||pushX y xs'||]}) ctx)
       ||]

execChoices :: forall x xs ks a s i. [WQ (x -> Bool)] -> [Exec s xs ks a i] -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execChoices fs ks γ = do ctx <- ask; return [|| let (x, xs') = popX $$(xs γ) in $$(go [||x||] fs ks (γ {xs = [||xs'||]}) ctx) ||]
  where
    go :: TExpQ x -> [WQ (x -> Bool)] -> [Exec s xs ks a i] -> Γ s xs ks a -> Ctx s a -> QST s (Maybe a)
    go _ [] [] γ _ = raiseΓ γ
    go x (f:fs) (k:ks) γ ctx = [||
        if $$(_code f) $$x then $$(run k γ ctx)
        else $$(go x fs ks γ ctx)
      ||]


execChainIter :: ΣVar x -> MVar xs ks a -> Γ s ((x -> x) ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execChainIter u (MVar μ) γ@(Γ !xs ks o hs cidx cs d) =
  do ctx <- ask
     let !(QSTRef σ) = (σm ctx) DMap.! u
     case (μs ctx) Map.! μ of
       GenExec k -> return [||
         do let !(g, xs') = popX $$xs
            modifyΣ $$σ g
            pokeC $$o $$cidx $$cs
            let I# o# = $$o
            let I# cidx# = $$cidx
            let I# d# = $$d
            $$(coerce k) xs' $$ks o# $$hs cidx# $$cs d#
         ||]

execChainInit :: WQ x -> ΣVar x -> Exec s xs ks a i -> MVar xs ks a -> Exec s (x ': xs) ks a i
                  -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execChainInit deflt u l (MVar μ) k γ@(Γ !xs ks o _ _ _ d) =
  do ctx <- ask
     let !(QSTRef σ) = (σm ctx) DMap.! u
     let xs' = [|| popX $$xs ||]
     let handler = [||\o# hs cidx# cs d'# ->
          do $$(rollback (σs ctx)) ((I# d'#) - $$d)
             (c, cidx') <- popC (I# cidx#) cs
             if c == (I# o#) then do y <- pokeΣ $$σ $$(_code deflt)
                                     $$(run k (γ {xs = [|| pushX y (snd $$xs') ||],
                                                  o = [||I# o#||],
                                                  hs = [||hs||],
                                                  cidx = [||cidx'||],
                                                  cs = [||cs||]}) ctx)
             else do writeΣ $$σ $$(_code deflt); raise hs cidx' cs (I# o#) $$d
          ||]
     return $! (setupHandlerΓ γ handler (\γ' -> [||
       -- NOTE: Only the offset and the cs array can change between interations of a chainPre
       do writeΣ $$σ (fst $$xs')
          let I# o# = $$o
          fix (\r o# cs ->
            $$(let μs' = Map.insert μ (GenExec [|| \_ _ o# _ _ cs _ -> r o# cs ||]) (μs ctx)
               in run l (Γ [||snd $$xs'||] ks [||I# o#||] (hs γ') (cidx γ') [||cs||] d) (ctx {μs = μs'})))
            o# $$(cs γ')||]))

preludeString :: String -> Char -> Γ s xs ks a -> Ctx s a -> String -> TExpQ String
preludeString name dir γ ctx ends = [|| concat [$$prelude, $$eof, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    offset       = o γ
    indent       = replicate (debugLevel ctx * 2) ' '
    start        = [|| max ($$offset - 5) 0 ||]
    end          = [|| min ($$offset + 6) $$(size (input ctx)) ||]
    sub          = [|| $$(substr (input ctx)) $$start ($$end - 1) ||]
    inputTrace   = [|| let replace '\n' = color Green "↙"
                           replace ' '  = color White "·"
                           replace c    = return c
                       in concatMap replace (elems $$sub) ||]
    eof          = [|| if $$end == $$(size (input ctx)) then $$inputTrace ++ color Red "•" else $$inputTrace ||]
    prelude      = [|| concat [indent, dir : name, dir : " (", show $$offset, "): "] ||]
    caretSpace   = [|| replicate (length $$prelude + $$offset - $$start) ' ' ||]


execLogEnter :: String -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLogEnter name k γ =
  do ctx <- ask
     let handler = [||\o hs cidx cs d' -> trace $$(preludeString name '<' (γ {o = [||I# o||]}) ctx (color Red " Fail")) (raise hs (I# cidx) cs (I# o) (I# d')) ||]
     return $! (setupHandlerΓ γ handler (\γ' -> [|| trace $$(preludeString name '>' γ ctx "") $$(run k γ' (debugUp ctx))||]))


execLogExit :: String -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLogExit name k γ =
  do ctx <- ask
     return $! [|| trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(run k γ (debugDown ctx)) ||]