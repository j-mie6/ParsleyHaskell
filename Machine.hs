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

import MachineOps            --()
import Indexed               (IFunctor, Free(Op), Void, Const(..), imap, absurd, fold, getConst)
import Utils                 (bug, WQ(..), lift', (>*<), TExpQ)
import Data.Function         (fix)
import Control.Monad.ST      (ST)
import Control.Monad.Reader  (ask, Reader, runReader, local)
import Data.STRef            (STRef, modifySTRef', newSTRef)
import Data.Map.Strict       (Map)
import Data.Dependent.Map    (DMap)
import Data.GADT.Compare     (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))
import Data.Array.Unboxed    (listArray)
import Data.Array.Base       (UArray(..), unsafeAt, MArray, numElements, ixmap, elems)
import GHC.Prim              (Int#, Char#, newByteArray#, indexWideCharArray#)
import GHC.Exts              (Int(..), Char(..), (-#), (+#), (*#))
import Safe.Coerce           (coerce)
import Debug.Trace           (trace)
import System.Console.Pretty (color, Color(Green, White, Red, Blue))
import qualified Data.Map.Strict    as Map
import qualified Data.Dependent.Map as DMap

newtype Machine a = Machine { getMachine :: Free M Void '[] '[] a () }
newtype ΣVar a = ΣVar Int
newtype MVar xs ks a = MVar Int
newtype ΦVar a = ΦVar Int
type ΦDecl k x xs ks a i = (ΦVar x, k (x ': xs) ks a i)
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
  HardFork  :: !(k xs ks a i) -> !(k xs ks a i) -> !(Maybe (ΦDecl k x xs ks a i)) -> M k xs ks a i
  SoftFork  :: !(Maybe Int) -> !(k xs ks a i) -> !(k xs ks a i) -> !(Maybe (ΦDecl k x xs ks a i)) -> M k xs ks a i
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

data Γ s xs ks a = Γ { xs    :: QX xs
                     , ks    :: QK s ks a
                     , o     :: QO
                     , hs    :: QH s a
                     , cidx  :: QCIdx
                     , cs    :: QC s
                     , d     :: QD }

data GenExec s a = forall xs ks. GenExec (TExpQ (X xs -> K s ks a -> O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)))
newtype GenJoin s a x = GenJoin (TExpQ (x -> O# -> ST s (Maybe a)))
data Σ s = Σ { save :: QST s (), restore :: QST s (), rollback :: TExpQ (D -> ST s ()) }
type IMVar = Int
newtype QSTRef s a = QSTRef (TExpQ (STRef s (SList a)))
data Ctx s a = Ctx { μs         :: Map IMVar (GenExec s a)
                   , φs         :: DMap ΦVar (GenJoin s a)
                   , σm         :: DMap ΣVar (QSTRef s)
                   , σs         :: {-# UNPACK #-} !(Σ s)
                   , input      :: {-# UNPACK #-} !Input
                   , constCount :: Int
                   , debugLevel :: Int }

addConstCount :: Int -> Ctx s a -> Ctx s a
addConstCount x ctx = ctx {constCount = constCount ctx + x}

skipBounds :: Ctx s a -> Bool
skipBounds ctx = constCount ctx > 0

debugUp :: Ctx s a -> Ctx s a
debugUp ctx = ctx {debugLevel = debugLevel ctx + 1}

debugDown :: Ctx s a -> Ctx s a
debugDown ctx = ctx {debugLevel = debugLevel ctx - 1}

type ΣVars = [ΣState]
data ΣState = forall a. ΣState !a !(TExpQ a) !(ΣVar a)
makeΣ :: ΣVars -> (DMap ΣVar (QSTRef s) -> Σ s -> QST s r) -> QST s r
makeΣ ps = makeΣ' ps (DMap.empty) [|| return () ||] [|| return () ||] [|| const (return ()) ||]
  where
    makeΣ' :: ΣVars -> DMap ΣVar (QSTRef s) -> QST s () -> QST s () -> TExpQ (D -> ST s ()) -> (DMap ΣVar (QSTRef s) -> Σ s -> QST s r) -> QST s r
    makeΣ' [] m save restore rollback k =
      [|| let save' = $$save
              restore' = $$restore
              rollback' n = if n == 0 then return () else $$rollback n
          in $$(let !σs = Σ [||save'||] [||restore'||] [||rollback'||] in k m σs) ||]
    makeΣ' (ΣState x qx (ΣVar v):ps) m save restore rollback k = [||
      do σ <- newSTRef ($$qx:::SNil)
         $$(let save' = [|| do modifySTRef' σ ($$qx:::); $$save ||]
                restore' = [|| do modifySTRef' σ (\(_:::xs) -> xs); $$restore ||]
                rollback' = [||\n -> do modifySTRef' σ (sdrop n); $$rollback n ||]
                m' = DMap.insert (ΣVar v) (QSTRef [|| σ ||]) m
            in makeΣ' ps m' save' restore' rollback' k)
      ||]

sdrop :: Int -> SList a -> SList a
sdrop 0 xs = xs
sdrop n (_ ::: xs) = sdrop (n-1) xs

newtype Exec s xs ks a i = Exec (Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a)))
run :: Exec s xs ks a i -> Γ s xs ks a -> (Ctx s a) -> QST s (Maybe a)
run (Exec m) γ ctx = runReader (m γ) ctx

exec :: TExpQ String -> (Machine a, ΣVars) -> QST s (Maybe a)
exec input (Machine !m, vss) = [||
  do xs <- makeX
     ks <- makeK
     hs <- makeH
     !(cidx, cs) <- makeC
     let !(UArray _ _ size input#) = listArray (0, length $$input-1) $$input-- $$(toArray input)
     let charAt (I# i#) = C# (indexWideCharArray# input# i#)
     let substr i j = ixmap (i, j) id (UArray 0 (size - 1) size input#) :: UArray Int Char
     $$(makeΣ vss (\σm σs ->
       run (fold absurd alg m) (Γ [||xs||] [||ks||] [||0||] [||hs||] [||cidx||] [||cs||] [||0||])
                               (Ctx Map.empty DMap.empty σm σs (Input [||charAt||] [||size||] [||substr||]) 0 0)))
  ||]
  where
    --toArray :: TExpQ String -> TExpQ (UArray Int Char)
    --toArray input = [|| listArray (0, length $$input-1) $$input ||]
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

execHalt :: Γ s (a ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execHalt γ = return $! [|| return (Just (peekX ($$(xs γ)))) ||]

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
execLift2 f (Exec k) γ = k (γ {xs = [|| let !(# y, xs' #) = popX $$(xs γ); !(# x, xs'' #) = popX xs' in pushX ($$(_code f) x y) xs'' ||]})

execSat :: WQ (Char -> Bool) -> Exec s (Char ': xs) ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execSat p k γ =
  do ctx <- ask
     return $! (nextSafe (skipBounds ctx) (input ctx) (o γ) (_code p) (\o c -> run k (γ {xs = [|| pushX $$c $$(xs γ) ||], o = o}) ctx) (raiseΓ γ))

execEmpt :: Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execEmpt γ = return (raiseΓ γ)

execCommit :: Bool -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execCommit exit (Exec k) γ = local (\ctx -> if exit then addConstCount (-1) ctx else ctx)
                            (k (γ {hs = [|| popH_ $$(hs γ) ||], cidx = [|| popC_ $$(cidx γ) ||]}))

execHardFork :: Exec s xs ks a i -> Exec s xs ks a i -> Maybe (ΦDecl (Exec s) x xs ks a i) -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execHardFork p q decl γ = setupJoinPoint decl γ $
  do ctx <- ask
     let handler = [||\o# hs cidx# cs d'# ->
           do (c, cidx') <- popC (I# cidx#) cs
              if c == (I# o#) then do $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
                                      $$(run q (γ {o = [||I# o#||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx)
              else raise hs cidx' cs (I# o#) (I# d'#)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' -> run p γ' ctx))

execSoftFork :: Maybe Int -> Exec s xs ks a i -> Exec s xs ks a i -> Maybe (ΦDecl (Exec s) x xs ks a i) -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execSoftFork constantInput p q decl γ = setupJoinPoint decl γ $
  do ctx <- ask
     let handler = [||\_ hs cidx# cs d'# ->
           do !(o, cidx') <- popC (I# cidx#) cs
              $$(rollback (σs ctx)) ((I# d'#) - $$(d γ))
              $$(run q (γ {o = [||o||], hs = [||hs||], cidx = [||cidx'||], cs = [||cs||]}) ctx)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' -> inputSizeCheck constantInput p γ' ctx))

execJoin :: ΦVar x -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execJoin φ γ = fmap (\(GenJoin k) -> [|| let !(I# o#) = $$(o γ) in $$k (peekX $$(xs γ)) o# ||]) (fmap ((DMap.! φ) . φs) ask)

execAttempt :: Maybe Int -> Exec s xs ks a i -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execAttempt constantInput k γ =
  do ctx <- ask
     let handler = [||\(_ :: O#) hs cidx# cs d'# ->
           do !(o, cidx') <- popC (I# cidx#) cs
              raise hs cidx' cs o (I# d'#)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' -> inputSizeCheck constantInput k γ' ctx))

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
         let !(# e, xs' #) = popX $$(xs γ)
         in case e of
           Left x -> $$(run p (γ {xs = [||pushX x xs'||]}) ctx)
           Right y  -> $$(run q (γ {xs = [||pushX y xs'||]}) ctx)
       ||]

execChoices :: forall x xs ks a s i. [WQ (x -> Bool)] -> [Exec s xs ks a i] -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execChoices fs ks γ = do ctx <- ask; return [|| let (# x, xs' #) = popX $$(xs γ) in $$(go [||x||] fs ks (γ {xs = [||xs'||]}) ctx) ||]
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
         do let !(# g, xs' #) = popX $$xs
            modifyΣ $$σ g
            pokeC $$o $$cidx $$cs
            let I# o# = $$o
            let I# cidx# = $$cidx
            let I# d# = $$d
            $$(coerce k) xs' $$ks o# $$hs cidx# $$cs d#
         ||]

fst# :: (# a, b #) -> a
fst# (# x, _ #) = x

snd# :: (# a, b #) -> b
snd# (# _, y #) = y

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
                                     $$(run k (γ {xs = [|| pushX y (snd# $$xs') ||],
                                                  o = [||I# o#||],
                                                  hs = [||hs||],
                                                  cidx = [||cidx'||],
                                                  cs = [||cs||]}) ctx)
             else do writeΣ $$σ $$(_code deflt); raise hs cidx' cs (I# o#) $$d
          ||]
     return $! (setupHandlerΓ γ handler (\γ' -> [||
       -- NOTE: Only the offset and the cs array can change between interations of a chainPre
       do writeΣ $$σ (fst# $$xs')
          let I# o# = $$o
          fix (\r o# cs ->
            $$(let μs' = Map.insert μ (GenExec [|| \_ _ o# _ _ cs _ -> r o# cs ||]) (μs ctx)
               in run l (Γ [||snd# $$xs'||] ks [||I# o#||] (hs γ') (cidx γ') [||cs||] d) (ctx {μs = μs'})))
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

{-# INLINE setupHandlerΓ #-}
setupHandlerΓ :: Γ s xs ks a -> TExpQ (O# -> H s a -> CIdx# -> C s -> D# -> ST s (Maybe a)) ->
                                (Γ s xs ks a -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandlerΓ γ !h !k = setupHandler (hs γ) (cidx γ) (cs γ) (o γ) h (\hs cidx cs -> k (γ {hs = hs, cidx = cidx, cs = cs}))

setupJoinPoint :: Maybe (ΦDecl (Exec s) x xs ks a i) -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a)) -> Reader (Ctx s a) (QST s (Maybe a))
setupJoinPoint Nothing γ mx = mx
setupJoinPoint (Just (φ, k)) γ mx =
  do ctx <- ask
     return $! [||
       let join x (o# :: O#) = $$(run k (γ {xs = [||pushX x $$(xs γ)||], o = [||I# o#||]}) ctx)
       in $$(runReader mx (ctx {φs = DMap.insert φ (GenJoin [||join||]) (φs ctx)}))
       ||]

inputSizeCheck :: Maybe Int -> Exec s xs ks a i -> Γ s xs ks a -> Ctx s a -> QST s (Maybe a)
inputSizeCheck Nothing p γ ctx = run p γ ctx
inputSizeCheck (Just n) p γ ctx
  | skipBounds ctx = run p γ (addConstCount 1 ctx)
  | otherwise      = [||
      if $$(size (input ctx)) > (n + $$(o γ) - 1) then $$(run p γ (addConstCount 1 ctx))
      else $$(raiseΓ γ)
    ||]

raiseΓ :: Γ s xs ks a -> QST s (Maybe a)
raiseΓ γ = [|| raise $$(hs γ) $$(cidx γ) $$(cs γ) $$(o γ) $$(d γ) ||]

suspend :: Exec s xs ks a i -> Ctx s a -> QK s ks a -> QK s (xs ': ks) a
suspend m ctx ks =
  [|| pushK (\xs ks o hs cidx cs d ->
    $$(run m (Γ[||xs||] [||ks||] [||I# o||] [||hs||] [||I# cidx||] [||cs||] [||I# d||]) ctx)) $$ks ||]

resume :: Γ s xs (xs ': ks) a -> QST s (Maybe a)
resume (Γ xs ks o hs cidx cs d) =
  -- TODO: Check if bug is still needed now we use popK
  [|| let ks' = bug ($$ks) :: K s (xs ': ks) a
          I# o# = $$o
          I# cidx# = $$cidx
          I# d# = $$d
          !(# k, ks'' #) = popK ks'
      in k $$(bug xs) ks'' o# $$hs cidx# $$cs d#
  ||]

instance IFunctor M where
  imap f Halt                           = Halt
  imap f Ret                            = Ret
  imap f (Push x k)                     = Push x (f k)
  imap f (Pop k)                        = Pop (f k)
  imap f (Lift2 g k)                    = Lift2 g (f k)
  imap f (Sat g k)                      = Sat g (f k)
  imap f (Call m v k)                   = Call (f m) v (f k)
  imap f (MuCall v k)                   = MuCall v (f k)
  imap f Empt                           = Empt
  imap f (Commit exit k)                = Commit exit (f k)
  imap f (SoftFork n p q (Just (φ, k))) = SoftFork n (f p) (f q) (Just (φ, f k))
  imap f (SoftFork n p q Nothing)       = SoftFork n (f p) (f q) Nothing
  imap f (HardFork p q (Just (φ, k)))   = HardFork (f p) (f q) (Just (φ, f k))
  imap f (HardFork p q Nothing)         = HardFork (f p) (f q) Nothing
  imap f (Join φ)                       = Join φ
  imap f (Attempt n k)                  = Attempt n (f k)
  imap f (Look k)                       = Look (f k)
  imap f (NegLook m k)                  = NegLook (f m) (f k)
  imap f (Restore k)                    = Restore (f k)
  imap f (Case p q)                     = Case (f p) (f q)
  imap f (Choices fs ks)                = Choices fs (map f ks)
  imap f (ChainIter σ v)                = ChainIter σ v
  imap f (ChainInit x σ l v k)          = ChainInit x σ (f l) v (f k)
  imap f (LogEnter name k)              = LogEnter name (f k)
  imap f (LogExit name k)               = LogExit name (f k)

instance Show (Machine a) where show = show . getMachine
instance Show (Free M f xs ks a i) where
  show = getConst . fold (const (Const "")) (Const . alg) where
    alg :: forall i j k l. M (Const String) i j k l -> String
    alg Halt                                       = "Halt"
    alg Ret                                        = "Ret"
    alg (Call m (MVar v) k)                        = "{Call μ" ++ show v ++ " " ++ getConst m ++ " " ++ getConst k ++ "}"
    alg (MuCall (MVar v) k)                        = "(μCall μ" ++ show v ++ " " ++ getConst k ++ ")"
    alg (Push _ k)                                 = "(Push x " ++ getConst k ++ ")"
    alg (Pop k)                                    = "(Pop " ++ getConst k ++ ")"
    alg (Lift2 _ k)                                = "(Lift2 f " ++ getConst k ++ ")"
    alg (Sat _ k)                                  = "(Sat f " ++ getConst k ++ ")"
    alg Empt                                       = "Empt"
    alg (Commit True k)                            = "(Commit end " ++ getConst k ++ ")"
    alg (Commit False k)                           = "(Commit " ++ getConst k ++ ")"
    alg (SoftFork Nothing p q Nothing)             = "(SoftFork " ++ getConst p ++ " " ++ getConst q ++ ")"
    alg (SoftFork (Just n) p q Nothing)            = "(SoftFork " ++ show n ++ " " ++ getConst p ++ " " ++ getConst q ++ ")"
    alg (SoftFork Nothing p q (Just (ΦVar φ, k)))  = "(SoftFork " ++ getConst p ++ " " ++ getConst q ++ " (φ" ++ show φ ++ " = " ++ getConst k ++ "))"
    alg (SoftFork (Just n) p q (Just (ΦVar φ, k))) = "(SoftFork " ++ show n ++ " " ++ getConst p ++ " " ++ getConst q ++ " (φ" ++ show φ ++ " = " ++ getConst k ++ "))"
    alg (HardFork p q Nothing)                     = "(HardFork " ++ getConst p ++ " " ++ getConst q ++ ")"
    alg (HardFork p q (Just (ΦVar φ, k)))          = "(HardFork " ++ getConst p ++ " " ++ getConst q ++ " (φ" ++ show φ ++ " = " ++ getConst k ++ "))"
    alg (Join (ΦVar φ))                            = "φ" ++ show φ
    alg (Attempt Nothing k)                        = "(Try " ++ getConst k ++ ")"
    alg (Attempt (Just n) k)                       = "(Try " ++ show n ++ " " ++ getConst k ++ ")"
    alg (Look k)                                   = "(Look " ++ getConst k ++ ")"
    alg (NegLook m k)                              = "(NegLook " ++ getConst m ++ " " ++ getConst k ++ ")"
    alg (Restore k)                                = "(Restore " ++ getConst k ++ ")"
    alg (Case m k)                                 = "(Case " ++ getConst m ++ " " ++ getConst k ++ ")"
    alg (Choices _ ks)                             = "(Choices " ++ show (map getConst ks) ++ ")"
    alg (ChainIter (ΣVar σ) (MVar v))              = "(ChainIter σ" ++ show σ ++ " μ" ++ show v ++ ")"
    alg (ChainInit _ (ΣVar σ) m (MVar v) k)        = "{ChainInit σ" ++ show σ ++ " μ" ++ show v ++ " " ++ getConst m ++ " " ++ getConst k ++ "}"
    alg (LogEnter _ k)                             = getConst k
    alg (LogExit _ k)                              = getConst k
  
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
