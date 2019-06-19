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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Machine where

import MachineOps            --()
import Indexed               (IFunctor3, Free3(Op3), Void3, Const3(..), imap3, absurd, fold3)
import Utils                 (WQ(..), lift', (>*<), TExpQ)
import Data.Function         (fix)
import Data.Word             (Word64)
import Control.Monad.ST      (ST)
import Control.Monad.Reader  (ask, Reader, runReader, local)
import Data.STRef            (STRef, modifySTRef', newSTRef)
import Data.Dependent.Map    (DMap)
import Data.GADT.Compare     (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))
import Data.Array.Unboxed    (listArray)
import Data.Array.Base       (UArray(..), unsafeAt, MArray, numElements, ixmap, elems)
import GHC.Prim              (Int#, Char#, newByteArray#, indexWideCharArray#)
import GHC.Exts              (Int(..), Char(..), (-#), (+#), (*#))
import Safe.Coerce           (coerce)
import Debug.Trace           (trace)
import System.Console.Pretty (color, Color(Green, White, Red, Blue))
import qualified Data.Dependent.Map as DMap

newtype Machine a = Machine { getMachine :: Free3 M Void3 '[] '[] a }
newtype ΣVar a = ΣVar IΣVar
newtype MVar a = MVar IMVar
newtype ΦVar a = ΦVar IΦVar
type ΦDecl k x xs ks a = (ΦVar x, k (x ': xs) ks a)
newtype AbstractedStack k x a = AbstractedStack (forall xs ks. k xs ((x ': xs) ': ks) a)
abstract :: k xs ((x ': xs) ': ks) a -> AbstractedStack k x a
abstract k = AbstractedStack (coerce k)

data M k xs ks a where
  Halt      :: M k '[a] '[] a
  Ret       :: M k (x ': xs) ((x ': xs) ': ks) a
  Push      :: WQ x -> !(k (x ': xs) ks a) -> M k xs ks a
  Pop       :: !(k xs ks a) -> M k (x ': xs) ks a
  Lift2     :: !(WQ (x -> y -> z)) -> !(k (z ': xs) ks a) -> M k (y ': x ': xs) ks a
  Sat       :: WQ (Char -> Bool) -> !(k (Char ': xs) ks a) -> M k xs ks a
  Call      :: Maybe (AbstractedStack k x a) -> !(MVar x) -> !(k (x ': xs) ks a) -> M k xs ks a
  Jump      :: Maybe (AbstractedStack k x a) -> !(MVar x) -> M k xs ((x ': xs) ': ks) a
  Empt      :: M k xs ks a
  Commit    :: !Bool -> !(k xs ks a) -> M k xs ks a
  HardFork  :: !(k xs ks a) -> !(k xs ks a) -> !(Maybe (ΦDecl k x xs ks a)) -> M k xs ks a
  SoftFork  :: !(Maybe Int) -> !(k xs ks a) -> !(k xs ks a) -> !(Maybe (ΦDecl k x xs ks a)) -> M k xs ks a
  Join      :: !(ΦVar x) -> M k (x ': xs) ks a
  Attempt   :: !(Maybe Int) -> !(k xs ks a) -> M k xs ks a
  Look      :: !(k xs ks a) -> M k xs ks a
  NegLook   :: !(k xs ks a) -> !(k xs ks a) -> M k xs ks a
  Restore   :: !(k xs ks a) -> M k xs ks a
  Case      :: !(k (x ': xs) ks a) -> !(k (y ': xs) ks a) -> M k (Either x y ': xs) ks a
  Choices   :: ![WQ (x -> Bool)] -> ![k xs ks a] -> M k (x ': xs) ks a
  ChainIter :: !(ΣVar x) -> !(MVar x) -> M k ((x -> x) ': xs) ((x ': xs) ': ks) a
  ChainInit :: !(WQ x) -> !(ΣVar x) -> !(k xs ((x ': xs) ': ks) a) -> !(MVar x) -> !(k (x ': xs) ks a) -> M k (x ': xs) ks a
  LogEnter  :: String -> !(k xs ks a) -> M k xs ks a
  LogExit   :: String -> !(k xs ks a) -> M k xs ks a

fmapInstr :: WQ (x -> y) -> Free3 M f (y ': xs) ks a -> Free3 M f (x ': xs) ks a
fmapInstr !f !m = Op3 (Push f (Op3 (Lift2 (lift' flip >*< lift' ($)) m)))

data Γ s xs ks a = Γ { xs    :: QX xs
                     , ks    :: QK s ks a
                     , o     :: QO
                     , hs    :: QH s a
                     , cs    :: QC
                     , d     :: QD }

newtype AbsExec s a x = AbsExec { runConcrete :: forall xs ks. X xs -> K s ((x ': xs) ': ks) a -> O# -> H s a -> C -> D# -> ST s (Maybe a) }
newtype QAbsExec s a x = QAbsExec (TExpQ (AbsExec s a x))
newtype QJoin s a x = QJoin (TExpQ (x -> O# -> ST s (Maybe a)))
newtype IMVar = IMVar Word64 deriving (Ord, Eq, Num, Enum)
newtype IΦVar = IΦVar Word64 deriving (Ord, Eq, Num, Enum)
newtype IΣVar = IΣVar Word64 deriving (Ord, Eq, Num, Enum)
newtype QSTRef s a = QSTRef (TExpQ (STRef s (SList a)))
data Ctx s a = Ctx { μs         :: DMap MVar (QAbsExec s a)
                   , φs         :: DMap ΦVar (QJoin s a)
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
makeΣ ps = makeΣ' ps (DMap.empty) [|| return () :: ST s () ||] [|| return () :: ST s () ||] [|| const (return () :: ST s ()) ||]
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

newtype Exec s xs ks a = Exec (Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a)))
run :: Exec s xs ks a -> Γ s xs ks a -> Ctx s a -> QST s (Maybe a)
run (Exec m) γ ctx = runReader (m γ) ctx

exec :: TExpQ String -> (Machine a, ΣVars) -> QST s (Maybe a)
exec input (Machine !m, vss) = [||
  do xs <- makeX
     ks <- makeK
     hs <- makeH
     cs <- makeC
     let !(UArray _ _ size input#) = listArray (0, length $$input-1) $$input
     let charAt (I# i#) = C# (indexWideCharArray# input# i#)
     let substr i j = ixmap (i, j) id (UArray 0 (size - 1) size input#) :: UArray Int Char
     $$(makeΣ vss (\σm σs ->
       run (fold3 absurd alg m) (Γ [||xs||] [||ks||] [||0||] [||hs||] [||cs||] [||0||])
                                (Ctx DMap.empty DMap.empty σm σs (Input [||charAt||] [||size||] [||substr||]) 0 0)))
  ||]
  where
    alg :: M (Exec s) xs ks a -> Exec s xs ks a
    alg Halt                  = Exec $ execHalt
    alg Ret                   = Exec $ execRet
    alg (Call m μ k)          = Exec $ execCall m μ k
    alg (Jump m μ)            = Exec $ execJump m μ
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
    alg (ChainIter σ μ)       = Exec $ execChainIter σ μ
    alg (ChainInit x σ l μ k) = Exec $ execChainInit x σ l μ k
    alg (LogEnter name k)     = Exec $ execLogEnter name k
    alg (LogExit name k)      = Exec $ execLogExit name k

execHalt :: Γ s '[a] ks a -> Reader (Ctx s a) (QST s (Maybe a))
execHalt γ = return $! [|| return $! Just $! peekX ($$(xs γ)) ||]

execRet :: Γ s (x ': xs) ((x ': xs) ': ks) a -> Reader (Ctx s a) (QST s (Maybe a))
execRet γ = do ctx <- ask; return $! [|| do $$(restore (σs ctx)); $$(resume γ) ||]

execCall :: Maybe (AbstractedStack (Exec s) x a) -> MVar x -> Exec s (x ': xs) ks a
         -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execCall (Just (AbstractedStack m)) μ k γ@(Γ xs ks o hs cs d) =
  do (ctx :: Ctx s a) <- ask
     return $! [|| do let !(I# o#) = $$o
                      let !(I# d#) = $$d + 1
                      $$(save (σs ctx))
                      runConcrete (fix (\r -> 
                        AbsExec (\(!xs) (!ks) o# (!hs) (!cs) d# ->
                          $$(let μs' = DMap.insert μ (QAbsExec [||r||]) (μs ctx)
                            in run m (Γ [||xs||] [||ks||] [||I# o#||] [||hs||] [||cs||] [||I# d#||]) (ctx {μs = μs'}))
                          ))) $$xs $$(suspend k γ ctx) o# $$hs $$cs d# ||]
execCall Nothing μ k γ@(Γ xs ks o hs cs d) =
  do ctx <- ask
     let (QAbsExec m) = (μs ctx) DMap.! μ
     return $! [|| do let !(I# o#) = $$o
                      let !(I# d#) = $$d + 1
                      $$(save (σs ctx))
                      runConcrete $$m $$xs $$(suspend k γ ctx) o# $$hs $$cs d# ||]

execJump :: Maybe (AbstractedStack (Exec s) x a) -> MVar x 
         -> Γ s xs ((x ': xs) ': ks) a -> Reader (Ctx s a) (QST s (Maybe a))
execJump (Just (AbstractedStack m)) μ γ@(Γ xs ks o hs cs d) =
  do (ctx :: Ctx s a) <- ask
     return $! [|| let !(I# o#) = $$o
                       !(I# d#) = $$d
                   in runConcrete (fix (\r -> 
                        AbsExec (\(!xs) (!ks) o# (!hs) (!cs) d# ->
                          $$(let μs' = DMap.insert μ (QAbsExec [||r||]) (μs ctx)
                            in run m (Γ [||xs||] [||ks||] [||I# o#||] [||hs||] [||cs||] [||I# d#||]) (ctx {μs = μs'}))
                          ))) $$xs $$ks o# $$hs $$cs d# ||]         
execJump Nothing μ γ@(Γ xs ks o hs cs d) =
  do ctx <- ask
     let (QAbsExec m) = (μs ctx) DMap.! μ
     return $! [|| let !(I# o#) = $$o
                       !(I# d#) = $$d
                   in runConcrete $$m $$xs $$ks o# $$hs $$cs d# ||]

execPush :: WQ x -> Exec s (x ': xs) ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execPush x (Exec k) γ = k (γ {xs = [|| pushX $$(_code x) $$(xs γ) ||]})

execPop :: Exec s xs ks a -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execPop (Exec k) γ = k (γ {xs = [|| popX_ $$(xs γ) ||]})

execLift2 :: WQ (x -> y -> z) -> Exec s (z ': xs) ks a -> Γ s (y ': x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLift2 f (Exec k) γ = k (γ {xs = [|| let !(# y, xs' #) = popX $$(xs γ); !(# x, xs'' #) = popX xs' in pushX ($$(_code f) x y) xs'' ||]})

execSat :: WQ (Char -> Bool) -> Exec s (Char ': xs) ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execSat p k γ =
  do ctx <- ask
     return $! (nextSafe (skipBounds ctx) (input ctx) (o γ) (_code p) (\o c -> run k (γ {xs = [|| pushX $$c $$(xs γ) ||], o = o}) ctx) (raiseΓ γ))

execEmpt :: Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execEmpt γ = return (raiseΓ γ)

execCommit :: Bool -> Exec s xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execCommit exit (Exec k) γ = local (\ctx -> if exit then addConstCount (-1) ctx else ctx)
                                   (k (γ {hs = [|| popH_ $$(hs γ) ||], cs = [|| popC_ $$(cs γ) ||]}))

execHardFork :: Exec s xs ks a -> Exec s xs ks a -> Maybe (ΦDecl (Exec s) x xs ks a) -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execHardFork p q decl γ = setupJoinPoint decl γ $
  do ctx <- ask
     let handler = [||\o# hs cs d'# ->
           let !(# c, cs' #) = popC cs
           in if c == (I# o#) then $$(recoverΓ [||I# d'#||] q (γ {o = [||I# o#||], hs = [||hs||], cs = [||cs'||]}) ctx)
              else raise hs cs' (I# o#) (I# d'#)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' -> run p γ' ctx))

execSoftFork :: Maybe Int -> Exec s xs ks a -> Exec s xs ks a -> Maybe (ΦDecl (Exec s) x xs ks a) -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execSoftFork constantInput p q decl γ = setupJoinPoint decl γ $
  do ctx <- ask
     let handler = [||\_ hs cs d'# ->
           let !(# o, cs' #) = popC cs
           in $$(recoverΓ [||I# d'#||] q (γ {o = [||o||], hs = [||hs||], cs = [||cs'||]}) ctx)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' -> inputSizeCheck constantInput p γ' ctx))

execJoin :: ΦVar x -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execJoin φ γ = fmap (\(QJoin k) -> [|| let !(I# o#) = $$(o γ) in $$k (peekX $$(xs γ)) o# ||]) (fmap ((DMap.! φ) . φs) ask)

execAttempt :: Maybe Int -> Exec s xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execAttempt constantInput k γ =
  do ctx <- ask
     let handler = [||\(_ :: O#) hs cs d'# -> let !(# o, cs' #) = popC cs in raise hs cs' o (I# d'#)||]
     return $! (setupHandlerΓ γ handler (\γ' -> inputSizeCheck constantInput k γ' ctx))

execLook :: Exec s xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLook k γ =
  do ctx <- ask
     let handler = [||\o# hs cs d'# -> raise hs (popC_ cs) (I# o#) (I# d'#)||]
     return $! (setupHandlerΓ γ handler (\γ' -> run k γ' ctx))

execNegLook :: Exec s xs ks a -> Exec s xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execNegLook m k γ =
  do ctx <- ask
     let handler = [||\_ hs cs d'# ->
           let !(# o, cs' #) = popC cs
           in $$(recoverΓ [||I# d'#||] k (γ {o = [||o||], hs = [||hs||], cs = [||cs'||]}) ctx)
           ||]
     return $! (setupHandlerΓ γ handler (\γ' -> run m γ' ctx))

execRestore :: Exec s xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execRestore k γ =
  do ctx <- ask
     return $! [||
       let !(# o, cs' #) = popC $$(cs γ)
       in $$(run k (γ {o = [||o||], hs = [|| popH_ $$(hs γ) ||], cs = [||cs'||]}) ctx)
       ||]

execCase :: Exec s (x ': xs) ks a -> Exec s (y ': xs) ks a -> Γ s (Either x y ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execCase p q γ =
  do ctx <- ask
     return $! [||
         let !(# e, xs' #) = popX $$(xs γ)
         in case e of
           Left x -> $$(run p (γ {xs = [||pushX x xs'||]}) ctx)
           Right y  -> $$(run q (γ {xs = [||pushX y xs'||]}) ctx)
       ||]

execChoices :: forall x xs ks a s. [WQ (x -> Bool)] -> [Exec s xs ks a] -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execChoices fs ks γ = do ctx <- ask; return [|| let (# x, xs' #) = popX $$(xs γ) in $$(go [||x||] fs ks (γ {xs = [||xs'||]}) ctx) ||]
  where
    go :: TExpQ x -> [WQ (x -> Bool)] -> [Exec s xs ks a] -> Γ s xs ks a -> Ctx s a -> QST s (Maybe a)
    go _ [] [] γ _ = raiseΓ γ
    go x (f:fs) (k:ks) γ ctx = [||
        if $$(_code f) $$x then $$(run k γ ctx)
        else $$(go x fs ks γ ctx)
      ||]


execChainIter :: ΣVar x -> MVar x -> Γ s ((x -> x) ': xs) ((x ': xs) ': ks) a -> Reader (Ctx s a) (QST s (Maybe a))
execChainIter u μ (Γ xs ks o hs cs d) =
  do ctx <- ask
     let !(QSTRef σ) = (σm ctx) DMap.! u
     case (μs ctx) DMap.! μ of
       QAbsExec k -> return [||
         do let !(# g, xs' #) = popX $$xs
            modifyΣ $$σ g
            let cs' = pokeC $$o $$cs
            let I# o# = $$o
            let I# d# = $$d
            runConcrete $$k xs' $$ks o# $$hs cs' d#
         ||]

fst# :: (# a, b #) -> a
fst# (# x, _ #) = x

snd# :: (# a, b #) -> b
snd# (# _, y #) = y

execChainInit :: WQ x -> ΣVar x -> Exec s xs ((x ': xs) ': ks) a -> MVar x -> Exec s (x ': xs) ks a
              -> Γ s (x ': xs) ks a -> Reader (Ctx s a) (QST s (Maybe a))
execChainInit deflt u l μ k γ@(Γ xs ks o _ _ d) =
  do (ctx :: Ctx s a) <- ask
     let !(QSTRef σ) = (σm ctx) DMap.! u
     let handler = [||\o# hs cs d'# ->
          let !(# c, cs' #) = popC cs
          in $$(recover (σs ctx) [||(I# d'#) - $$d||] [||
               if c == (I# o#) then
                 do y <- pokeΣ $$σ $$(_code deflt)
                    $$(run k (γ {xs = [|| pokeX y $$xs ||],
                                 o = [||I# o#||],
                                 hs = [||hs||],
                                 cs = [||cs'||]}) ctx)
                else do writeΣ $$σ $$(_code deflt); raise hs cs' (I# o#) $$d >>= runHandler
              ||])
          ||]
     return $! (setupHandlerΓ γ handler (\γ' -> [||
       -- NOTE: Only the offset and the check stack can change between interations of a chainPre
       do let !(# x, xs' #) = popX $$xs
          writeΣ $$σ x
          let I# o# = $$o
          fix (\r o# (!cs) ->
            $$(let μs' = DMap.insert μ (QAbsExec [|| AbsExec (\_ _ o# _ cs _ -> r o# cs) ||]) (μs ctx)
               in run l (Γ [||xs'||] [||pushK noreturn $$ks||] [||I# o#||] (hs γ') [||cs||] d) (ctx {μs = μs'})))
            o# $$(cs γ') ||]))

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

execLogEnter :: String -> Exec s xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLogEnter name k γ =
  do ctx <- ask
     let handler = [||\o hs cs d' -> trace $$(preludeString name '<' (γ {o = [||I# o||]}) ctx (color Red " Fail")) (raise hs cs (I# o) (I# d')) ||]
     return $! (setupHandlerΓ γ handler (\γ' -> [|| trace $$(preludeString name '>' γ ctx "") $$(run k γ' (debugUp ctx))||]))

execLogExit :: String -> Exec s xs ks a -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a))
execLogExit name k γ =
  do ctx <- ask
     return $! [|| trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(run k γ (debugDown ctx)) ||]

setupHandlerΓ :: Γ s xs ks a -> TExpQ (O# -> H s a -> C -> D# -> ST s (Handled s a)) ->
                                (Γ s xs ks a -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandlerΓ γ !h !k = setupHandler (hs γ) (cs γ) (o γ) h (\hs cs -> k (γ {hs = hs, cs = cs}))

setupJoinPoint :: Maybe (ΦDecl (Exec s) x xs ks a) -> Γ s xs ks a -> Reader (Ctx s a) (QST s (Maybe a)) -> Reader (Ctx s a) (QST s (Maybe a))
setupJoinPoint Nothing γ mx = mx
setupJoinPoint (Just (φ, k)) γ mx =
  do ctx <- ask
     return $! [||
       let join x (o# :: O#) = $$(run k (γ {xs = [||pushX x $$(xs γ)||], o = [||I# o#||]}) ctx)
       in $$(runReader mx (ctx {φs = DMap.insert φ (QJoin [||join||]) (φs ctx)}))
       ||]

inputSizeCheck :: Maybe Int -> Exec s xs ks a -> Γ s xs ks a -> Ctx s a -> QST s (Maybe a)
inputSizeCheck Nothing p γ ctx = run p γ ctx
inputSizeCheck (Just n) p γ ctx
  | skipBounds ctx = run p γ (addConstCount 1 ctx)
  | otherwise      = [||
      if $$(size (input ctx)) > (n + $$(o γ) - 1) then $$(run p γ (addConstCount 1 ctx))
      else $$(raiseΓ γ)
    ||]

raiseΓ :: Γ s xs ks a -> QST s (Maybe a)
raiseΓ γ = [|| raise $$(hs γ) $$(cs γ) $$(o γ) $$(d γ) >>= runHandler ||]

recoverΓ :: QD -> Exec s xs ks a -> Γ s xs ks a -> Ctx s a -> QST s (Handled s a)
recoverΓ d' k γ ctx = recover (σs ctx) [||$$d' - $$(d γ)||] (run k γ ctx)

suspend :: Exec s (x ': xs) ks a -> Γ s xs ks a -> Ctx s a -> QK s ((x ': xs) ': ks) a
suspend m γ ctx = [|| pushK (\xs o# -> $$(run m (γ {xs = [||xs||], o = [||I# o#||]}) ctx)) $$(ks γ) ||]

resume :: Γ s (x ': xs) ((x ': xs) ': ks) a -> QST s (Maybe a)
resume γ = [|| let I# o# = $$(o γ) in peekK $$(ks γ) $$(xs γ) o# ||]

instance IFunctor3 M where
  imap3 f Halt                                  = Halt
  imap3 f Ret                                   = Ret
  imap3 f (Push x k)                            = Push x (f k)
  imap3 f (Pop k)                               = Pop (f k)
  imap3 f (Lift2 g k)                           = Lift2 g (f k)
  imap3 f (Sat g k)                             = Sat g (f k)
  imap3 f (Call (Just (AbstractedStack m)) μ k) = Call (Just (AbstractedStack (f m))) μ (f k)
  imap3 f (Call Nothing μ k)                    = Call Nothing μ (f k)
  imap3 f (Jump (Just (AbstractedStack m)) μ)   = Jump (Just (AbstractedStack (f m))) μ
  imap3 f (Jump Nothing μ)                      = Jump Nothing μ
  imap3 f Empt                                  = Empt
  imap3 f (Commit exit k)                       = Commit exit (f k)
  imap3 f (SoftFork n p q (Just (φ, k)))        = SoftFork n (f p) (f q) (Just (φ, f k))
  imap3 f (SoftFork n p q Nothing)              = SoftFork n (f p) (f q) Nothing
  imap3 f (HardFork p q (Just (φ, k)))          = HardFork (f p) (f q) (Just (φ, f k))
  imap3 f (HardFork p q Nothing)                = HardFork (f p) (f q) Nothing
  imap3 f (Join φ)                              = Join φ
  imap3 f (Attempt n k)                         = Attempt n (f k)
  imap3 f (Look k)                              = Look (f k)
  imap3 f (NegLook m k)                         = NegLook (f m) (f k)
  imap3 f (Restore k)                           = Restore (f k)
  imap3 f (Case p q)                            = Case (f p) (f q)
  imap3 f (Choices fs ks)                       = Choices fs (map f ks)
  imap3 f (ChainIter σ μ)                       = ChainIter σ μ
  imap3 f (ChainInit x σ l μ k)                 = ChainInit x σ (f l) μ (f k)
  imap3 f (LogEnter name k)                     = LogEnter name (f k)
  imap3 f (LogExit name k)                      = LogExit name (f k)

instance Show (Machine a) where show = show . getMachine
instance Show (Free3 M f xs ks a) where
  show = getConst3 . fold3 (const (Const3 "")) (Const3 . alg) where
    alg :: forall i j k. M (Const3 String) i j k -> String
    alg Halt                                  = "Halt"
    alg Ret                                   = "Ret"
    alg (Call (Just (AbstractedStack m)) μ k) = "{Call " ++ show μ ++ " " ++ getConst3 m ++ " " ++ getConst3 k ++ "}"
    alg (Call Nothing μ k)                    = "(Call " ++ show μ ++ " " ++ getConst3 k ++ ")"
    alg (Jump (Just (AbstractedStack m)) μ)   = "{Jump " ++ show μ ++ " " ++ getConst3 m ++ "}"
    alg (Jump Nothing μ)                      = "(Jump " ++ show μ ++ ")"
    alg (Push _ k)                            = "(Push x " ++ getConst3 k ++ ")"
    alg (Pop k)                               = "(Pop " ++ getConst3 k ++ ")"
    alg (Lift2 _ k)                           = "(Lift2 f " ++ getConst3 k ++ ")"
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
    alg (Look k)                              = "(Look " ++ getConst3 k ++ ")"
    alg (NegLook m k)                         = "(NegLook " ++ getConst3 m ++ " " ++ getConst3 k ++ ")"
    alg (Restore k)                           = "(Restore " ++ getConst3 k ++ ")"
    alg (Case m k)                            = "(Case " ++ getConst3 m ++ " " ++ getConst3 k ++ ")"
    alg (Choices _ ks)                        = "(Choices " ++ show (map getConst3 ks) ++ ")"
    alg (ChainIter σ μ)                       = "(ChainIter " ++ show σ ++ " " ++ show μ ++ ")"
    alg (ChainInit _ σ m μ k)                 = "{ChainInit " ++ show σ ++ " " ++ show μ ++ " " ++ getConst3 m ++ " " ++ getConst3 k ++ "}"
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