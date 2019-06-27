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
{-# LANGUAGE FlexibleContexts #-}
module Machine (module Machine, Input(..)) where

import MachineOps
import Indexed                    (IFunctor3, Free3(Op3), Void3, Const3(..), imap3, absurd, fold3)
import Utils                      (WQ(..), lift', (>*<), TExpQ)
import Data.Word                  (Word64)
import Control.Monad              (forM)
import Control.Monad.ST           (ST)
import Control.Monad.Reader       (ask, asks, local, Reader, runReader, MonadReader)
import Data.STRef                 (STRef)
import Data.Dependent.Map         (DMap)
import Data.GADT.Compare          (GEq, GCompare, gcompare, geq, (:~:)(Refl), GOrdering(..))
import Data.Array.Unboxed         (listArray)
import Data.Array.Base            (UArray(..), unsafeAt, MArray, numElements, ixmap, elems)
import GHC.Prim                   (Int#, Char#, newByteArray#, indexWideCharArray#)
import GHC.Exts                   (Int(..), Char(..), (-#), (+#), (*#))
import Safe.Coerce                (coerce)
import Debug.Trace                (trace)
import System.Console.Pretty      (color, Color(Green, White, Red, Blue))
import qualified Data.Dependent.Map as DMap ((!), insert, empty)

newtype Machine a = Machine { getMachine :: Free3 M Void3 '[] '[] a }
newtype ΣVar a = ΣVar IΣVar
newtype MVar a = MVar IMVar
newtype ΦVar a = ΦVar IΦVar
type ΦDecl k x xs ks a = (ΦVar x, k (x ': xs) ks a)
newtype LetBinding a x = LetBinding (forall xs. Free3 M Void3 xs (x ': xs) a)
letBind :: Free3 M Void3 xs (x ': xs) a -> LetBinding a x
letBind m = LetBinding (coerce m)

instance Show (LetBinding a x) where show (LetBinding m) = show m

data M k xs ks a where
  Halt      :: M k '[a] '[] a
  Ret       :: M k (x ': xs) (x ': xs) a
  Push      :: WQ x -> !(k (x ': xs) ks a) -> M k xs ks a
  Pop       :: !(k xs ks a) -> M k (x ': xs) ks a
  Lift2     :: !(WQ (x -> y -> z)) -> !(k (z ': xs) ks a) -> M k (y ': x ': xs) ks a
  Sat       :: WQ (Char -> Bool) -> !(k (Char ': xs) ks a) -> M k xs ks a
  Call      :: !(MVar x) -> !(k (x ': xs) ks a) -> M k xs ks a
  Jump      :: !(MVar x) -> M k xs (x ': xs) a
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
  Choices   :: ![WQ (x -> Bool)] -> ![k xs ks a] -> k xs ks a -> M k (x ': xs) ks a
  ChainIter :: !(ΣVar x) -> !(MVar x) -> M k ((x -> x) ': xs) (x ': xs) a
  ChainInit :: !(ΣVar x) -> !(k xs (x ': xs) a) -> !(MVar x) -> !(k (x ': xs) ks a) -> M k (x ': xs) ks a
  LogEnter  :: String -> !(k xs ks a) -> M k xs ks a
  LogExit   :: String -> !(k xs ks a) -> M k xs ks a

fmapInstr :: WQ (x -> y) -> Free3 M f (y ': xs) ks a -> Free3 M f (x ': xs) ks a
fmapInstr !f !m = Op3 (Push f (Op3 (Lift2 (lift' flip >*< lift' ($)) m)))

data Γ s xs ks a = Γ { xs    :: QX xs
                     , k     :: QK s ks a
                     , o     :: QO
                     , hs    :: QH s a
                     , cs    :: QC }

newtype AbsExec s a x = AbsExec { runConcrete :: forall xs. X xs -> K s (x ': xs) a -> O# -> H s a -> C -> ST s (Maybe a) }
newtype QAbsExec s a x = QAbsExec (TExpQ (AbsExec s a x))
newtype QJoin s a x = QJoin (TExpQ (x -> O# -> ST s (Maybe a)))
newtype IMVar = IMVar Word64 deriving (Ord, Eq, Num, Enum)
newtype IΦVar = IΦVar Word64 deriving (Ord, Eq, Num, Enum)
newtype IΣVar = IΣVar Word64 deriving (Ord, Eq, Num, Enum)
newtype QSTRef s x = QSTRef (TExpQ (STRef s x))
data Ctx s a = Ctx { μs         :: DMap MVar (QAbsExec s a)
                   , φs         :: DMap ΦVar (QJoin s a)
                   , σs         :: DMap ΣVar (QSTRef s)
                   , input      :: {-# UNPACK #-} !InputOps
                   , constCount :: Int
                   , debugLevel :: Int }

insertM :: MVar x -> TExpQ (AbsExec s a x) -> Ctx s a -> Ctx s a
insertM μ q ctx = ctx {μs = DMap.insert μ (QAbsExec q) (μs ctx)}

insertΦ :: ΦVar x -> TExpQ (x -> O# -> ST s (Maybe a)) -> Ctx s a -> Ctx s a
insertΦ φ qjoin ctx = ctx {φs = DMap.insert φ (QJoin qjoin) (φs ctx)}

insertΣ :: ΣVar x -> TExpQ (STRef s x) -> Ctx s a -> Ctx s a
insertΣ σ qref ctx = ctx {σs = DMap.insert σ (QSTRef qref) (σs ctx)}

addConstCount :: Int -> Ctx s a -> Ctx s a
addConstCount x ctx = ctx {constCount = constCount ctx + x}

skipBounds :: Ctx s a -> Bool
skipBounds ctx = constCount ctx > 0

debugUp :: Ctx s a -> Ctx s a
debugUp ctx = ctx {debugLevel = debugLevel ctx + 1}

debugDown :: Ctx s a -> Ctx s a
debugDown ctx = ctx {debugLevel = debugLevel ctx - 1}

newtype Exec s xs ks a = Exec (Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a)))
run :: Exec s xs ks a -> Γ s xs ks a -> Ctx s a -> QST s (Maybe a)
run (Exec m) γ ctx = runReader m ctx γ

exec :: TExpQ PreparedInput -> (Machine a, DMap MVar (LetBinding a), [IMVar]) -> QST s (Maybe a)
exec input (Machine !m, ms, topo) = [||
  do xs <- makeX
     ks <- makeK
     hs <- makeH
     cs <- makeC
     let !(PreparedInput charAt size) = $$input
     $$(readyCalls topo ms (readyExec m) 
         (Γ [||xs||] [||ks||] [||0||] [||hs||] [||cs||])
         (Ctx DMap.empty DMap.empty DMap.empty (InputOps [||charAt||] [||size||]) 0 0))
  ||]

readyCalls :: [IMVar] -> DMap MVar (LetBinding a) -> Exec s '[] '[] a -> Γ s '[] '[] a -> Ctx s a -> QST s (Maybe a)
readyCalls topo ms start γ = foldr readyFunc (run start γ) topo
  where
    readyFunc v rest ctx = 
      let μ = MVar v
          LetBinding k = ms DMap.! μ
      in [|| let recu = AbsExec (\(!xs) (!ks) o# (hs) (cs) -> 
                   $$(run (readyExec k) (Γ [||xs||] [||ks||] [||I# o#||] [||hs||] [||cs||]) 
                                        (insertM μ [||recu||] ctx)))
             in $$(rest (insertM μ [||recu||] ctx)) ||]

readyExec :: Free3 M Void3 xs ks a -> Exec s xs ks a
readyExec = fold3 absurd (Exec . alg)
  where
    alg Halt                = execHalt
    alg Ret                 = execRet
    alg (Call μ k)          = execCall μ k
    alg (Jump μ)            = execJump μ
    alg (Push x k)          = execPush x k
    alg (Pop k)             = execPop k
    alg (Lift2 f k)         = execLift2 f k
    alg (Sat p k)           = execSat p k
    alg Empt                = execEmpt
    alg (Commit exit k)     = execCommit exit k
    alg (HardFork p q φ)    = execHardFork p q φ
    alg (SoftFork n p q φ)  = execSoftFork n p q φ
    alg (Join φ)            = execJoin φ
    alg (Attempt n k)       = execAttempt n k
    alg (Look k)            = execLook k
    alg (NegLook m k)       = execNegLook m k
    alg (Restore k)         = execRestore k
    alg (Case p q)          = execCase p q
    alg (Choices fs ks def) = execChoices fs ks def
    alg (ChainIter σ μ)     = execChainIter σ μ
    alg (ChainInit σ l μ k) = execChainInit σ l μ k
    alg (LogEnter name k)   = execLogEnter name k
    alg (LogExit name k)    = execLogExit name k

execHalt :: Reader (Ctx s a) (Γ s '[a] ks a -> QST s (Maybe a))
execHalt = return $! \γ -> [|| return $! Just $! peekX ($$(xs γ)) ||]

execRet :: Reader (Ctx s a) (Γ s (x ': xs) (x ': xs) a -> QST s (Maybe a))
execRet = return $! \γ -> [|| let I# o# = $$(o γ) in $$(k γ) $$(xs γ) o# ||]

execCall :: MVar x -> Exec s (x ': xs) ks a -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execCall μ (Exec k) =
  do !(QAbsExec m) <- askM μ
     mk <- k
     return $! \γ@(Γ xs ks o hs cs) -> [|| let !(I# o#) = $$o in runConcrete $$m $$xs $$(suspend mk γ) o# $$hs $$cs ||]

execJump :: MVar x -> Reader (Ctx s a) (Γ s xs (x ': xs) a -> QST s (Maybe a))
execJump μ =
  do !(QAbsExec m) <- askM μ
     return $! \γ@(Γ xs ks o hs cs) -> [|| let !(I# o#) = $$o in runConcrete $$m $$xs $$ks o# $$hs $$cs ||]

execPush :: WQ x -> Exec s (x ': xs) ks a -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execPush x (Exec k) = fmap (\m γ -> m (γ {xs = [|| pushX $$(_code x) $$(xs γ) ||]})) k

execPop :: Exec s xs ks a -> Reader (Ctx s a) (Γ s (x ': xs) ks a -> QST s (Maybe a))
execPop (Exec k) = fmap (\m γ -> m (γ {xs = [|| popX_ $$(xs γ) ||]})) k

execLift2 :: WQ (x -> y -> z) -> Exec s (z ': xs) ks a -> Reader (Ctx s a) (Γ s (y ': x ': xs) ks a -> QST s (Maybe a))
execLift2 f (Exec k) = fmap (\m γ -> m (γ {xs = [|| let (# y, xs' #) = popX $$(xs γ); (# x, xs'' #) = popX xs' in pushX ($$(_code f) x y) xs'' ||]})) k

execSat :: WQ (Char -> Bool) -> Exec s (Char ': xs) ks a -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execSat p (Exec k) =
  do mk <- k
     asks $! \ctx γ -> nextSafe (skipBounds ctx) (input ctx) (o γ) (_code p) (\o c -> mk (γ {xs = [|| pushX $$c $$(xs γ) ||], o = o})) (raiseΓ γ)

execEmpt :: Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execEmpt = return raiseΓ

execCommit :: Bool -> Exec s xs ks a -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execCommit exit (Exec k) = local (\ctx -> if exit then addConstCount (-1) ctx else ctx)
                                 (fmap (\m γ -> m (γ {hs = [|| popH_ $$(hs γ) ||], cs = [|| popC_ $$(cs γ) ||]})) k)

execHardFork :: Exec s xs ks a -> Exec s xs ks a -> Maybe (ΦDecl (Exec s) x xs ks a) -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execHardFork (Exec p) (Exec q) decl = setupJoinPoint decl $
  do mp <- p
     mq <- q
     asks $! \ctx γ ->
       let handler = [||\hs o# cs ->
             let !(# c, cs' #) = popC cs
             in if c == (I# o#) then $$(mq (γ {o = [||I# o#||], hs = [||hs||], cs = [||cs'||]}))
                else raise hs cs' (I# o#)
             ||]
       in setupHandlerΓ γ handler mp

execSoftFork :: Maybe Int -> Exec s xs ks a -> Exec s xs ks a -> Maybe (ΦDecl (Exec s) x xs ks a) -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execSoftFork constantInput (Exec p) (Exec q) decl = setupJoinPoint decl $
  do mp <- inputSizeCheck constantInput p
     mq <- q
     asks $! \ctx γ ->
       let handler = [||\hs _ cs ->
             let !(# o, cs' #) = popC cs
             in $$(mq (γ {o = [||o||], hs = [||hs||], cs = [||cs'||]}))
             ||]
       in setupHandlerΓ γ handler mp

execJoin :: ΦVar x -> Reader (Ctx s a) (Γ s (x ': xs) ks a -> QST s (Maybe a))
execJoin φ = fmap (\(QJoin k) γ -> [|| let !(I# o#) = $$(o γ) in $$k (peekX $$(xs γ)) o# ||]) (asks ((DMap.! φ) . φs))

execAttempt :: Maybe Int -> Exec s xs ks a -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execAttempt constantInput (Exec k) =
  let handler = [||\hs (_ :: O#) cs -> let !(# o, cs' #) = popC cs in raise hs cs' o||]
  in fmap (\mk γ -> setupHandlerΓ γ handler mk) (inputSizeCheck constantInput k)

execLook :: Exec s xs ks a -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execLook (Exec k) =
  let handler = [||\hs o# cs -> raise hs (popC_ cs) (I# o#)||]
  in fmap (\mk γ -> setupHandlerΓ γ handler mk) k

execNegLook :: Exec s xs ks a -> Exec s xs ks a -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execNegLook (Exec m) (Exec k) =
  do mm <- m
     mk <- k
     asks (\ctx γ ->
       let handler = [||\hs _ cs ->
             let !(# o, cs' #) = popC cs
             in $$(mk (γ {o = [||o||], hs = [||hs||], cs = [||cs'||]}))
             ||]
       in setupHandlerΓ γ handler mm)

execRestore :: Exec s xs ks a -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execRestore (Exec k) =
  do mk <- k
     return $! \γ -> [||
       let !(# o, cs' #) = popC $$(cs γ)
       in $$(mk (γ {o = [||o||], hs = [|| popH_ $$(hs γ) ||], cs = [||cs'||]}))
       ||]

execCase :: Exec s (x ': xs) ks a -> Exec s (y ': xs) ks a -> Reader (Ctx s a) (Γ s (Either x y ': xs) ks a -> QST s (Maybe a))
execCase (Exec p) (Exec q) =
  do mp <- p
     mq <- q
     return $! \γ -> [||
         let !(# e, xs' #) = popX $$(xs γ)
         in case e of
           Left x -> $$(mp (γ {xs = [||pushX x xs'||]}))
           Right y  -> $$(mq (γ {xs = [||pushX y xs'||]}))
       ||]

execChoices :: forall x xs ks a s. [WQ (x -> Bool)] -> [Exec s xs ks a] -> Exec s xs ks a -> Reader (Ctx s a) (Γ s (x ': xs) ks a -> QST s (Maybe a))
execChoices fs ks (Exec def) = 
  do mdef <- def
     fmap (\mks γ -> [|| let !(# x, xs' #) = popX $$(xs γ) in $$(go [||x||] fs mks mdef (γ {xs = [||xs'||]})) ||]) (forM ks (\(Exec k) -> k))
  where
    go :: TExpQ x -> [WQ (x -> Bool)] -> [Γ s xs ks a -> QST s (Maybe a)] -> (Γ s xs ks a -> QST s (Maybe a)) -> Γ s xs ks a -> QST s (Maybe a)
    go _ [] [] def γ = def γ
    go x (f:fs) (mk:mks) def γ = [||
        if $$(_code f) $$x then $$(mk γ)
        else $$(go x fs mks def γ)
      ||]


execChainIter :: ΣVar x -> MVar x -> Reader (Ctx s a) (Γ s ((x -> x) ': xs) (x ': xs) a -> QST s (Maybe a))
execChainIter σ μ =
  do !(QSTRef ref) <- askΣ σ
     !(QAbsExec k) <- askM μ
     return $! \(Γ xs ks o hs cs) -> [||
       do let (# g, xs' #) = popX $$xs
          modifyΣ $$ref g
          let I# o# = $$o
          runConcrete $$k xs' $$ks o# $$hs (pokeC $$o $$cs)
       ||]

execChainInit :: ΣVar x -> Exec s xs (x ': xs) a -> MVar x -> Exec s (x ': xs) ks a
              -> Reader (Ctx s a) (Γ s (x ': xs) ks a -> QST s (Maybe a))
execChainInit σ l μ k =
  do asks $! \ctx γ@(Γ xs ks o _ _) -> [||
       do let !(# x, xs' #) = popX $$xs
          ref <- newΣ x
          $$(let handler = [||\hs o# cs ->
                  let !(# c, cs' #) = popC cs
                  in if c == (I# o#) then
                       do y <- readΣ ref
                          $$(run k (γ {xs = [|| pokeX y $$xs ||],
                                       o = [||I# o#||],
                                       hs = [||hs||],
                                       cs = [||cs'||]}) ctx)
                     else raise hs cs' (I# o#)
                   ||]
             in setupHandlerΓ γ handler (\γ' -> [||
              -- NOTE: Only the offset and the check stack can change between interations of a chainPre
              do let I# o# = $$o
                 let loop o# !cs =
                       $$(run l (Γ [||xs'||] [||noreturn||] [||I# o#||] (hs γ') [||cs||])
                                (insertM μ [||AbsExec (\_ _ o# _ (!cs) -> loop o# cs)||] (insertΣ σ [||ref||] ctx)))
                 loop o# $$(cs γ')
            ||]))
      ||]

preludeString :: String -> Char -> Γ s xs ks a -> Ctx s a -> String -> TExpQ String
preludeString name dir γ ctx ends = [|| concat [$$prelude, $$eof, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    offset       = o γ
    indent       = replicate (debugLevel ctx * 2) ' '
    start        = [|| max ($$offset - 5) 0 ||]
    end          = [|| min ($$offset + 6) $$(size (input ctx)) ||]
    sub          = [|| [$$(charAt (input ctx)) i | i <- [$$start..($$end - 1)]] ||]
    inputTrace   = [|| let replace '\n' = color Green "↙"
                           replace ' '  = color White "·"
                           replace c    = return c
                       in concatMap replace $$sub ||]
    eof          = [|| if $$end == $$(size (input ctx)) then $$inputTrace ++ color Red "•" else $$inputTrace ||]
    prelude      = [|| concat [indent, dir : name, dir : " (", show $$offset, "): "] ||]
    caretSpace   = [|| replicate (length $$prelude + $$offset - $$start) ' ' ||]

execLogEnter :: String -> Exec s xs ks a -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execLogEnter name k =
  do asks $! \ctx γ ->
      let handler = [||\hs o# cs -> trace $$(preludeString name '<' (γ {o = [||I# o#||]}) ctx (color Red " Fail")) (raise hs cs (I# o#)) ||]
      in (setupHandlerΓ γ handler (\γ' -> [|| trace $$(preludeString name '>' γ ctx "") $$(run k γ' (debugUp ctx))||]))

execLogExit :: String -> Exec s xs ks a -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
execLogExit name k = asks $! \ctx γ -> [|| trace $$(preludeString name '<' γ (debugDown ctx) (color Green " Good")) $$(run k γ (debugDown ctx)) ||]

setupHandlerΓ :: Γ s xs ks a -> TExpQ (H s a -> O# -> C -> ST s (Maybe a)) ->
                                (Γ s xs ks a -> QST s (Maybe a)) -> QST s (Maybe a)
setupHandlerΓ γ !h !k = setupHandler (hs γ) (cs γ) (o γ) h (\hs cs -> k (γ {hs = hs, cs = cs}))

setupJoinPoint :: Maybe (ΦDecl (Exec s) x xs ks a) -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a)) -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
setupJoinPoint Nothing mx = mx
setupJoinPoint (Just (φ, (Exec k))) mx =
  do ctx <- ask
     fmap (\mk γ -> [||
       let join x (o# :: O#) = $$(mk (γ {xs = [||pushX x $$(xs γ)||], o = [||I# o#||]}))
       in $$(run (Exec mx) γ (insertΦ φ [||join||] ctx))
       ||]) k

inputSizeCheck :: Maybe Int -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a)) -> Reader (Ctx s a) (Γ s xs ks a -> QST s (Maybe a))
inputSizeCheck Nothing p = p
inputSizeCheck (Just n) p =
  do skip <- asks skipBounds
     mp <- local (addConstCount 1) p
     if skip then return $! mp
     else fmap (\ctx γ -> [|| 
       if $$(size (input ctx)) > (n + $$(o γ) - 1) then $$(mp γ)
       else $$(raiseΓ γ)
      ||]) ask

raiseΓ :: Γ s xs ks a -> QST s (Maybe a)
raiseΓ γ = [|| raise $$(hs γ) $$(cs γ) $$(o γ) ||]

suspend :: (Γ s (x ': xs) ks a -> QST s (Maybe a)) -> Γ s xs ks a -> QK s (x ': xs) a
suspend m γ = [|| \xs o# -> $$(m (γ {xs = [||xs||], o = [||I# o#||]})) ||]

askM :: MonadReader (Ctx s a) m => MVar x -> m (QAbsExec s a x)
askM μ = asks (((DMap.! μ) . μs))

askΣ :: MonadReader (Ctx s a) m => ΣVar x -> m (QSTRef s x)
askΣ σ = asks ((DMap.! σ) . σs)

askΦ :: MonadReader (Ctx s a) m => ΦVar x -> m (QJoin s a x)
askΦ φ = asks ((DMap.! φ) . φs)

instance IFunctor3 M where
  imap3 f Halt                           = Halt
  imap3 f Ret                            = Ret
  imap3 f (Push x k)                     = Push x (f k)
  imap3 f (Pop k)                        = Pop (f k)
  imap3 f (Lift2 g k)                    = Lift2 g (f k)
  imap3 f (Sat g k)                      = Sat g (f k)
  imap3 f (Call μ k)                     = Call μ (f k)
  imap3 f (Jump μ)                       = Jump μ
  imap3 f Empt                           = Empt
  imap3 f (Commit exit k)                = Commit exit (f k)
  imap3 f (SoftFork n p q (Just (φ, k))) = SoftFork n (f p) (f q) (Just (φ, f k))
  imap3 f (SoftFork n p q Nothing)       = SoftFork n (f p) (f q) Nothing
  imap3 f (HardFork p q (Just (φ, k)))   = HardFork (f p) (f q) (Just (φ, f k))
  imap3 f (HardFork p q Nothing)         = HardFork (f p) (f q) Nothing
  imap3 f (Join φ)                       = Join φ
  imap3 f (Attempt n k)                  = Attempt n (f k)
  imap3 f (Look k)                       = Look (f k)
  imap3 f (NegLook m k)                  = NegLook (f m) (f k)
  imap3 f (Restore k)                    = Restore (f k)
  imap3 f (Case p q)                     = Case (f p) (f q)
  imap3 f (Choices fs ks def)            = Choices fs (map f ks) (f def)
  imap3 f (ChainIter σ μ)                = ChainIter σ μ
  imap3 f (ChainInit σ l μ k)            = ChainInit σ (f l) μ (f k)
  imap3 f (LogEnter name k)              = LogEnter name (f k)
  imap3 f (LogExit name k)               = LogExit name (f k)

instance Show (Machine a) where show = show . getMachine
instance Show (Free3 M f xs ks a) where
  show = getConst3 . fold3 (const (Const3 "")) (Const3 . alg) where
    alg :: forall i j k. M (Const3 String) i j k -> String
    alg Halt                                  = "Halt"
    alg Ret                                   = "Ret"
    alg (Call μ k)                            = "(Call " ++ show μ ++ " " ++ getConst3 k ++ ")"
    alg (Jump μ)                              = "(Jump " ++ show μ ++ ")"
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
    alg (Choices _ ks def)                    = "(Choices " ++ show (map getConst3 ks) ++ " " ++ getConst3 def ++ ")"
    alg (ChainIter σ μ)                       = "(ChainIter " ++ show σ ++ " " ++ show μ ++ ")"
    alg (ChainInit σ m μ k)                   = "{ChainInit " ++ show σ ++ " " ++ show μ ++ " " ++ getConst3 m ++ " " ++ getConst3 k ++ "}"
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