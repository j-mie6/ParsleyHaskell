{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, UndecidableInstances, AllowAmbiguousTypes #-}
module Compiler(compile) where

import Prelude hiding (pred)
import ParserAST                  (ParserF(..), Parser(..))
import Optimiser                  (optimise)
import Analyser                   (terminationAnalysis)
import CodeGenerator              (codeGen, halt, ret)
import Machine                    (Machine(..), ΣVars, IMVar, IΣVar, MVar(..), letBind, LetBinding)
import Indexed                    (Free(Op), Void, fold', absurd)
import Control.Applicative        (liftA2, liftA3)
import Control.Monad              (forM_)
import Control.Monad.Reader       (ReaderT, runReaderT, local, ask, asks, MonadReader)
import Control.Monad.State.Strict (StateT, get, gets, put, runStateT, execStateT, modify', MonadState)
import Data.List                  (foldl')
import Fresh                      (HFreshT, newVar, newScope, runFreshT)
import Control.Monad.Trans        (liftIO, MonadIO)
import System.IO.Unsafe           (unsafePerformIO)
import GHC.StableName             (StableName(..), makeStableName, hashStableName, eqStableName)
import Data.Hashable              (Hashable, hashWithSalt, hash)
import Data.HashMap.Strict        (HashMap)
import Data.HashSet               (HashSet)
import Data.Dependent.Map         (DMap)
import GHC.Prim                   (StableName#)
import Debug.Trace                (traceShow)
import qualified Data.HashMap.Strict as HashMap ((!), lookup, insert, empty, insertWith, foldrWithKey)
import qualified Data.HashSet        as HashSet (member, insert, empty, union)
import qualified Data.Dependent.Map  as DMap    ((!), empty, insert, foldrWithKey)
import Data.GADT.Show (GShow(..))
import Data.Dependent.Sum (ShowTag(..))
import Debug.Trace (traceShow)

compile :: Parser a -> (Machine a, DMap MVar (LetBinding a), ΣVars, [IMVar])
compile (Parser p) = 
  let !(p', μs, maxV, topo) = preprocess p
      !(m, σs, maxΣ) = codeGen ({-terminationAnalysis -}p') halt (maxV + 1) 0
      !(ms, σs') = compileLets μs σs (maxV + 1) maxΣ
  in traceShow ms (Machine m, ms, σs', topo)

compileLets :: DMap MVar (Free ParserF Void) -> ΣVars -> IMVar -> IΣVar -> (DMap MVar (LetBinding a), ΣVars)
compileLets μs σs maxV maxΣ = let (ms, σs', _) = DMap.foldrWithKey compileLet (DMap.empty, σs, maxΣ) μs in (ms, σs')
  where
    compileLet :: MVar x -> Free ParserF Void x -> (DMap MVar (LetBinding a), ΣVars, IΣVar) -> (DMap MVar (LetBinding a), ΣVars, IΣVar)
    compileLet (MVar μ) p (ms, σs, maxΣ) =
      let (m, σs', maxΣ') = codeGen p ret maxV (maxΣ + 1)
      in (DMap.insert (MVar μ) (letBind m) ms, σs ++ σs', maxΣ')

preprocess :: Free ParserF Void a -> (Free ParserF Void a, DMap MVar (Free ParserF Void), IMVar, [IMVar])
preprocess p = let (lets, recs, topo) = findLets p in letInsertion lets recs topo p

data StableParserName = forall a. StableParserName (StableName# (Free ParserF Void a))
data LetFinderState = LetFinderState { preds  :: HashMap StableParserName Int
                                     , recs   :: HashSet StableParserName
                                     , before :: HashSet StableParserName
                                     , topo   :: [StableParserName] }
type LetFinderCtx   = HashSet StableParserName
newtype LetFinder a = LetFinder { runLetFinder :: StateT LetFinderState (ReaderT LetFinderCtx IO) () }

reverseFilter :: (a -> Bool) -> [a] -> [a]
reverseFilter p = foldl' (\xs x -> if p x then x : xs else xs) []

findLets :: Free ParserF Void a -> (HashSet StableParserName, HashSet StableParserName, [StableParserName])
findLets p = (lets, recs, reverseFilter letBound topo) 
  where
    letBound = flip HashSet.member (HashSet.union lets recs)
    state = LetFinderState HashMap.empty HashSet.empty HashSet.empty []
    ctx = HashSet.empty
    LetFinderState preds recs _ topo = unsafePerformIO (runReaderT (execStateT (runLetFinder (fold' absurd findLetsAlg p)) state) ctx)
    lets = HashMap.foldrWithKey (\k n ls -> if n > 1 then HashSet.insert k ls else ls) HashSet.empty preds

findLetsAlg :: Free ParserF Void a -> ParserF LetFinder a -> LetFinder a
findLetsAlg p q = LetFinder $ do 
  name <- makeStableParserName p
  addPred name
  ifSeen name 
    (do addRec name)
    (ifNotProcessedBefore name
      (do addName name (case q of
            pf :<*>: px     -> do runLetFinder pf; runLetFinder px
            p :*>: q        -> do runLetFinder p;  runLetFinder q
            p :<*: q        -> do runLetFinder p;  runLetFinder q
            p :<|>: q       -> do runLetFinder p;  runLetFinder q
            Try n p         -> do runLetFinder p
            LookAhead p     -> do runLetFinder p
            NotFollowedBy p -> do runLetFinder p
            Branch b p q    -> do runLetFinder b;  runLetFinder p; runLetFinder q
            Match p _ qs    -> do runLetFinder p;  forM_ qs runLetFinder
            ChainPre op p   -> do runLetFinder op; runLetFinder p
            ChainPost p op  -> do runLetFinder p;  runLetFinder op
            Debug _ p       -> do runLetFinder p
            _               -> do return ())
          doNotProcessAgain name
          addToTopology name))

newtype LetInserter a =
  LetInserter {
      runLetInserter :: HFreshT IMVar 
                        (StateT ( HashMap StableParserName IMVar
                                , DMap MVar (Free ParserF Void)) IO) 
                        (Free ParserF Void a)
    }
letInsertion :: HashSet StableParserName -> HashSet StableParserName -> [StableParserName] -> Free ParserF Void a -> (Free ParserF Void a, DMap MVar (Free ParserF Void), IMVar, [IMVar])
letInsertion lets recs topo p = (p', μs, μMax, map (vs HashMap.!) topo)
  where
    m = fold' absurd alg p
    ((p', μMax), (vs, μs)) = unsafePerformIO (runStateT (runFreshT (runLetInserter m) 0) (HashMap.empty, DMap.empty))
    alg :: Free ParserF Void a -> ParserF LetInserter a -> LetInserter a
    alg p q = LetInserter $ do
      name <- makeStableParserName p
      (vs, μs) <- get
      if | HashSet.member name recs ->
             case HashMap.lookup name vs of
               Just v  -> let μ = MVar v in return $! Op (Let True μ (μs DMap.! μ))
               Nothing -> mdo
                 v <- newVar
                 let μ = MVar v
                 put (HashMap.insert name v vs, DMap.insert μ q' μs)
                 q' <- runLetInserter (postprocess q)
                 return $! Op (Let True μ q')
         | HashSet.member name lets ->
             case HashMap.lookup name vs of
               Just v  -> let μ = MVar v in return $! optimise (Let False μ (μs DMap.! μ))
               Nothing -> do -- no mdo here, let bindings are not recursive!
                 v <- newVar
                 let μ = MVar v
                 q' <- runLetInserter (postprocess q)
                 put (HashMap.insert name v vs, DMap.insert μ q' μs)
                 return $! optimise (Let False μ q')
         | otherwise -> do runLetInserter (postprocess q)

postprocess :: ParserF LetInserter a -> LetInserter a
postprocess (pf :<*>: px)     = LetInserter (fmap optimise (liftA2 (:<*>:) (runLetInserter pf) (runLetInserter px)))
postprocess (p :*>: q)        = LetInserter (fmap optimise (liftA2 (:*>:)  (runLetInserter p)  (runLetInserter q)))
postprocess (p :<*: q)        = LetInserter (fmap optimise (liftA2 (:<*:)  (runLetInserter p)  (runLetInserter q)))
postprocess (p :<|>: q)       = LetInserter (fmap optimise (liftA2 (:<|>:) (runLetInserter p)  (runLetInserter q)))
postprocess Empty             = LetInserter (return        (Op Empty))
postprocess (Try n p)         = LetInserter (fmap optimise (fmap (Try n) (runLetInserter p)))
postprocess (LookAhead p)     = LetInserter (fmap optimise (fmap LookAhead (runLetInserter p)))
postprocess (NotFollowedBy p) = LetInserter (fmap optimise (fmap NotFollowedBy (runLetInserter p)))
postprocess (Branch b p q)    = LetInserter (fmap optimise (liftA3 Branch (runLetInserter b) (runLetInserter p) (runLetInserter q)))
postprocess (Match p fs qs)   = LetInserter (fmap optimise (liftA3 Match (runLetInserter p) (return fs) (traverse runLetInserter qs)))
postprocess (ChainPre op p)   = LetInserter (fmap Op       (liftA2 ChainPre (runLetInserter op) (runLetInserter p)))
postprocess (ChainPost p op)  = LetInserter (fmap Op       (liftA2 ChainPost (runLetInserter p) (runLetInserter op)))
postprocess (Debug name p)    = LetInserter (fmap Op       (fmap (Debug name) (runLetInserter p)))
postprocess (Pure x)          = LetInserter (return        (Op (Pure x)))
postprocess (Satisfy f)       = LetInserter (return        (Op (Satisfy f)))

getPreds :: MonadState LetFinderState m => m (HashMap StableParserName Int)
getPreds = gets preds

getRecs :: MonadState LetFinderState m => m (HashSet StableParserName)
getRecs = gets recs

getBefore :: MonadState LetFinderState m => m (HashSet StableParserName)
getBefore = gets before

modifyPreds :: MonadState LetFinderState m => (HashMap StableParserName Int -> HashMap StableParserName Int) -> m ()
modifyPreds f = modify' (\st -> st {preds = f (preds st)})

modifyRecs :: MonadState LetFinderState m => (HashSet StableParserName -> HashSet StableParserName) -> m ()
modifyRecs f = modify' (\st -> st {recs = f (recs st)})

modifyBefore :: MonadState LetFinderState m => (HashSet StableParserName -> HashSet StableParserName) -> m ()
modifyBefore f = modify' (\st -> st {before = f (before st)})

modifyTopo :: MonadState LetFinderState m => ([StableParserName] -> [StableParserName]) -> m ()
modifyTopo f = modify' (\st -> st {topo = f (topo st)})

addPred :: MonadState LetFinderState m => StableParserName -> m ()
addPred k = modifyPreds (HashMap.insertWith (+) k 1)

addRec :: MonadState LetFinderState m => StableParserName -> m ()
addRec = modifyRecs . HashSet.insert

ifSeen :: MonadReader LetFinderCtx m => StableParserName -> m a -> m a -> m a
ifSeen x yes no = do !seen <- ask; if HashSet.member x seen then yes else no

ifNotProcessedBefore :: MonadState LetFinderState m => StableParserName -> m () -> m ()
ifNotProcessedBefore x m = do !before <- getBefore; if HashSet.member x before then return () else m

doNotProcessAgain :: MonadState LetFinderState m => StableParserName -> m ()
doNotProcessAgain x = modifyBefore (HashSet.insert x)

addToTopology :: MonadState LetFinderState m => StableParserName -> m ()
addToTopology x = modifyTopo (x:)

addName :: MonadReader LetFinderCtx m => StableParserName -> m b -> m b
addName x = local (HashSet.insert x)

makeStableParserName :: MonadIO m => Free ParserF Void a -> m StableParserName
-- Force evaluation of p to ensure that the stableName is correct first time
makeStableParserName !p =
  do !(StableName name) <- liftIO (makeStableName p)
     return $! StableParserName name

showM :: Parser a -> String
showM = show . (\(x, _, _, _) -> x) . compile

instance Eq StableParserName where 
  (StableParserName n) == (StableParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable StableParserName where
  hash (StableParserName n) = hashStableName (StableName n)
  hashWithSalt salt (StableParserName n) = hashWithSalt salt (StableName n)

instance Show (Free ParserF Void a) => ShowTag MVar (Free ParserF Void) where showTaggedPrec m = showsPrec
instance Show (LetBinding a x) => ShowTag MVar (LetBinding a) where showTaggedPrec m = showsPrec