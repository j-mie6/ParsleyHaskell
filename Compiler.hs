{-# LANGUAGE GADTs,
             DataKinds,
             RecursiveDo,
             RankNTypes,
             BangPatterns,
             MagicHash,
             FlexibleContexts,
             FlexibleInstances,
             MultiParamTypeClasses,
             UndecidableInstances,
             AllowAmbiguousTypes #-}
module Compiler(compile) where

import Prelude hiding (pred)
import ParserAST                  (ParserF(..), Parser(..), prettyParserOrigin)
import Optimiser                  (optimise)
import Analyser                   (terminationAnalysis)
import CodeGenerator              (codeGen, halt, ret)
import Machine                    (Machine(..), IMVar, IΣVar, MVar(..), LetBinding(..))
import Indexed                    (Free(Op), Void1, fold', absurd)
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
import GHC.Prim                   (StableName#, unsafeCoerce#)
import GHC.Exts                   (Int(..))
import GHC.Stack
import Debug.Trace                (trace)
import qualified Data.HashMap.Strict as HashMap ((!), lookup, insert, empty, insertWith, foldrWithKey)
import qualified Data.HashSet        as HashSet (member, insert, empty, union)
import qualified Data.Dependent.Map  as DMap    ((!), empty, insert, foldrWithKey, size)

compile :: Parser a -> (Machine o a, DMap MVar (LetBinding o a), [IMVar])
compile (Parser p) =
  let !(p', μs, maxV, topo) = preprocess p
      !(m, maxΣ) = codeGen (terminationAnalysis p') halt (maxV + 1) 0
      !ms = compileLets μs (maxV + 1) maxΣ
  in trace ("COMPILING NEW PARSER WITH " ++ show ((DMap.size ms)) ++ " LET BINDINGS") $ (Machine m, ms, topo)

compileLets :: DMap MVar (Free ParserF Void1) -> IMVar -> IΣVar -> DMap MVar (LetBinding o a)
compileLets μs maxV maxΣ = let (ms, _) = DMap.foldrWithKey compileLet (DMap.empty, maxΣ) μs in ms
  where
    compileLet :: MVar x -> Free ParserF Void1 x -> (DMap MVar (LetBinding o a), IΣVar) -> (DMap MVar (LetBinding o a), IΣVar)
    compileLet (MVar μ) p (ms, maxΣ) =
      let (m, maxΣ') = codeGen p ret maxV (maxΣ + 1)
      in (DMap.insert (MVar μ) (LetBinding m) ms, maxΣ')

preprocess :: Free ParserF Void1 a -> (Free ParserF Void1 a, DMap MVar (Free ParserF Void1), IMVar, [IMVar])
preprocess p = unsafePerformIO $ do
  (lets, recs, topo) <- findLets p
  letInsertion lets recs topo p

data StableParserName = forall a. StableParserName (StableName# (Free ParserF Void1 a))
data LetFinderState = LetFinderState { preds  :: HashMap StableParserName Int
                                     , recs   :: HashSet StableParserName
                                     , before :: HashSet StableParserName
                                     , topo   :: [StableParserName] }
type LetFinderCtx   = HashSet StableParserName
newtype LetFinder a = LetFinder { runLetFinder :: StateT LetFinderState (ReaderT LetFinderCtx IO) () }

reverseFilter :: (a -> Bool) -> [a] -> [a]
reverseFilter p = foldl' (\xs x -> if p x then x : xs else xs) []

findLets :: Free ParserF Void1 a -> IO (HashSet StableParserName, HashSet StableParserName, [StableParserName])
findLets p = do
  let state = LetFinderState HashMap.empty HashSet.empty HashSet.empty []
  let ctx = HashSet.empty
  LetFinderState preds recs _ topo <-runReaderT (execStateT (runLetFinder (fold' absurd findLetsAlg p)) state) ctx
  let lets = HashMap.foldrWithKey (\k n ls -> if n > 1 then HashSet.insert k ls else ls) HashSet.empty preds
  let letBound = flip HashSet.member (HashSet.union lets recs)
  return $! (lets, recs, reverseFilter letBound topo)

findLetsAlg :: Free ParserF Void1 a -> ParserF LetFinder a -> LetFinder a
findLetsAlg orig p = LetFinder $ do
  name <- makeStableParserName orig
  addPred name
  ifSeen name
    (do addRec name)
    (ifNotProcessedBefore name
      (do addName name (case p of
            pf :<*>: px     -> do runLetFinder pf; runLetFinder px
            p :*>: q        -> do runLetFinder p;  runLetFinder q
            p :<*: q        -> do runLetFinder p;  runLetFinder q
            p :<|>: q       -> do runLetFinder p;  runLetFinder q
            Try n p         -> do runLetFinder p
            LookAhead p     -> do runLetFinder p
            NotFollowedBy p -> do runLetFinder p
            Branch b p q    -> do runLetFinder b;  runLetFinder p; runLetFinder q
            Match p _ qs d  -> do runLetFinder p;  forM_ qs runLetFinder; runLetFinder d
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
                                , DMap MVar (Free ParserF Void1)) IO)
                        (Free ParserF Void1 a)
    }
letInsertion :: HashSet StableParserName -> HashSet StableParserName -> [StableParserName] -> Free ParserF Void1 a -> IO (Free ParserF Void1 a, DMap MVar (Free ParserF Void1), IMVar, [IMVar])
letInsertion lets recs topo p =
  do let m = fold' absurd alg p
     ((p', μMax), (vs, μs)) <- runStateT (runFreshT (runLetInserter m) 0) (HashMap.empty, DMap.empty)
     return $! (p', μs, μMax, map (vs HashMap.!) topo)
  where
    alg :: Free ParserF Void1 a -> ParserF LetInserter a -> LetInserter a
    alg orig p = LetInserter $ do
      trace (prettyParserOrigin p) $ return ()
      name <- makeStableParserName orig
      (vs, μs) <- get
      let bound = HashSet.member name lets
      let recu  = HashSet.member name recs
      if bound || recu then case HashMap.lookup name vs of
        Just v  -> let μ = MVar v in return $! Op (Let recu μ (μs DMap.! μ))
        Nothing -> mdo
          v <- newVar
          let μ = MVar v
          put (HashMap.insert name v vs, DMap.insert μ p' μs)
          p' <- runLetInserter (postprocess p)
          return $! Op (Let recu μ p')
      else do runLetInserter (postprocess p)

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
postprocess (Match p fs qs d) = LetInserter (fmap optimise (liftA4 Match (runLetInserter p) (return fs) (traverse runLetInserter qs) (runLetInserter d)))
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

makeStableParserName :: MonadIO m => Free ParserF Void1 a -> m StableParserName
-- Force evaluation of p to ensure that the stableName is correct first time
makeStableParserName !p =
  do !(StableName name) <- liftIO (makeStableName p)
     return $! StableParserName name

showM :: Parser a -> String
showM = show . (\(x, _, _) -> x) . compile

liftA4 :: Applicative f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftA4 f u v w x = liftA3 f u v w <*> x

instance Eq StableParserName where
  (StableParserName n) == (StableParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable StableParserName where
  hash (StableParserName n) = hashStableName (StableName n)
  hashWithSalt salt (StableParserName n) = hashWithSalt salt (StableName n)

-- There is great evil in this world, and I'm probably responsible for half of it
instance Show StableParserName where show (StableParserName n) = show (I# (unsafeCoerce# n))