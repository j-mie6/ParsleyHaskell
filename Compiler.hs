{-# LANGUAGE GADTs,
             DataKinds,
             RecursiveDo,
             RankNTypes,
             BangPatterns,
             MagicHash,
             FlexibleContexts,
             MultiWayIf,
             FlexibleInstances, 
             MultiParamTypeClasses, 
             UndecidableInstances, 
             AllowAmbiguousTypes #-}
module Compiler(compile) where

import Prelude hiding (pred)
import ParserAST                  (ParserF(..), Parser(..))
import Optimiser                  (optimise)
import Analyser                   (terminationAnalysis)
import CodeGenerator              (codeGen, halt, ret)
import Machine                    (Machine(..), IMVar, IΣVar, MVar(..), LetBinding(..))
import Indexed                    (Free(Op), Void1, fold', absurd, Tag(..))
import Control.Applicative        (liftA, liftA2, liftA3)
import Control.Monad              (forM, forM_)
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
import Debug.Trace                (trace)
import qualified Data.HashMap.Strict as HashMap ((!), lookup, insert, empty, insertWith, foldrWithKey)
import qualified Data.HashSet        as HashSet (member, insert, empty, union)
import qualified Data.Dependent.Map  as DMap    ((!), empty, insert, foldrWithKey, size)

compile :: Parser a -> (Machine o a, DMap MVar (LetBinding o a), [IMVar])
compile (Parser p) = 
  let !(p', μs, maxV, topo) = preprocess p
      !(m, maxΣ) = codeGen ({-terminationAnalysis -}p') halt (maxV + 1) 0
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
preprocess p = unsafePerformIO $
  do tagged <- tagParser p
     (lets, recs, topo) <- findLets p 
     letInsertion lets recs topo p

data ParserName = forall a. ParserName (StableName# (Free ParserF Void1 a))

newtype Namer a = Namer { runNamer :: Free (Tag ParserName ParserF) Void1 a }

tagParser :: Free ParserF Void1 a -> IO (Free (Tag ParserName ParserF) Void1 a)
tagParser = return . runNamer . fold' absurd tagAlg

tagAlg :: Free ParserF Void1 a -> ParserF Namer a -> Namer a
tagAlg p q = Namer $ unsafePerformIO $ do
  name <- makeParserName p
  let mkTag = Op . Tag name
  return $ case q of
    pf :<*>: px     -> mkTag (runNamer pf :<*>: runNamer px)
    p :*>: q        -> mkTag (runNamer p :*>: runNamer q)
    p :<*: q        -> mkTag (runNamer p :<*: runNamer q)
    p :<|>: q       -> mkTag (runNamer p :<|>: runNamer q)
    Try n p         -> mkTag (Try n (runNamer p))
    LookAhead p     -> mkTag (LookAhead (runNamer p))
    NotFollowedBy p -> mkTag (NotFollowedBy (runNamer p))
    Branch b p q    -> mkTag (Branch (runNamer b) (runNamer p) (runNamer q))
    Match p fs qs d -> mkTag (Match (runNamer p) fs (map runNamer qs) (runNamer d))
    ChainPre op p   -> mkTag (ChainPre (runNamer op) (runNamer p))
    ChainPost p op  -> mkTag (ChainPost (runNamer p) (runNamer op))
    Debug name p    -> mkTag (Debug name (runNamer p))
    Pure x          -> mkTag (Pure x)
    Empty           -> mkTag Empty
    _               -> undefined

data LetFinderState = LetFinderState { preds  :: HashMap ParserName Int
                                     , recs   :: HashSet ParserName
                                     , before :: HashSet ParserName
                                     , topo   :: [ParserName] }
type LetFinderCtx   = HashSet ParserName
newtype LetFinder a = LetFinder { runLetFinder :: StateT LetFinderState (ReaderT LetFinderCtx IO) () }

reverseFilter :: (a -> Bool) -> [a] -> [a]
reverseFilter p = foldl' (\xs x -> if p x then x : xs else xs) []

findLets :: Free ParserF Void1 a -> IO (HashSet ParserName, HashSet ParserName, [ParserName])
findLets p = return (lets, recs, reverseFilter letBound topo) 
  where
    letBound = flip HashSet.member (HashSet.union lets recs)
    state = LetFinderState HashMap.empty HashSet.empty HashSet.empty []
    ctx = HashSet.empty
    LetFinderState preds recs _ topo = unsafePerformIO (runReaderT (execStateT (runLetFinder (fold' absurd findLetsAlg p)) state) ctx)
    lets = HashMap.foldrWithKey (\k n ls -> if n > 1 then HashSet.insert k ls else ls) HashSet.empty preds

findLetsAlg :: Free ParserF Void1 a -> ParserF LetFinder a -> LetFinder a
findLetsAlg p q = LetFinder $ do 
  name <- makeParserName p
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
                        (StateT ( HashMap ParserName IMVar
                                , DMap MVar (Free ParserF Void1)) IO) 
                        (Free ParserF Void1 a)
    }
letInsertion :: HashSet ParserName -> HashSet ParserName -> [ParserName] -> Free ParserF Void1 a -> IO (Free ParserF Void1 a, DMap MVar (Free ParserF Void1), IMVar, [IMVar])
letInsertion lets recs topo p = return (p', μs, μMax, map (vs HashMap.!) topo)
  where
    m = fold' absurd alg p
    ((p', μMax), (vs, μs)) = unsafePerformIO (runStateT (runFreshT (runLetInserter m) 0) (HashMap.empty, DMap.empty))
    alg :: Free ParserF Void1 a -> ParserF LetInserter a -> LetInserter a
    alg p q = LetInserter $ do
      name <- makeParserName p
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
               Nothing -> mdo -- no mdo here, let bindings are not recursive! (well, actually, I want to do the put before the recursion soooo....)
                 v <- newVar
                 let μ = MVar v
                 put (HashMap.insert name v vs, DMap.insert μ q' μs)
                 q' <- runLetInserter (postprocess q)
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
postprocess (Match p fs qs d) = LetInserter (fmap optimise (liftA4 Match (runLetInserter p) (return fs) (traverse runLetInserter qs) (runLetInserter d)))
postprocess (ChainPre op p)   = LetInserter (fmap Op       (liftA2 ChainPre (runLetInserter op) (runLetInserter p)))
postprocess (ChainPost p op)  = LetInserter (fmap Op       (liftA2 ChainPost (runLetInserter p) (runLetInserter op)))
postprocess (Debug name p)    = LetInserter (fmap Op       (fmap (Debug name) (runLetInserter p)))
postprocess (Pure x)          = LetInserter (return        (Op (Pure x)))
postprocess (Satisfy f)       = LetInserter (return        (Op (Satisfy f)))

getPreds :: MonadState LetFinderState m => m (HashMap ParserName Int)
getPreds = gets preds

getRecs :: MonadState LetFinderState m => m (HashSet ParserName)
getRecs = gets recs

getBefore :: MonadState LetFinderState m => m (HashSet ParserName)
getBefore = gets before

modifyPreds :: MonadState LetFinderState m => (HashMap ParserName Int -> HashMap ParserName Int) -> m ()
modifyPreds f = modify' (\st -> st {preds = f (preds st)})

modifyRecs :: MonadState LetFinderState m => (HashSet ParserName -> HashSet ParserName) -> m ()
modifyRecs f = modify' (\st -> st {recs = f (recs st)})

modifyBefore :: MonadState LetFinderState m => (HashSet ParserName -> HashSet ParserName) -> m ()
modifyBefore f = modify' (\st -> st {before = f (before st)})

modifyTopo :: MonadState LetFinderState m => ([ParserName] -> [ParserName]) -> m ()
modifyTopo f = modify' (\st -> st {topo = f (topo st)})

addPred :: MonadState LetFinderState m => ParserName -> m ()
addPred k = modifyPreds (HashMap.insertWith (+) k 1)

addRec :: MonadState LetFinderState m => ParserName -> m ()
addRec = modifyRecs . HashSet.insert

ifSeen :: MonadReader LetFinderCtx m => ParserName -> m a -> m a -> m a
ifSeen x yes no = do !seen <- ask; if HashSet.member x seen then yes else no

ifNotProcessedBefore :: MonadState LetFinderState m => ParserName -> m () -> m ()
ifNotProcessedBefore x m = do !before <- getBefore; if HashSet.member x before then return () else m

doNotProcessAgain :: MonadState LetFinderState m => ParserName -> m ()
doNotProcessAgain x = modifyBefore (HashSet.insert x)

addToTopology :: MonadState LetFinderState m => ParserName -> m ()
addToTopology x = modifyTopo (x:)

addName :: MonadReader LetFinderCtx m => ParserName -> m b -> m b
addName x = local (HashSet.insert x)

makeParserName :: MonadIO m => Free ParserF Void1 a -> m ParserName
-- Force evaluation of p to ensure that the stableName is correct first time
makeParserName !p =
  do !(StableName name) <- liftIO (makeStableName p)
     return $! ParserName name

showM :: Parser a -> String
showM = show . (\(x, _, _) -> x) . compile

liftA4 :: Applicative f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftA4 f u v w x = liftA3 f u v w <*> x

instance Eq ParserName where 
  (ParserName n) == (ParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable ParserName where
  hash (ParserName n) = hashStableName (StableName n)
  hashWithSalt salt (ParserName n) = hashWithSalt salt (StableName n)

-- There is great evil in this world, and I'm probably responsible for half of it
instance Show ParserName where show (ParserName n) = show (I# (unsafeCoerce# n))