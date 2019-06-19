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

import ParserAST                  (ParserF(..), Parser(..))
import Optimiser                  (optimise)
import Analyser                   (terminationAnalysis)
import CodeGenerator              (codeGen)
import Machine                    (Machine(..), ΣVars, IMVar, MVar(..))
import Indexed                    (Free(Op), Void, fold', absurd)
import Control.Applicative        (liftA2, liftA3)
import Control.Monad              (forM_)
import Control.Monad.Reader       (ReaderT, runReaderT, local, asks, MonadReader)
import Control.Monad.State.Strict (StateT, get, gets, put, runStateT, execStateT, modify', MonadState)
import Data.Tuple.Extra           (first, second)
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
import qualified Data.HashMap.Strict as HashMap (lookup, insert, empty, insertWith, foldrWithKey)
import qualified Data.HashSet        as HashSet (member, insert, empty, singleton, union, size)
import qualified Data.Dependent.Map  as DMap    ((!), empty, insert)
import Data.GADT.Show (GShow(..))
import Data.Dependent.Sum (ShowTag(..))

compile :: Parser a -> (Machine a, ΣVars)
compile (Parser p) = 
  let (p', maxV) = preprocess p
      (m, σs) = codeGen ({-terminationAnalysis -}p') (maxV + 1) in (Machine m, σs)

preprocess :: Free ParserF Void a -> (Free ParserF Void a, IMVar)
preprocess p =
  let (lets, recs) = findLets p
      (p', μs, maxV) = letInsertion lets recs p
  in traceShow μs (p', maxV)

data StableParserName = forall a. StableParserName (StableName# (Free ParserF Void a))
newtype LetFinder a =
  LetFinder {
    runLetFinder :: StateT ( HashMap StableParserName (HashSet StableParserName)
                           , HashSet StableParserName)
                    (ReaderT (Maybe StableParserName, HashSet StableParserName) IO)
                    () 
    }

findLets :: Free ParserF Void a -> (HashSet StableParserName, HashSet StableParserName)
findLets p = first lets (unsafePerformIO (runReaderT (execStateT (runLetFinder (fold' absurd findLetsAlg p)) (HashMap.empty, HashSet.empty)) (Nothing, HashSet.empty)))
  where
    lets = HashMap.foldrWithKey (\k vs ls -> if HashSet.size vs > 1 then HashSet.insert k ls else ls) HashSet.empty

findLetsAlg :: Free ParserF Void a -> ParserF LetFinder a -> LetFinder a
findLetsAlg p q = LetFinder $ do 
  name <- makeStableParserName p
  pred <- askPred
  maybe (return ()) (addPred name) pred
  ifSeen name 
    (do addRec name)
    (do addName name (localPred (Just name) (case q of
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
          _               -> do return ())))

newtype LetInserter a =
  LetInserter {
      runLetInserter :: HFreshT IMVar 
                        (StateT ( HashMap StableParserName IMVar
                                , DMap MVar (Free ParserF Void)) IO) 
                        (Free ParserF Void a)
    }
letInsertion :: HashSet StableParserName -> HashSet StableParserName -> Free ParserF Void a -> (Free ParserF Void a, DMap MVar (Free ParserF Void), IMVar)
letInsertion lets recs p = (p', μs, μMax)
  where
    m = fold' absurd alg p
    ((p', μMax), (_, μs)) = unsafePerformIO (runStateT (runFreshT (runLetInserter m) 0) (HashMap.empty, DMap.empty))
    alg :: Free ParserF Void a -> ParserF LetInserter a -> LetInserter a
    alg p q = LetInserter $ do
      name <- makeStableParserName p
      (vs, μs) <- get
      if | HashSet.member name recs ->
             case HashMap.lookup name vs of
               Just v  -> let μ = MVar v in return $! Op (Rec μ (μs DMap.! μ))
               Nothing -> mdo
                 v <- newVar
                 let μ = MVar v
                 put (HashMap.insert name v vs, DMap.insert μ q' μs)
                 q' <- runLetInserter (postprocess q)
                 return $! Op (Rec μ q')
         | HashSet.member name lets ->
             case HashMap.lookup name vs of
               Just v  -> let μ = MVar v in return $! optimise (Let μ (μs DMap.! μ))
               Nothing -> do -- no mdo here, let bindings are not recursive!
                 v <- newVar
                 let μ = MVar v
                 q' <- runLetInserter (postprocess q)
                 put (HashMap.insert name v vs, DMap.insert μ q' μs)
                 return $! optimise (Let μ q')
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

getPreds :: MonadState (s1, s2) m => m s1
getPreds = gets fst

getRecs :: MonadState (s1, s2) m => m s2
getRecs = gets snd

modifyPreds :: MonadState (s1, s2) m => (s1 -> s1) -> m ()
modifyPreds = modify' . first

modifyRecs :: MonadState (s1, s2) m => (s2 -> s2) -> m ()
modifyRecs = modify' . second

addPred :: (Eq k, Hashable k, Eq v, Hashable v, MonadState (HashMap k (HashSet v), s2) m) => k -> v -> m ()
addPred k v = modifyPreds (HashMap.insertWith HashSet.union k (HashSet.singleton v))

addRec :: (Eq a, Hashable a, MonadState (s1, HashSet a) m) => a -> m ()
addRec = modifyRecs . HashSet.insert

askPred :: MonadReader (r1, r2) m => m r1
askPred = asks fst

askSeen :: MonadReader (r1, r2) m => m r2
askSeen = asks snd

localPred :: MonadReader (r1, r2) m => r1 -> m a -> m a
localPred x = local (first (const x))

localSeen :: MonadReader (r1, r2) m => (r2 -> r2) -> m a -> m a
localSeen f = local (second f)

ifSeen :: (Eq a, Hashable a, MonadReader (r1, HashSet a) m) => a -> m b -> m b -> m b
ifSeen x yes no = do !seen <- askSeen; if HashSet.member x seen then yes else no

addName :: (Eq a, Hashable a, MonadReader (r1, HashSet a) m) => a -> m b -> m b
addName x = localSeen (HashSet.insert x)

makeStableParserName :: MonadIO m => Free ParserF Void a -> m StableParserName
-- Force evaluation of p to ensure that the stableName is correct first time
makeStableParserName !p =
  do !(StableName name) <- liftIO (makeStableName p)
     return $! StableParserName name

showM :: Parser a -> String
showM = show . fst . compile

instance Eq StableParserName where 
  (StableParserName n) == (StableParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable StableParserName where
  hash (StableParserName n) = hashStableName (StableName n)
  hashWithSalt salt (StableParserName n) = hashWithSalt salt (StableName n)

instance GShow MVar where gshowsPrec = showsPrec
instance Show (Free ParserF Void a) => ShowTag MVar (Free ParserF Void) where showTaggedPrec m = showsPrec