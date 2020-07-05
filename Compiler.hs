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
             AllowAmbiguousTypes,
             ScopedTypeVariables #-}
module Compiler(compile) where

import Prelude hiding (pred)
import CombinatorAST              (Combinator(..), Parser(..))
import Optimiser                  (optimise)
import CombinatorAnalyser         (analyse, emptyFlags, AnalysisFlags(..))
import CodeGenerator              (codeGen)
import Instructions               (Program(..), IMVar, IΣVar, MVar(..), LetBinding(..))
import Indexed                    (Fix(In), cata, cata', Tag(..), imap)
import Utils                      (Quapplicative, WQ)
import Control.Applicative        (liftA, liftA2, liftA3)
import Control.Monad              (forM, forM_)
import Control.Monad.Reader       (Reader, runReader, local, ask, asks, MonadReader)
import Control.Monad.State.Strict (State, StateT, get, gets, put, runState, execStateT, modify', MonadState)
import Data.List                  (foldl')
import Fresh                      (HFreshT, newVar, newScope, runFreshT)
import System.IO.Unsafe           (unsafePerformIO)
import Data.IORef                 (IORef, newIORef, readIORef, writeIORef)
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
import qualified Data.Set            as Set     (null)

compile :: Parser a -> (Program o a, DMap MVar (LetBinding WQ o a))
compile (Parser p) =
  let !(p', μs, maxV) = preprocess p
      !(m, maxΣ) = codeGen False (analyse emptyFlags p') (maxV + 1) 0
      !ms = compileLets μs (maxV + 1) maxΣ
  in trace ("COMPILING NEW PARSER WITH " ++ show ((DMap.size ms)) ++ " LET BINDINGS") $ (Program m, ms)

compileLets :: Quapplicative q => DMap MVar (Fix (Combinator q)) -> IMVar -> IΣVar -> DMap MVar (LetBinding q o a)
compileLets μs maxV maxΣ = let (ms, _) = DMap.foldrWithKey compileLet (DMap.empty, maxΣ) μs in ms
  where
    compileLet :: Quapplicative q => MVar x -> Fix (Combinator q) x -> (DMap MVar (LetBinding q o a), IΣVar) -> (DMap MVar (LetBinding q o a), IΣVar)
    compileLet (MVar μ) p (ms, maxΣ) =
      let (m, maxΣ') = codeGen True (analyse (emptyFlags {letBound = True}) p) maxV (maxΣ + 1)
      in (DMap.insert (MVar μ) (LetBinding m) ms, maxΣ')

preprocess :: Quapplicative q => Fix (Combinator q) a -> (Fix (Combinator q) a, DMap MVar (Fix (Combinator q)), IMVar)
preprocess p =
  let q = tagParser p
      (lets, recs) = findLets q
  in letInsertion lets recs q

data ParserName = forall a q. ParserName (StableName# (Fix (Combinator q) a))
newtype Tagger q a = Tagger { runTagger :: Fix (Tag ParserName (Combinator q)) a }

tagParser :: Fix (Combinator q) a -> Fix (Tag ParserName (Combinator q)) a
tagParser = runTagger . cata' alg
  where
    alg p q = Tagger (In (Tag (makeParserName p) (imap runTagger q)))

data LetFinderState = LetFinderState { preds  :: HashMap ParserName Int
                                     , recs   :: HashSet ParserName
                                     , before :: HashSet ParserName }
type LetFinderCtx   = HashSet ParserName
newtype LetFinder a = LetFinder { runLetFinder :: StateT LetFinderState (Reader LetFinderCtx) () }

findLets :: Fix (Tag ParserName (Combinator q)) a -> (HashSet ParserName, HashSet ParserName)
findLets p = (lets, recs)
  where
    state = LetFinderState HashMap.empty HashSet.empty HashSet.empty
    ctx = HashSet.empty
    LetFinderState preds recs _ = runReader (execStateT (runLetFinder (cata findLetsAlg p)) state) ctx
    lets = HashMap.foldrWithKey (\k n ls -> if n > 1 then HashSet.insert k ls else ls) HashSet.empty preds

findLetsAlg :: Tag ParserName (Combinator q) LetFinder a -> LetFinder a
findLetsAlg p = LetFinder $ do
  let name = tag p
  let q = tagged p
  addPred name
  ifSeen name
    (do addRec name)
    (ifNotProcessedBefore name
      (do addName name (case q of
            pf :<*>: px       -> do runLetFinder pf; runLetFinder px
            p :*>: q          -> do runLetFinder p;  runLetFinder q
            p :<*: q          -> do runLetFinder p;  runLetFinder q
            p :<|>: q         -> do runLetFinder p;  runLetFinder q
            Try p             -> do runLetFinder p
            LookAhead p       -> do runLetFinder p
            NotFollowedBy p   -> do runLetFinder p
            Branch b p q      -> do runLetFinder b;  runLetFinder p; runLetFinder q
            Match p _ qs d    -> do runLetFinder p;  forM_ qs runLetFinder; runLetFinder d
            ChainPre op p     -> do runLetFinder op; runLetFinder p
            ChainPost p op    -> do runLetFinder p;  runLetFinder op
            Debug _ p         -> do runLetFinder p
            _                 -> do return ())
          doNotProcessAgain name))

newtype LetInserter q a =
  LetInserter {
      runLetInserter :: HFreshT IMVar
                        (State ( HashMap ParserName IMVar
                               , DMap MVar (Fix (Combinator q))))
                        (Fix (Combinator q) a)
    }
letInsertion :: Quapplicative q => HashSet ParserName -> HashSet ParserName -> Fix (Tag ParserName (Combinator q)) a -> (Fix (Combinator q) a, DMap MVar (Fix (Combinator q)), IMVar)
letInsertion lets recs p = (p', μs, μMax)
  where
    m = cata alg p
    ((p', μMax), (vs, μs)) = runState (runFreshT (runLetInserter m) 0) (HashMap.empty, DMap.empty)
    alg :: Quapplicative q => Tag ParserName (Combinator q) (LetInserter q) a -> LetInserter q a
    alg p = LetInserter $ do
      let name = tag p
      let q = tagged p
      (vs, μs) <- get
      let bound = HashSet.member name lets
      let recu = HashSet.member name recs
      if bound || recu then case HashMap.lookup name vs of
        Just v  -> let μ = MVar v in return $! optimise (Let recu μ (μs DMap.! μ))
        Nothing -> mdo
          v <- newVar
          let μ = MVar v
          put (HashMap.insert name v vs, DMap.insert μ q' μs)
          q' <- runLetInserter (postprocess q)
          return $! optimise (Let recu μ q')
      else do runLetInserter (postprocess q)

postprocess :: Quapplicative q => Combinator q (LetInserter q) a -> LetInserter q a
postprocess (pf :<*>: px)       = LetInserter (fmap optimise (liftA2 (:<*>:) (runLetInserter pf) (runLetInserter px)))
postprocess (p :*>: q)          = LetInserter (fmap optimise (liftA2 (:*>:)  (runLetInserter p)  (runLetInserter q)))
postprocess (p :<*: q)          = LetInserter (fmap optimise (liftA2 (:<*:)  (runLetInserter p)  (runLetInserter q)))
postprocess (p :<|>: q)         = LetInserter (fmap optimise (liftA2 (:<|>:) (runLetInserter p)  (runLetInserter q)))
postprocess Empty               = LetInserter (return        (In Empty))
postprocess (Try p)             = LetInserter (fmap optimise (fmap Try (runLetInserter p)))
postprocess (LookAhead p)       = LetInserter (fmap optimise (fmap LookAhead (runLetInserter p)))
postprocess (NotFollowedBy p)   = LetInserter (fmap optimise (fmap NotFollowedBy (runLetInserter p)))
postprocess (Branch b p q)      = LetInserter (fmap optimise (liftA3 Branch (runLetInserter b) (runLetInserter p) (runLetInserter q)))
postprocess (Match p fs qs d)   = LetInserter (fmap optimise (liftA4 Match (runLetInserter p) (return fs) (traverse runLetInserter qs) (runLetInserter d)))
postprocess (ChainPre op p)     = LetInserter (fmap optimise (liftA2 ChainPre (runLetInserter op) (runLetInserter p)))
postprocess (ChainPost p op)    = LetInserter (fmap optimise (liftA2 ChainPost (runLetInserter p) (runLetInserter op)))
postprocess (Debug name p)      = LetInserter (fmap optimise (fmap (Debug name) (runLetInserter p)))
postprocess (Pure x)            = LetInserter (return        (In (Pure x)))
postprocess (Satisfy f)         = LetInserter (return        (In (Satisfy f)))

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

addName :: MonadReader LetFinderCtx m => ParserName -> m b -> m b
addName x = local (HashSet.insert x)

makeParserName :: Fix (Combinator q) a -> ParserName
-- Force evaluation of p to ensure that the stableName is correct first time
makeParserName !p = unsafePerformIO (fmap (\(StableName name) -> ParserName name) (makeStableName p))

showM :: Parser a -> String
showM = show . fst . compile

liftA4 :: Applicative f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftA4 f u v w x = liftA3 f u v w <*> x

instance Eq ParserName where
  (ParserName n) == (ParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable ParserName where
  hash (ParserName n) = hashStableName (StableName n)
  hashWithSalt salt (ParserName n) = hashWithSalt salt (StableName n)

-- There is great evil in this world, and I'm probably responsible for half of it
instance Show ParserName where show (ParserName n) = show (I# (unsafeCoerce# n))