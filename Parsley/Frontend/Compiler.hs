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
             ScopedTypeVariables,
             KindSignatures #-}
module Parsley.Frontend.Compiler (compile) where

import Prelude hiding (pred)
import Data.Dependent.Map                  (DMap)
import Data.Hashable                       (Hashable, hashWithSalt, hash)
import Data.HashMap.Strict                 (HashMap)
import Data.HashSet                        (HashSet)
import Data.List                           (foldl')
import Data.IORef                          (IORef, newIORef, readIORef, writeIORef)
import Debug.Trace                         (trace)
import Control.Applicative                 (liftA, liftA2, liftA3)
import Control.Monad                       (forM, forM_)
import Control.Monad.Reader                (Reader, runReader, local, ask, asks, MonadReader)
import Control.Monad.State.Strict          (State, StateT, get, gets, put, runState, execStateT, modify', MonadState)
import GHC.Exts                            (Int(..))
import GHC.Prim                            (StableName#, unsafeCoerce#)
import GHC.StableName                      (StableName(..), makeStableName, hashStableName, eqStableName)
import Numeric                             (showHex)
import Parsley.Core.CombinatorAST          (Combinator(..))
import Parsley.Core.Primitives             (Parser(..))
import Parsley.Core.Identifiers            (IMVar, MVar(..))
import Parsley.Common.Fresh                (HFreshT, newVar, newScope, runFreshT)
import Parsley.Common.Indexed              (Fix(In), cata, cata', IFunctor(imap))
import Parsley.Frontend.Optimiser          (optimise)
import Parsley.Frontend.CombinatorAnalyser (analyse, emptyFlags, AnalysisFlags(..))
import System.IO.Unsafe                    (unsafePerformIO)

import qualified Data.Dependent.Map  as DMap    ((!), empty, insert, map, size)
import qualified Data.HashMap.Strict as HashMap ((!), lookup, insert, empty, insertWith, foldrWithKey)
import qualified Data.HashSet        as HashSet (member, insert, empty, union)
import qualified Data.Set            as Set     (null)

compile :: forall compiled a. Parser a -> (forall x. Bool -> Fix Combinator x -> IMVar -> compiled x) -> (compiled a, DMap MVar compiled)
compile (Parser p) codeGen = trace ("COMPILING NEW PARSER WITH " ++ show ((DMap.size ms)) ++ " LET BINDINGS") $ (m, ms)
  where
    (p', μs, maxV) = preprocess p

    codeGen' :: Bool -> Fix Combinator x -> compiled x
    codeGen' letBound p = codeGen letBound (analyse (emptyFlags {letBound = letBound}) p) (maxV + 1)

    ms = DMap.map (codeGen' True) μs
    m = codeGen' False p'


preprocess :: Fix Combinator a -> (Fix Combinator a, DMap MVar (Fix Combinator), IMVar)
preprocess p =
  let q = tagParser p
      (lets, recs) = findLets q
  in letInsertion lets recs q

data ParserName = forall a. ParserName (StableName# (Fix Combinator a))
data Tag t f (k :: * -> *) a = Tag {tag :: t, tagged :: f k a}
newtype Tagger a = Tagger { runTagger :: Fix (Tag ParserName Combinator) a }

tagParser :: Fix Combinator a -> Fix (Tag ParserName Combinator) a
tagParser = runTagger . cata' alg
  where
    alg p q = Tagger (In (Tag (makeParserName p) (imap runTagger q)))

data LetFinderState = LetFinderState { preds  :: HashMap ParserName Int
                                     , recs   :: HashSet ParserName
                                     , before :: HashSet ParserName }
type LetFinderCtx   = HashSet ParserName
newtype LetFinder a = LetFinder { runLetFinder :: StateT LetFinderState (Reader LetFinderCtx) () }

findLets :: Fix (Tag ParserName Combinator) a -> (HashSet ParserName, HashSet ParserName)
findLets p = (lets, recs)
  where
    state = LetFinderState HashMap.empty HashSet.empty HashSet.empty
    ctx = HashSet.empty
    LetFinderState preds recs _ = runReader (execStateT (runLetFinder (cata findLetsAlg p)) state) ctx
    lets = HashMap.foldrWithKey (\k n ls -> if n > 1 then HashSet.insert k ls else ls) HashSet.empty preds

findLetsAlg :: Tag ParserName Combinator LetFinder a -> LetFinder a
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

newtype LetInserter a =
  LetInserter {
      runLetInserter :: HFreshT IMVar
                        (State ( HashMap ParserName IMVar
                               , DMap MVar (Fix Combinator)))
                        (Fix Combinator a)
    }
letInsertion :: HashSet ParserName -> HashSet ParserName -> Fix (Tag ParserName Combinator) a -> (Fix Combinator a, DMap MVar (Fix Combinator), IMVar)
letInsertion lets recs p = (p', μs, μMax)
  where
    m = cata alg p
    ((p', μMax), (vs, μs)) = runState (runFreshT (runLetInserter m) 0) (HashMap.empty, DMap.empty)
    alg :: Tag ParserName Combinator LetInserter a -> LetInserter a
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

postprocess :: Combinator LetInserter a -> LetInserter a
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
ifSeen x yes no = do seen <- ask; if HashSet.member x seen then yes else no

ifNotProcessedBefore :: MonadState LetFinderState m => ParserName -> m () -> m ()
ifNotProcessedBefore x m = do !before <- getBefore; if HashSet.member x before then return () else m

doNotProcessAgain :: MonadState LetFinderState m => ParserName -> m ()
doNotProcessAgain x = modifyBefore (HashSet.insert x)

addName :: MonadReader LetFinderCtx m => ParserName -> m b -> m b
addName x = local (HashSet.insert x)

makeParserName :: Fix Combinator a -> ParserName
-- Force evaluation of p to ensure that the stableName is correct first time
makeParserName !p = unsafePerformIO (fmap (\(StableName name) -> ParserName name) (makeStableName p))

liftA4 :: Applicative f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftA4 f u v w x = liftA3 f u v w <*> x

instance IFunctor f => IFunctor (Tag t f) where
  imap f (Tag t k) = Tag t (imap f k)

instance Eq ParserName where
  (ParserName n) == (ParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable ParserName where
  hash (ParserName n) = hashStableName (StableName n)
  hashWithSalt salt (ParserName n) = hashWithSalt salt (StableName n)

-- There is great evil in this world, and I'm probably responsible for half of it
instance Show ParserName where showsPrec _ (ParserName n) = showHex (I# (unsafeCoerce# n))