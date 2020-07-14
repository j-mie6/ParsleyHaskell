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
             KindSignatures,
             TypeOperators #-}
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
import Parsley.Core.CombinatorAST          (Combinator(..), ScopeRegister(..), Reg(..))
import Parsley.Core.Primitives             (Parser(..))
import Parsley.Core.Identifiers            (IMVar, MVar(..), IΣVar, ΣVar(..))
import Parsley.Common.Fresh                (HFreshT, newVar, newScope, runFreshT)
import Parsley.Common.Indexed              (Fix(In), cata, cata', IFunctor(imap), (:+:)(..), (\/), Const1(..))
import Parsley.Frontend.Optimiser          (optimise)
import Parsley.Frontend.CombinatorAnalyser (analyse, emptyFlags, AnalysisFlags(..))
import System.IO.Unsafe                    (unsafePerformIO)

import qualified Data.Dependent.Map  as DMap    ((!), empty, insert, map, size)
import qualified Data.HashMap.Strict as HashMap ((!), lookup, insert, empty, insertWith, foldrWithKey)
import qualified Data.HashSet        as HashSet (member, insert, empty, union)

compile :: forall compiled a. Parser a -> (forall x. Bool -> Fix Combinator x -> IMVar -> compiled x) -> (compiled a, DMap MVar compiled)
compile (Parser p) codeGen = trace ("COMPILING NEW PARSER WITH " ++ show ((DMap.size ms)) ++ " LET BINDINGS") $ (m, ms)
  where
    (p', μs, maxV) = preprocess p

    codeGen' :: Bool -> Fix Combinator x -> compiled x
    codeGen' letBound p = codeGen letBound (analyse (emptyFlags {letBound = letBound}) p) (maxV + 1)

    ms = DMap.map (codeGen' True) μs
    m = codeGen' False p'

preprocess :: Fix (Combinator :+: ScopeRegister) a -> (Fix Combinator a, DMap MVar (Fix Combinator), IMVar)
preprocess p =
  let q = tagParser p
      (lets, recs) = findLets q
  in letInsertion lets recs q

data ParserName = forall a. ParserName (StableName# (Fix (Combinator :+: ScopeRegister) a))
data Tag t f (k :: * -> *) a = Tag {tag :: t, tagged :: f k a}
newtype Tagger a = Tagger { runTagger :: Fix (Tag ParserName Combinator) a }

tagParser :: Fix (Combinator :+: ScopeRegister) a -> Fix (Tag ParserName Combinator) a
tagParser = runTagger . cata' (\p -> Tagger . In . Tag (makeParserName p) . (imap runTagger \/ descope))
  where
    regMaker = newRegMaker
    descope (ScopeRegister p f) = freshReg regMaker (\(reg@(Reg σ)) -> MakeRegister σ (runTagger p) (runTagger (f reg)))

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
  addPred name
  ifSeen name
    (do addRec name)
    (ifNotProcessedBefore name
      (do addName name (traverseCombinator (fmap Const1 . runLetFinder) (tagged p))
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
postprocess = LetInserter . fmap optimise . traverseCombinator runLetInserter

traverseCombinator :: Applicative m => (forall a. f a -> m (k a)) -> Combinator f a -> m (Combinator k a)
traverseCombinator expose (pf :<*>: px)        = liftA2 (:<*>:) (expose pf) (expose px)
traverseCombinator expose (p :*>: q)           = liftA2 (:*>:) (expose p) (expose q)
traverseCombinator expose (p :<*: q)           = liftA2 (:<*:)  (expose p)  (expose q)
traverseCombinator expose (p :<|>: q)          = liftA2 (:<|>:) (expose p)  (expose q)
traverseCombinator expose Empty                = pure Empty
traverseCombinator expose (Try p)              = fmap Try (expose p)
traverseCombinator expose (LookAhead p)        = fmap LookAhead (expose p)
traverseCombinator expose (NotFollowedBy p)    = fmap NotFollowedBy (expose p)
traverseCombinator expose (Branch b p q)       = liftA3 Branch (expose b) (expose p) (expose q)
traverseCombinator expose (Match p fs qs d)    = liftA4 Match (expose p) (pure fs) (traverse expose qs) (expose d)
traverseCombinator expose (ChainPre op p)      = liftA2 ChainPre (expose op) (expose p)
traverseCombinator expose (ChainPost p op)     = liftA2 ChainPost (expose p) (expose op)
traverseCombinator expose (MakeRegister σ p q) = liftA2 (MakeRegister σ) (expose p) (expose q)
traverseCombinator expose (GetRegister σ)      = pure (GetRegister σ)
traverseCombinator expose (PutRegister σ p)    = fmap (PutRegister σ) (expose p)
traverseCombinator expose (Debug name p)       = fmap (Debug name) (expose p)
traverseCombinator expose (Pure x)             = pure (Pure x)
traverseCombinator expose (Satisfy f)          = pure (Satisfy f)

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

makeParserName :: Fix (Combinator :+: ScopeRegister) a -> ParserName
-- Force evaluation of p to ensure that the stableName is correct first time
makeParserName !p = unsafePerformIO (fmap (\(StableName name) -> ParserName name) (makeStableName p))

{-# NOINLINE newRegMaker #-}
newRegMaker :: IORef IΣVar
newRegMaker = unsafePerformIO (newIORef 0)

{-# NOINLINE freshReg #-}
freshReg :: IORef IΣVar -> (forall r. Reg r a -> x) -> x
freshReg maker scope = scope $ unsafePerformIO $ do
  x <- readIORef maker
  writeIORef maker (x + 1)
  return $! (Reg (ΣVar x))

{-# NOINLINE numRegisters #-}
numRegisters :: IORef IΣVar -> IΣVar
numRegisters = unsafePerformIO . readIORef

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