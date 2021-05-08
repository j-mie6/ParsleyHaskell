{-# OPTIONS_GHC -fno-hpc #-}
{-# LANGUAGE AllowAmbiguousTypes,
             MagicHash,
             MultiParamTypeClasses,
             MultiWayIf,
             RecursiveDo,
             UndecidableInstances #-}
module Parsley.Internal.Frontend.Compiler (compile) where

import Prelude hiding (pred)
import Data.Dependent.Map                           (DMap)
import Data.Hashable                                (Hashable, hashWithSalt, hash)
import Data.HashMap.Strict                          (HashMap)
import Data.HashSet                                 (HashSet)
import Data.IORef                                   (IORef, newIORef, readIORef, writeIORef)
import Data.Kind                                    (Type)
import Data.Maybe                                   (isJust)
import Data.Set                                     (Set)
import Control.Arrow                                (first, second)
import Control.Monad                                (void, when)
import Control.Monad.Reader                         (ReaderT, runReaderT, local, ask, MonadReader)
import GHC.Exts                                     (Int(..), unsafeCoerce#)
import GHC.Prim                                     (StableName#)
import GHC.StableName                               (StableName(..), makeStableName, hashStableName, eqStableName)
import Numeric                                      (showHex)
import Parsley.Internal.Core.CombinatorAST          (Combinator(..), ScopeRegister(..), Reg(..), Parser(..), traverseCombinator)
import Parsley.Internal.Core.Identifiers            (IMVar, MVar(..), IΣVar, ΣVar(..))
import Parsley.Internal.Common.Fresh                (HFreshT, newVar, runFreshT)
import Parsley.Internal.Common.Indexed              (Fix(In), cata, cata', IFunctor(imap), (:+:)(..), (\/), Const1(..))
import Parsley.Internal.Common.State                (State, get, gets, runState, execState, modify', MonadState)
import Parsley.Internal.Frontend.Optimiser          (optimise)
import Parsley.Internal.Frontend.CombinatorAnalyser (analyse, emptyFlags, AnalysisFlags(..))
import Parsley.Internal.Frontend.Dependencies       (dependencyAnalysis)
import Parsley.Internal.Trace                       (Trace(trace))
import System.IO.Unsafe                             (unsafePerformIO)

import qualified Data.Dependent.Map  as DMap    ((!), empty, insert, mapWithKey, size)
import qualified Data.HashMap.Strict as HashMap (lookup, insert, empty, insertWith, foldrWithKey, (!))
import qualified Data.HashSet        as HashSet (member, insert, empty)
import qualified Data.Map            as Map     ((!))
import qualified Data.Set            as Set     (empty)

{-# INLINEABLE compile #-}
compile :: forall compiled a. Trace => Parser a -> (forall x. Maybe (MVar x) -> Fix Combinator x -> Set IΣVar -> IMVar -> IΣVar -> compiled x) -> (compiled a, DMap MVar compiled)
compile (Parser p) codeGen = trace ("COMPILING NEW PARSER WITH " ++ show (DMap.size μs') ++ " LET BINDINGS") (codeGen' Nothing p', DMap.mapWithKey (codeGen' . Just) μs')
  where
    (p', μs, maxV) = preprocess p
    (μs', frs, maxΣ) = dependencyAnalysis p' μs

    freeRegs :: Maybe (MVar x) -> Set IΣVar
    freeRegs = maybe Set.empty (\(MVar v) -> frs Map.! v)

    codeGen' :: Maybe (MVar x) -> Fix Combinator x -> compiled x
    codeGen' letBound p = codeGen letBound (analyse (emptyFlags {letBound = isJust letBound}) p) (freeRegs letBound) (maxV + 1) (maxΣ + 1)

preprocess :: Fix (Combinator :+: ScopeRegister) a -> (Fix Combinator a, DMap MVar (Fix Combinator), IMVar)
preprocess p =
  let q = tagParser p
      (lets, recs) = findLets q
      (p', μs, maxV) = letInsertion lets recs q
  in (p', μs, maxV)

data ParserName = forall a. ParserName (StableName# (Fix (Combinator :+: ScopeRegister) a))
data Tag t f (k :: Type -> Type) a = Tag {tag :: t, tagged :: f k a}

tagParser :: Fix (Combinator :+: ScopeRegister) a -> Fix (Tag ParserName Combinator) a
tagParser p = cata' tagAlg p
  where
    tagAlg p = In . Tag (makeParserName p) . (id \/ descope)
    descope (ScopeRegister p f) = freshReg regMaker (\reg@(Reg σ) -> MakeRegister σ p (f reg))
    regMaker :: IORef IΣVar
    regMaker = newRegMaker p

data LetFinderState = LetFinderState { preds  :: HashMap ParserName Int
                                     , recs   :: HashSet ParserName }
type LetFinderCtx   = HashSet ParserName
newtype LetFinder a = LetFinder { doLetFinder :: ReaderT LetFinderCtx (State LetFinderState) () }

findLets :: Fix (Tag ParserName Combinator) a -> (HashSet ParserName, HashSet ParserName)
findLets p = (lets, recs)
  where
    state = LetFinderState HashMap.empty HashSet.empty
    ctx = HashSet.empty
    LetFinderState preds recs = execState (runReaderT (doLetFinder (cata findLetsAlg p)) ctx) state
    lets = HashMap.foldrWithKey (\k n ls -> if n > 1 then HashSet.insert k ls else ls) HashSet.empty preds

findLetsAlg :: Tag ParserName Combinator LetFinder a -> LetFinder a
findLetsAlg p = LetFinder $ do
  let name = tag p
  addPred name
  ifSeen name
    (do addRec name)
    (ifNotProcessedBefore name
      (void (addName name (traverseCombinator (fmap Const1 . doLetFinder) (tagged p)))))

newtype LetInserter a =
  LetInserter {
      doLetInserter :: HFreshT IMVar
                       (State ( HashMap ParserName IMVar
                              , DMap MVar (Fix Combinator)))
                       (Fix Combinator a)
    }
letInsertion :: HashSet ParserName -> HashSet ParserName -> Fix (Tag ParserName Combinator) a -> (Fix Combinator a, DMap MVar (Fix Combinator), IMVar)
letInsertion lets recs p = (p', μs, μMax)
  where
    m = cata alg p
    ((p', μMax), (_, μs)) = runState (runFreshT (doLetInserter m) 0) (HashMap.empty, DMap.empty)
    alg :: Tag ParserName Combinator LetInserter a -> LetInserter a
    alg p = LetInserter $ do
      let name = tag p
      let q = tagged p
      (vs, μs) <- get
      let bound = HashSet.member name lets
      let recu = HashSet.member name recs
      if bound || recu then case HashMap.lookup name vs of
        Just v  -> let μ = MVar v in return $! optimise (Let recu μ (μs DMap.! μ))
        Nothing -> do
          v <- newVar
          let μ = MVar v
          modify' (first (HashMap.insert name v))
          rec
            modify' (second (DMap.insert μ q'))
            q' <- doLetInserter (postprocess q) -- This line should be moved above when there is an inliner pass
          return $! optimise (Let recu μ q')
      else do doLetInserter (postprocess q)

postprocess :: Combinator LetInserter a -> LetInserter a
postprocess = LetInserter . fmap optimise . traverseCombinator doLetInserter

modifyPreds :: MonadState LetFinderState m => (HashMap ParserName Int -> HashMap ParserName Int) -> m ()
modifyPreds f = modify' (\st -> st {preds = f (preds st)})

modifyRecs :: MonadState LetFinderState m => (HashSet ParserName -> HashSet ParserName) -> m ()
modifyRecs f = modify' (\st -> st {recs = f (recs st)})

addPred :: MonadState LetFinderState m => ParserName -> m ()
addPred k = modifyPreds (HashMap.insertWith (+) k 1)

addRec :: MonadState LetFinderState m => ParserName -> m ()
addRec = modifyRecs . HashSet.insert

ifSeen :: MonadReader LetFinderCtx m => ParserName -> m a -> m a -> m a
ifSeen x yes no = do seen <- ask; if HashSet.member x seen then yes else no

ifNotProcessedBefore :: MonadState LetFinderState m => ParserName -> m () -> m ()
ifNotProcessedBefore x m =
  do oneReference <- gets ((== 1) . (HashMap.! x) . preds)
     when oneReference m

addName :: MonadReader LetFinderCtx m => ParserName -> m b -> m b
addName x = local (HashSet.insert x)

makeParserName :: Fix (Combinator :+: ScopeRegister) a -> ParserName
-- Force evaluation of p to ensure that the stableName is correct first time
makeParserName !p = unsafePerformIO (fmap (\(StableName name) -> ParserName name) (makeStableName p))

-- The argument here stops GHC from floating it out, it should be provided something from the scope
{-# NOINLINE newRegMaker #-}
newRegMaker :: a -> IORef IΣVar
newRegMaker x = x `seq` unsafePerformIO (newIORef 0)

{-# NOINLINE freshReg #-}
freshReg :: IORef IΣVar -> (forall r. Reg r a -> x) -> x
freshReg maker scope = scope $ unsafePerformIO $ do
  x <- readIORef maker
  writeIORef maker (x + 1)
  return $! Reg (ΣVar x)

instance IFunctor f => IFunctor (Tag t f) where
  imap f (Tag t k) = Tag t (imap f k)

instance Eq ParserName where
  (ParserName n) == (ParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable ParserName where
  hash (ParserName n) = hashStableName (StableName n)
  hashWithSalt salt (ParserName n) = hashWithSalt salt (StableName n)

-- There is great evil in this world, and I'm probably responsible for half of it
instance Show ParserName where showsPrec _ (ParserName n) = showHex (I# (unsafeCoerce# n))