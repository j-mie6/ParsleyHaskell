{-# LANGUAGE AllowAmbiguousTypes,
             MagicHash,
             MultiParamTypeClasses,
             MultiWayIf,
             RecursiveDo,
             TupleSections,
             UndecidableInstances #-}
module Parsley.Frontend.Compiler (compile) where

import Prelude hiding (pred)
import Data.Dependent.Map                  (DMap)
import Data.Hashable                       (Hashable, hashWithSalt, hash)
import Data.HashMap.Strict                 (HashMap)
import Data.HashSet                        (HashSet)
import Data.IORef                          (IORef, newIORef, readIORef, writeIORef)
import Data.Kind                           (Type)
import Data.Maybe                          (isJust)
import Data.Set                            (Set)
import Debug.Trace                         (trace)
import Control.Monad                       (void, when)
import Control.Monad.Reader                (Reader, runReader, local, ask)
import Control.Monad.State.Strict          (State, StateT, get, put, runState, execStateT, modify', MonadState)
import GHC.Exts                            (Int(..))
import GHC.Prim                            (StableName#, unsafeCoerce#)
import GHC.StableName                      (StableName(..), makeStableName, hashStableName, eqStableName)
import Numeric                             (showHex)
import Parsley.Core.CombinatorAST          (Combinator(..), ScopeRegister(..), Reg(..), Parser(..), traverseCombinator)
import Parsley.Core.Identifiers            (IMVar, MVar(..), IΣVar, ΣVar(..))
import Parsley.Common.Fresh                (HFreshT, newVar, runFreshT)
import Parsley.Common.Indexed              (Fix(In), cata, cata', IFunctor(imap), (:+:)(..), (\/), Const1(..))
import Parsley.Frontend.Optimiser          (optimise)
import Parsley.Frontend.CombinatorAnalyser (analyse, emptyFlags, AnalysisFlags(..))
import Parsley.Frontend.Dependencies       (dependencyAnalysis)
import System.IO.Unsafe                    (unsafePerformIO)

import qualified Data.Dependent.Map  as DMap    ((!), empty, insert, mapWithKey, size)
import qualified Data.HashMap.Strict as HashMap (lookup, insert, empty, insertWith, foldrWithKey, alterF)
import qualified Data.HashSet        as HashSet (member, insert, empty)
import qualified Data.Map            as Map     ((!))
import qualified Data.Set            as Set     (empty)

compile :: forall compiled a. Parser a -> (forall x. Maybe (MVar x) -> Fix Combinator x -> Set IΣVar -> IMVar -> IΣVar -> compiled x) -> (compiled a, DMap MVar compiled)
compile (Parser p) codeGen = trace ("COMPILING NEW PARSER WITH " ++ show (DMap.size μs') ++ " LET BINDINGS") $ (codeGen' Nothing p', DMap.mapWithKey (codeGen' . Just) μs')
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
    descope (ScopeRegister p f) = freshReg regMaker (\(reg@(Reg σ)) -> MakeRegister σ p (f reg))
    regMaker :: IORef IΣVar
    regMaker = newRegMaker p

data LetFinderState = LetFinderState { preds  :: HashMap ParserName Int
                                     , recs   :: HashSet ParserName
                                     }
type LetFinderCtx   = HashSet ParserName
newtype LetFinder a = LetFinder { doLetFinder :: StateT LetFinderState (Reader LetFinderCtx) () }

findLets :: Fix (Tag ParserName Combinator) a -> (HashSet ParserName, HashSet ParserName)
findLets p = (lets, recs)
  where
    state = LetFinderState HashMap.empty HashSet.empty
    ctx = HashSet.empty
    LetFinderState preds recs = runReader (execStateT (doLetFinder (cata findLetsAlg p)) state) ctx
    lets = HashMap.foldrWithKey (\k n ls -> if n > 1 then HashSet.insert k ls else ls) HashSet.empty preds

findLetsAlg :: Tag ParserName Combinator LetFinder a -> LetFinder a
findLetsAlg p = LetFinder $ do
  let name = tag p
  st <- get
  let (before, preds') = HashMap.alterF (\v -> (v, Just (maybe 1 (+ 1) v))) name (preds st)
  seen <- ask
  if HashSet.member name seen
   then
     put st{preds=preds', recs = HashSet.insert name (recs st)}
   else do
     put st{preds=preds'}
     when (before == Nothing) $
       local (HashSet.insert name) $
         void $ traverseCombinator (fmap Const1 . doLetFinder) (tagged p)

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
        Nothing -> mdo
          v <- newVar
          let μ = MVar v
          put (HashMap.insert name v vs, DMap.insert μ q' μs)
          q' <- doLetInserter (postprocess q)
          return $! optimise (Let recu μ q')
      else do doLetInserter (postprocess q)

postprocess :: Combinator LetInserter a -> LetInserter a
postprocess = LetInserter . fmap optimise . traverseCombinator doLetInserter

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
