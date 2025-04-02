{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Parsley.Internal.Frontend.Analysis.Dependencies
Description : Calculate dependencies of a collection of bindings.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes `dependencyAnalysis`, which is used to calculate information
regarding the dependencies of each let-bound parser, as well as their
free-registers.

@since 1.5.0.0
-}
module Parsley.Internal.Frontend.Analysis.Dependencies (dependencyAnalysis) where

import Control.Monad                        (unless, forM_)
import Control.Monad.ST                     (ST)
import Data.Array                           (Array)
import Data.Array.MArray                    (readArray, writeArray, newArray, newArray_)
import Data.Array.ST                        (STArray, runSTUArray, runSTArray)
import Data.Array.Unboxed                   (UArray)
import Data.Dependent.Map                   (DMap)
import Data.Foldable                        (foldl', traverse_)
import Data.Map.Strict                      (Map)
import Data.Set                             (Set)
import Data.STRef                           (newSTRef, readSTRef, writeSTRef)
import Parsley.Internal.Common.Indexed      (Fix, cata, Const1(..), (:*:)(..), zipper)
import Parsley.Internal.Common.State        (State, MonadState (get), execState, modify')
import Parsley.Internal.Core.CombinatorAST  (Combinator(..), traverseCombinator, traverseCombinatorRev)
import Parsley.Internal.Core.Identifiers    (IMVar(..), MVar(..), ΣVar, SomeΣVar(..))

import qualified Data.Dependent.Map as DMap   (foldrWithKey, filterWithKey)
import qualified Data.Map.Strict    as Map    ((!), empty, insert, insertWith, findMax, elems, maxView, fromList, fromDistinctAscList, foldlWithKey)
import qualified Data.Set           as Set    (toList, insert, union, unions, member, notMember, empty, (\\), fromDistinctAscList, size, singleton)
import qualified Data.Array         as Array  ((!), listArray, bounds, indices)
import qualified Data.Array.Unboxed as UArray ((!), assocs)
import qualified Data.List          as List   (partition)
import Debug.Trace (trace)

type Graph = Array IMVar [IMVar]
type PQueue k a = Map k a

{-|
Given a top-level parser and a collection of its let-bound subjects performs the following tasks:

* Determines which parser depend on which others.
* Use the previous information to remove any dead bindings.
* Calculate the direct free registers for each binding.
* Propogate the free registers according to transitive need via the dependency graph.

Returns the non-dead bindings, the information about each bindings free registers, and the next
free index for any registers created in code generation. 

@since 1.5.0.0
-}
-- TODO This actually should be in the backend... dead bindings and the topological ordering can be computed here
--      but the register stuff should come after register optimisation and instruction peephole
dependencyAnalysis :: Fix Combinator a -> DMap MVar (Fix Combinator) -> (DMap MVar (Fix Combinator), Map IMVar (Set SomeΣVar))
dependencyAnalysis toplevel μs =
  let -- Step 1: find roots of the toplevel
      roots = directDependencies toplevel
      -- Step 2: build immediate dependencies
      DependencyMaps{..} = buildDependencyMaps μs
      -- Step 3: Build a call graph
      callees = buildGraph immediateDependencies
      -- Step 4: traverse the call graph, finding unreachable nodes and establishing a topological dfnum for each node
      (dfnums, lives, dead) = topoOrdering roots callees
      -- Step 5: reverse the call graph to make a callers graph
      callers = invertGraph callers dead
      -- Step 6: iterate over the live registers, and propagate the free registers until fix-point
      regs = propagateRegs lives dfnums usedRegisters definedRegisters callees callers
  in (DMap.filterWithKey (\(MVar v) _ -> Set.notMember v dead) μs, regs)

buildGraph :: Map IMVar (Set IMVar) -> Graph
buildGraph deps = Array.listArray (0, fst (Map.findMax deps)) (map Set.toList (Map.elems deps))

invertGraph :: Graph -> Set IMVar -> Graph
invertGraph g unreachable = runSTArray $ do
  g' <- newArray (Array.bounds g) []
  forM_ (Array.indices g) $ \n ->
    unless (Set.member n unreachable) $
      forM_ (g Array.! n) $ \s -> do
        preds <- readArray g' s
        writeArray g' s (n : preds)
  return g'

type DFNum = Int
topoOrdering :: Set IMVar -> Graph -> (UArray IMVar DFNum, [IMVar], Set IMVar)
topoOrdering roots graph =
  let dfnums :: UArray IMVar DFNum
      dfnums = runSTUArray $ do
        dfnums <- newArray (Array.bounds graph) 0
        nextDfnum <- newSTRef 1
        let dfs v = do seen <- (/= 0) <$> readArray dfnums v
                       unless seen $
                         do dfnum <- readSTRef nextDfnum
                            writeArray dfnums v dfnum
                            writeSTRef nextDfnum (dfnum + 1)
                            forM_ (graph Array.! v) dfs
        -- Assign a DFNum to each IMVar
        forM_ roots dfs
        return dfnums
      -- if something still has dfnum 0, it was not visited, and is dead
      lives, deads :: [(IMVar, DFNum)]
      (lives, deads) = List.partition ((/= 0) . snd) (UArray.assocs dfnums)
      -- The DFNums are unique
  in (dfnums, map fst lives, Set.fromDistinctAscList (map fst deads))

propagateRegs :: [IMVar] -> UArray IMVar DFNum -> Map IMVar (Set SomeΣVar) -> Map IMVar (Set SomeΣVar) -> Graph -> Graph -> Map IMVar (Set SomeΣVar)
propagateRegs reachables dfnums uses defs callees callers = toMap $ runSTArray $
  do freeRegs <- newArray_ (Array.bounds callees)
     forM_ reachables $ \v -> writeArray freeRegs v ((uses Map.! v) Set.\\ (defs Map.! v))
     let worklist = Map.fromList (map (\v -> (dfnums UArray.! v, v)) reachables)
     maybe (return ()) (unfoldM_ (uncurry (propagate freeRegs))) (Map.maxView worklist)
     return freeRegs
  where
    propagate :: STArray s IMVar (Set SomeΣVar) -> IMVar -> PQueue DFNum IMVar -> ST s (Maybe (IMVar, PQueue DFNum IMVar))
    propagate freeRegs v work = do
      !frees        <- readArray freeRegs v
      !freesCallees <- Set.unions <$> traverse (readArray freeRegs) (callees Array.! v)
      let !frees'   =  frees `Set.union` (freesCallees Set.\\ (defs Map.! v))
      if Set.size frees /= Set.size frees' then do
        writeArray freeRegs v frees'
        return (Map.maxView (addWork (callers Array.! v) work))
      else return (Map.maxView work)

    addWork :: [IMVar] -> PQueue DFNum IMVar -> PQueue DFNum IMVar
    addWork vs work = foldl' (flip (\v -> Map.insert (dfnums UArray.! v) v)) work vs

    unfoldM_ :: Monad m => (s -> m (Maybe s)) -> s -> m ()
    unfoldM_ f s = f s >>= mapM_ (unfoldM_ f)

    toMap arr = Map.fromDistinctAscList (map (\v -> (v, arr Array.! v)) reachables)

-- IMMEDIATE DEPENDENCY MAPS
data DependencyMaps = DependencyMaps {
  usedRegisters         :: !(Map IMVar (Set SomeΣVar)), -- Leave Lazy
  immediateDependencies :: !(Map IMVar (Set IMVar)), -- Could be Strict
  definedRegisters      :: !(Map IMVar (Set SomeΣVar)),
  -- returnContRegisters: For each let-bound parser, set of ΣVars that are free   after a call to the parser from extrinsic contexts
  returnContRegisters   :: !(Map IMVar (Set SomeΣVar)) 
  }

buildDependencyMaps :: DMap MVar (Fix Combinator) -> DependencyMaps
buildDependencyMaps = DMap.foldrWithKey (\(MVar v) p deps@DependencyMaps{..} ->
  let (uses, defs, ds, retFrees) = freeRegistersAndDependencies v p
  in deps { usedRegisters = Map.insert v uses usedRegisters
          , immediateDependencies = Map.insert v ds immediateDependencies
          , definedRegisters = Map.insert v defs definedRegisters
          , returnContRegisters = Map.foldlWithKey (\a k b -> Map.insertWith Set.union k b a) returnContRegisters retFrees})
           (DependencyMaps Map.empty Map.empty Map.empty Map.empty)

freeRegistersAndDependencies :: IMVar -> Fix Combinator a -> (Set SomeΣVar,  Set SomeΣVar, Set IMVar, Map IMVar (Set SomeΣVar))
freeRegistersAndDependencies v p =
  let frsm :*: depsm = zipper freeRegistersAlg (dependenciesAlg (Just v)) p
      (uses, defs, retFrees) = runFreeRegisters frsm
      ds = {-trace ("JYRYS FREES:" ++ show frees) $-} runDependencies depsm
  in (uses, defs, ds, retFrees)

-- DEPENDENCY ANALYSIS
newtype Dependencies a = Dependencies { doDependencies :: State (Set IMVar) () }
runDependencies :: Dependencies a -> Set IMVar
runDependencies = flip execState Set.empty . doDependencies

directDependencies :: Fix Combinator a -> Set IMVar
directDependencies = runDependencies . cata (dependenciesAlg Nothing)

{-# INLINE dependenciesAlg #-}
dependenciesAlg :: Maybe IMVar -> Combinator Dependencies a -> Dependencies a
dependenciesAlg (Just v) (Let μ@(MVar u)) = Dependencies $ do unless (u == v) (dependsOn μ)
dependenciesAlg Nothing  (Let μ)          = Dependencies $ do dependsOn μ
dependenciesAlg _ p                       = Dependencies $ do traverseCombinator (fmap Const1 . doDependencies) p; return ()

dependsOn :: MonadState (Set IMVar) m => MVar a -> m ()
dependsOn (MVar v) = modify' (Set.insert v)

-- FREE REGISTER ANALYSIS
newtype FreeRegisters a = FreeRegisters { doFreeRegisters :: State (Set SomeΣVar, Set SomeΣVar, Map IMVar (Set SomeΣVar)) () }
runFreeRegisters :: FreeRegisters a -> (Set SomeΣVar, Set SomeΣVar, Map IMVar (Set SomeΣVar))
runFreeRegisters = flip execState (Set.empty, Set.empty, Map.empty) . doFreeRegisters

{-# INLINE freeRegistersAlg #-}
freeRegistersAlg :: Combinator FreeRegisters a -> FreeRegisters a
freeRegistersAlg (GetRegister σ)      = FreeRegisters $ do uses σ
freeRegistersAlg (PutRegister σ p)    = FreeRegisters $ do uses σ; doFreeRegisters p
freeRegistersAlg (MakeRegister σ p q) = FreeRegisters $ do defs σ; doFreeRegisters p; doFreeRegisters q
freeRegistersAlg (Let µ)              = FreeRegisters $ do freeAfterRet µ; return ()
freeRegistersAlg p                    = FreeRegisters $ do traverseCombinatorRev (fmap Const1 . doFreeRegisters) p; return ()

first3 :: (a -> a') -> (a,b,c) -> (a', b, c)
first3 f (a, b, c) = (f a, b, c)

second3 :: (b -> b') -> (a,b,c) -> (a, b', c)
second3 f (a, b, c) = (a, f b, c)

third3 :: (c -> c') -> (a,b,c) -> (a, b, c')
third3 f (a, b, c) = (a, b, f c)

uses :: MonadState (Set SomeΣVar, vs, vs') m => ΣVar a -> m ()
uses σ = modify' (first3 (Set.insert (SomeΣVar σ)))

defs :: MonadState (vs, Set SomeΣVar, vs') m => ΣVar a -> m ()
defs σ = modify' (second3 (Set.insert (SomeΣVar σ)))

freeAfterRet :: MonadState (Set SomeΣVar, Set SomeΣVar, Map IMVar (Set SomeΣVar)) m => MVar a -> m ()
freeAfterRet (MVar µ) = do
  (use, def, _) <- get
  traverse_ (modify' . third3 . Map.insertWith Set.union µ . Set.singleton) (use Set.\\ def)