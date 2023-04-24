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

import Control.Arrow                        (first, second)
import Control.Monad                        (unless, forM_)
import Data.Array                           (Array, (!), listArray)
import Data.Array.MArray                    (readArray, writeArray, newArray)
import Data.Array.ST                        (runSTUArray)
import Data.Array.Unboxed                   (UArray, assocs)
import Data.Dependent.Map                   (DMap)
import Data.List                            (foldl', partition, sortOn)
import Data.Map.Strict                      (Map)
import Data.Set                             (Set, insert, (\\), union, notMember, empty)
import Data.STRef                           (newSTRef, readSTRef, writeSTRef)
import Parsley.Internal.Common.Indexed      (Fix, cata, Const1(..), (:*:)(..), zipper)
import Parsley.Internal.Common.State        (State, MonadState, execState, modify')
import Parsley.Internal.Core.CombinatorAST  (Combinator(..), traverseCombinator)
import Parsley.Internal.Core.Identifiers    (IMVar, MVar(..), ΣVar, SomeΣVar(..))

import qualified Data.Dependent.Map as DMap (foldrWithKey, filterWithKey)
import qualified Data.Map.Strict    as Map  ((!), empty, insert, findMax, elems, maxView, fromList, adjust)
import qualified Data.Set           as Set  (elems, empty, insert, fromDistinctAscList, size, delete)
import qualified Data.Array.Unboxed as UArray ((!))

type Graph = Array IMVar [IMVar]
type PQueue k a = Map k a

next :: PQueue k a -> Maybe (a, PQueue k a)
next = Map.maxView

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
      -- Step 3: find the largest name
      n = fst (Map.findMax immediateDependencies)
      -- Step 4: Build a dependency graph
      graph = buildGraph n immediateDependencies
      -- Step 5: construct the seen set (dfnum)
      -- Step 6: dfs from toplevel (via roots) all with same seen set
      -- Step 7: elems of seen set with dfnum 0 are dead, otherwise they are collected into a list in descending order
      (topo, dfnums, dead) = topoOrdering roots n graph
      -- the dfnums is a map from IMVar to DFNum, and DFNum's are used as the unique keys to a
      -- Data.Map priority queue
      -- this iteratively propagates free registers upwards:
      regs = propagateRegs topo dfnums usedRegisters definedRegisters immediateDependencies (callerMap topo immediateDependencies)
  in (DMap.filterWithKey (\(MVar v) _ -> notMember v dead) μs, regs)

buildGraph :: IMVar -> Map IMVar (Set IMVar) -> Graph
buildGraph n = listArray (0, n) . map Set.elems . Map.elems

type DFNum = Int

topoOrdering :: Set IMVar -> IMVar -> Graph -> ([IMVar], UArray IMVar DFNum, Set IMVar)
topoOrdering roots n graph =
  let dfnums :: UArray IMVar DFNum
      dfnums = runSTUArray $ do
        dfnums <- newArray (0, n) 0
        nextDfnum <- newSTRef 1
        let hasSeen v = (/= 0) <$> readArray dfnums v
        let setSeen v = do dfnum <- readSTRef nextDfnum
                           writeArray dfnums v dfnum
                           writeSTRef nextDfnum (dfnum + 1)
        -- Assign a DFNum to each IMVar
        forM_ roots (dfs hasSeen setSeen graph)
        return dfnums
      -- if something still has dfnum 0, it was not visited, and is dead
      lives, deads :: [(IMVar, DFNum)]
      (lives, deads) = partition ((/= 0) . snd) (assocs dfnums)
      -- The DFNums are unique
  in (reverseMap fst (sortOn snd lives), dfnums, Set.fromDistinctAscList (map fst deads))

reverseMap :: (a -> b) -> [a] -> [b]
reverseMap f = foldl' (\xs x -> f x : xs) []

propagateRegs :: [IMVar] -> UArray IMVar DFNum -> Map IMVar (Set SomeΣVar) -> Map IMVar (Set SomeΣVar) -> Map IMVar (Set IMVar) -> Map IMVar (Set IMVar) -> Map IMVar (Set SomeΣVar)
propagateRegs vs dfnums uses defs callees callers =
  go ((Map.fromList (map (\v -> (dfnums UArray.! v, v)) vs)))
     (Map.fromList (map (\v -> (v, (uses Map.! v) \\ (defs Map.! v))) vs))
  where
    go :: PQueue DFNum IMVar -> Map IMVar (Set SomeΣVar) -> Map IMVar (Set SomeΣVar)
    go pqueue freeRegs = case next pqueue of
      Nothing -> freeRegs
      Just (v, q')  ->
        let frees = freeRegs Map.! v
            freesCallees = foldMap (freeRegs Map.!) (callees Map.! v)
            frees' = frees `union` (freesCallees \\ (defs Map.! v))
        in if Set.size frees /= Set.size frees'
           then go (foldl' (flip (\caller -> Map.insert (dfnums UArray.! caller) caller)) pqueue (Set.delete v (callers Map.! v))) (Map.insert v frees' freeRegs)
           else go q' freeRegs

callerMap :: [IMVar] -> Map IMVar (Set IMVar) -> Map IMVar (Set IMVar)
callerMap lives deps =
  foldl' (\callers k -> foldl' (flip (Map.adjust (Set.insert k))) callers (deps Map.! k))
         (Map.fromList (zip lives (repeat Set.empty)))
         lives

dfs :: Monad m => (IMVar -> m Bool) -> (IMVar -> m ()) -> Graph -> IMVar -> m ()
dfs hasSeen setSeen graph = go
  where
    go v = do seen <- hasSeen v
              unless seen $
                do setSeen v
                   forM_ (graph ! v) go

-- IMMEDIATE DEPENDENCY MAPS
data DependencyMaps = DependencyMaps {
  usedRegisters         :: Map IMVar (Set SomeΣVar), -- Leave Lazy
  immediateDependencies :: Map IMVar (Set IMVar), -- Could be Strict
  definedRegisters      :: Map IMVar (Set SomeΣVar)
}

buildDependencyMaps :: DMap MVar (Fix Combinator) -> DependencyMaps
buildDependencyMaps = DMap.foldrWithKey (\(MVar v) p deps@DependencyMaps{..} ->
  let (frs, defs, ds) = freeRegistersAndDependencies v p
  in deps { usedRegisters = Map.insert v frs usedRegisters
          , immediateDependencies = Map.insert v ds immediateDependencies
          , definedRegisters = Map.insert v defs definedRegisters}) (DependencyMaps Map.empty Map.empty Map.empty)

freeRegistersAndDependencies :: IMVar -> Fix Combinator a -> (Set SomeΣVar,  Set SomeΣVar, Set IMVar)
freeRegistersAndDependencies v p =
  let frsm :*: depsm = zipper freeRegistersAlg (dependenciesAlg (Just v)) p
      (frs, defs) = runFreeRegisters frsm
      ds = runDependencies depsm
  in (frs, defs, ds)

-- DEPENDENCY ANALYSIS
newtype Dependencies a = Dependencies { doDependencies :: State (Set IMVar) () }
runDependencies :: Dependencies a -> Set IMVar
runDependencies = flip execState empty. doDependencies

directDependencies :: Fix Combinator a -> Set IMVar
directDependencies = runDependencies . cata (dependenciesAlg Nothing)

{-# INLINE dependenciesAlg #-}
dependenciesAlg :: Maybe IMVar -> Combinator Dependencies a -> Dependencies a
dependenciesAlg (Just v) (Let _ μ@(MVar u)) = Dependencies $ do unless (u == v) (dependsOn μ)
dependenciesAlg Nothing  (Let _ μ)          = Dependencies $ do dependsOn μ
dependenciesAlg _ p                         = Dependencies $ do traverseCombinator (fmap Const1 . doDependencies) p; return ()

dependsOn :: MonadState (Set IMVar) m => MVar a -> m ()
dependsOn (MVar v) = modify' (insert v)

-- FREE REGISTER ANALYSIS
newtype FreeRegisters a = FreeRegisters { doFreeRegisters :: State (Set SomeΣVar, Set SomeΣVar) () }
runFreeRegisters :: FreeRegisters a -> (Set SomeΣVar, Set SomeΣVar)
runFreeRegisters = flip execState (empty, empty) . doFreeRegisters

{-# INLINE freeRegistersAlg #-}
freeRegistersAlg :: Combinator FreeRegisters a -> FreeRegisters a
freeRegistersAlg (GetRegister σ)      = FreeRegisters $ do uses σ
freeRegistersAlg (PutRegister σ p)    = FreeRegisters $ do uses σ; doFreeRegisters p
freeRegistersAlg (MakeRegister σ p q) = FreeRegisters $ do defs σ; doFreeRegisters p; doFreeRegisters q
freeRegistersAlg p                    = FreeRegisters $ do traverseCombinator (fmap Const1 . doFreeRegisters) p; return ()

uses :: MonadState (Set SomeΣVar, vs) m => ΣVar a -> m ()
uses σ = modify' (first (insert (SomeΣVar σ)))

defs :: MonadState (vs, Set SomeΣVar) m => ΣVar a -> m ()
defs σ = modify' (second (insert (SomeΣVar σ)))
