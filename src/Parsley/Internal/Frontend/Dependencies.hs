{-# LANGUAGE RecordWildCards #-}
module Parsley.Internal.Frontend.Dependencies (dependencyAnalysis) where

import Control.Arrow                        (first, second)
import Control.Monad                        (unless, forM_)
import Data.Array                           (Array, (!), listArray)
import Data.Array.MArray                    (readArray, writeArray, newArray)
import Data.Array.ST                        (runSTUArray)
import Data.Array.Unboxed                   (assocs)
import Data.Dependent.Map                   (DMap)
import Data.List                            (foldl', partition, sortOn)
import Data.Map.Strict                      (Map)
import Data.Maybe                           (fromMaybe)
import Data.Set                             (Set, insert, (\\), union, notMember, empty)
import Data.STRef                           (newSTRef, readSTRef, writeSTRef)
import Parsley.Internal.Common.Indexed      (Fix, cata, Const1(..), (:*:)(..), zipper)
import Parsley.Internal.Common.State        (State, MonadState, execState, modify')
import Parsley.Internal.Core.CombinatorAST  (Combinator(..), traverseCombinator)
import Parsley.Internal.Core.Identifiers    (IMVar, MVar(..), IΣVar, ΣVar(..))

import qualified Data.Dependent.Map as DMap (foldrWithKey, filterWithKey)
import qualified Data.Map.Strict    as Map  ((!), empty, insert, mapMaybeWithKey, findMax, elems, lookup, foldMapWithKey)
import qualified Data.Set           as Set  (elems, empty, insert, lookupMax)

type Graph = Array IMVar [IMVar]

-- TODO This actually should be in the backend... dead bindings and the topological ordering can be computed here
--      but the register stuff should come after register optimisation and instruction peephole

dependencyAnalysis :: Fix Combinator a -> DMap MVar (Fix Combinator) -> (DMap MVar (Fix Combinator), Map IMVar (Set IΣVar), IΣVar)
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
      (topo, dead) = topoOrdering roots n graph
      -- Step 8: perform a dfs on each of the topo, with a new seen set for each,
      --         building the flattened dependency map. If the current focus has
      --         already been computed, add all its deps to the seen set and skip.
      --         The end seen set becomes out flattened deps.
      trueDeps = flattenDependencies topo (minMax topo) graph
      -- Step 8: Compute the new registers, and remove dead ones
      addNewRegs v uses
        | notMember v dead = let deps = trueDeps Map.! v
                                 defs = definedRegisters Map.! v
                                 subUses = foldMap (usedRegisters Map.!) deps
                                 subDefs = foldMap (definedRegisters Map.!) deps
                             in Just $ (uses \\ defs) `union` (subUses \\ subDefs)
        | otherwise        = Nothing
      trueRegs = Map.mapMaybeWithKey addNewRegs usedRegisters
      largestRegister = fromMaybe (-1) (Set.lookupMax (Map.foldMapWithKey (const id) definedRegisters))
  in (DMap.filterWithKey (\(MVar v) _ -> notMember v dead) μs, trueRegs, largestRegister)

minMax :: Ord a => [a] -> (a, a)
minMax []     = error "cannot find minimum or maximum of empty list"
minMax (x:xs) = foldl' (\(small, big) x -> (min small x, max big x)) (x, x) xs

buildGraph :: IMVar -> Map IMVar (Set IMVar) -> Graph
buildGraph n = listArray (0, n) . map Set.elems . Map.elems

topoOrdering :: Set IMVar -> IMVar -> Graph -> ([IMVar], Set IMVar)
topoOrdering roots n graph =
  let dfnums = runSTUArray $ do
        dfnums <- newArray (0, n) (0 :: Int)
        nextDfnum <- newSTRef 1
        let hasSeen v = (/= 0) <$> readArray dfnums v
        let setSeen v = do dfnum <- readSTRef nextDfnum
                           writeArray dfnums v dfnum
                           writeSTRef nextDfnum (dfnum + 1)
        forM_ roots (dfs hasSeen setSeen graph)
        return dfnums
      (lives, deads) = partition ((/= 0) . snd) (assocs dfnums)
  in (reverseMap fst (sortOn snd lives), foldl' (\ds v0 -> Set.insert (fst v0) ds) Set.empty deads)

reverseMap :: (a -> b) -> [a] -> [b]
reverseMap f = foldl' (\xs x -> f x : xs) []

flattenDependencies :: [IMVar] -> (IMVar, IMVar) -> Graph -> Map IMVar (Set IMVar)
flattenDependencies topo range graph = foldl' reachable Map.empty topo
  where
    reachable :: Map IMVar (Set IMVar) -> IMVar -> Map IMVar (Set IMVar)
    reachable deps root =
      let seen = runSTUArray $ do
            seen <- newArray range False
            let setSeen v = writeArray seen v True
            let seenOrSkip v = case Map.lookup v deps of
                  Nothing -> readArray seen v
                  Just ds -> setSeen v >> forM_ ds setSeen >> return True
            dfs seenOrSkip setSeen graph root
            return seen
          ds = foldl' (\ds (v, b) -> if b then Set.insert v ds else ds) Set.empty (assocs seen)
      in Map.insert root ds deps

dfs :: Monad m => (IMVar -> m Bool) -> (IMVar -> m ()) -> Graph -> IMVar -> m ()
dfs hasSeen setSeen graph = go
  where
    go v = do seen <- hasSeen v
              unless seen $
                do setSeen v
                   forM_ (graph ! v) go

-- IMMEDIATE DEPENDENCY MAPS
data DependencyMaps = DependencyMaps {
  usedRegisters         :: Map IMVar (Set IΣVar), -- Leave Lazy
  immediateDependencies :: Map IMVar (Set IMVar), -- Could be Strict
  definedRegisters      :: Map IMVar (Set IΣVar)
}

buildDependencyMaps :: DMap MVar (Fix Combinator) -> DependencyMaps
buildDependencyMaps = DMap.foldrWithKey (\(MVar v) p deps@DependencyMaps{..} ->
  let (frs, defs, ds) = freeRegistersAndDependencies v p
  in deps { usedRegisters = Map.insert v frs usedRegisters
          , immediateDependencies = Map.insert v ds immediateDependencies
          , definedRegisters = Map.insert v defs definedRegisters}) (DependencyMaps Map.empty Map.empty Map.empty)

freeRegistersAndDependencies :: IMVar -> Fix Combinator a -> (Set IΣVar,  Set IΣVar, Set IMVar)
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
dependenciesAlg (Just v) (Let _ μ@(MVar u) _) = Dependencies $ do unless (u == v) (dependsOn μ)
dependenciesAlg Nothing  (Let _ μ _)          = Dependencies $ do dependsOn μ
dependenciesAlg _ p                           = Dependencies $ do traverseCombinator (fmap Const1 . doDependencies) p; return ()

dependsOn :: MonadState (Set IMVar) m => MVar a -> m ()
dependsOn (MVar v) = modify' (insert v)

-- FREE REGISTER ANALYSIS
newtype FreeRegisters a = FreeRegisters { doFreeRegisters :: State (Set IΣVar, Set IΣVar) () }
runFreeRegisters :: FreeRegisters a -> (Set IΣVar, Set IΣVar)
runFreeRegisters = flip execState (empty, empty) . doFreeRegisters

{-# INLINE freeRegistersAlg #-}
freeRegistersAlg :: Combinator FreeRegisters a -> FreeRegisters a
freeRegistersAlg (GetRegister σ)      = FreeRegisters $ do uses σ
freeRegistersAlg (PutRegister σ p)    = FreeRegisters $ do uses σ; doFreeRegisters p
freeRegistersAlg (MakeRegister σ p q) = FreeRegisters $ do defs σ; doFreeRegisters p; doFreeRegisters q
freeRegistersAlg Let{}                = FreeRegisters $ do return () -- TODO This can be removed when Let doesn't have the body in it...
freeRegistersAlg p                    = FreeRegisters $ do traverseCombinator (fmap Const1 . doFreeRegisters) p; return ()

uses :: MonadState (Set IΣVar, vs) m => ΣVar a -> m ()
uses (ΣVar σ) = modify' (first (insert σ)) --tell (singleton σ, mempty)

defs :: MonadState (vs, Set IΣVar) m => ΣVar a -> m ()
defs (ΣVar σ) = modify' (second (insert σ)) --tell (mempty, singleton σ)