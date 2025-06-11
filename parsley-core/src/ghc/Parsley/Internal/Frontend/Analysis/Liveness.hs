{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}

module Parsley.Internal.Frontend.Analysis.Liveness (livenessAnalysis, LivenessData (..), LivenessAnalysisResult) where

import Control.Monad (when)
import Control.Monad.Fix (fix)
import Control.Monad.State (State, get, put, runState, execState, gets, modify)
import Data.Foldable (sequenceA_)
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Map (Map)
import qualified Data.Set as S
import qualified Data.Set as Set
import Parsley.Internal.Backend.Machine.Identifiers ()
import Parsley.Internal.Core.Identifiers (SomeΣVar)
import Parsley.Internal.Frontend.Analysis.CFG (CFG (..), NodeID, ΣNodeData (..))
import Control.Monad (unless)
import Data.Maybe (fromJust, isNothing, isJust)

-- |
--    Pertinent liveness data associated with each CFG node.
data LivenessData = LivenessData {liveIn :: Set SomeΣVar, liveOut :: Set SomeΣVar} deriving stock (Show)

type LivenessAnalysisResult = Map NodeID LivenessData

data LivenessState = LivenessState { worklist :: [NodeID], livenessSets :: LivenessAnalysisResult}

popWL :: State LivenessState NodeID
popWL = do
      LivenessState{worklist} <- get 
      let (head : tail) = worklist
      modify (\state -> state{worklist=tail})
      return head
  

emptyWL :: State LivenessState Bool
emptyWL = gets (null . worklist) 

addToWL :: Set NodeID -> State LivenessState ()
addToWL preds = do
      state@LivenessState{worklist} <- get
      put $ state{worklist=foldl (flip (:)) worklist preds}

updateLivenessSets :: NodeID -> LivenessData -> State LivenessState () 
updateLivenessSets id sets = modify (\state@LivenessState{livenessSets} -> state{livenessSets=Map.insert id sets livenessSets})



livenessAnalysis :: CFG -> LivenessAnalysisResult
livenessAnalysis (CFG start _ adj) = livenessSets $ execState iter initState
  where
    maxID = Map.foldlWithKey (\a k (_, b) -> max k $ S.foldl max a b) start adj
    succ = Map.map snd adj
    useDefs = Map.map fromJust $ Map.filter isJust $ Map.map fst adj
    pred =
      Map.foldlWithKey
        ( \g n nsucc ->
            foldl
              (\g s -> Map.insertWith Set.union s (Set.singleton n) g)
              g
              nsucc
        )
        (Map.fromList [(x, mempty) | x <- [0 .. maxID]])
        succ
    initWL = Map.keys succ
    initLiveSets = foldl (\a k -> a <> Map.singleton k (LivenessData mempty mempty)) Map.empty [0 .. maxID]
    initState = LivenessState initWL initLiveSets
    
    iter :: State LivenessState ()
    iter = do 
      node <- popWL
      propNode node 
      isEmpty <- emptyWL
      unless isEmpty iter 
    propNode :: NodeID -> State LivenessState ()
    propNode nodeid = do 
      LivenessState{livenessSets} <- get 
      let LivenessData{liveIn=currIn, liveOut=currOut} = livenessSets Map.! nodeid
      let succs = Map.findWithDefault Set.empty nodeid succ
      let liveout' = Set.foldl (\l s -> Set.union l $ liveIn (livenessSets Map.! s)) Set.empty succs
      let livein' = case Map.lookup nodeid useDefs of
            Just (ΣGet{which}) -> Set.insert which currOut
            Just x -> Set.union (use x) (Set.delete (which x) liveout') -- use eqn.
            Nothing -> liveout' -- No use/def data
      updateLivenessSets nodeid LivenessData{liveIn=livein', liveOut=liveout'}
      when (livein' /= currIn || liveout' /= currOut) $ 
        addToWL $ Map.findWithDefault (error "could not find pred") nodeid pred