{-# LANGUAGE DerivingStrategies #-}

module Parsley.Internal.Frontend.Analysis.Liveness (livenessAnalysis) where

import Data.Set (Set)
import qualified Data.Set as S
import Parsley.Internal.Common (Fix(..))
import Parsley.Internal.Core.CombinatorAST (Combinator(..), PosSelector (..))
import qualified Data.Map as M
import qualified Data.Dependent.Map as DM
import Parsley.Internal.Backend.Machine.Identifiers ()
import Parsley.Internal.Frontend.Analysis.CFG (buildCFG, tagCombinator, NodeID, CFG(..))
import Parsley.Internal.Core.Identifiers (SomeΣVar, MVar (..))
import Control.Monad.Fix (fix)
import Control.Monad (when)
import qualified Data.Set as Set
import Control.Monad.State (State(..), get, put, runState)
import Data.Foldable (sequenceA_)

{-|
    Pertinent liveness data associated with each CFG node.
-}
data LivenessData = LivenessData { liveIn :: Set SomeΣVar, liveOut :: Set SomeΣVar } deriving stock Show

type LivenessAnalysisResult = M.Map NodeID LivenessData

{-| 
Given a CFG of the parser, compute the liveIn and liveOut for each node.
-}
livenessAnalysis :: CFG -> LivenessAnalysisResult
livenessAnalysis cfg@(CFG start _ adj) = snd . fst $ flip runState (False, initSets)  $ do
        fix $ \loop -> do
            (_, m) <- get
            put (False, m)
            round cfg
            (change, _) <- get
            when change loop
        get
    where
        maxID :: NodeID
        maxID = M.foldlWithKey (\a k (_, _, b) -> max k $ S.foldl max a b) start adj
        
        initSets :: LivenessAnalysisResult
        initSets = M.fromList [(i, LivenessData Set.empty Set.empty) | i <- [0..maxID]]

        round :: CFG -> State (Bool, LivenessAnalysisResult) ()
        round (CFG _ _ m) = sequenceA_ (M.mapWithKey update m)

        update :: NodeID -> (Set SomeΣVar, Set SomeΣVar, Set NodeID) -> State (Bool, LivenessAnalysisResult) ()
        update t (use, def, succ) = do
            (_, m) <- get
            let curr = m M.! t
            let liveIn' = Set.union use (Set.difference (liveOut curr) def)
            let liveOut' = Set.foldl (\l s -> Set.union l $ liveIn (m M.! s)) Set.empty succ
            let mNew = M.adjust (\_ -> LivenessData liveIn' liveOut') t m
            when (liveIn curr /= liveIn' || liveOut curr /= liveOut') $ put (True, mNew)