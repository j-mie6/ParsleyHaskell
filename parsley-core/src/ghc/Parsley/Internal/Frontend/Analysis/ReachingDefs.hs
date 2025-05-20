{-# LANGUAGE DerivingStrategies #-}
module Parsley.Internal.Frontend.Analysis.ReachingDefs (SoleReacherData(..), soleReachers) where

import Parsley.Internal.Frontend.Analysis (NodeID, ΣNodeData (..))
import qualified Data.Map as M
import qualified Data.Set as Set
import Parsley.Internal.Backend.Machine.Identifiers ( SomeΣVar )
import Parsley.Internal.Frontend.Analysis.CFG (CFG(..))
import Control.Monad.Fix (fix)
import Control.Monad (when)
import Control.Monad.State (State, get, put, runState)
import Data.Foldable (sequenceA_)
import Debug.Trace (trace)


data ReachingDefs = ReachingDefs {reachIn :: Set.Set NodeID, reachOut :: Set.Set NodeID} deriving stock Show

data SoleReacherData = SoleReacherData {hasSoleReacher :: M.Map NodeID  (SomeΣVar -> Bool),  isSoleReacher :: M.Map NodeID (SomeΣVar -> Bool) }

{-|
    Perform reaching definition analysis and return a map from NodeID to function "does ΣVar have a single reaching definition here?"
-}
soleReachers :: CFG -> SoleReacherData
soleReachers cfg@(CFG start _ adj) = wrapNeatly $ snd . fst $ flip Control.Monad.State.runState (False, initSets)  $ do
        fix $ \loop -> do
            (_, m) <- Control.Monad.State.get
            Control.Monad.State.put (False, m)
            round cfg
            (change, _) <- Control.Monad.State.get
            when change loop
        Control.Monad.State.get
    where
        wrapNeatly :: M.Map NodeID ReachingDefs -> SoleReacherData
        wrapNeatly rdefs = SoleReacherData {hasSoleReacher = hasSoleReacher, isSoleReacher = isSoleReacher}
            where 
                reachTo = M.foldlWithKey (\acc nid rdefs -> Set.foldl (\acc d -> M.insertWith Set.union d (Set.singleton nid) acc) acc rdefs) M.empty (M.map reachIn rdefs)
                hasSoleReacher = M.map (\rdefs svar -> Set.size (defs M.! svar `Set.intersection` reachIn rdefs) == 1) rdefs
                isSoleReacher  = M.map (\reachTo svar -> Set.foldl (\a b -> a && (hasSoleReacher M.! b $ svar)) True $ (uses M.! svar) `Set.intersection` reachTo) reachTo
        maxID :: NodeID
        maxID = M.foldlWithKey (\a k (_, b) -> max k $ Set.foldl max a b) start adj

        initSets = M.fromList [(i, ReachingDefs Set.empty Set.empty) | i <- [0..maxID]]

        -- Defs map: all nodes that assign to ΣVar (makes and puts)
        defs :: M.Map SomeΣVar (Set.Set NodeID)
        defs = M.foldlWithKey (\a k (info, _)
                                -> case info of
                                    Nothing -> a
                                    Just (ΣGet{}) -> a
                                    Just x -> M.insertWith Set.union (which x) (Set.singleton k) a) M.empty adj
        -- uses map: all nodes that use a ΣVar (makes and puts)
        uses :: M.Map SomeΣVar (Set.Set NodeID)
        uses = M.foldlWithKey (\a k (info, _)
                                -> case info of
                                    Nothing -> a
                                    Just (ΣPut{}) -> a
                                    Just (ΣMake{}) -> a
                                    Just x ->  M.insertWith Set.union (which x) (Set.singleton k) a) M.empty adj

        pred :: M.Map NodeID (Set.Set NodeID)
        pred = M.foldlWithKey (\a k (_, succ) -> foldl (\m s -> M.insertWith Set.union s (Set.singleton k) m) a succ) M.empty adj

        round :: CFG -> Control.Monad.State.State (Bool, M.Map NodeID ReachingDefs) ()
        round (CFG _ _ m) = sequenceA_ (M.mapWithKey update m)

        update :: NodeID -> (Maybe ΣNodeData, Set.Set NodeID) -> Control.Monad.State.State (Bool, M.Map NodeID ReachingDefs) ()
        update t (info, _) = do
            (_, m) <- Control.Monad.State.get
            let curr = m M.! t
            let reachOut' = case info of
                    Just ΣGet{} -> reachIn curr -- get
                    Just x -> Set.union (Set.singleton t) (Set.difference (reachIn curr) (defs M.! which x)) -- make/put
                    Nothing -> reachIn curr -- Not ΣVar op
            let reachIn' = Set.foldl (\l s -> Set.union l $ reachOut (m M.! s)) Set.empty (if t == start then Set.empty else pred M.! t)
            let mNew = M.adjust (\_ -> ReachingDefs reachIn' reachOut') t m
            when (reachIn curr /= reachIn' || reachOut curr /= reachOut') $ Control.Monad.State.put (True, mNew)