{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DerivingStrategies #-}

module Parsley.Internal.Frontend.Analysis.Liveness (livenessAnalysis, tagCombinator, buildCFG) where
import Data.Set (Set)
import Parsley.Internal.Common (Fix(..), MonadFresh (..), intercalateDiff, HFresh)
import Parsley.Internal.Core.CombinatorAST (Combinator(..), PosSelector (..))
import Data.Kind (Type)
import qualified Data.Map as M
import qualified Data.Dependent.Map as DM
import Parsley.Internal.Backend.Machine.Identifiers (MVar, SomeΣVar (SomeΣVar))
import Parsley.Internal.Common.Fresh (runFresh)
import Parsley.Internal.Core.Identifiers (SomeΣVar)
import Control.Monad.ST.Lazy (ST, runST)
import Parsley.Internal.Common.Indexed (Const1(..), cata, IFunctor(..))
import Data.STRef.Lazy (STRef, newSTRef)
import Control.Monad.Fix (fix)
import Control.Monad (when)
import qualified Data.Set as Set
import Control.Monad.State (State(..), get, put, runState)
import Data.Foldable (sequenceA_)
import qualified Debug.Trace as Debug

-- Auxilary types used in the internal orchestration of CFG creation
type NodeID = Integer
-- CFG data of CFG <start node> <set of leaf nodes> <node -> (use, def, successors)>)
data CFG = CFG NodeID (Set NodeID) (M.Map NodeID (Set SomeΣVar, Set SomeΣVar, Set.Set NodeID)) deriving stock Show

-- Make it possible to merge two CFGs together with left-biased choice of start node

data Tag t f (k :: Type -> Type) a = Tag {tag :: t, tagged :: f k a}
instance IFunctor f => IFunctor (Tag t f) where
  imap f (Tag t k) = Tag t (imap f k)


data LivenessData = LivenessData { liveIn :: Set SomeΣVar, liveOut :: Set SomeΣVar } deriving stock Show
type LivenessAnalysisResult = M.Map NodeID LivenessData
type TaggedCombinator = Tag NodeID Combinator

instance Show (Fix TaggedCombinator a) where
  show = ($ "") . getConst1 . cata (Const1 . alg)
    where
      alg (Tag t (Pure x))                                  = "{" . shows t . "} pure " . shows x
      alg (Tag t (Satisfy f))                               = "{" . shows t . "} satisfy " . shows f
      alg (Tag t (Const1 pf :<*>: Const1 px))               = "{" . shows t . "} (" . pf . " <*> " .  px . ")"
      alg (Tag t (Const1 p :*>: Const1 q))                  = "{" . shows t . "} (" . p . " *> " . q . ")"
      alg (Tag t (Const1 p :<*: Const1 q))                  = "{" . shows t . "} (" . p . " <* " . q . ")"
      alg (Tag t (Const1 p :<|>: Const1 q))                 = "{" . shows t . "} (" . p . " <|> " . q . ")"
      alg (Tag t Empty)                                     = "{" . shows t . "} empty"
      alg (Tag t (Try (Const1 p)))                          = "{" . shows t . "} try (". p . ")"
      alg (Tag t (LookAhead (Const1 p)))                    = "{" . shows t . "} lookAhead (" . p . ")"
      alg (Tag t (Let v))                                   = "{" . shows t . "} let-bound " . shows v
      alg (Tag t (NotFollowedBy (Const1 p)))                = "{" . shows t . "} notFollowedBy (" . p . ")"
      alg (Tag t (Branch (Const1 b) (Const1 p) (Const1 q))) = "{" . shows t . "} branch (" . b . ") (" . p . ") (" . q . ")"
      alg (Tag t (Match (Const1 p) fs qs (Const1 def)))     = "{" . shows t . "} match (" . p . ") " . shows fs . " [" . intercalateDiff ", " (map getConst1 qs) . "] ("  . def . ")"
      alg (Tag t (Loop (Const1 body) (Const1 exit)))        = "{" . shows t . "} loop (" . body . ") (" . exit . ")"
      alg (Tag t (MakeRegister σ (Const1 p) (Const1 q)))    = "{" . shows t . "} make " . shows σ . " (" . p . ") (" . q . ")"
      alg (Tag t (GetRegister σ))                           = "{" . shows t . "} get " . shows σ
      alg (Tag t (PutRegister σ (Const1 p)))                = "{" . shows t . "} put " . shows σ . " (" . p . ")"
      alg (Tag t (Position Line))                           = "{" . shows t . "} line"
      alg (Tag t (Position Col))                            = "{" . shows t . "} col"
      alg (Tag t (Debug _ (Const1 p)))                      = p
      alg (Tag t (MetaCombinator m (Const1 p)))             = p . " [" . shows m . "]"

{-| 
Given a forest of parsers, compute the liveIn and liveOut for each Combinator AST node and tag them with it. 
-}
livenessAnalysis :: Fix Combinator a -> DM.DMap MVar (Fix Combinator) -> LivenessAnalysisResult
livenessAnalysis p ms = snd . fst $ flip runState (False, initSets)  $ do
        fix $ \loop -> do
            (_, m) <- get
            put (False, m)
            Debug.trace ("Round : " ++ show cfg)  $ round cfg
            (change, _) <- get
            when change loop
        get
    where
        initSets :: LivenessAnalysisResult
        initSets = M.fromList [(i, LivenessData Set.empty Set.empty) | i <- [0..(maxID -1)]]
        (pTagged, msTagged, maxID) = tagCombinator p ms

        cfg = buildCFG pTagged msTagged

        round :: CFG -> State (Bool, LivenessAnalysisResult) ()
        round (CFG _ _ m) = sequenceA_ (M.mapWithKey update m)

        update :: NodeID -> (Set SomeΣVar, Set SomeΣVar, Set NodeID) -> State (Bool, LivenessAnalysisResult) ()
        update t (use, def, succ) = do
            (change, m) <- get
            let curr = m M.! t
            let liveIn' = Debug.trace ("use"  ++ show t  ++":" ++  show use) $ Set.union use (Set.difference (liveOut curr) def)
            let liveOut' = Set.foldl (\l s -> Set.union l $ liveIn (m M.! s)) Set.empty succ
            let mNew = M.adjust (\_ -> LivenessData liveIn' liveOut') t m
            when (liveIn curr /= liveIn' || liveOut curr /= liveOut') $ put (True, mNew)



buildCFG :: Fix TaggedCombinator a -> DM.DMap MVar (Fix TaggedCombinator) -> CFG
buildCFG p mus = DM.foldlWithKey (\(CFG s ts m1) _ v -> let CFG _ _ m2 = graph v in CFG s ts (mergeEdges m1 m2)) (graph p) mus
    where
        -- 1. Find for each tree in our CAST the initial tag that will be the root of that CFG. We optimistically cull non-effectual combinators
        findEntryTag :: Fix TaggedCombinator a -> NodeID
        findEntryTag (In Tag{tag=t, tagged=taggedP}) = go t taggedP
            where
                go :: NodeID -> Combinator (Fix TaggedCombinator) a -> NodeID
                go _ (p :*>: _) = findEntryTag p
                go _ (p :<*: _) = findEntryTag p
                go _ (Try p) = findEntryTag p
                go _ (LookAhead p) = findEntryTag p
                go _ (NotFollowedBy p) = findEntryTag p
                go _ (Branch p _ _) = findEntryTag p
                go _ (Match p _ _ _) = findEntryTag p
                go _ (Loop p _) = findEntryTag p
                go _ (Debug _ p) = findEntryTag p
                go _ (MetaCombinator _ p) = findEntryTag p
                -- All other cases, the initial tag is not deeper into the tree
                go t _ = t

        -- Various helpers in our CFG construction
        mergeEdges :: M.Map NodeID (Set SomeΣVar, Set SomeΣVar, Set NodeID) -> M.Map NodeID (Set SomeΣVar, Set SomeΣVar, Set NodeID) -> M.Map NodeID (Set SomeΣVar, Set SomeΣVar, Set NodeID)
        mergeEdges = M.unionWith (\(use, def, x) (_, _, y) -> (use, def, Set.union x y))

        addEdge ::  NodeID -> NodeID -> M.Map NodeID (Set SomeΣVar, Set SomeΣVar, Set NodeID) ->  M.Map NodeID (Set SomeΣVar, Set SomeΣVar, Set NodeID)
        addEdge v w =  M.adjust (\(use, def, edges) -> (use, def, Set.insert w edges)) v

        -- seqCFG: take CFGs G and H, joining all control paths from terminals of G to start of H 
        seqCFG (CFG s1 t1 m1) (CFG s2 t2 m2) = CFG s1 t2 (Set.foldl (flip (M.adjust (\(u, d, s) -> (u, d, Set.insert s2 s)))) m t1)
            where
                m = mergeEdges m1 m2

        -- 2. Main entry point for creating a CFG for a given tagged CAST. Recurse through tree and construct 
        graph :: Fix TaggedCombinator a -> CFG
        graph (In Tag{tag, tagged})= graph' tag tagged

        leaf :: NodeID -> CFG
        leaf t = CFG t (Set.singleton t) (M.fromList [(t, (Set.empty, Set.empty, Set.empty))])

        -- Handle each node type in our CAST. Optimistically cull any tags that are purely transitionary (e.g. tagged metacombinators)
        graph' :: NodeID -> Combinator (Fix TaggedCombinator) a ->  CFG
        graph' _ (pf :<*>: px) = graph pf `seqCFG` graph px
        graph' _ (p :*>: q) =  graph p `seqCFG` graph q
        graph' _ (p :<*: q) = graph p `seqCFG` graph q
        graph' t (p :<|>: q) = let
             CFG ps pts mp = graph p
             CFG qs qts mq = graph q
             m = mp `mergeEdges` mq
             in CFG t (Set.union pts qts) (addEdge t qs (addEdge t ps m))
        graph' _ (Try p) = graph p
        graph' _ (LookAhead p) = graph p
        graph' t (Let mvar) = leaf t
        graph' _ (NotFollowedBy p) = graph p
        graph' _ (Branch b p q) = let
             CFG bs bts mb = graph b
             CFG ps pts mp = graph p
             CFG qs qts mq = graph q
             m = mb `mergeEdges` mp `mergeEdges` mq
             m' = Set.foldl (\x n -> addEdge n qs (addEdge n ps x)) m bts
             in CFG bs (Set.union pts qts) m'
        graph' _ (Match p fs qs def) = undefined -- TODO: implement
        graph' _ (Loop body exit) = let
            CFG bs bts bm = graph body
            CFG es ets em = graph exit
            m = bm `mergeEdges` em
            m' = Set.foldl (\x n -> addEdge n es x) m bts -- add exit edges
            m'' = Set.foldl (\x n -> addEdge n bs x) m' bts -- add loopback edges
            in CFG bs ets m''
        graph' t (MakeRegister σ p q) = let
            -- leaf node that just defines σ 
            g = CFG t (Set.singleton t) (M.fromList [(t, (Set.empty, Set.singleton $ SomeΣVar σ, Set.empty))])
            in graph p `seqCFG` g `seqCFG` graph q
        graph' t (GetRegister σ) = CFG t (Set.singleton t) (M.fromList [(t, (Set.singleton $ SomeΣVar σ, Set.empty, Set.empty))])
        graph' t (PutRegister σ p) = let
            g = CFG t (Set.singleton t) (M.fromList [(t, (Set.empty, Set.singleton $ SomeΣVar σ, Set.empty))])
            in graph p `seqCFG` g
        graph' t (Position _) = leaf t
        graph' _ (Debug _ p) = graph p -- skip annotational combinator
        graph' _ (MetaCombinator _ p) = graph p -- skip annotational combinator 
        graph' t Empty = leaf t
        -- left-over dead-end cases: Pure, Satisfy 
        graph' t _ = leaf t


{-|
Tag every node of the parser AST with a unique identifier of type `NodeID`. Returns tagged forest and max `NodeID` assigned.
-}
tagCombinator :: Fix Combinator a -> DM.DMap MVar (Fix Combinator) ->  (Fix TaggedCombinator a, DM.DMap MVar (Fix TaggedCombinator), NodeID)
tagCombinator p ps = (a, b, maxV')
    where
        init = 0
        (a, maxV) = runFresh (tagCombinatorNodes p) init
        (b, maxV') = runFresh (DM.traverseWithKey (\_ a -> tagCombinatorNodes a) ps) (succ maxV)

wrap p = newVar >>= (\t -> return $ In (Tag t p))

tagCombinatorNodes :: forall a. Fix Combinator a -> HFresh NodeID (Fix TaggedCombinator a)
tagCombinatorNodes (In (Pure x)) = wrap (Pure x)
tagCombinatorNodes (In (Satisfy f)) = wrap (Satisfy f)
tagCombinatorNodes (In Empty) = wrap Empty
tagCombinatorNodes (In (pf :<*>: px)) = do
    pft <- tagCombinatorNodes pf
    pxt <- tagCombinatorNodes px
    wrap (pft :<*>: pxt)
tagCombinatorNodes (In (p :*>: q) ) = do
    pt <- tagCombinatorNodes p
    qt <- tagCombinatorNodes q
    wrap (pt :*>: qt)
tagCombinatorNodes (In (p :<*: q) ) = do
    pt <- tagCombinatorNodes p
    qt <- tagCombinatorNodes q
    wrap (pt :<*: qt)
tagCombinatorNodes (In (p :<|>: q) ) = do
    pt <- tagCombinatorNodes p
    qt <- tagCombinatorNodes q
    wrap (pt :<|>: qt)
tagCombinatorNodes (In (Try p)) = tagCombinatorNodes p >>= wrap . Try
tagCombinatorNodes (In (LookAhead p)) = tagCombinatorNodes p >>= wrap . LookAhead
tagCombinatorNodes (In (Let v)) = wrap (Let v)
tagCombinatorNodes (In (NotFollowedBy p)) = tagCombinatorNodes p >>= wrap . NotFollowedBy
tagCombinatorNodes (In (Branch b p q)) = do
    bt <- tagCombinatorNodes b
    pt <- tagCombinatorNodes p
    qt <- tagCombinatorNodes q
    wrap (Branch bt pt qt)
tagCombinatorNodes (In (Match p fs qs def)) = do
    pt <- tagCombinatorNodes p
    qst <- traverse tagCombinatorNodes qs
    deft <- tagCombinatorNodes def
    wrap (Match pt fs qst deft)
tagCombinatorNodes (In (Loop body exit)) = do
    bodyt <- tagCombinatorNodes body
    exitt <- tagCombinatorNodes exit
    wrap (Loop bodyt exitt)
tagCombinatorNodes (In (MakeRegister σ p q)) =  do
    pt <- tagCombinatorNodes p
    qt <- tagCombinatorNodes q
    wrap (MakeRegister σ pt qt)
tagCombinatorNodes (In (GetRegister σ)) = wrap (GetRegister σ)
tagCombinatorNodes (In (PutRegister σ p)) = do
    pt <- tagCombinatorNodes p
    wrap (PutRegister σ pt)
tagCombinatorNodes (In (Position p)) = wrap (Position p)
tagCombinatorNodes (In (Debug d p)) = tagCombinatorNodes p >>= (wrap . Debug d)
tagCombinatorNodes (In (MetaCombinator m p)) = tagCombinatorNodes p >>= (wrap . MetaCombinator m)