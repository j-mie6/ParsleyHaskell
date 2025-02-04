{-# LANGUAGE OverloadedStrings, DerivingStrategies #-}
{-# LANGUAGE NamedFieldPuns #-}

module Parsley.Internal.Frontend.Analysis.CFG (TaggedCombinator, NodeID, CFG(..), ΣNodeData(..), tagCombinator, buildCFG) where

import Parsley.Internal.Common.Indexed (Const1(..), cata, Tag(..), Fix (..))
import Data.Set (Set)
import Parsley.Internal.Core.CombinatorAST (Combinator (..), PosSelector (..))
import Parsley.Internal.Core.Identifiers (MVar(..), SomeΣVar(..), IMVar)
import Data.DList (DList)
import Parsley.Internal.Common (HFresh, intercalateDiff, MonadFresh(..), runFresh)
import qualified Data.DList as DList
import qualified Data.Map as M
import qualified Data.Set as Set
import qualified Data.Dependent.Map as DM

{-| 
    Type of the identifier given to nodes in `TaggedCombinator`. Used to uniquely identify each node
-}
type NodeID = Integer

{-|
    CFG data of CFG <start node> <set of leaf nodes> <node -> (NodeData, successors)>) 
-}
data CFG = CFG NodeID (Set NodeID) (M.Map NodeID (Maybe ΣNodeData, Set.Set NodeID)) deriving stock Show

{-| 
    Meta-data attached to a node that interfaces with ΣVars. 
-}
data ΣNodeData = ΣMake {use :: Set.Set SomeΣVar, which :: SomeΣVar}
              | ΣGet  {use :: Set.Set SomeΣVar, which :: SomeΣVar}
              | ΣPut  {use :: Set.Set SomeΣVar, which :: SomeΣVar} deriving stock Show

{-|
    A Combinator AST with every node tagged with `NodeID`. All `NodeID` tags ought to be unique and this is promised by `tagCombinator`
-}
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
      alg (Tag t (Debug _ (Const1 p)))                      = "{" . shows t . "} " . p
      alg (Tag t (MetaCombinator m (Const1 p)))             =  "{" . shows t . "} " .p . " [" . shows m . "]"

buildCFG :: Fix TaggedCombinator a -> DM.DMap MVar (Fix TaggedCombinator) -> CFG
buildCFG p mus = cfg
    where
        -- a. Create CFGs for each let-bound AST
        (initCFG, initCalls) = graph p
        (cfgForest, calls) = DM.foldlWithKey
                                (\(m, c) (MVar imvar) p ->
                                        let
                                            (cfg', calls') = graph p
                                        in (M.insert imvar cfg' m, c <> calls'))
                                        (M.empty, mempty)
                                        mus
        -- b. join all trees into one
        cfgWithoutCalls = M.foldl mergeCFG initCFG cfgForest
        -- c. join all calls (callNode, imvar) within the cfg forest to a single cfg
        cfg = foldl (\c (callNode, imvar) ->
                        let CFG start terms _ = cfgForest M.! imvar
                        in addEdge' callNode start $ foldr (`addEdge'` callNode) c terms
                    ) cfgWithoutCalls (initCalls <> calls)

        -- Various helpers in our CFG construction
        mergeEdges :: M.Map NodeID (Maybe ΣNodeData, Set.Set NodeID) -> M.Map NodeID (Maybe ΣNodeData, Set.Set NodeID) -> M.Map NodeID (Maybe ΣNodeData, Set.Set NodeID)
        mergeEdges = M.unionWith (\(info, x) (_, y) -> (info, Set.union x y))
        -- Merge CFGs using left-biased determintion of starting and terminal nodes
        mergeCFG :: CFG -> CFG -> CFG
        mergeCFG (CFG s1 t1 m1) (CFG _ _ m2) = CFG s1 t1 (mergeEdges m1 m2)
        addEdge ::  NodeID -> NodeID ->M.Map NodeID (Maybe ΣNodeData, Set.Set NodeID) -> M.Map NodeID (Maybe ΣNodeData, Set.Set NodeID)
        addEdge v w =  M.adjust (\(info, edges) -> (info, Set.insert w edges)) v
        addEdge' ::  NodeID -> NodeID -> CFG -> CFG
        addEdge' v w (CFG a b m) = CFG a b (addEdge v w m)

        -- seqCFG: take CFGs G and H, joining all control paths from terminals of G to start of H 
        seqCFG (CFG s1 t1 m1) (CFG s2 t2 m2) = CFG s1 t2 (Set.foldl (flip (M.adjust (\(info, s) -> (info, Set.insert s2 s)))) m t1)
            where
                m = mergeEdges m1 m2


        -- Main entry point for creating a CFG for a given tagged CAST. Recurse through tree and construct the CFG. 
        -- We do this inside `Writer` monad because we need to keep track of `Let` nodes that perform a call to 
        graph :: Fix TaggedCombinator a -> (CFG, DList (NodeID, IMVar))
        graph (In Tag{tag, tagged})= graph' tag tagged

        leaf :: NodeID -> CFG
        leaf t = CFG t (Set.singleton t) (M.fromList [(t, (Nothing, Set.empty))])

        -- find uses of any registers in a parser by parsing the use-defs gathereed
        findUsages = M.foldl (\m (info, _) ->
            case info of
                Just x -> m `Set.union` use x `Set.union` Set.singleton (which x)
                Nothing -> m)
            Set.empty

        -- Handle each node type in our CAST. Optimistically cull any tags that are purely transitionary (e.g. tagged metacombinators)       
        graph' :: NodeID -> Combinator (Fix TaggedCombinator) a -> (CFG, DList (NodeID, IMVar))
        graph' _ (pf :<*>: px) = let
            (pfg, calls1) = graph pf
            (pxg, calls2) = graph px
            in (pfg `seqCFG` pxg, calls1 <> calls2)
        graph' _ (p :*>: q) = let
            (pg, calls1) = graph p
            (qg, calls2) = graph q
            in (pg `seqCFG` qg, calls1 <> calls2)
        graph' _ (p :<*: q) = let
            (pg, calls1) = graph p
            (qg, calls2) = graph q
            in (pg `seqCFG` qg, calls1 <> calls2)
        graph' t (p :<|>: q) = let
            -- TODO: currently we add edges for all nodes in p to qs. This is not efficient as we only need edges from nodes that can fail.
            (CFG ps pts mp, calls1) = graph p
            (CFG qs qts mq, calls2) = graph q
            pexits = M.foldlWithKey (\a k(_, x) -> a `Set.union` x `Set.union` Set.singleton k) pts mp
            m = mp `mergeEdges` mq
                   `mergeEdges` M.fromSet (const (Nothing, Set.singleton qs)) pexits -- 
                   `mergeEdges` M.fromList [(t, (Nothing, Set.fromList [qs, ps]))] -- root node to the start of both
            in (CFG t (Set.union pts qts) m, calls1 <> calls2)
        graph' _ (Try p) = graph p
        graph' _ (LookAhead p) = graph p
        graph' t (Let (MVar im)) = (leaf t, DList.fromList [(t, im)])
        graph' _ (NotFollowedBy p) = graph p
        graph' _ (Branch b p q) = let
            (CFG bs bts mb, calls1) = graph b
            (CFG ps pts mp, calls2) = graph p
            (CFG qs qts mq, calls3) = graph q
            m = mb `mergeEdges` mp `mergeEdges` mq
            m' = Set.foldl (\x n -> addEdge n qs (addEdge n ps x)) m bts
            in (CFG bs (Set.union pts qts) m', calls1 <> calls2 <> calls3)
        graph' _ (Match p _ qs def) = let -- TODO: double check this works
            (CFG ps pts mp, callsp) = graph p
            (CFG ds dts md, callsdef) = graph def
            qsGraphs = map graph qs
            qsCalls = map snd qsGraphs
            qsCFGs = map fst qsGraphs
            qsTerminals = foldl (\a (CFG _ t _) -> Set.union t a) Set.empty qsCFGs
            m = foldl (\a (CFG s _ m') -> a `mergeEdges` M.fromSet (const (Nothing, Set.singleton s)) pts `mergeEdges`  m')
                    (M.fromSet (const (Nothing, Set.singleton ds)) pts `mergeEdges` mp `mergeEdges` md) qsCFGs
            in (CFG ps (Set.union qsTerminals dts) m, foldl (<>) callsp qsCalls <> callsdef)
        graph' _ (Loop body exit) = let
            (CFG bs bts bm, calls1) = graph body
            (CFG es ets em, calls2) = graph exit
            m = bm `mergeEdges` em
            -- add exit edges (can be anywhere in the body due to failure)
            bexits = M.foldlWithKey (\a k(_, x) -> a `Set.union` x `Set.union` Set.singleton k) bts bm
            m' = m `mergeEdges` M.fromSet (const (Nothing, Set.singleton es)) bexits 
            m'' = Set.foldl (\x n -> addEdge n bs x) m' bts -- add loopback edges
            in (CFG bs ets m'', calls1 <> calls2)
        graph' t (MakeRegister σ p q) = let
            -- leaf node that just defines σ 
            g = CFG t (Set.singleton t) (M.fromList [(t, (Just $ ΣMake{use=usages, which=SomeΣVar σ}, Set.empty))])
            -- find uses of any registers in `p` by parsing the use-defs gathereed
            usages = findUsages pm
            (gp@(CFG _ _ pm), calls1) = graph p
            (gq, calls2) = graph q
            in (gp `seqCFG` g `seqCFG` gq, calls1 <> calls2)
        graph' t (GetRegister σ) = (CFG t (Set.singleton t) (M.fromList [(t, (Just $ ΣGet{use=Set.singleton $ SomeΣVar σ, which=SomeΣVar σ}, Set.empty))]), mempty)
        graph' t (PutRegister σ p) = let
            g = CFG t (Set.singleton t) (M.fromList [(t, (Just $ ΣPut{use=usages, which=SomeΣVar σ}, Set.empty))])
            -- find uses of any registers in `p` by parsing the use-defs gathereed
            usages = findUsages pm
            (gp@(CFG _ _ pm), calls) = graph p
            in (gp `seqCFG` g, calls)
        graph' t (Position _) = (leaf t, mempty)
        graph' _ (Debug _ p) = graph p -- skip annotational combinator
        graph' _ (MetaCombinator _ p) = graph p -- skip annotational combinator 
        graph' t Empty = (leaf t, mempty)
        -- left-over dead-end cases: Pure, Satisfy 
        graph' t _ = (leaf t, mempty)

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