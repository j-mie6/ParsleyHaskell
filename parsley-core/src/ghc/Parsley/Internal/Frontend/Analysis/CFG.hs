{-# LANGUAGE OverloadedStrings, DerivingStrategies, NamedFieldPuns #-}

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

newtype Grapher a = Grapher { unGraph :: (CFG, DList (NodeID, IMVar)) }

buildCFG :: Fix TaggedCombinator a -> DM.DMap MVar (Fix TaggedCombinator) -> CFG
buildCFG p mus = cfg
    where
        -- a. Create CFGs for each let-bound AST
        makeGraph :: Fix TaggedCombinator a -> (CFG, DList (NodeID, IMVar))
        makeGraph p = unGraph $ cata (Grapher . (\Tag{tag, tagged} -> alg tag tagged)) p 
    
        (initCFG, initCalls) = makeGraph p
        (cfgForest, calls) = DM.foldlWithKey
                                (\(m, c) (MVar imvar) p ->
                                        let
                                            (cfg', calls') = makeGraph p
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


        leaf :: NodeID -> CFG
        leaf t = CFG t (Set.singleton t) (M.fromList [(t, (Nothing, Set.empty))])

        -- find uses of any registers in a parser by parsing the use-defs gathereed
        findUsages = M.foldl (\m (info, _) ->
            case info of
                Just x -> m `Set.union` use x `Set.union` Set.singleton (which x)
                Nothing -> m)
            Set.empty

        -- CFG construction Algebra for what to do for each combinator constructor
        alg :: NodeID -> Combinator Grapher a -> (CFG, DList (NodeID, IMVar))
        alg _ (pf :<*>: px) = let
            (pfg, calls1) = unGraph pf
            (pxg, calls2) = unGraph px
            in (pfg `seqCFG` pxg, calls1 <> calls2)
        alg _ (p :*>: q) = let
            (pg, calls1) = unGraph p
            (qg, calls2) = unGraph q
            in (pg `seqCFG` qg, calls1 <> calls2)
        alg _ (p :<*: q) = let
            (pg, calls1) = unGraph p
            (qg, calls2) = unGraph q
            in (pg `seqCFG` qg, calls1 <> calls2)
        alg t (p :<|>: q) = let
            (CFG ps pts mp, calls1) = unGraph p
            (CFG qs qts mq, calls2) = unGraph q
            pexits = M.foldlWithKey (\a k(_, x) -> a `Set.union` x `Set.union` Set.singleton k) pts mp
            m = mp `mergeEdges` mq
                   `mergeEdges` M.fromSet (const (Nothing, Set.singleton qs)) pexits -- 
                   `mergeEdges` M.fromList [(t, (Nothing, Set.fromList [qs, ps]))] -- root node to the start of both
            in (CFG t (Set.union pts qts) m, calls1 <> calls2)
        alg _ (Try p) = unGraph p
        alg _ (LookAhead p) = unGraph p
        alg t (Let (MVar im)) = (leaf t, DList.fromList [(t, im)])
        alg _ (NotFollowedBy p) = unGraph p
        alg _ (Branch b p q) = let
            (CFG bs bts mb, calls1) = unGraph b
            (CFG ps pts mp, calls2) = unGraph p
            (CFG qs qts mq, calls3) = unGraph q
            m = mb `mergeEdges` mp `mergeEdges` mq
            m' = Set.foldl (\x n -> addEdge n qs (addEdge n ps x)) m bts
            in (CFG bs (Set.union pts qts) m', calls1 <> calls2 <> calls3)
        alg _ (Match p _ qs def) = let
            (CFG ps pts mp, callsp) = unGraph p
            (CFG ds dts md, callsdef) = unGraph def
            qsGraphs = map unGraph qs
            qsCalls = map snd qsGraphs
            qsCFGs = map fst qsGraphs
            qsTerminals = foldl (\a (CFG _ t _) -> Set.union t a) Set.empty qsCFGs
            m = foldl (\a (CFG s _ m') -> a `mergeEdges` M.fromSet (const (Nothing, Set.singleton s)) pts `mergeEdges`  m')
                    (M.fromSet (const (Nothing, Set.singleton ds)) pts `mergeEdges` mp `mergeEdges` md) qsCFGs
            in (CFG ps (Set.union qsTerminals dts) m, foldl (<>) callsp qsCalls <> callsdef)
        alg _ (Loop body exit) = let
            (CFG bs bts bm, calls1) = unGraph body
            (CFG es ets em, calls2) = unGraph exit
            m = bm `mergeEdges` em
            -- add exit edges (can be anywhere in the body due to failure)
            bexits = M.foldlWithKey (\a k(_, x) -> a `Set.union` x `Set.union` Set.singleton k) bts bm
            m' = m `mergeEdges` M.fromSet (const (Nothing, Set.singleton es)) bexits 
            m'' = Set.foldl (\x n -> addEdge n bs x) m' bts -- add loopback edges
            in (CFG bs ets m'', calls1 <> calls2)
        alg t (MakeRegister σ p q) = let
            -- leaf node that just defines σ 
            g = CFG t (Set.singleton t) (M.fromList [(t, (Just $ ΣMake{use=usages, which=SomeΣVar σ}, Set.empty))])
            -- find uses of any registers in `p` by parsing the use-defs gathereed
            usages = findUsages pm
            (gp@(CFG _ _ pm), calls1) = unGraph p
            (gq, calls2) = unGraph q
            in (gp `seqCFG` g `seqCFG` gq, calls1 <> calls2)
        alg t (GetRegister σ) = (CFG t (Set.singleton t) (M.fromList [(t, (Just $ ΣGet{use=Set.singleton $ SomeΣVar σ, which=SomeΣVar σ}, Set.empty))]), mempty)
        alg t (PutRegister σ p) = let
            g = CFG t (Set.singleton t) (M.fromList [(t, (Just $ ΣPut{use=usages, which=SomeΣVar σ}, Set.empty))])
            -- find uses of any registers in `p` by parsing the use-defs gathereed
            usages = findUsages pm
            (gp@(CFG _ _ pm), calls) = unGraph p
            in (gp `seqCFG` g, calls)
        alg t (Position _) = (leaf t, mempty)
        alg _ (Debug _ p) = unGraph p -- skip annotational combinator
        alg _ (MetaCombinator _ p) = unGraph p -- skip annotational combinator 
        alg t Empty = (leaf t, mempty)
        -- left-over dead-end cases: Pure, Satisfy 
        alg t _ = (leaf t, mempty)

{-|
Tag every node of the parser AST with a unique identifier of type `NodeID`. Returns tagged forest and max `NodeID` assigned.
-}
tagCombinator :: Fix Combinator a -> DM.DMap MVar (Fix Combinator) ->  (Fix TaggedCombinator a, DM.DMap MVar (Fix TaggedCombinator), NodeID)
tagCombinator p ps = (a, b, maxV')
    where
        init = 0
        (a, maxV) = runFresh (tagCombinatorNodes p) init
        (b, maxV') = runFresh (DM.traverseWithKey (\_ a -> tagCombinatorNodes a) ps) (succ maxV)

newtype Tagger a = Tagger { unTagger :: HFresh NodeID (Fix TaggedCombinator a) }

tagCombinatorNodes :: forall a. Fix Combinator a -> HFresh NodeID (Fix TaggedCombinator a)
tagCombinatorNodes ast = unTagger $ cata (Tagger . alg) ast
    where 
        wrap p = newVar >>= (\t -> return $ In (Tag t p))

        alg :: forall a. Combinator Tagger a -> HFresh NodeID (Fix TaggedCombinator a)
        alg (Pure x)             = wrap (Pure x)
        alg (Satisfy f)          = wrap (Satisfy f)
        alg Empty                = wrap Empty
        alg (pf :<*>: px)        = do
                                    pft <- unTagger pf
                                    pxt <- unTagger px
                                    wrap (pft :<*>: pxt)
        alg (p :*>: q)           = do
                                    pt <- unTagger p
                                    qt <- unTagger q
                                    wrap (pt :*>: qt)
        alg (p :<*: q)           = do
                                    pt <- unTagger p
                                    qt <- unTagger q
                                    wrap (pt :<*: qt)
        alg (p :<|>: q)          = do
                                    pt <- unTagger p
                                    qt <- unTagger q
                                    wrap (pt :<|>: qt)
        alg (Try p)              = unTagger p >>= wrap . Try
        alg (LookAhead p)        = unTagger p >>= wrap . LookAhead
        alg (Let v)              = wrap (Let v)
        alg (NotFollowedBy p)    = unTagger p >>= wrap . NotFollowedBy
        alg (Branch b p q)       = do
                                    bt <- unTagger b
                                    pt <- unTagger p
                                    qt <- unTagger q
                                    wrap (Branch bt pt qt)
        alg (Match p fs qs def)  = do
                                    pt <- unTagger p
                                    qst <- traverse unTagger qs
                                    deft <- unTagger def
                                    wrap (Match pt fs qst deft)
        alg (Loop body exit)     = do
                                    bodyt <- unTagger body
                                    exitt <- unTagger exit
                                    wrap (Loop bodyt exitt)
        alg (MakeRegister σ p q) = do
                                    pt <- unTagger p
                                    qt <- unTagger q
                                    wrap (MakeRegister σ pt qt)
        alg (GetRegister σ)      = wrap (GetRegister σ)
        alg (PutRegister σ p)    = unTagger p >>= wrap . PutRegister σ
        alg (Position p)         = wrap (Position p)
        alg (Debug d p)          = unTagger p >>= (wrap . Debug d)
        alg (MetaCombinator m p) = unTagger p >>= (wrap . MetaCombinator m)