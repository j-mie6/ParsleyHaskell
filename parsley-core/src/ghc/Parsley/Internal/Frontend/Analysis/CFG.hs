{-# LANGUAGE OverloadedStrings, DerivingStrategies, NamedFieldPuns #-}

module Parsley.Internal.Frontend.Analysis.CFG (TaggedCombinator, NodeID, CFG(..), ΣNodeData(..), tagCombinator, buildCFG) where

import Parsley.Internal.Common.Indexed     (cata, Tag(..), Fix (..))
import Parsley.Internal.Core.CombinatorAST (Combinator (..))
import Parsley.Internal.Core.Identifiers   (MVar(..), SomeΣVar(..), IMVar)
import Parsley.Internal.Common             (HFresh, MonadFresh(..), runFresh)
import Control.Monad.Writer                (Writer, MonadWriter (..), runWriter)
import Control.Applicative                 (liftA2)
import Data.Functor                        (($>))

import Data.DList (DList)
import qualified Data.DList as DList
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DM

{-| 
    Type of the identifier given to nodes in `TaggedCombinator`. Used to uniquely identify each node
-}
type NodeID = Integer

{-|
    CFG data of CFG <start node> <set of leaf nodes> <node -> (NodeData, successors)>) 
-}
data CFG = CFG {start :: NodeID, leaves :: Set NodeID, usedef :: Map NodeID (Maybe ΣNodeData, Set.Set NodeID)} deriving stock Show

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

newtype Grapher a = Grapher { unGraph :: Writer (DList (NodeID, IMVar)) CFG }

buildCFG :: Fix TaggedCombinator a -> DM.DMap MVar (Fix TaggedCombinator) -> CFG
buildCFG p mus = cfg
    where
        -- a. Create CFGs for each let-bound AST
        makeGraph :: Fix TaggedCombinator a -> (CFG, DList (NodeID, IMVar))
        makeGraph p = runWriter $ unGraph $ cata (Grapher . (\Tag{tag, tagged} -> alg tag tagged)) p 
    
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
        alg :: NodeID -> Combinator Grapher a -> Writer (DList (NodeID, IMVar)) CFG
        alg _ (pf :<*>: px) = liftA2 seqCFG (unGraph pf) (unGraph px)
        alg _ (p :*>: q) = liftA2 seqCFG (unGraph p) (unGraph q)
        alg _ (p :<*: q) = do
            pg <- unGraph p
            qg <- unGraph q
            return $ pg `seqCFG` qg
        alg t (p :<|>: q) = do
            CFG ps pts mp <- unGraph p
            CFG qs qts mq <- unGraph q
            let pexits = M.foldlWithKey (\a k(_, x) -> a `Set.union` x `Set.union` Set.singleton k) pts mp
            let m = mp `mergeEdges` mq
                   `mergeEdges` M.fromSet (const (Nothing, Set.singleton qs)) pexits
                   `mergeEdges` M.fromList [(t, (Nothing, Set.fromList [qs, ps]))] -- root node to the start of both
            return $ CFG t (Set.union pts qts) m
        alg _ (Try p) = unGraph p
        alg _ (LookAhead p) = unGraph p
        alg t (Let (MVar im)) = tell (DList.singleton (t,im)) $> leaf t
        alg _ (NotFollowedBy p) = unGraph p
        alg _ (Branch b p q) = do 
            CFG bs bts mb <- unGraph b
            CFG ps pts mp <- unGraph p
            CFG qs qts mq <- unGraph q
            let m = mb `mergeEdges` mp `mergeEdges` mq
            let m' = Set.foldl (\x n -> addEdge n qs (addEdge n ps x)) m bts
            return $ CFG bs (Set.union pts qts) m'
        alg _ (Match p _ qs def) = do
            CFG ps pts mp <- unGraph p
            CFG ds dts md <- unGraph def
            qsGraphs      <- traverse unGraph qs
            let qsTerminals = foldl (\a (CFG _ t _) -> Set.union t a) Set.empty qsGraphs
            let m = foldl (\a (CFG s _ m') -> a `mergeEdges` M.fromSet (const (Nothing, Set.singleton s)) pts `mergeEdges`  m')
                    (M.fromSet (const (Nothing, Set.singleton ds)) pts `mergeEdges` mp `mergeEdges` md) qsGraphs
            return $ CFG ps (Set.union qsTerminals dts) m
        alg _ (Loop body exit) = do
            CFG bs bts bm <- unGraph body
            CFG es ets em <- unGraph exit
            let m = bm `mergeEdges` em
            -- add exit edges (can be anywhere in the body due to failure)
            let bexits = M.foldlWithKey (\a k(_, x) -> a `Set.union` x `Set.union` Set.singleton k) bts bm
            let m' = m `mergeEdges` M.fromSet (const (Nothing, Set.singleton es)) bexits 
            let m'' = Set.foldl (\x n -> addEdge n bs x) m' bts -- add loopback edges
            return $ CFG bs ets m''
        alg t (MakeRegister σ p q) = do
            gp@(CFG _ _ pm) <-  unGraph p
            let usages = findUsages pm
            -- leaf node that just defines σ 
            let g = CFG t (Set.singleton t) (M.fromList [(t, (Just $ ΣMake{use=usages, which=SomeΣVar σ}, Set.empty))])
            gq <- unGraph q
            return $ gp `seqCFG` g `seqCFG` gq
        alg t (GetRegister σ) = pure $ CFG t (Set.singleton t) (M.fromList [(t, (Just $ ΣGet{use=Set.singleton $ SomeΣVar σ, which=SomeΣVar σ}, Set.empty))])
        alg t (PutRegister σ p) = do
            gp@(CFG _ _ pm) <- unGraph p
            let usages = findUsages pm
            let g = CFG t (Set.singleton t) (M.fromList [(t, (Just $ ΣPut{use=usages, which=SomeΣVar σ}, Set.empty))])
            return $ gp `seqCFG` g
        alg t (Position _) = pure $ leaf t
        alg _ (Debug _ p) = unGraph p
        alg _ (MetaCombinator _ p) = unGraph p
        alg t Empty = pure $ leaf t
        -- left-over dead-end cases
        alg t _ = pure $ leaf t
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