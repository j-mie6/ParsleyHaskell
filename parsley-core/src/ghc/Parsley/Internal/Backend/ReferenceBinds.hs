{-# LANGUAGE 
            NamedFieldPuns, 
            OverloadedStrings,
            ImplicitParams, 
            DerivingStrategies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-|
Module      : Parsley.Internal.Backend.Analysis.ReferenceBinds
Description : Translation of Combinator AST into Machine
License     : BSD-3-Clause
Maintainer  : TBD
Stability   : experimental

This module exports an optimisation pass `bindReferences` that will attach `MetaInstr`s for each return continuation, join points, handler
telling which references might live through that code element. This allows for the full tenderisation of registers
by making every reference access `Soft`. 

The determination of free references at each point is much alike to the algorithm performed in `Parsley.Internal.Frontend.Analysis.Dependencies`.

-}
module Parsley.Internal.Backend.ReferenceBinds (bindReferences) where

import Parsley.Internal.Opt (Flags (totalReferenceBinds))
import Parsley.Internal.Trace (Trace)
import Parsley.Internal.Backend.Machine.LetBindings (LetBinding (..))
import Parsley.Internal.Common (One)
import Parsley.Internal.Common.Fresh (HFresh, MonadFresh(..), runFresh)
import Parsley.Internal.Common.Indexed (Fix4, IFunctor4, Fix4(..), Const4(..), cata4, IFunctor4(imap4))
import Parsley.Internal.Common.Utils (intercalateDiff)
import Parsley.Internal.Backend.Machine (Input, ΣVar, Access (..))
import Parsley.Internal.Backend.Machine.Identifiers (SomeΣVar(..), IΦVar, ΦVar(..), IMVar, MVar (..))
import Parsley.Internal.Backend.Machine.Instructions (Instr(..), Handler(..), PosSelector(..), MetaInstr(..))
import Parsley.Internal.Backend.Machine.Types.Registers (makeRegs)

import Control.Monad.Writer (Writer, MonadWriter (..))
import Control.Monad.Writer.Lazy (runWriter)
import Control.Monad.State (StateT (..), MonadTrans (..), MonadState (..), when, evalState)
import Control.Monad.State.Lazy (State)
import Control.Monad.State (gets, execState)
import Control.Monad (unless)

import Debug.Trace (trace)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Void (Void)

import qualified Data.Dependent.Map as DMap
import Data.Dependent.Map (DMap)
import Parsley.Internal.Backend.Machine (ΣVar(..))


{-|
`bindReferences` performs global analysis on the forest of let-bound parsers and turns as many references
into bound variables as possible. 
-}
bindReferences :: forall input a. (Input input, Trace, ?flags::Flags) => (LetBinding input a a, DMap MVar (LetBinding input a)) -> (LetBinding input a a, DMap MVar (LetBinding input a))
bindReferences (p, μs)
    | totalReferenceBinds ?flags  = trace traceString (pOptimised, μsOptimised)
    | otherwise = (p, μs)
    where
        
        -- debugging purposes. TODO: remove in final code
        traceString = "MACHINES:\n" ++ tagTrace ++ "\nGRAPH (starting at " ++ show (start cfg) ++ "): \n" ++ show (unGraph $ graph cfg)
                    ++ "\nUSE-DEFS: \n" ++ show (useDefs cfg)
        tagTrace = DMap.foldlWithKey (\s k b -> s ++ "\n    let-bound " ++ show k ++ " => " ++ show (taggedBody b) ) ("    top-level    => " ++ show pTagged) μsTagged

        -- 1. Tag every instruction with a unique identifier
        (pTagged, maxV) = tagInstructions 0 (body p)
        (μsTagged, maxV') = DMap.foldlWithKey (\(m, max) μ p -> let (tagged, max') = tagInstructions max (body p)
                                                            in (DMap.insert μ (TaggedBinding tagged) m, max'))
                                                            (DMap.empty :: DMap MVar (TaggedBinding input a), maxV) μs

        -- 2. create CFG of the whole forest of machines 
        cfg = constructCFG (TaggedBinding pTagged, μsTagged)

        -- 3. generate map tag -> set of free registers that are used later in control-flow
        frees = freeRegisters maxV' cfg

        -- 4. Mark loop bodies
        mvars = DMap.foldlWithKey (\s (MVar m) _ -> Set.insert m s) Set.empty μs
        pTagged' = TaggedBinding $ markLoopBodies mvars frees pTagged
        μsTagged' = DMap.map (\x -> TaggedBinding $ markLoopBodies mvars frees (taggedBody x)) μsTagged

        -- 5. Unwrap tags, reattach freeRegs and meta of original bind
        rewrap :: MVar x -> Fix4 (Instr input) '[] One x a -> LetBinding input a x
        rewrap μ new = let old = μs DMap.! μ in old {body = new}
        pOptimised = p {body = unTag $ taggedBody pTagged'}
        μsOptimised = DMap.mapWithKey (\m a -> rewrap m (unTag $ taggedBody a) ) μsTagged' 
        

-- Tagging Instructions

-- We need to tag each instruction with a unique ID so we can perform liveness analysis
data Tag4 t f k xs n r a = Tag4 {tag :: t, tagged :: f k xs n r a} deriving stock Show
instance IFunctor4 f => IFunctor4 (Tag4 t f) where
    imap4 f Tag4{tag, tagged} = Tag4 tag (imap4 f tagged)

{-|
Type which we use to tag each instruction with
-}
type InstrID = Int

{-|
Type synonym to help work with wrapping instructions in Tags
-}
type TaggedInstr a = Tag4 InstrID (Instr a)

-- Just a helper type for working with `DMap`
data TaggedBinding o a x = TaggedBinding { taggedBody :: Fix4 (TaggedInstr o) '[] One x a }

-- Show instance for debugging
instance Show (Fix4 (TaggedInstr o) xs n r a) where
  show = ($ "") . getConst4 . cata4 (Const4 . alg)
    where
      alg :: forall xs n r a. TaggedInstr o (Const4 (String -> String)) xs n r a -> String -> String
      alg (Tag4 t Ret)                        = shows t . ": Ret"
      alg (Tag4 t (Call μ l k))                 = "(" . shows t . ": Call " . shows μ . (if l then " [LOOP] " else " ") . getConst4 k . ")"
      alg (Tag4 t (Push x k))                 = "(" . shows t . ": Push " . shows x . " " . getConst4 k . ")"
      alg (Tag4 t (Pop k))                    = "(" . shows t . ": Pop " . getConst4 k . ")"
      alg (Tag4 t (Lift2 f k))                = "(" . shows t . ": Lift2 " . shows f . " " . getConst4 k . ")"
      alg (Tag4 t (Sat f k))                  = "(" . shows t . ": Sat " . shows f . " " . getConst4 k . ")"
      alg (Tag4 t Empt)                       = shows t . ": Empt"
      alg (Tag4 t (Commit k))                 = "(" . shows t . ": Commit " . getConst4 k . ")"
      alg (Tag4 t (Catch p h))                = "(" . shows t . ": Catch " . getConst4 p . " " . shows h . ")"
      alg (Tag4 t (Tell k))                   = "(" . shows t . ": Tell " . getConst4 k . ")"
      alg (Tag4 t (Seek k))                   = "(" . shows t . ": Seek " . getConst4 k . ")"
      alg (Tag4 t (Case p q))                 = "(" . shows t . ": Case " . getConst4 p . " " . getConst4 q . ")"
      alg (Tag4 t (Choices fs ks def))        = "(" . shows t . ": Choices " . shows fs . " [" . intercalateDiff ", " (map getConst4 ks) . "] " . getConst4 def . ")"
      alg (Tag4 t (Iter μ _ l h))             = shows t . ": {Iter " . shows μ . " " . getConst4 l . " " . shows h . "}"
      alg (Tag4 t (Join φ))                   = shows t . ": " . shows φ
      alg (Tag4 t (MkJoin φ p k))             = "(" . shows t . ": let " . shows φ . " = " . getConst4 p . " in " . getConst4 k . ")"
      alg (Tag4 t (Swap k))                   = "(" . shows t . ": Swap " . getConst4 k . ")"
      alg (Tag4 t (Dup k))                    = "(" . shows t . ": Dup " . getConst4 k . ")"
      alg (Tag4 t (Make σ a k))               = "(" . shows t . ": Make " . shows σ . " " . shows a . " " . getConst4 k . ")"
      alg (Tag4 t (Get σ a k))                = "(" . shows t . ": Get " . shows σ . " " . shows a . " " . getConst4 k . ")"
      alg (Tag4 t (Put σ a k))                = "(" . shows t . ": Put " . shows σ . " " . shows a . " " . getConst4 k . ")"
      alg (Tag4 t (SelectPos Line k))         = "(" . shows t . ": Line " . getConst4 k . ")"
      alg (Tag4 t (SelectPos Col k))          = "(" . shows t . ": Col " . getConst4 k . ")"
      alg (Tag4 t (LogEnter _ k))             = shows t . ": " . getConst4 k
      alg (Tag4 t (LogExit _ k))              = shows t . ": " . getConst4 k
      alg (Tag4 t (MetaInstr BlockCoins{} k)) = shows t . ": " . getConst4 k
      alg (Tag4 t (MetaInstr m k))            = shows t . ": [" . shows m . "] " . getConst4 k

-- we need to perform a mcata on a machine's instructions , and we do this via this newtype monad pattern thing.
newtype Tagger o xs n r a = Tagger {doTagger :: HFresh InstrID (Fix4 (TaggedInstr o) xs n r a)}

{-|
Does what it says on the tin. Take a fixed-point representation of our machine and run it past the tagger algebra that uses `Tagger`.
-}
tagInstructions :: InstrID -> Fix4 (Instr o) xs n r a -> (Fix4 (TaggedInstr o) xs n r a, Int)
tagInstructions initID instrs = runFresh (doTagger $ cata4 (Tagger . alg) instrs) initID
    where
        wrap p = newVar >>= (\t -> return (In4 (Tag4 t p)))

        -- Casework
        alg :: Instr o (Tagger o) xs n r a -> HFresh InstrID (Fix4 (TaggedInstr o) xs n r a)
        alg Ret                 = wrap Ret
        alg (Call μ l k)        = doTagger k >>= (wrap . Call μ l)
        alg (Push x k)          = doTagger k >>= (wrap . Push x)
        alg (Pop k)             = doTagger k >>= (wrap . Pop)
        alg (Lift2 f k)         = doTagger k >>= (wrap . Lift2 f)
        alg (Sat f k)           = doTagger k >>= (wrap . Sat f)
        alg Empt                = wrap Empt
        alg (Commit k)          = doTagger k >>= (wrap . Commit)
        alg (Catch p h)         = do
                                    p' <- doTagger p
                                    h' <- case h of
                                        (Same a ka b kb) -> do
                                                                ka' <- doTagger ka
                                                                kb' <- doTagger kb
                                                                return $ Same a ka' b kb'
                                        (Always x k) -> do
                                                                k' <- doTagger k
                                                                return $ Always x k'
                                    wrap (Catch p' h')
        alg (Tell k)            = doTagger k >>= (wrap . Tell)
        alg (Seek k)            = doTagger k >>= (wrap . Seek)
        alg (Case p q)          = do
                                    p' <- doTagger p
                                    q' <- doTagger q
                                    wrap (Case p' q')
        alg (Choices fs ks def) = do
                                    ks' <- traverse doTagger ks
                                    def' <- doTagger def
                                    wrap (Choices fs ks' def')
        alg (Iter μ _ l h)      = do
                                    l' <- doTagger l
                                    h' <- case h of
                                        (Same a ka b kb) -> do
                                                                ka' <- doTagger ka
                                                                kb' <- doTagger kb
                                                                return $ Same a ka' b kb'
                                        (Always x k) -> do
                                                                k' <- doTagger k
                                                                return $ Always x k'
                                    wrap (Iter μ Nothing l' h')
        alg (Join φ)            = wrap (Join φ)
        alg (MkJoin φ p k)      = do
                                    p' <- doTagger p
                                    k' <- doTagger k
                                    wrap (MkJoin φ p' k')
        alg (Swap k)            = doTagger k >>= (wrap . Swap)
        alg (Dup k)             = doTagger k >>= (wrap . Dup)
        alg (Make σ a k)        = doTagger k >>= (wrap . Make σ a)
        alg (Get σ a k)         = doTagger k >>= (wrap . Get σ a)
        alg (Put σ a k)         = doTagger k >>= (wrap . Put σ a)
        alg (SelectPos p k)     = doTagger k >>= (wrap . SelectPos p)
        alg (LogEnter l k)      = doTagger k >>= (wrap . LogEnter l)
        alg (LogExit l k)       = doTagger k >>= (wrap . LogExit l)
        alg (MetaInstr m k)     = doTagger k >>= (wrap . MetaInstr m)

-- CFG construction

-- TODO: rename or remove
type FreeReferences = Map InstrID (Set SomeΣVar)

-- PhiData: (InstrID of join to ΦVar, IΦVar to join point's InstrID ). Used internally in CFG construction.
type PhiData = (DList (InstrID, IΦVar), DList (IΦVar, InstrID))

{-| 
Generic graph data type. 
-}
newtype Graph = Graph { unGraph :: Map InstrID (Set InstrID) }

{-|
Keep graph and use-def data together. 
-}
data CFG = CFG {
    graph      :: Graph,            -- ^ graph of the CFG
    start      :: InstrID,          -- ^ Start node of the CFG
    useDefs    :: UseDefData,       -- ^ The use-defs, duh!
    calleeTags :: Map IMVar InstrID -- ^ Which tag each μ-call can lead to 
}

-- Make some instances for Graph construction to make things easier and more ergonomic.
instance Semigroup Graph where
    a <> b = Graph $ Map.unionWith Set.union (unGraph a) (unGraph b)
instance Monoid Graph where
    mempty = Graph Map.empty

instance Semigroup GraphConstruction where
    (GraphConstruction p1 g1 r1) <> (GraphConstruction p2 g2 r2) = GraphConstruction (p1 <> p2) (g1 <> g2) (r1 <> r2)
instance Monoid GraphConstruction where
    mempty = GraphConstruction mempty mempty mempty

-- map instrID to (use, def)
type UseDefData = Map InstrID (Set SomeΣVar, Set SomeΣVar)

-- State to pass around during construction
data GraphConstruction = GraphConstruction { phiData :: PhiData, graphData :: Graph, refData :: UseDefData}

-- LoopAndHandlerScope: stack of handler insturction IDs
data HandlerEntry = SameH InstrID InstrID | AlwaysH InstrID deriving stock Show
type HandlerEntries = [HandlerEntry]

data GraphConstructionState = GraphConstructionState { loopTags :: Map IMVar InstrID, handlerStack:: HandlerEntries }

{- 
Grapher: State for if we are in a loop body and what the beginning instruction of the current handler is. Moreover,
          a `Writer` instance to write the graph into as well as  record  data about Phi Joins and MkJoins that will
          be joined later
-}
newtype Grapher o xs n r a = Grapher { doGrapher :: StateT GraphConstructionState (Writer GraphConstruction) InstrID }

{-| 
`skimTopTag` just returns the tag of the entry point to a series of instructions.
-}
skimTopTag :: forall o xs n r a. Fix4 (TaggedInstr o) xs n r a -> InstrID
skimTopTag (In4 Tag4{tag}) = tag

constructCFG :: forall input a. (TaggedBinding input a a, DMap MVar (TaggedBinding input a)) -> CFG
constructCFG (p, μs) = cfg
    where
        -- Skim the starting tags of the parsers (NB: ignoring entry machine `p`)
        starts = DMap.foldlWithKey (\m (MVar k) b -> Map.insert k (skimTopTag $ taggedBody b) m) Map.empty μs

        -- Construct the global CFG from the let-bound parsers
        cfg = DMap.foldlWithKey (\cfg _ b -> cfg `mergeCFGs` constructMachineCFG starts (taggedBody b)) (constructMachineCFG starts (taggedBody p)) μs

        -- left-biased merge of two CFGs
        mergeCFGs :: CFG -> CFG -> CFG
        mergeCFGs cfg1 cfg2 = CFG {graph = graph cfg1 <> graph cfg2,
                                   start = start cfg1,
                                   useDefs = Map.union (useDefs cfg1) (useDefs cfg2),
                                   calleeTags = Map.union (calleeTags cfg1) (calleeTags cfg2)}

constructMachineCFG :: forall o xs n r a. Map IMVar InstrID -- ^ Map of MVar -> tag of the first instruction of machine
                    -> Fix4 (TaggedInstr o) xs n r a  -- ^ Machine instructions
                    -> CFG
constructMachineCFG starts instrs = CFG{ graph = graph, start = skimTopTag instrs, useDefs = usedefs, calleeTags = Map.union starts (loopTags endState)}
    where
        -- 1. Construct graph by attaching join points, loops, and sequential instructions (in reverse) (_, GraphConstruction phidata graph usedefs)
        emptyConstructionState =  GraphConstructionState Map.empty []
        ((_, endState), GraphConstruction (joins, joinPts) partialGraph usedefs) = (runWriter . flip runStateT emptyConstructionState . doGrapher) $ cata4 (Grapher . alg) instrs

        -- 2. Turn our partial graph' into a full one with phidata
        graph = Graph $ foldl (\g (join, phi) -> Map.unionWith Set.union g $ Map.fromList [(join, Set.singleton $ joinPtsMap Map.! phi)]) (unGraph partialGraph) joins
        joinPtsMap = Map.fromList $ DList.toList joinPts

        alg :: forall o xs n r a. TaggedInstr o (Grapher o) xs n r a -> StateT GraphConstructionState (Writer GraphConstruction) InstrID
        alg (Tag4 t Ret)                 = handlerEdge t >> addStump t >> pure t
        alg (Tag4 t (Call (MVar μ) _ k)) = do
                                            handlerEdge t
                                            callTag <- if Map.member μ starts
                                                        then pure $ starts Map.! μ -- call to let-bound
                                                        else getLoopTag μ -- loop call-back
                                            addEdge t callTag
                                            edgeToK t k
        alg (Tag4 t (Push _ k))          = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Pop k))             = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Lift2 _ k))         = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Sat _ k))           = handlerEdge t >> edgeToK t k
        alg (Tag4 t Empt)                = handlerEdge t >> addStump t >> pure t
        alg (Tag4 t (Commit k))          = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Catch p h))         = handlerEdge t >> pushHandler h >> edgeToK t p >> popHandler >> pure t
        alg (Tag4 t (Tell k))            = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Seek k))            = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Case p q))          = handlerEdge t >> edgeToK t p >> edgeToK t q
        alg (Tag4 t (Choices _ ks def))  = handlerEdge t >> traverse (edgeToK t) ks >> edgeToK t def
        alg (Tag4 t (Iter (MVar μ) _ l h)) = do
                                                pushHandler h
                                                addLoopTag μ t
                                                entry <- doGrapher l
                                                addEdge t entry
                                                removeLoopTag μ
                                                popHandler
                                                pure t
        alg (Tag4 t (Join φ))            = handlerEdge t >> addJoin t φ >> pure t
        alg (Tag4 t (MkJoin φ p k))      = handlerEdge t >> doGrapher p >>= flip addMkJoin φ >> edgeToK t k
        alg (Tag4 t (Swap k))            = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Dup k))             = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Make σ _ k))        = handlerEdge t >> addDef t (SomeΣVar σ) >> edgeToK t k
        alg (Tag4 t (Get σ _ k))         = handlerEdge t >> addUse t (SomeΣVar σ) >> edgeToK t k
        alg (Tag4 t (Put σ _ k))         = handlerEdge t >> addUse t (SomeΣVar σ) >> edgeToK t k
        alg (Tag4 t (SelectPos _ k))     = handlerEdge t >> edgeToK t k
        alg (Tag4 t (LogEnter _ k))      = handlerEdge t >> edgeToK t k
        alg (Tag4 t (LogExit _ k))       = handlerEdge t >> edgeToK t k
        alg (Tag4 t (MetaInstr _ k))     = handlerEdge t >> edgeToK t k

        -- Smart constructors for creating constitutient parts of `GraphConstruction`
        phiGCon :: PhiData -> GraphConstruction
        phiGCon p = GraphConstruction p mempty mempty
        graphGCon :: Graph -> GraphConstruction
        graphGCon g = GraphConstruction mempty g mempty
        refGCon :: UseDefData -> GraphConstruction
        refGCon = GraphConstruction mempty mempty

        -- Various monadic helpers for graph construction
        addJoin t (ΦVar  φ)   = (lift . tell) (phiGCon (DList.fromList [(t, φ)], DList.empty))
        addMkJoin t (ΦVar  φ) = (lift . tell) (phiGCon (DList.empty, DList.fromList [(φ, t)]))

        addStump a = (lift . tell . graphGCon . Graph) (Map.fromList [(a, mempty)])
        addEdge a b = (lift . tell . graphGCon . Graph) (Map.fromList [(a, Set.singleton b)])

        edgeToK t k = doGrapher k >>= addEdge t >> pure t

        -- Handler state helpers
        pushHandler :: forall o xs n r a. Handler o (Grapher o) xs n r a -> StateT GraphConstructionState (Writer GraphConstruction) HandlerEntry
        pushHandler (Same _ k1 _ k2) = do
                                        state <- get
                                        let GraphConstructionState{handlerStack} = state
                                        t1 <- doGrapher k1
                                        t2 <- doGrapher k2
                                        let h = SameH t1 t2
                                        put state{handlerStack = h:handlerStack}
                                        pure h
        pushHandler (Always _ k)     = do
                                        state <- get
                                        let GraphConstructionState{handlerStack} = state
                                        t <- doGrapher k
                                        let h = AlwaysH t
                                        put state{handlerStack = h:handlerStack}
                                        pure h

        popHandler :: StateT GraphConstructionState (Writer GraphConstruction) ()
        popHandler = do
                        state <- get
                        put state{handlerStack = (\(_:hs) -> hs) $ handlerStack state}
        handlerEdge t = get >>= (\stack -> do
                                            case stack of
                                                [] -> pure ()
                                                ((AlwaysH h):_) -> addEdge t h
                                                ((SameH h1 h2 ):_) -> addEdge t h1 >> addEdge t h2) . handlerStack

        -- loop start position state helpers
        getLoopTag :: IMVar -> StateT GraphConstructionState (Writer GraphConstruction) InstrID
        getLoopTag μ = do
            GraphConstructionState{loopTags} <- get
            return $ loopTags Map.! μ

        addLoopTag :: IMVar -> InstrID -> StateT GraphConstructionState (Writer GraphConstruction) ()
        addLoopTag μ t = do
                            state <- get
                            put state{loopTags = Map.insert μ t (loopTags state)}
                            return ()

        removeLoopTag :: IMVar -> StateT GraphConstructionState (Writer GraphConstruction) ()
        removeLoopTag μ = do
                            state <- get
                            put state{loopTags = Map.delete μ (loopTags state)}
                            return ()

        -- Register use/def writers
        addUse t σ = (lift . tell . refGCon . Map.fromList) [(t, (Set.singleton σ, mempty))]
        addDef t σ = (lift . tell . refGCon . Map.fromList) [(t, (mempty, Set.singleton σ))]


freeRegisters :: InstrID -> CFG -> FreeReferences
freeRegisters maxID CFG{graph, useDefs} = Map.map (uncurry (Set.\\)) usedefs'
    where
        -- Propagate the (use, def) sets upwards. 
        usedefs' = propagateRegs graph useDefs
        propagateRegs :: Graph -> UseDefData -> UseDefData
        propagateRegs graph usedef = snd $ execState iter (initWL, initMap)
            where
                succ = unGraph graph
                -- flip the graph for predessors
                pred = Map.foldlWithKey (\g n nsucc -> foldl
                                            (\g s -> Map.insertWith Set.union s (Set.singleton n) g) g nsucc)
                                        (Map.fromList [(x, mempty) | x <- [0..maxID]]) -- make sure all nodes have an entry in there
                                        succ
                -- All graph nodes
                initWL = Map.keys succ
                initMap = foldl (\a k -> a <> Map.singleton k (mempty, mempty)) usedef [0..maxID]

                iter :: State ([InstrID], UseDefData) ()
                iter = do
                    node <- popWL
                    propagateNode pred succ node
                    isEmpty <- emptyWL
                    unless isEmpty iter


        popWL :: State ([InstrID], UseDefData) InstrID
        popWL = do
            (wl, b) <- get
            let (a:as) = wl
            put (as, b)
            return a
        emptyWL :: State ([InstrID], UseDefData) Bool
        emptyWL  = do
            gets (null . fst)

        propagateNode :: Map InstrID (Set InstrID) -> Map InstrID (Set InstrID) -> InstrID -> State ([InstrID], UseDefData) ()
        propagateNode pred succ nodeid = do
            (wl, refData) <- get
            -- propagate from all successors
            let !(use, def) = refData Map.! nodeid
            let !(use', def') = foldl (\b s -> b <> refData Map.! s) (use, def) $ succ Map.! nodeid
            put (wl, Map.insert nodeid (use', def') refData) -- update (use, def) in state
            -- update worklist as necessary
            when (Set.size use' /= Set.size use || Set.size def' /= Set.size def) $ do
                    -- update worklist 
                    addToWorkList (pred Map.! nodeid)

        addToWorkList :: Set InstrID -> State ([InstrID], UseDefData) ()
        addToWorkList preds = do
            (wl, ref) <- get
            put (foldl (flip (:)) wl preds, ref)

markThreadables :: FreeReferences -> Fix4 (TaggedInstr o) xs n r a -> Fix4 (Instr o) xs n r a
markThreadables frees = undefined
    where
        alg :: FreeReferences -> TaggedInstr o (Fix4 (Instr o)) xs n r a -> Fix4 (Instr o) xs n r a
        alg frees Tag4{tag, tagged} = In4 $ attachData (frees Map.! tag) tagged

        attachData :: Set SomeΣVar -> Instr o (Fix4 (Instr o)) xs n r a -> Instr o (Fix4 (Instr o)) xs n r a
        -- attachData frees Ret                   = Ret
        -- attachData frees (Call x k)            = undefined
        -- attachData frees (Catch m h)           = undefined
        attachData frees (Iter name _ body h)     = Iter name (Just $ makeRegs frees) (body) h
        -- attachData frees (Join x)              = undefined
        -- attachData frees (MkJoin x body scope) = undefined
        -- no need to attach free reference data
        attachData _ instr = instr

{- 
Keeps state of which loops are currently in scope. Helps us to know when to mark calls as loop calls 
and decide at calls/joins which registers solidfy.
-}
data LoopMarkerState = LoopMarkerState { toBind:: Set SomeΣVar, loopBinds :: [Set SomeΣVar] }
newtype LoopMarker o xs n r a = LoopMarker {doLoopMarking :: State LoopMarkerState (Fix4 (TaggedInstr o) xs n r a) }


markLoopBodies :: Set IMVar -> FreeReferences -> Fix4 (TaggedInstr o) xs n r a -> Fix4 (TaggedInstr o) xs n r a
markLoopBodies letBounds frees instrs = evalState marking emptyLoopMarkerState
    where
        emptyLoopMarkerState = LoopMarkerState Set.empty []
        marking = doLoopMarking $ cata4 (LoopMarker . alg) instrs
        alg :: TaggedInstr o (LoopMarker o) xs n r a -> State LoopMarkerState (Fix4 (TaggedInstr o) xs n r a)
        alg (Tag4 t Ret)                 = wrap t Ret
        alg (Tag4 t (Call (MVar μ) _ k)) = do
                                            k' <- doLoopMarking k
                                            -- TODO: remove this whenever we have total binds. Just here to get intermediary stuff working.
                                            if Set.member μ letBounds
                                                then wrap t (Call (MVar μ) False k') -- Is let-bound parser
                                                else wrap t (Call (MVar μ) True k') -- Is loop
        alg (Tag4 t (Push x k))          = doLoopMarking k >>= wrap t . Push x
        alg (Tag4 t (Pop k))             = doLoopMarking k >>= wrap t . Pop
        alg (Tag4 t (Lift2 f k))         = doLoopMarking k >>= wrap t . Lift2 f
        alg (Tag4 t (Sat f k))           = doLoopMarking k >>= wrap t . Sat f
        alg (Tag4 t Empt)                = wrap t Empt
        alg (Tag4 t (Commit k))          = doLoopMarking k >>= wrap t . Commit
        alg (Tag4 t (Catch p h))         = do
                                            p' <- doLoopMarking p
                                            h' <- doHandler h
                                            wrap t (Catch p' h')
        alg (Tag4 t (Tell k))            = doLoopMarking k >>= wrap t . Tell
        alg (Tag4 t (Seek k))            = doLoopMarking k >>= wrap t . Seek
        alg (Tag4 t (Case p q))          = do
                                            p' <- doLoopMarking p
                                            q' <- doLoopMarking q
                                            wrap t (Case p' q')
        alg (Tag4 t (Choices fs ks def)) = do
                                            ks' <- traverse doLoopMarking ks
                                            def' <- doLoopMarking def
                                            wrap t (Choices fs ks' def')
        alg (Tag4 t (Iter μ _ l h))      = do
                                            h' <- doHandler h
                                            -- Just bind the frees in loop, not those that escape.
                                            -- TODO: when handler continuations work, this should change
                                            let regsToBind = (frees Map.! t) Set.\\ handlerFrees h'
                                            addLoopBinds regsToBind
                                            l' <- doLoopMarking l
                                            popLoopBinds
                                            wrap t (Iter μ (Just $ makeRegs regsToBind) l' h')
        alg (Tag4 t (Join φ))            = wrap t (Join φ)
        alg (Tag4 t (MkJoin φ p k))      = do
                                            p' <- doLoopMarking p
                                            k' <- doLoopMarking k
                                            wrap t (MkJoin φ p' k')
        alg (Tag4 t (Swap k))            = doLoopMarking k >>= wrap t . Swap
        alg (Tag4 t (Dup k))             = doLoopMarking k >>= wrap t . Dup
        alg (Tag4 t (Make σ a k))        = do 
                                            k' <- doLoopMarking k
                                            bound <- isBound σ
                                            wrap t $ if bound then Make σ Bound k' else Make σ a k' 
        alg (Tag4 t (Get σ a k))         =do 
                                            k' <- doLoopMarking k
                                            bound <- isBound σ
                                            wrap t $ if bound then Get σ Bound k' else Get σ a k' 
        alg (Tag4 t (Put σ a k))         = do 
                                            k' <- doLoopMarking k
                                            bound <- isBound σ
                                            wrap t $ if bound then Put σ Bound k' else Put σ a k' 
        alg (Tag4 t (SelectPos p k))     = doLoopMarking k >>= wrap t . SelectPos p
        alg (Tag4 t (LogEnter l k))      = doLoopMarking k >>= wrap t . LogEnter l
        alg (Tag4 t (LogExit l k))       = doLoopMarking k >>= wrap t . LogExit l
        alg (Tag4 t (MetaInstr m k))     = doLoopMarking k >>= wrap t . MetaInstr m

        wrap :: InstrID -> Instr o (Fix4 (TaggedInstr o)) xs n r a -> State LoopMarkerState (Fix4 (TaggedInstr o) xs n r a)
        wrap t instrs = pure $ In4 (Tag4 t instrs)

        -- TODO: when handler continuations are done, this state logic is wrong as we should thread the variables across handler boundaries as well
        addLoopBinds :: Set SomeΣVar -> State LoopMarkerState ()
        addLoopBinds regs = do
                            state <- get
                            put $ state{toBind = Set.union (toBind state) regs, loopBinds = regs:loopBinds state}

        popLoopBinds :: State LoopMarkerState ()
        popLoopBinds = do 
                        LoopMarkerState{toBind, loopBinds} <- get
                        let (x:xs) = loopBinds
                        put $ LoopMarkerState{toBind=toBind Set.\\ x, loopBinds = xs}


        doHandler :: Handler o (LoopMarker o) xs n r a -> State LoopMarkerState (Handler o (Fix4 (TaggedInstr o)) xs n r a)
        doHandler (Same x k1 y k2) = do
                                        k1' <- doLoopMarking k1
                                        k2' <- doLoopMarking k2
                                        return (Same x k1' y k2')
        doHandler (Always x k)     = do
                                        k' <- doLoopMarking k
                                        return (Always x k')
        handlerFrees :: Handler o (Fix4 (TaggedInstr o)) xs n r a -> Set SomeΣVar
        handlerFrees (Same _ (In4 h1) _ (In4 h2)) = (frees Map.! (tag h1)) `Set.union` (frees Map.! (tag h2)) 
        handlerFrees (Always _ (In4 h))           = frees Map.! tag h

        isBound :: forall x. ΣVar x -> State LoopMarkerState Bool
        isBound σ = get >>= pure . Set.member (SomeΣVar σ) . toBind

{-| 
Forgetfully removes tags from instructions. 
-}
unTag :: Fix4 (TaggedInstr o) xs n r a -> Fix4 (Instr o) xs n r a
unTag = cata4 alg
    where 
        alg :: TaggedInstr o (Fix4 (Instr o)) xs n r a -> Fix4 (Instr o) xs n r a
        alg Tag4{tagged} = In4 tagged