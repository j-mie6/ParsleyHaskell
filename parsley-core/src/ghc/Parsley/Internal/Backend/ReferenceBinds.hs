{-# LANGUAGE NamedFieldPuns, OverloadedStrings, DerivingStrategies #-}

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

import Control.Monad                                    (unless)
import Control.Monad.Writer                             (Writer, MonadWriter (..), runWriter)
import Control.Monad.State                              (State, StateT (..), MonadTrans (..), MonadState (..), when, evalState, gets, execState, modify)
import Data.Foldable                                    (traverse_)
import Data.Functor                                     (($>))
import Parsley.Internal.Backend.Machine.LetBindings     (LetBinding (..))
import Parsley.Internal.Common                          (One)
import Parsley.Internal.Common.Fresh                    (HFresh, MonadFresh(..), runFresh)
import Parsley.Internal.Common.Indexed                  (Fix4, IFunctor4, Fix4(..), Const4(..), cata4, IFunctor4(imap4))
import Parsley.Internal.Common.Utils                    (intercalateDiff)
import Parsley.Internal.Backend.Machine                 (Access (..))
import Parsley.Internal.Backend.Machine.Identifiers     (SomeΣVar(..), IΦVar, ΦVar(..), IMVar, MVar (..))
import Parsley.Internal.Backend.Machine.Instructions    (Instr(..), Handler(..), PosSelector(..), MetaInstr(..))
import Parsley.Internal.Backend.Machine.Types.Registers (makeRegs)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Dependent.Map (DMap)
import qualified Data.Dependent.Map as DMap


{-|
`bindReferences` performs global analysis on the forest of let-bound parsers and turns as many references
into bound variables as possible. 
-}
bindReferences :: forall input a. (LetBinding input a a, DMap MVar (LetBinding input a)) -> (LetBinding input a a, DMap MVar (LetBinding input a))
bindReferences (p, μs) =  (pOptimised, μsOptimised)
    where
        -- 1. Tag every instruction with a unique identifier
        (pTagged, maxV) = tagInstructions 0 (body p)
        (μsTagged, maxV') = DMap.foldlWithKey (\(m, max) μ p -> let (tagged, max') = tagInstructions max (body p)
                                                                in (DMap.insert μ (TaggedBinding tagged) m, max'))
                                                                (DMap.empty :: DMap MVar (TaggedBinding input a), maxV) μs

        -- 2. create CFG of the whole forest of machines 
        cfg = constructCFG (TaggedBinding pTagged, μsTagged)

        -- 3. generate map tag -> set of free registers that are used later in control-flow
        freeRegData = cfgAnalysis maxV' cfg

        -- 4. Mark loop bodies
        (!pTagged', !μsTagged') = markRegisterBinds freeRegData (TaggedBinding pTagged, μsTagged)

        -- 5. Unwrap tags, reattach freeRegs and meta of original bind
        letHandlerRegs = fst $ callAndHandlerRegs freeRegData
        letReturnRegs = returnContinuations freeRegData
        rewrap :: MVar x -> Fix4 (Instr input) '[] One x a -> LetBinding input a x
        rewrap μ new = let old = μs DMap.! μ
                         in old {body = new,
                                 -- `handlerFrees` and `returnFrees` can be tweaked.
                                 handlerFrees = freeRegs old,
                                 returnFrees = freeRegs old }
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
newtype TaggedBinding o a x = TaggedBinding { taggedBody :: Fix4 (TaggedInstr o) '[] One x a }

-- Show instance for debugging
instance Show (Fix4 (TaggedInstr o) xs n r a) where
  show = ($ "") . getConst4 . cata4 (Const4 . alg)
    where
      alg :: forall xs n r a. TaggedInstr o (Const4 (String -> String)) xs n r a -> String -> String
      alg (Tag4 t Ret)                        = shows t . ": Ret"
      alg (Tag4 t (Call μ k))                 = "(" . shows t . ": Call " . shows μ . getConst4 k . ")"
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
      alg (Tag4 t (MkJoin φ _ p k))           = "(" . shows t . ": let " . shows φ . " = " . getConst4 p . " in " . getConst4 k . ")"
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
tagInstructions initID instrs = runFresh (doTagger $ cata4 (Tagger . alg) instrs) (initID + 1)
    where
        wrap p = newVar >>= (\t -> return (In4 (Tag4 t p)))

        -- Casework
        alg :: Instr o (Tagger o) xs n r a -> HFresh InstrID (Fix4 (TaggedInstr o) xs n r a)
        alg Ret                 = wrap Ret
        alg (Call μ k)          = doTagger k >>= (wrap . Call μ)
        alg (Push x k)          = doTagger k >>= (wrap . Push x)
        alg (Pop k)             = doTagger k >>= (wrap . Pop)
        alg (Lift2 f k)         = doTagger k >>= (wrap . Lift2 f)
        alg (Sat f k)           = doTagger k >>= (wrap . Sat f)
        alg Empt                = wrap Empt
        alg (Commit k)          = doTagger k >>= (wrap . Commit)
        alg (Catch p h)         = do
                                    p' <- doTagger p
                                    h' <- case h of
                                        (Same _ a ka b kb) -> do
                                                                ka' <- doTagger ka
                                                                kb' <- doTagger kb
                                                                return $ Same Nothing a ka' b kb'
                                        (Always _ x k) -> do
                                                                k' <- doTagger k
                                                                return $ Always Nothing x k'
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
                                        (Same _ a ka b kb) -> do
                                                                ka' <- doTagger ka
                                                                kb' <- doTagger kb
                                                                return $ Same Nothing a ka' b kb'
                                        (Always _ x k) -> do
                                                                k' <- doTagger k
                                                                return $ Always Nothing x k'
                                    wrap (Iter μ Nothing l' h')
        alg (Join φ)            = wrap (Join φ)
        alg (MkJoin φ _ p k)      = do
                                    p' <- doTagger p
                                    k' <- doTagger k
                                    wrap (MkJoin φ Nothing p' k')
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

data CFGAnalysisData = CFGAnalysisData { livenessSets :: !(Map InstrID (Set SomeΣVar, Set SomeΣVar))
                                       , callAndHandlerRegs :: !(Map IMVar (Set SomeΣVar), Map InstrID (Set SomeΣVar))
                                       , returnContinuations :: !(Map IMVar (Set SomeΣVar))}

-- PhiData: (InstrID of join to ΦVar, IΦVar to join point's InstrID ). Used internally in CFG construction.
type PhiData = (DList (InstrID, IΦVar), DList (IΦVar, InstrID))

-- A singular graph unit
type CFGGraph = Map InstrID (Set InstrID)

{-|
Keep graph and use-def data together. 
-}
data CFG = CFG {
      graph          :: !CFGGraph
    , subs           :: !(Map IMVar CFGGraph) -- ^ graph of the CFG
    , start          :: !InstrID                              -- ^ Start node of the CFG
    , useDefs        :: !UseDefData                           -- ^ The use-defs, duh!
    , calleeTags     :: !(Map IMVar InstrID)                  -- ^ Which tag each μ-bound parser starts at.
    , handlerTags    :: !(Set InstrID)                        -- ^ The tags that are entry points of a handler 
    , callerTags     :: !(Map IMVar (Set (Maybe IMVar, InstrID, InstrID))) -- ^ Each node that is a call to a given let-bound, along the ret. cont. tag
    , letBoundStarts :: !(Map IMVar InstrID)                  -- ^ InstrID of the start for each let bound parser
    , letBoundTags   :: !(Map IMVar (Set InstrID))            -- ^ Which instruction tags belong to which let bound parser 
    , returnTags     :: !(Map IMVar (Set InstrID))            -- ^ Which tags are return calls from let-bound parsers.
}

instance Semigroup GraphConstruction where
    (GraphConstruction p1 g1 r1) <> (GraphConstruction p2 g2 r2) = GraphConstruction (p1 <> p2) (Map.unionWith Set.union g1  g2) (r1 <> r2)
instance Monoid GraphConstruction where
    mempty = GraphConstruction mempty mempty mempty

-- map instrID to (use, def)
type UseDefData = Map InstrID (Set SomeΣVar, Set SomeΣVar)

-- State to pass around during construction
data GraphConstruction = GraphConstruction PhiData CFGGraph UseDefData

-- LoopAndHandlerScope: stack of handler insturction IDs
data HandlerEntry = SameH InstrID InstrID | AlwaysH InstrID deriving stock Show

type HandlerEntries = [HandlerEntry]

data GraphConstructionState = GraphConstructionState {
      loopTags               :: !(Map IMVar InstrID)
    , handlerStack           :: !HandlerEntries
    -- TODO: maybe the three below fields should bein `GraphConstruction` instead...
    , collectedHTags         :: !(Set InstrID)
    , collectedCallsites     :: !(Map IMVar [(InstrID, InstrID, Maybe HandlerEntry)])
    , collectedRetTags       :: !(Set InstrID)
    , collectedHandlerStumps :: !(Set InstrID)
    , collectedTags          :: !(Set InstrID)
}

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
        -- 1. Skim the starting tags of the parsers (NB: ignoring entry machine `p`)
        starts = DMap.foldlWithKey (\m (MVar k) b -> Map.insert k (skimTopTag $ taggedBody b) m) Map.empty μs

        -- 2. Construct the global CFG from the top-level and let-bound parsers
        (cfg, handlerStumpData) = DMap.foldlWithKey (\(cfg, handls) (MVar k) b -> let (cfg', handls') = constructMachineCFG starts (Just k) (taggedBody b)
                                                               in (cfg `mergeCFGs` cfg', joinHandlerStumpData handls handls') ) 
                                                               (constructMachineCFG starts Nothing (taggedBody p)) μs
        
        {- 
        -- Below is redundant code for when I constructed a global CFG instead of small CFGs per each let bound. This required a lot of messing around with
        -- joining hanging handler entries to their respective places.    

        -- 3. propagate handlers to each callee's starts and handler stumps using `handlerStumpData`

        --    a) We create a graph where edge (a, b) denotes that "a is a call-site to the parser containing b and b is a handler stump"
        HandlerStumpData callSites handlerStumps = handlerStumpData
        -- We add the head of each parser to the set of handler stumps because we will use this for analysis later when we do handler-call register unification.
        handlerStumpsWithStarts = Map.foldlWithKey (\acc mvar start -> Map.insertWith Set.union mvar (Set.singleton start) acc) handlerStumps starts

        allStumps = foldl Set.union Set.empty $ Map.elems handlerStumpsWithStarts

        -- Initial stump handler data that we will let flow
        stumpsAndCallsiteHandlers' = Set.foldl (\acc s -> Map.insert s Set.empty acc) Map.empty allStumps
        stumpsAndCallsiteHandlers = Map.foldlWithKey (\acc _ callsites -> Set.foldl (\acc (callsite, handler) -> case handler of
                                                                                            Just x -> Map.insertWith Set.union callsite (Set.singleton x) acc
                                                                                            _ -> Map.insertWith Set.union callsite (Set.empty) acc) acc callsites)
                                                    stumpsAndCallsiteHandlers' callSites

        -- Make a graph of call-site connections
        stumpGraph = Map.foldlWithKey (\acc mvar callsites -> Set.foldl (\acc (callsite, _) -> Map.insert callsite (handlerStumpsWithStarts Map.! mvar) acc) acc callsites)
                                       Map.empty callSites

        --    b) Let the handlers flow till convergence using a worklist algorithm
        flowHandlers :: State ([InstrID], (Map InstrID (Set InstrID))) ()
        flowHandlers = do
            (worklist, handlerSets) <- get
            case worklist of
                [] -> return ()
                (x:xs) -> do
                            put (xs, handlerSets)
                            flowNode x
                            flowHandlers
        flowNode :: InstrID -> State ([InstrID], (Map InstrID (Set InstrID))) ()
        flowNode nodeid = do
            (worklist, handlerSets) <- get
            let handlers = Map.findWithDefault (error "336") nodeid handlerSets
            let children = Map.findWithDefault Set.empty nodeid stumpGraph
            -- add handlers to all immediate children nodes
            let (handlerSets', changes) = Set.foldl (\(hs, chngs) child -> let childSet  = Map.findWithDefault (error "339") child handlerSets
                                                                               childSet' = childSet `Set.union` handlers
                                                                               changed = Set.size childSet /= Set.size childSet'
                                                                            in
                                                                               (Map.insert child childSet' hs, if changed then child:chngs else chngs))
                                                    (handlerSets, []) children
            -- When we changed some children, add them to the worklist
            let updatedWorklist = foldl (\acc change -> change:acc) worklist changes
            -- Update state and recutse
            put (updatedWorklist, handlerSets')

        initWorklist = Set.toList $ Set.unions $ Map.elems $ Map.map (Set.map fst) callSites
        (_, (_, finalStumpAndCallHandlers)) = trace ("STUMPGRAPH!!!!" ++ show stumpGraph) $ runState flowHandlers (initWorklist, stumpsAndCallsiteHandlers)

        --    c) enrich the almost-complete cfg with these handler edges
        addStumpEdges :: CFGGraph -> InstrID -> Set InstrID -> CFGGraph
        addStumpEdges g t handlers = Set.foldl (\acc he -> Map.insertWith Set.union t (Set.singleton he) acc) g handlers
        cfg = cfg'' {graph = Set.foldl (\g stump -> addStumpEdges g stump (finalStumpAndCallHandlers Map.! stump) ) (graph cfg'') allStumps}
        -}

        -- left-biased merge of two CFGs
        mergeCFGs :: CFG -> CFG -> CFG
        mergeCFGs cfg1 cfg2 = CFG {graph          = graph cfg1,
                                   subs           = subs cfg1 <> subs cfg2,
                                   start          = start cfg1,
                                   useDefs        = Map.union (useDefs cfg1) (useDefs cfg2),
                                   calleeTags     = Map.union (calleeTags cfg1) (calleeTags cfg2),
                                   handlerTags    = Set.union (handlerTags cfg1) (handlerTags cfg2),
                                   callerTags     = Map.unionWith Set.union (callerTags cfg1) (callerTags cfg2),
                                   letBoundStarts = letBoundStarts cfg1,
                                   letBoundTags   = Map.union (letBoundTags cfg1) (letBoundTags cfg2),
                                   returnTags     = Map.unionWith Set.union (returnTags cfg1) (returnTags cfg2)}
        
        -- join for handler stump data
        joinHandlerStumpData :: HandlerStumpData -> HandlerStumpData -> HandlerStumpData
        joinHandlerStumpData (HandlerStumpData a b) (HandlerStumpData a' b') = HandlerStumpData (Map.unionWith Set.union a a') (Map.unionWith Set.union b b')
{-
When we have a call instruction, we transfer the handler to the callee parser. This means that any other non-top-level 
parser can have failures without a local handler in scope which means that handler needs to be inherited from one of
the call-sites. This is not known locally, so we need to keep track of 
    1) local stumps of a let-bound parser that require a handler connection  
    2) which handler entries are in scope to a let bound call
However, a stumped call can occur which means that a callee might not inherit the immediate caller's handler but some
ancestor of it. Furthermore, the caller-callee graph is not necessarily acyclic.  

HandlerStumpData could be included in the CFG but we do not want to expose this.
-}
data HandlerStumpData = HandlerStumpData (Map IMVar (Set (InstrID, Maybe InstrID))) -- ^ Record of call-sites and possible handlers (if not stumped)
                                         (Map IMVar (Set InstrID))                  -- ^ Set of stumped instructions per each let-bound parser
                        deriving stock Show

constructMachineCFG :: forall o xs n r a. Map IMVar InstrID -- ^ Map of MVar -> tag of the first instruction of machine
                    -> Maybe IMVar -- ^ Which let-bound parser are we constructing now?
                    -> Fix4 (TaggedInstr o) xs n r a  -- ^ Machine instructions
                    -> (CFG, HandlerStumpData)
constructMachineCFG starts mvar instrs = (cfg, handlerStumpData)
    where
        cfg = CFG{
                   graph       = graph
                 , subs        = case mvar of 
                                    Nothing -> Map.empty
                                    (Just x) -> Map.singleton x graph
                 , start       = skimTopTag instrs
                 , useDefs     = usedefs
                 , calleeTags  = Map.union starts (loopTags endState)
                 , handlerTags = collectedHTags endState
                 , callerTags  = Map.map (Set.fromList . map (\(a, b,_) -> (mvar, a, b))) $ collectedCallsites endState
                 , letBoundStarts = starts
                 , letBoundTags = case mvar of
                     Just k -> Map.fromList [(k, allTags)]
                     _ -> Map.empty
                 , returnTags = case mvar of
                     Just k -> Map.fromList [(k, collectedRetTags endState)]
                     _ -> Map.empty
                 }

        handlerStumps = case mvar of
                    Just m -> Map.singleton m (collectedHandlerStumps endState)
                    _ -> Map.empty -- no stumps at the top level.

        -- convert from HandlerEntry to just InstrID.
        gatherHandlerConns :: Set (InstrID, Maybe InstrID) -> (InstrID, InstrID, Maybe HandlerEntry) -> Set (InstrID, Maybe InstrID)
        gatherHandlerConns acc (a, _, Nothing)            = Set.insert (a, Nothing) acc
        gatherHandlerConns acc (a, _, Just (AlwaysH h))   = Set.insert (a, Just h) acc
        gatherHandlerConns acc (a, _, Just (SameH h1 h2)) = Set.insert (a, Just h1) $ Set.insert (a, Just h2) acc

        handlerStumpData = HandlerStumpData (Map.map (foldl gatherHandlerConns Set.empty) $ collectedCallsites endState) handlerStumps

        -- 1. Construct graph by attaching join points, loops, and sequential instructions (in reverse) (_, GraphConstruction phidata graph usedefs)
        emptyConstructionState =  GraphConstructionState Map.empty [] Set.empty Map.empty Set.empty Set.empty Set.empty

        ((_, endState), GraphConstruction (joins, joinPts) partialGraph usedefs) = (runWriter . flip runStateT emptyConstructionState . doGrapher) $ cata4 (Grapher . alg) instrs

        -- 2. Turn our partial graph' into a full one with phidata
        graph = foldl (\g (join, phi) -> Map.unionWith Set.union g $ Map.fromList [(join, Set.singleton $ Map.findWithDefault (error "341") phi joinPtsMap)]) partialGraph joins
        joinPtsMap = Map.fromList $ DList.toList joinPts

        allTags = Map.foldlWithKey (\b k a -> Set.insert k $ b `Set.union` a) Set.empty graph

        alg :: forall o xs n r a. TaggedInstr o (Grapher o) xs n r a -> StateT GraphConstructionState (Writer GraphConstruction) InstrID
        alg (Tag4 t Ret)                 = handlerEdge t >> addRetTag t >> addStump t >> pure t
        alg (Tag4 t (Call (MVar μ) k))   = do
                                            -- handlerEdge t
                                            let notLoop = Map.member μ starts
                                            -- Don't add a real call if loop call.
                                            when notLoop $ do
                                                kt <- doGrapher k
                                                addEdge t kt
                                                addCall μ t kt
                                            return t
        alg (Tag4 t (Push _ k))          = edgeToK t k
        alg (Tag4 t (Pop k))             = edgeToK t k
        alg (Tag4 t (Lift2 _ k))         = edgeToK t k
        alg (Tag4 t (Sat _ k))           = handlerEdge t >> edgeToK t k
        alg (Tag4 t Empt)                = handlerEdge t >> addStump t >> pure t
        alg (Tag4 t (Commit k))          = edgeToK t k
        alg (Tag4 t (Catch p h))         = pushHandler h >> edgeToK t p >> popHandler >> pure t
        alg (Tag4 t (Tell k))            = edgeToK t k
        alg (Tag4 t (Seek k))            = edgeToK t k
        alg (Tag4 t (Case p q))          = edgeToK t p >> edgeToK t q
        alg (Tag4 t (Choices _ ks def))  = traverse_ (edgeToK t) ks >> edgeToK t def
        alg (Tag4 t (Iter (MVar μ) _ l h)) = do
                                                pushHandler h
                                                addLoopTag μ t
                                                entry <- doGrapher l
                                                addEdge t entry
                                                removeLoopTag μ
                                                popHandler
                                                pure t
        alg (Tag4 t (Join φ))            = addJoin t φ >> pure t
        alg (Tag4 t (MkJoin φ _ p k))    = doGrapher p >>= flip addMkJoin φ >> edgeToK t k
        alg (Tag4 t (Swap k))            = edgeToK t k
        alg (Tag4 t (Dup k))             = edgeToK t k
        alg (Tag4 t (Make σ _ k))        = addDef t (SomeΣVar σ) >> edgeToK t k
        alg (Tag4 t (Get σ _ k))         = addUse t (SomeΣVar σ) >> edgeToK t k
        alg (Tag4 t (Put σ _ k))         = addDef t (SomeΣVar σ) >> edgeToK t k
        alg (Tag4 t (SelectPos _ k))     = handlerEdge t >> edgeToK t k
        alg (Tag4 t (LogEnter _ k))      = handlerEdge t >> edgeToK t k
        alg (Tag4 t (LogExit _ k))       = handlerEdge t >> edgeToK t k
        alg (Tag4 t (MetaInstr _ k))     = edgeToK t k

        -- Smart constructors for creating constitutient parts of `GraphConstruction`
        phiGCon :: PhiData -> GraphConstruction
        phiGCon p = GraphConstruction p mempty mempty
        graphGCon :: CFGGraph -> GraphConstruction
        graphGCon g = GraphConstruction mempty g mempty
        refGCon :: UseDefData -> GraphConstruction
        refGCon = GraphConstruction mempty mempty

        -- Various monadic helpers for graph construction
        addJoin t (ΦVar  φ)   = (lift . tell) (phiGCon (DList.fromList [(t, φ)], DList.empty))
        addMkJoin t (ΦVar  φ) = (lift . tell) (phiGCon (DList.empty, DList.fromList [(φ, t)]))
        addStump a = (lift . tell . graphGCon) (Map.fromList [(a, mempty)])
        addEdge a b = (lift . tell . graphGCon) (Map.fromList [(a, Set.singleton b)])

        edgeToK t k = doGrapher k >>= addEdge t >> pure t

        -- Handler state helpers
        pushHandler :: forall o xs n r a. Handler o (Grapher o) xs n r a -> StateT GraphConstructionState (Writer GraphConstruction) HandlerEntry
        pushHandler (Same _ _ k1 _ k2) = do
                                        t1 <- doGrapher k1
                                        t2 <- doGrapher k2
                                        state <- get
                                        let GraphConstructionState{handlerStack, collectedHTags} = state
                                        let h = SameH t1 t2
                                        put state{handlerStack = h:handlerStack, collectedHTags = collectedHTags `Set.union` Set.fromList [t1, t2]}
                                        pure h
        pushHandler (Always _ _ k)     = do
                                        t <- doGrapher k
                                        let h = AlwaysH t
                                        state <- get
                                        let GraphConstructionState{handlerStack, collectedHTags} = state
                                        put state{handlerStack = h:handlerStack, collectedHTags = Set.insert t collectedHTags}
                                        pure h

        popHandler :: StateT GraphConstructionState (Writer GraphConstruction) ()
        popHandler = do
                        state <- get
                        put state{handlerStack = (\(_:hs) -> hs) $ handlerStack state}
        handlerEdge :: InstrID -> StateT GraphConstructionState (Writer GraphConstruction) ()
        handlerEdge t = get >>= (\stack -> do
                                            case stack of
                                                [] -> do
                                                    -- Add this instruction as a handler stump that will be joined later
                                                    state <- get
                                                    put state{collectedHandlerStumps = Set.insert t (collectedHandlerStumps state)}
                                                ((AlwaysH h):_) -> addEdge t h
                                                ((SameH h1 h2 ):_) -> addEdge t h1 >> addEdge t h2) . handlerStack


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

        -- Register call sites 
        addCall :: IMVar -> InstrID -> InstrID -> StateT GraphConstructionState (Writer GraphConstruction) ()
        addCall μ t kt = do
                        state <- get
                        let GraphConstructionState{handlerStack, collectedCallsites} = state
                        let handlerEntry = case handlerStack of
                                                (h:_) -> Just h
                                                [] -> Nothing
                        let cTags = Map.insertWith (++) μ [(t, kt, handlerEntry)] collectedCallsites
                        put $ state{collectedCallsites = cTags}

        addRetTag :: InstrID -> StateT GraphConstructionState (Writer GraphConstruction) ()
        addRetTag t = do
                        state <- get
                        let GraphConstructionState{collectedRetTags} = state
                        put $ state{collectedRetTags = Set.insert t collectedRetTags}

        addTag :: InstrID -> StateT GraphConstructionState (Writer GraphConstruction) ()
        addTag t = do
                    state <- get
                    let GraphConstructionState{collectedTags} = state
                    put state {collectedTags = Set.insert t collectedTags}

algamateGraphs :: CFG -> CFGGraph 
algamateGraphs CFG{graph, subs} = Map.foldl (Map.unionWith Set.union) graph subs 

{-| 
Analyse the CFG and its register data to find data pertaining to register usage such as 
    - Free registers required from  each instruction onwards
    - Handlers free registers and which free handler registers each let bound parser should expect in calls
    - Return continuation free registers
-}
cfgAnalysis :: InstrID -> CFG -> CFGAnalysisData
cfgAnalysis maxID cfg = CFGAnalysisData { livenessSets = livesets
                                            , callAndHandlerRegs = (Map.empty, Map.empty)
                                            , returnContinuations = Map.empty }
    where
        -- 1. make `bigGraph` which is the disjoin union of
        !livesets = propagateRegs $ algamateGraphs cfg
        propagateRegs :: CFGGraph -> Map InstrID (Set SomeΣVar, Set SomeΣVar)
        propagateRegs succ = snd $ execState iter (initWL, initMap)
            where
                -- flip the graph for predessors
                pred = Map.foldlWithKey (\g n nsucc -> foldl
                                            (\g s -> Map.insertWith Set.union s (Set.singleton n) g) g nsucc)
                                        (Map.fromList [(x, mempty) | x <- [0..maxID]]) -- make sure all nodes have an entry in there
                                        succ
                -- All graph nodes
                initWL = Map.keys succ
                initMap = foldl (\a k -> a <> Map.singleton k (mempty,  mempty)) Map.empty [0..maxID]

                iter :: State ([InstrID], Map InstrID (Set SomeΣVar, Set SomeΣVar)) ()
                iter = do
                    node <- popWL
                    propagateNode pred succ node
                    isEmpty <- emptyWL
                    unless isEmpty iter

        popWL :: State ([InstrID], Map InstrID (Set SomeΣVar, Set SomeΣVar)) InstrID
        popWL = do
            (wl, b) <- get
            let (a:as) = wl
            put (as, b)
            return a

        emptyWL :: State ([InstrID], Map InstrID (Set SomeΣVar, Set SomeΣVar)) Bool
        emptyWL  = do
            gets (null . fst)

        propagateNode :: Map InstrID (Set InstrID) -> Map InstrID (Set InstrID) -> InstrID -> State ([InstrID], Map InstrID (Set SomeΣVar, Set SomeΣVar)) ()
        propagateNode pred succ nodeid = do
            (wl, liveSets) <- get
            -- calculate using data-flow equations
            let !(livein, liveout) = Map.findWithDefault (error "515") nodeid liveSets
            let succs = Map.findWithDefault Set.empty nodeid succ
            let liveout' = Set.foldl (\l s -> Set.union l $ fst (liveSets Map.! s)) Set.empty succs  -- eqn.
            let livein' = case Map.lookup nodeid (useDefs cfg) of
                                Just (use, def) -> Set.union use (Set.difference liveout' def) -- use eqn.
                                Nothing -> liveout' -- No use/def data
            put (wl, Map.insert nodeid (livein', liveout') liveSets) -- update live sets in state
            when  (livein' /= livein || liveout' /= liveout) $ do
                    -- update worklist as necessary
                    addToWorkList $ (Map.findWithDefault (error "521") nodeid pred)


        addToWorkList :: Set InstrID -> State ([InstrID], Map InstrID (Set SomeΣVar, Set SomeΣVar)) ()
        addToWorkList preds = do
            (wl, ref) <- get
            put (foldl (flip (:)) wl preds, ref)

        -- 2. use the live sets to find out over which registers are live-out of each sub through their handlers
        {-
        --    a) Which handlers reach which let bound parsers. During construction, we make an edge from the start of each let-bound parser that is called
        --       with all possible handlers it is called under.
        callHandlerConns = Map.foldlWithKey (\hconns k start -> Map.insert k (getHandlerAttached start) hconns ) Map.empty letBoundStarts
        handlerCallConns = Map.foldlWithKey (\acc k x -> Set.foldl (\acc m -> Map.insertWith Set.union m (Set.singleton k) acc ) acc x) Map.empty callHandlerConns

        getHandlerAttached :: InstrID -> Set InstrID
        getHandlerAttached id = Set.filter (flip Set.member handlerTags) (Map.findWithDefault Set.empty id graph)

        --    b) For each MVar, get the union of all the handler's free registers that reach it. Then assign that union to all the reaching
        --       handlers. Repeat till convergence. 
        (_, callerHandlerRegs) = runState (unifyHandlerCallRegs handlerCallConns callHandlerConns) (initCSets, initHSets)
        !initCSets = Map.fromList $ map (\x -> (x, Set.empty :: Set SomeΣVar)) (Map.keys callerTags)
        !initHSets = Map.fromList $ map (\x -> (x, fst $ Map.findWithDefault (error "547") x livesets)) $ Set.toList handlerTags
        unifyHandlerCallRegs :: Map InstrID (Set IMVar) -> Map IMVar (Set InstrID) -> State (Map IMVar (Set SomeΣVar), Map InstrID (Set SomeΣVar)) ()
        unifyHandlerCallRegs hConns cConns = trace ("hConns: " ++ show hConns ++ "\ncConns: " ++ show cConns) $ do
            -- Step 1: accumulate to IMVars
            (cSets, hSets) <- get
            let cSets' = Map.mapWithKey (\mvar s -> Set.foldl (\agg id -> agg `Set.union` (Map.findWithDefault (error "csets'") id hSets)) s (Map.findWithDefault (error "552") mvar cConns)) cSets
            -- Step 2: check for convergence
            unless (cSets' == cSets) $ do
                -- Step 3: propagate new union to handlers
                let hSets' = Map.mapWithKey (\id s -> Set.foldl (\agg id -> agg `Set.union` (Map.findWithDefault (error "hsets'") id cSets')) s (Map.findWithDefault Set.empty id hConns)) hSets
                trace ("TRACE !!!" ++ show (cSets', hSets')) $ pure ()
                put (cSets', hSets')
                unifyHandlerCallRegs hConns cConns
        
        -- 3. find return continuation free registers from `callerTags` data and `frees`.
        retContData = Map.mapWithKey (\k frees -> frees `Set.intersection` (Map.findWithDefault (error "561") k letboundUses)) retFrees
        retFrees = Map.map (\rets -> Set.foldl (\acc ret -> acc `Set.union` (snd $ Map.findWithDefault (error "562") ret livesets)) Set.empty rets) returnTags
        letboundUses = Map.map (\tags -> Set.foldl (\b tag -> b `Set.union` (fst $ Map.findWithDefault (mempty, mempty) tag  useDefs)) Set.empty tags) letBoundTags
        -}


{- 
State for `markRegisterBinds` that keeps track of a few things. 
Used to contain a lot more before the completion of total binds.
-}
data RegMarkerState = RegMarkerState { lastTag :: InstrID }

newtype RegMarker o xs n r a = FreeRegMarker { doFreeRegMarking :: State RegMarkerState (Fix4 (TaggedInstr o) xs n r a) }

{-|
Use the computed `FreeRegisters` to populate our instructions with the free registers they ought to rely upon. 
Significant steps: 
    1. Find all loops and make sure we make all registers bound within all loop bodies, properly
    2. Mark handlers and calls with the proper registers that pass through them 
    3. Mark our return continuation registers as well (TODO)
    4. Mark join point free registers (TODO)
-}
markRegisterBinds :: CFGAnalysisData -> (TaggedBinding input a a, DMap MVar (TaggedBinding input a)) -> (TaggedBinding input a a, DMap MVar (TaggedBinding input a))
markRegisterBinds freeRegsData (p, μs) = (pResult, μsResult)
    where
        pResult = TaggedBinding $ doMarking p
        μsResult = DMap.foldlWithKey (\b k a -> DMap.insert k (TaggedBinding $ doMarking a) b) DMap.empty μs

        -- `frees`: set of free registers
        livesets = livenessSets freeRegsData
        (_, handlerRegs) = callAndHandlerRegs freeRegsData

        -- 1. Mark all free registers
        emptyRegMarkerState = RegMarkerState 0
        doMarking bind = evalState (doFreeRegMarking $ cata4 (FreeRegMarker . alg) $ taggedBody bind) emptyRegMarkerState
        alg :: TaggedInstr o (RegMarker o) xs n r a -> State RegMarkerState (Fix4 (TaggedInstr o) xs n r a)
        alg (Tag4 t Ret)                 = wrap t Ret
        alg (Tag4 t (Call (MVar μ) k))   = do
                                            k' <- doFreeRegMarking k
                                            wrap t (Call (MVar μ)  k')
        alg (Tag4 t (Push x k))          = doFreeRegMarking k >>= wrap t . Push x
        alg (Tag4 t (Pop k))             = doFreeRegMarking k >>= wrap t . Pop
        alg (Tag4 t (Lift2 f k))         = doFreeRegMarking k >>= wrap t . Lift2 f
        alg (Tag4 t (Sat f k))           = doFreeRegMarking k >>= wrap t . Sat f
        alg (Tag4 t Empt)                = wrap t Empt
        alg (Tag4 t (Commit k))          = doFreeRegMarking k >>= wrap t . Commit
        alg (Tag4 t (Catch p h))         = do
                                            p' <- doFreeRegMarking p
                                            h' <- doHandler h
                                            wrap t (Catch p' h')
        alg (Tag4 t (Tell k))            = doFreeRegMarking k >>= wrap t . Tell
        alg (Tag4 t (Seek k))            = doFreeRegMarking k >>= wrap t . Seek
        alg (Tag4 t (Case p q))          = do
                                            p' <- doFreeRegMarking p
                                            q' <- doFreeRegMarking q
                                            wrap t (Case p' q')
        alg (Tag4 t (Choices fs ks def)) = do
                                            ks' <- traverse doFreeRegMarking ks
                                            def' <- doFreeRegMarking def
                                            wrap t (Choices fs ks' def')
        alg (Tag4 t (Iter μ _ l h))      = do
                                            h' <- doHandler h
                                            -- Just bind the frees in loop, not those that escape.
                                            l' <- doFreeRegMarking l
                                            t' <- getLastTag
                                            let regsToBind = fst $ Map.findWithDefault (error "638") t' livesets
                                            wrap t (Iter μ (Just $ makeRegs regsToBind) l' h')
        alg (Tag4 t (Join φ))            = wrap t (Join φ)
        alg (Tag4 t (MkJoin φ _ p k))      = do
                                            p' <- doFreeRegMarking p
                                            t' <- getLastTag
                                            k' <- doFreeRegMarking k
                                            let livein = fst $ Map.findWithDefault (error "648") t' livesets
                                            wrap t (MkJoin φ (Just $ makeRegs livein) p' k')
        alg (Tag4 t (Swap k))            = doFreeRegMarking k >>= wrap t . Swap
        alg (Tag4 t (Dup k))             = doFreeRegMarking k >>= wrap t . Dup
        alg (Tag4 t (Make σ a k))        = do
                                            k' <- doFreeRegMarking k
                                            let a' = case a of 
                                                        Soft -> Soft
                                                        _    -> Bound
                                            wrap t $ Make σ a' k'
        alg (Tag4 t (Get σ a k))         = do
                                            k' <- doFreeRegMarking k
                                            let a' = case a of 
                                                        Soft -> Soft
                                                        _    -> Bound
                                            wrap t $ Get σ a' k'
        alg (Tag4 t (Put σ a k))         = do
                                            k' <- doFreeRegMarking k
                                            let a' = case a of 
                                                        Soft -> Soft
                                                        _    -> Bound
                                            wrap t $ Put σ a' k'
        alg (Tag4 t (SelectPos p k))     = doFreeRegMarking k >>= wrap t . SelectPos p
        alg (Tag4 t (LogEnter l k))      = doFreeRegMarking k >>= wrap t . LogEnter l
        alg (Tag4 t (LogExit l k))       = doFreeRegMarking k >>= wrap t . LogExit l
        alg (Tag4 t (MetaInstr m k))     = doFreeRegMarking k >>= wrap t . MetaInstr m

        wrap :: InstrID -> Instr o (Fix4 (TaggedInstr o)) xs n r a -> State RegMarkerState (Fix4 (TaggedInstr o) xs n r a)
        wrap t instrs = do
                        markLastTag t
                        return $ In4 (Tag4 t instrs)


        wrap' :: InstrID -> Instr o (Fix4 (TaggedInstr o)) xs n r a -> State RegMarkerState (Fix4 (TaggedInstr o) xs n r a)
        wrap' t instrs = modify (\state -> state{lastTag=t}) $> In4 (Tag4 t instrs)

        doHandler :: Handler o (RegMarker o) xs n r a -> State RegMarkerState (Handler o (Fix4 (TaggedInstr o)) xs n r a)
        doHandler (Same _ x k1 y k2) = do
                                        k1' <- doFreeRegMarking k1
                                        t1 <- getLastTag
                                        k2' <- doFreeRegMarking k2
                                        t2 <- getLastTag
                                        let regs = (fst $ Map.findWithDefault (error "692a") t1 livesets) `Set.union` (fst $ Map.findWithDefault (error "692b") t2 livesets)
                                        return (Same (Just $ makeRegs regs) x k1' y k2')
        doHandler (Always _ x k)     = do
                                        k' <- doFreeRegMarking k
                                        tlast <- getLastTag
                                        let regs = fst $ Map.findWithDefault (error $ "804") tlast livesets
                                        return (Always (Just $ makeRegs regs) x k')

        markLastTag :: InstrID -> State RegMarkerState ()
        markLastTag t = get >>= (\state -> put state{lastTag=t})

        getLastTag :: State RegMarkerState InstrID
        getLastTag = get >>= (pure . lastTag)

{-| 
Forgetfully removes tags from instructions. 
-}
unTag :: Fix4 (TaggedInstr o) xs n r a -> Fix4 (Instr o) xs n r a
unTag = cata4 alg
    where
        alg :: TaggedInstr o (Fix4 (Instr o)) xs n r a -> Fix4 (Instr o) xs n r a
        alg Tag4{tagged} = In4 tagged

-- Compute the DOT program of a given graph. Slow, but useful for debugging CFG problems
_computeDOT :: CFG -> CFGAnalysisData -> String
_computeDOT cfg CFGAnalysisData{livenessSets} = computedCFG ""
    where
        graph = algamateGraphs cfg
        CFG{start, useDefs, letBoundStarts, handlerTags, letBoundTags} = cfg
        showNode :: InstrID -> ShowS
        showNode id = "N" . shows id

        showConn :: InstrID -> Set InstrID -> ShowS
        showConn a bs = Set.foldl (\head b -> head . " " . showNode b) (" " . showNode a . " -> {") bs . "}\n"

        computeGraph :: ShowS -> Set InstrID -> ShowS
        computeGraph name instrs = Set.foldl (\head a -> head . showConn a (Map.findWithDefault Set.empty a graph)) header instrs . "}\n"
            where
                header = "subgraph " . name . "{ \n"  . thing . name . "\";\n"
                thing = " label = \"" :: ShowS
        
        allNodes = Map.foldlWithKey (\acc k b -> Set.insert k (acc `Set.union` b)) Set.empty graph
        letBoundNodes = Map.foldl Set.union Set.empty letBoundTags
        isTopLevel x = not $ Set.member x letBoundNodes
        topLevelNodes = Set.filter isTopLevel allNodes

        computedCFG :: ShowS
        computedCFG = "digraph {\n" . toplevel . "\n\n" . letboundsShown . "\n" . startTag . computeHTags handlerTags . usedefs . parserStarts . "}\n"
            where
                letbounds = Map.mapWithKey (\k b -> computeGraph ("mu_" . shows k) b) letBoundTags
                letboundsShown = Map.foldl (.) ("" :: ShowS) letbounds
                toplevel = computeGraph "top_level" topLevelNodes
                startTag = " " . showNode start . " [style=filled, color=red, shape=Msquare];\n" :: ShowS
                parserStarts = Map.foldlWithKey (\acc mu x -> acc . showNode x . "[label=\"" . showNode x . "[" .shows mu . "]\"style=filled,color=red];\n") ("" :: ShowS) letBoundStarts
                usedefs = attachLabelsToNodes allNodes

        computeHTags :: Set InstrID -> ShowS
        computeHTags = Set.foldl (\b a -> b . " " . showNode a . " [style=filled, color=green];\n") ("" :: ShowS)

        attachLabelsToNodes :: Set InstrID -> ShowS
        attachLabelsToNodes = Set.foldl (\b a -> b . attachLabel a . "\n") ("\n" :: ShowS)

        attachLabel :: InstrID -> ShowS
        attachLabel id = " " . showNode id . (" [xlabel=\"" :: ShowS) . label . "\"];"
            where
                label = udlabel . freelabel
                udlabel = if Map.member id useDefs then "UD: (" . shows (Set.toList use) . "," . shows (Set.toList def) . ")\\n" else ""
                freelabel = ("live sets: " :: ShowS) . if Map.member id livenessSets then shows (both Set.toList (livenessSets Map.! id)) else "{0}"
                (use, def) = useDefs Map.! id
        
        both f (a,b) = (f a, f b)