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

import Parsley.Internal.Common.Fresh (HFresh, MonadFresh(..), runFresh)
import Parsley.Internal.Common.Indexed (Fix4, IFunctor4)
import Parsley.Internal.Common.Utils (intercalateDiff)
import Parsley.Internal.Common.Indexed (Fix4 (..), Const4 (..), cata4, IFunctor4 (imap4))
import Parsley.Internal.Backend.Machine.Identifiers (SomeΣVar(..), IΦVar, ΦVar(..), IMVar, MVar (..))
import Parsley.Internal.Backend.Machine.Instructions (Instr(..), Handler(..), PosSelector(..), MetaInstr(..))
import Parsley.Internal.Backend.Machine.Types.Registers (makeRegs)

import Control.Monad.Writer (Writer, MonadWriter (..))
import Control.Monad.Writer.Lazy (runWriter)
import Control.Monad.State (StateT (..), MonadTrans (..), MonadState (..), when, runState, evalState)
import Control.Monad.State.Lazy (State)
import Control.Monad.State (gets, execState)
import Control.Monad (unless, liftM2)
import Debug.Trace (trace)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.DList (DList)
import qualified Data.DList as DList
import Data.Void (Void)
import Parsley.Internal.Backend.Machine (Input)
import Parsley.Internal.Opt (Flags)
import Parsley.Internal.Trace (Trace)
import Parsley.Internal.Backend.Machine.LetBindings (LetBinding)
import Data.Dependent.Map (DMap)


bindReferences :: forall input a. (Input input, Trace, ?flags::Flags) => (LetBinding input a a, DMap MVar (LetBinding input a)) -> (LetBinding input a a, DMap MVar (LetBinding input a))
bindReferences (p, μs) = (p, μs) 
    where
        -- 1. tag the instructions
        -- (taggedInstrs, maxTag) = tagInstructions instrs

        -- 2. Perform analysis to get map of Instruction ID -> references that are free at some point here
        -- threadables = threadableRefs maxTag taggedInstrs

        -- 3. Use `liveSets` to tag each join point, handler, and return continuation with references that might live through it
        -- TOOD

        -- 4. Mark loop bodies
        -- instrs' = markLoopBodies frees threadables taggedInstrs


-- We need to tag each instruction with a unique ID so we can perform liveness analysis
data Tag4 t f k xs n r a = Tag4 {tag :: t, tagged :: f k xs n r a} deriving stock Show
instance IFunctor4 f => IFunctor4 (Tag4 t f) where
    imap4 f Tag4{tag, tagged} = Tag4 tag (imap4 f tagged)

type InstrID = Int
type TaggedInstr a = Tag4 InstrID (Instr a)
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

newtype Tagger o xs n r a = Tagger {doTagger :: HFresh InstrID (Fix4 (TaggedInstr o) xs n r a)}
-- mcata
tagInstructions :: Fix4 (Instr o) xs n r a -> (Fix4 (TaggedInstr o) xs n r a, Int)
tagInstructions instrs = runFresh (doTagger $ cata4 alg instrs) initID
    where
        initID = 0 :: InstrID

        wrap p = newVar >>= (\t -> return (In4 (Tag4 t p)))

        alg :: Instr o (Tagger o) xs n r a -> Tagger o xs n r a
        alg Ret                 = Tagger $ wrap Ret
        alg (Call μ l k)        = Tagger $ doTagger k >>= (wrap . Call μ l)
        alg (Push x k)          = Tagger $ doTagger k >>= (wrap . Push x)
        alg (Pop k)             = Tagger $ doTagger k >>= (wrap . Pop)
        alg (Lift2 f k)         = Tagger $ doTagger k >>= (wrap . Lift2 f)
        alg (Sat f k)           = Tagger $ doTagger k >>= (wrap . Sat f)
        alg Empt                = Tagger $ wrap Empt
        alg (Commit k)          = Tagger $ doTagger k >>= (wrap . Commit)
        alg (Catch p h)         = Tagger $ do
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
        alg (Tell k)            = Tagger $ doTagger k >>= (wrap . Tell)
        alg (Seek k)            = Tagger $ doTagger k >>= (wrap . Seek)
        alg (Case p q)          = Tagger $ do
                                    p' <- doTagger p
                                    q' <- doTagger q
                                    wrap (Case p' q')
        alg (Choices fs ks def) = Tagger $ do
                                    ks' <- traverse doTagger ks
                                    def' <- doTagger def
                                    wrap (Choices fs ks' def')
        alg (Iter μ _ l h)        = Tagger $ do
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
        alg (Join φ)            = Tagger $ wrap (Join φ)
        alg (MkJoin φ p k)      = Tagger $ do
                                    p' <- doTagger p
                                    k' <- doTagger k
                                    wrap (MkJoin φ p' k')
        alg (Swap k)            = Tagger $ doTagger k >>= (wrap . Swap)
        alg (Dup k)             = Tagger $ doTagger k >>= (wrap . Dup)
        alg (Make σ a k)        = Tagger $ doTagger k >>= (wrap . Make σ a)
        alg (Get σ a k)         = Tagger $ doTagger k >>= (wrap . Get σ a)
        alg (Put σ a k)         = Tagger $ doTagger k >>= (wrap . Put σ a)
        alg (SelectPos p k)     = Tagger $ doTagger k >>= (wrap . SelectPos p)
        alg (LogEnter l k)      = Tagger $ doTagger k >>= (wrap . LogEnter l)
        alg (LogExit l k)       = Tagger $ doTagger k >>= (wrap . LogExit l)
        alg (MetaInstr m k)     = Tagger $ doTagger k >>= (wrap . MetaInstr m)

-- Finding threadable references

-- Graph construction types
type ThreadableRefs = Map InstrID (Set SomeΣVar)
-- PhiData: (InstrID of join to ΦVar, IΦVar to join point's InstrID )
type PhiData = (DList (InstrID, IΦVar), DList (IΦVar, InstrID))
newtype Graph = Graph { unGraph :: Map InstrID (Set InstrID) }

instance Semigroup Graph where
    a <> b = Graph $ Map.unionWith Set.union (unGraph a) (unGraph b)
instance Monoid Graph where
    mempty = Graph Map.empty

-- map instrID to (use, def)
type ReferenceData = Map InstrID (Set SomeΣVar, Set SomeΣVar)

data GraphConstruction = GraphConstruction{ phiData :: PhiData, graphData :: Graph, refData :: ReferenceData}

-- Smart constructors for creating constitutient parts of `GraphConstruction`
phiGCon p = GraphConstruction p mempty mempty
graphGCon g = GraphConstruction mempty g mempty
refGCon = GraphConstruction mempty mempty

instance Semigroup GraphConstruction where
    (GraphConstruction p1 g1 r1) <> (GraphConstruction p2 g2 r2) = GraphConstruction (p1 <> p2) (g1 <> g2) (r1 <> r2)
instance Monoid GraphConstruction where
    mempty = GraphConstruction mempty mempty mempty

-- LoopAndHandlerScope: stack of handler insturction IDs
data HandlerEntry = SameH InstrID InstrID | AlwaysH InstrID deriving stock Show
type HandlerEntries = [HandlerEntry]

-- Grapher: State for if we are in a loop body and what the beginning instruction of the current handler is. Moreover,
--          a `Writer` instance to write the graph into as well as  record  data about Phi Joins and MkJoins that will
--          be joined later
newtype Grapher o xs n r a = Grapher {doGrapher :: StateT HandlerEntries (Writer GraphConstruction) InstrID }

threadableRefs :: InstrID -> Fix4 (TaggedInstr o) xs n r a -> ThreadableRefs
threadableRefs maxID instrs = result
    where
        -- 1. Construct graph by attaching join points, loops, and sequential instructions (in reverse) (_, GraphConstruction phidata graph usedefs)

        (_, GraphConstruction phidata graph' usedefs) = (runWriter . flip runStateT [] . doGrapher) $ cata4 (Grapher . alg) instrs
        -- Turn our partial graph' into a full one with phidata
        graph = Graph $ foldl (\g (join, phi) -> Map.unionWith Set.union g $ Map.fromList [(join, Set.singleton $ joinPtsMap Map.! phi)]) (unGraph graph') joins
            where
                (joins, joinPts) = phidata
                joinPtsMap = Map.fromList $ DList.toList joinPts

        alg :: TaggedInstr o (Grapher o) xs n r a ->  StateT HandlerEntries (Writer GraphConstruction) InstrID
        alg (Tag4 t Ret)                = handlerEdge t >> addStump t >> pure t
        alg (Tag4 t (Call _ _ k))       = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Push _ k))         = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Pop k))            = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Lift2 _ k))        = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Sat _ k))          = handlerEdge t >> edgeToK t k
        alg (Tag4 t Empt)               = handlerEdge t >> addStump t >> pure t
        alg (Tag4 t (Commit k))         = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Catch p h))        = handlerEdge t >> pushHandler h >> edgeToK t p >> popHandler >> pure t
        alg (Tag4 t (Tell k))           = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Seek k))           = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Case p q))         = handlerEdge t >> edgeToK t p >> edgeToK t q
        alg (Tag4 t (Choices _ ks def)) = handlerEdge t >> traverse (edgeToK t) ks >> edgeToK t def
        alg (Tag4 t (Iter _ _ l h))     = do
                                                handlerEdge t
                                                he <- pushHandler h
                                                entry <- doGrapher l
                                                addEdge t entry
                                                -- FIXME: this is semantically incorrect (we won't leave the handler back to the loop), 
                                                --        but it is functionally correct for the control-flow structure we care about.
                                                --        Only efficient fix I can think of includes threading _even more_ state around
                                                -- Join loop iterations together
                                                case he of
                                                    (SameH a _) -> addEdge a entry
                                                    (AlwaysH a) -> addEdge a entry
                                                popHandler
                                                pure t
        alg (Tag4 t (Join φ))           = handlerEdge t >> addJoin t φ >> pure t
        alg (Tag4 t (MkJoin φ p k))     = handlerEdge t >> doGrapher p >>= flip addMkJoin φ >> edgeToK t k
        alg (Tag4 t (Swap k))           = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Dup k))            = handlerEdge t >> edgeToK t k
        alg (Tag4 t (Make σ _ k))       = handlerEdge t >> addDef t (SomeΣVar σ) >> edgeToK t k
        alg (Tag4 t (Get σ _ k))        = handlerEdge t >> addUse t (SomeΣVar σ) >> edgeToK t k
        alg (Tag4 t (Put σ _ k))        = handlerEdge t >> addUse t (SomeΣVar σ) >> edgeToK t k
        alg (Tag4 t (SelectPos _ k))    = handlerEdge t >> edgeToK t k
        alg (Tag4 t (LogEnter _ k))     = handlerEdge t >> edgeToK t k
        alg (Tag4 t (LogExit _ k))      = handlerEdge t >> edgeToK t k
        alg (Tag4 t (MetaInstr _ k))    = handlerEdge t >> edgeToK t k

        -- Various monadic helpers for graph construction
        addJoin t (ΦVar  φ)   = (lift . tell) (phiGCon (DList.fromList [(t, φ)], DList.empty))
        addMkJoin t (ΦVar  φ) = (lift . tell) (phiGCon (DList.empty, DList.fromList [(φ, t)]))

        addStump a = (lift . tell . graphGCon . Graph) (Map.fromList [(a, mempty)])
        addEdge a b = (lift . tell . graphGCon . Graph) (Map.fromList [(a, Set.singleton b)])
        edgeToK t k = doGrapher k >>= addEdge t >> pure t

        pushHandler :: Handler o (Grapher o) xs n r a -> StateT HandlerEntries (Writer GraphConstruction) HandlerEntry
        pushHandler (Same _ k1 _ k2) = do
                                        stack <- get
                                        t1 <- doGrapher k1
                                        t2 <- doGrapher k2
                                        let h = SameH t1 t2
                                        put (h:stack)
                                        pure h
        pushHandler (Always _ k)     = do
                                        stack <- get
                                        t <- doGrapher k
                                        let h = AlwaysH t
                                        put (h:stack)
                                        pure h

        popHandler :: StateT HandlerEntries (Writer GraphConstruction) ()
        popHandler = get >>= (\stack -> put $ case stack of
                                                [] -> []
                                                (_:hs) -> hs)

        handlerEdge t = get >>= \stack -> do
                                            case stack of
                                                [] -> pure ()
                                                ((AlwaysH h):_) -> addEdge t h
                                                ((SameH h1 h2 ):_) -> addEdge t h1 >> addEdge t h2

        addUse t σ = (lift . tell . refGCon . Map.fromList) [(t, (Set.singleton σ, mempty))]
        addDef t σ = (lift . tell . refGCon . Map.fromList) [(t, (mempty, Set.singleton σ))]

        -- 2. Propagate the (use, def) sets of each node through the graph using the data-flow equations
        usedefs' = propagateRegs graph usedefs
        propagateRegs :: Graph -> ReferenceData -> ReferenceData
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

                iter :: State ([InstrID], ReferenceData) ()
                iter = do
                    node <- popWL
                    propagateNode pred succ node
                    isEmpty <- emptyWL
                    unless isEmpty iter


        popWL :: State ([InstrID], ReferenceData) InstrID
        popWL = do
            (wl, b) <- get
            let (a:as) = wl
            put (as, b)
            return a
        emptyWL :: State ([InstrID], ReferenceData) Bool
        emptyWL  = do
            gets (null . fst)

        propagateNode :: Map InstrID (Set InstrID) -> Map InstrID (Set InstrID) -> InstrID -> State ([InstrID], ReferenceData) ()
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

        addToWorkList :: Set InstrID -> State ([InstrID], ReferenceData) ()
        addToWorkList preds = do
            (wl, ref) <- get
            put (foldl (flip (:)) wl preds, ref)

        -- 3. use the instrID -> (use, def) data to get the "future free registers" from each node with
        --    free = use \ def
        result = Map.map (uncurry (Set.\\)) usedefs'

markThreadables :: ThreadableRefs -> Fix4 (TaggedInstr o) xs n r a -> Fix4 (Instr o) xs n r a
markThreadables frees = undefined
    where
        alg :: ThreadableRefs -> TaggedInstr o (Fix4 (Instr o)) xs n r a -> Fix4 (Instr o) xs n r a
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
data LoopMarkerState = LoopMarkerState { loops :: Map IMVar (Set SomeΣVar) }
newtype LoopMarker o xs n r a = LoopMarker {doLoopMarking :: State LoopMarkerState (Fix4 (Instr o) xs n r a) }


markLoopBodies :: Map IMVar (Set SomeΣVar) -> ThreadableRefs -> Fix4 (TaggedInstr o) xs n r a -> Fix4 (Instr o) xs n r a
markLoopBodies mufrees frees instrs = evalState marking emptyLoopMarkerState
    where
        emptyLoopMarkerState = LoopMarkerState Map.empty
        marking = doLoopMarking $ cata4 (LoopMarker . alg) instrs
        alg :: TaggedInstr o (LoopMarker o) xs n r a -> State LoopMarkerState (Fix4 (Instr o) xs n r a)
        alg (Tag4 _ Ret)                 = wrap Ret
        alg (Tag4 _ (Call (MVar μ) _ k)) = do
                                            LoopMarkerState{loops} <- get
                                            k' <- doLoopMarking k
                                            if Map.member μ loops
                                                then wrap (Call (MVar μ) True k')
                                                else wrap (Call (MVar μ) False k')
        alg (Tag4 _ (Push x k))          = doLoopMarking k >>= wrap . Push x
        alg (Tag4 _ (Pop k))             = doLoopMarking k >>= wrap . Pop
        alg (Tag4 _ (Lift2 f k))         = doLoopMarking k >>= wrap . Lift2 f
        alg (Tag4 _ (Sat f k))           = doLoopMarking k >>= wrap . Sat f
        alg (Tag4 _ Empt)                = wrap Empt
        alg (Tag4 _ (Commit k))          = doLoopMarking k >>= wrap . Commit
        alg (Tag4 _ (Catch p h))         = do
                                            p' <- doLoopMarking p
                                            h' <- doHandler h
                                            wrap (Catch p' h')
        alg (Tag4 _ (Tell k))            = doLoopMarking k >>= wrap . Tell
        alg (Tag4 _ (Seek k))            = doLoopMarking k >>= wrap . Seek
        alg (Tag4 _ (Case p q))          = do
                                            p' <- doLoopMarking p
                                            q' <- doLoopMarking q
                                            wrap (Case p' q')
        alg (Tag4 _ (Choices fs ks def)) = do
                                            ks' <- traverse doLoopMarking ks
                                            def' <- doLoopMarking def
                                            wrap (Choices fs ks' def')
        alg (Tag4 t (Iter μ _ l h))      = do
                                            let loopRegs = frees Map.! t
                                            addLoop μ loopRegs
                                            l' <- doLoopMarking l
                                            removeLoop μ
                                            h' <- doHandler h
                                            wrap (Iter μ (Just $ makeRegs loopRegs) l' h')
        alg (Tag4 _ (Join φ))            = wrap (Join φ)
        alg (Tag4 _ (MkJoin φ p k))      = do
                                            p' <- doLoopMarking p
                                            k' <- doLoopMarking k
                                            wrap (MkJoin φ p' k')
        alg (Tag4 _ (Swap k))            = doLoopMarking k >>= wrap . Swap
        alg (Tag4 _ (Dup k))             = doLoopMarking k >>= wrap . Dup
        alg (Tag4 _ (Make σ a k))        = doLoopMarking k >>= wrap . Make σ a -- TODO: turn to bounded access if possible
        alg (Tag4 _ (Get σ a k))         = doLoopMarking k >>= wrap . Get σ a -- TODO: turn to bounded access if possible
        alg (Tag4 _ (Put σ a k))         = doLoopMarking k >>= wrap . Put σ a -- TODO: turn to bounded access if possible
        alg (Tag4 _ (SelectPos p k))     = doLoopMarking k >>= wrap . SelectPos p
        alg (Tag4 _ (LogEnter l k))      = doLoopMarking k >>= wrap . LogEnter l
        alg (Tag4 _ (LogExit l k))       = doLoopMarking k >>= wrap . LogExit l
        alg (Tag4 _ (MetaInstr m k))     = doLoopMarking k >>= wrap . MetaInstr m

        addLoop :: MVar Void -> Set SomeΣVar -> State LoopMarkerState ()
        addLoop (MVar μ) loopRegs = do 
                        state <- get 
                        put (state{loops = Map.insert μ loopRegs (loops state)})

        removeLoop :: MVar Void -> State LoopMarkerState ()
        removeLoop (MVar μ) = do 
                        state <- get 
                        put (state{loops = Map.delete μ (loops state)})

        wrap :: Instr o (Fix4 (Instr o)) xs n r a -> State LoopMarkerState (Fix4 (Instr o) xs n r a)
        wrap = pure . In4

        doHandler :: Handler o (LoopMarker o) xs n r a -> State LoopMarkerState (Handler o (Fix4 (Instr o)) xs n r a)
        doHandler (Same x k1 y k2) = do
                                        k1' <- doLoopMarking k1
                                        k2' <- doLoopMarking k2
                                        return (Same x k1' y k2')
        doHandler (Always x k)     = do
                                        k' <- doLoopMarking k
                                        return (Always x k')