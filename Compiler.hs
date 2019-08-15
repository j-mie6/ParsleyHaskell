{-# LANGUAGE GADTs,
             DataKinds,
             RecursiveDo,
             RankNTypes,
             BangPatterns,
             MagicHash,
             FlexibleContexts,
             MultiWayIf,
             FlexibleInstances, 
             MultiParamTypeClasses, 
             UndecidableInstances, 
             AllowAmbiguousTypes,
             ScopedTypeVariables #-}
module Compiler(compile) where

import Prelude hiding (pred)
import ParserAST                  (ParserF(..), Parser(..), Reg(..))
import Optimiser                  (optimise)
import Analyser                   (terminationAnalysis, freeRegisters)
import CodeGenerator              (codeGen, halt, ret)
import Machine                    (Machine(..), IMVar, IΣVar, MVar(..), LetBinding(..))
import Indexed                    (Free(Op), Void1, fold, fold', absurd, Tag(..))
import Control.Applicative        (liftA, liftA2, liftA3)
import Control.Monad              (forM, forM_)
import Control.Monad.Reader       (Reader, runReader, local, ask, asks, MonadReader)
import Control.Monad.State.Strict (State, StateT, get, gets, put, runState, execStateT, modify', MonadState)
import Data.List                  (foldl')
import Fresh                      (HFreshT, newVar, newScope, runFreshT)
import System.IO.Unsafe           (unsafePerformIO)
import Data.IORef                 (IORef, newIORef, readIORef, writeIORef)
import GHC.StableName             (StableName(..), makeStableName, hashStableName, eqStableName)
import Data.Hashable              (Hashable, hashWithSalt, hash)
import Data.HashMap.Strict        (HashMap)
import Data.HashSet               (HashSet)
import Data.Dependent.Map         (DMap)
import GHC.Prim                   (StableName#, unsafeCoerce#)
import GHC.Exts                   (Int(..))
import Debug.Trace                (trace)
import qualified Data.HashMap.Strict as HashMap ((!), lookup, insert, empty, insertWith, foldrWithKey)
import qualified Data.HashSet        as HashSet (member, insert, empty, union)
import qualified Data.Dependent.Map  as DMap    ((!), empty, insert, foldrWithKey, size)
import qualified Data.Set            as Set     (null)

compile :: Parser a -> (Machine o a, DMap MVar (LetBinding o a), [IMVar])
compile (Parser p) = 
  let !(p', μs, maxV, topo) = preprocess p
      !(m, maxΣ) = codeGen ({-terminationAnalysis -}p') halt (maxV + 1) 0
      !ms = compileLets μs (maxV + 1) maxΣ
  in trace ("COMPILING NEW PARSER WITH " ++ show ((DMap.size ms)) ++ " LET BINDINGS") $ (Machine m, ms, topo)

compileLets :: DMap MVar (Free ParserF Void1) -> IMVar -> IΣVar -> DMap MVar (LetBinding o a)
compileLets μs maxV maxΣ = let (ms, _) = DMap.foldrWithKey compileLet (DMap.empty, maxΣ) μs in ms
  where
    compileLet :: MVar x -> Free ParserF Void1 x -> (DMap MVar (LetBinding o a), IΣVar) -> (DMap MVar (LetBinding o a), IΣVar)
    compileLet (MVar μ) p (ms, maxΣ) =
      let (m, maxΣ') = codeGen p ret maxV (maxΣ + 1)
      in (DMap.insert (MVar μ) (LetBinding m (not (Set.null (freeRegisters p)))) ms, maxΣ')

preprocess :: Free ParserF Void1 a -> (Free ParserF Void1 a, DMap MVar (Free ParserF Void1), IMVar, [IMVar])
preprocess p =
  let q = tagParser p
      (lets, recs, topo) = findLets q
  in letInsertion lets recs topo q

data ParserName = forall a. ParserName (StableName# (Free ParserF Void1 a))
newtype Tagger a = Tagger { runTagger :: Free (Tag ParserName ParserF) Void1 a }

{-  TODO
    Need to preserve the numRegister count to prevent interference with registers created in CodeGen
    Ensure that top-level parser can still demand emergency binding
-}

tagParser :: Free ParserF Void1 a -> Free (Tag ParserName ParserF) Void1 a
tagParser = runTagger . fold' absurd alg
  where
    regMaker = newRegMaker
    concretiseRegister :: forall a b. Tagger a -> (forall r. Reg r a -> Tagger b) 
                                               -> (forall r. Reg r a -> ParserF (Free (Tag ParserName ParserF) Void1) b)
    concretiseRegister p g reg = let q = g reg in NewRegister reg (runTagger p) (runTagger q)
    alg p q = Tagger $
      let mkTag = Op . Tag (makeParserName p)
      in case q of
        pf :<*>: px       -> mkTag (runTagger pf :<*>: runTagger px)
        p :*>: q          -> mkTag (runTagger p :*>: runTagger q)
        p :<*: q          -> mkTag (runTagger p :<*: runTagger q)
        p :<|>: q         -> mkTag (runTagger p :<|>: runTagger q)
        Try n p           -> mkTag (Try n (runTagger p))
        LookAhead p       -> mkTag (LookAhead (runTagger p))
        NotFollowedBy p   -> mkTag (NotFollowedBy (runTagger p))
        Branch b p q      -> mkTag (Branch (runTagger b) (runTagger p) (runTagger q))
        Match p fs qs d   -> mkTag (Match (runTagger p) fs (map runTagger qs) (runTagger d))
        ChainPre op p     -> mkTag (ChainPre (runTagger op) (runTagger p))
        ChainPost p op    -> mkTag (ChainPost (runTagger p) (runTagger op))
        Debug name p      -> mkTag (Debug name (runTagger p))
        Pure x            -> mkTag (Pure x)
        Empty             -> mkTag Empty
        Satisfy f         -> mkTag (Satisfy f)
        GetRegister r     -> mkTag (GetRegister r)
        PutRegister r p   -> mkTag (PutRegister r (runTagger p))
        ScopeRegister p g -> mkTag (freshReg regMaker (concretiseRegister p g))

data LetFinderState = LetFinderState { preds  :: HashMap ParserName Int
                                     , recs   :: HashSet ParserName
                                     , before :: HashSet ParserName
                                     , topo   :: [ParserName] }
type LetFinderCtx   = HashSet ParserName
newtype LetFinder a = LetFinder { runLetFinder :: StateT LetFinderState (Reader LetFinderCtx) () }

reverseFilter :: (a -> Bool) -> [a] -> [a]
reverseFilter p = foldl' (\xs x -> if p x then x : xs else xs) []

findLets :: Free (Tag ParserName ParserF) Void1 a -> (HashSet ParserName, HashSet ParserName, [ParserName])
findLets p = (lets, recs, reverseFilter letBound topo)
  where
    letBound = flip HashSet.member (HashSet.union lets recs)
    state = LetFinderState HashMap.empty HashSet.empty HashSet.empty []
    ctx = HashSet.empty
    LetFinderState preds recs _ topo = runReader (execStateT (runLetFinder (fold absurd findLetsAlg p)) state) ctx
    lets = HashMap.foldrWithKey (\k n ls -> if n > 1 then HashSet.insert k ls else ls) HashSet.empty preds

findLetsAlg :: Tag ParserName ParserF LetFinder a -> LetFinder a
findLetsAlg p = LetFinder $ do 
  let name = tag p
  let q = tagged p
  addPred name
  ifSeen name 
    (do addRec name)
    (ifNotProcessedBefore name
      (do addName name (case q of
            pf :<*>: px       -> do runLetFinder pf; runLetFinder px
            p :*>: q          -> do runLetFinder p;  runLetFinder q
            p :<*: q          -> do runLetFinder p;  runLetFinder q
            p :<|>: q         -> do runLetFinder p;  runLetFinder q
            Try n p           -> do runLetFinder p
            LookAhead p       -> do runLetFinder p
            NotFollowedBy p   -> do runLetFinder p
            Branch b p q      -> do runLetFinder b;  runLetFinder p; runLetFinder q
            Match p _ qs d    -> do runLetFinder p;  forM_ qs runLetFinder; runLetFinder d
            ChainPre op p     -> do runLetFinder op; runLetFinder p
            ChainPost p op    -> do runLetFinder p;  runLetFinder op
            Debug _ p         -> do runLetFinder p
            PutRegister _ p   -> do runLetFinder p
            NewRegister _ p q -> do runLetFinder p; runLetFinder q
            _                 -> do return ())
          doNotProcessAgain name
          addToTopology name))

newtype LetInserter a =
  LetInserter {
      runLetInserter :: HFreshT IMVar 
                        (State ( HashMap ParserName IMVar
                               , DMap MVar (Free ParserF Void1))) 
                        (Free ParserF Void1 a)
    }
letInsertion :: HashSet ParserName -> HashSet ParserName -> [ParserName] -> Free (Tag ParserName ParserF) Void1 a -> (Free ParserF Void1 a, DMap MVar (Free ParserF Void1), IMVar, [IMVar])
letInsertion lets recs topo p = (p', μs, μMax, map (vs HashMap.!) topo)
  where
    m = fold absurd alg p
    ((p', μMax), (vs, μs)) = runState (runFreshT (runLetInserter m) 0) (HashMap.empty, DMap.empty)
    alg :: Tag ParserName ParserF LetInserter a -> LetInserter a
    alg p = LetInserter $ do
      let name = tag p
      let q = tagged p
      (vs, μs) <- get
      if | HashSet.member name recs ->
             case HashMap.lookup name vs of
               Just v  -> let μ = MVar v in return $! Op (Let True μ (μs DMap.! μ))
               Nothing -> mdo
                 v <- newVar
                 let μ = MVar v
                 put (HashMap.insert name v vs, DMap.insert μ q' μs)
                 q' <- runLetInserter (postprocess q)
                 return $! Op (Let True μ q')
         | HashSet.member name lets ->
             case HashMap.lookup name vs of
               Just v  -> let μ = MVar v in return $! optimise (Let False μ (μs DMap.! μ))
               Nothing -> mdo -- no mdo here, let bindings are not recursive! (well, actually, I want to do the put before the recursion soooo....)
                 v <- newVar
                 let μ = MVar v
                 put (HashMap.insert name v vs, DMap.insert μ q' μs)
                 q' <- runLetInserter (postprocess q)
                 return $! optimise (Let False μ q')
         | otherwise -> do runLetInserter (postprocess q)

postprocess :: ParserF LetInserter a -> LetInserter a
postprocess (pf :<*>: px)       = LetInserter (fmap optimise (liftA2 (:<*>:) (runLetInserter pf) (runLetInserter px)))
postprocess (p :*>: q)          = LetInserter (fmap optimise (liftA2 (:*>:)  (runLetInserter p)  (runLetInserter q)))
postprocess (p :<*: q)          = LetInserter (fmap optimise (liftA2 (:<*:)  (runLetInserter p)  (runLetInserter q)))
postprocess (p :<|>: q)         = LetInserter (fmap optimise (liftA2 (:<|>:) (runLetInserter p)  (runLetInserter q)))
postprocess Empty               = LetInserter (return        (Op Empty))
postprocess (Try n p)           = LetInserter (fmap optimise (fmap (Try n) (runLetInserter p)))
postprocess (LookAhead p)       = LetInserter (fmap optimise (fmap LookAhead (runLetInserter p)))
postprocess (NotFollowedBy p)   = LetInserter (fmap optimise (fmap NotFollowedBy (runLetInserter p)))
postprocess (Branch b p q)      = LetInserter (fmap optimise (liftA3 Branch (runLetInserter b) (runLetInserter p) (runLetInserter q)))
postprocess (Match p fs qs d)   = LetInserter (fmap optimise (liftA4 Match (runLetInserter p) (return fs) (traverse runLetInserter qs) (runLetInserter d)))
postprocess (ChainPre op p)     = LetInserter (fmap Op       (liftA2 ChainPre (runLetInserter op) (runLetInserter p)))
postprocess (ChainPost p op)    = LetInserter (fmap Op       (liftA2 ChainPost (runLetInserter p) (runLetInserter op)))
postprocess (Debug name p)      = LetInserter (fmap Op       (fmap (Debug name) (runLetInserter p)))
postprocess (Pure x)            = LetInserter (return        (Op (Pure x)))
postprocess (Satisfy f)         = LetInserter (return        (Op (Satisfy f)))
postprocess (GetRegister r)     = LetInserter (return        (Op (GetRegister r)))
postprocess (PutRegister r p)   = LetInserter (fmap optimise (fmap (PutRegister r) (runLetInserter p)))
postprocess (NewRegister r p q) = LetInserter (fmap optimise (liftA2 (NewRegister r) (runLetInserter p) (runLetInserter q)))

getPreds :: MonadState LetFinderState m => m (HashMap ParserName Int)
getPreds = gets preds

getRecs :: MonadState LetFinderState m => m (HashSet ParserName)
getRecs = gets recs

getBefore :: MonadState LetFinderState m => m (HashSet ParserName)
getBefore = gets before

modifyPreds :: MonadState LetFinderState m => (HashMap ParserName Int -> HashMap ParserName Int) -> m ()
modifyPreds f = modify' (\st -> st {preds = f (preds st)})

modifyRecs :: MonadState LetFinderState m => (HashSet ParserName -> HashSet ParserName) -> m ()
modifyRecs f = modify' (\st -> st {recs = f (recs st)})

modifyBefore :: MonadState LetFinderState m => (HashSet ParserName -> HashSet ParserName) -> m ()
modifyBefore f = modify' (\st -> st {before = f (before st)})

modifyTopo :: MonadState LetFinderState m => ([ParserName] -> [ParserName]) -> m ()
modifyTopo f = modify' (\st -> st {topo = f (topo st)})

addPred :: MonadState LetFinderState m => ParserName -> m ()
addPred k = modifyPreds (HashMap.insertWith (+) k 1)

addRec :: MonadState LetFinderState m => ParserName -> m ()
addRec = modifyRecs . HashSet.insert

ifSeen :: MonadReader LetFinderCtx m => ParserName -> m a -> m a -> m a
ifSeen x yes no = do !seen <- ask; if HashSet.member x seen then yes else no

ifNotProcessedBefore :: MonadState LetFinderState m => ParserName -> m () -> m ()
ifNotProcessedBefore x m = do !before <- getBefore; if HashSet.member x before then return () else m

doNotProcessAgain :: MonadState LetFinderState m => ParserName -> m ()
doNotProcessAgain x = modifyBefore (HashSet.insert x)

addToTopology :: MonadState LetFinderState m => ParserName -> m ()
addToTopology x = modifyTopo (x:)

addName :: MonadReader LetFinderCtx m => ParserName -> m b -> m b
addName x = local (HashSet.insert x)

makeParserName :: Free ParserF Void1 a -> ParserName
-- Force evaluation of p to ensure that the stableName is correct first time
makeParserName !p = unsafePerformIO (fmap (\(StableName name) -> ParserName name) (makeStableName p))


-- RegMaker is used to generate new register scopes during tagging
-- It _is_ safe to use this! Each fresh operation is atomic, and
-- the order of which new registers are allocated is not important
type RegMaker = IORef IΣVar
{-# NOINLINE newRegMaker #-}
newRegMaker :: RegMaker
newRegMaker = unsafePerformIO (newIORef 0)

{-# NOINLINE freshReg #-}
freshReg :: RegMaker -> (forall r. Reg r a -> ParserF k b) -> ParserF k b
freshReg maker scope = scope (unsafePerformIO $ do
  x <- readIORef maker
  writeIORef maker (x + 1)
  return $! (Reg x))

{-# NOINLINE numRegisters #-}
numRegisters :: RegMaker -> IΣVar 
numRegisters = unsafePerformIO . readIORef

showM :: Parser a -> String
showM = show . (\(x, _, _) -> x) . compile

liftA4 :: Applicative f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftA4 f u v w x = liftA3 f u v w <*> x

instance Eq ParserName where 
  (ParserName n) == (ParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable ParserName where
  hash (ParserName n) = hashStableName (StableName n)
  hashWithSalt salt (ParserName n) = hashWithSalt salt (StableName n)

-- There is great evil in this world, and I'm probably responsible for half of it
instance Show ParserName where show (ParserName n) = show (I# (unsafeCoerce# n))