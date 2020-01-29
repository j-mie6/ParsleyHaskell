{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
module CombinatorAnalyser (analyse) where

import ParserAST                  (ParserF(..), MetaP(..), CoinType(..))
import MachineAST                 (IMVar, MVar(..), IΣVar)
import Indexed                    (Free(..), History(Era), Void1, Const1(..), imap, fold, histo, present, (|>), absurd, (:*:)(..), ifst, isnd, (/\))
import Control.Applicative        (liftA2)
import Control.Monad.Reader       (ReaderT, ask, runReaderT, local)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Map.Strict            (Map)
import Data.Set                   (Set)
import Data.Monoid                ((<>))
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set

analyse :: Free ParserF f a -> Free ParserF f a
analyse = constantInput {-. terminationAnalysis-}

(<+>) :: (Num a, Monad m) => m a -> m a -> m a
(<+>) = liftA2 (+)
(<==>) :: Eq a => Maybe a -> Maybe a -> Maybe a
(Just x) <==> (Just y)
  | x == y    = Just x
  | otherwise = Nothing
_ <==> _ = Nothing

constantInput :: Free ParserF f a -> Free ParserF f a
constantInput = untag . ifst . fold (Var /\ const (Const1 False)) ((Op . alg) /\ (Const1 . forkNode))
  where
    tyTag ty n = MetaP (ConstInput ty n) . Op
    tag = tyTag Costs
    refunds = tyTag Refunded
    free n  = Op . MetaP (ConstInput Free n)
    untag (TaggedInput _ 0 p) = p
    untag (TaggedInput _ 1 p) = p
    untag p = p
    retag f n p = untag (CostsInput (max (f n) 0) p)
    get (TaggedInput _ n p :*: _) = (n, p)
    get (p :*: _) = (0, p)
    guardJoin (Const1 True) n = Op . MetaP (ConstInput Transports n)
    guardJoin (Const1 False) _ = id

    -- This should be sufficient? Worse case we add more length checks than necessary
    seqCost Costs n m = n + m
    seqCost Refunded n m = max n m

    -- We need to ensure that any join points are isolated from their corresponding forks
    -- They will be drained before entry AROUND the node and refunded INSIDE the node
    -- This affects any sequence node with a fork node to its left. We'll make a separate
    -- algebra to break out this separation of concerns
    forkNode :: ParserF f a -> Bool
    forkNode (_ :<|>: _)     = True
    forkNode (Branch _ _ _)  = True
    forkNode (Match _ _ _ _) = True
    forkNode _               = False

    alg :: ParserF (Free ParserF f :*: Const1 Bool) a -> ParserF (Free ParserF f) a
    alg (Pure x) = tag 0 (Pure x)
    alg (Satisfy p) = tag 1 (Satisfy p)
    alg ((TaggedInput ty n p :*: fork) :<*>: q) = let (m, q') = get q in tag (seqCost ty n m) (guardJoin fork m p :<*>: q')
    alg ((TaggedInput ty n p :*: fork) :*>: q) = let (m, q') = get q in tag (seqCost ty n m) (guardJoin fork m p :*>: q')
    alg ((TaggedInput ty n p :*: fork) :<*: q) = let (m, q') = get q in tag (seqCost ty n m) (guardJoin fork m p :<*: q')
    alg ((CostsInput n p :*: _) :<|>: (CostsInput m q :*: _)) -- TODO What about refunds?
      | n > m  = tag m (retag (subtract m) n p :<|>: q)
      | m > n  = tag n (p :<|>: retag (subtract n) m q)
      | n == m = tag n (p :<|>: q)
    alg Empty = tag 0 Empty
    alg (Try (TaggedInput ty n p :*: _)) = tyTag ty n (Try p)
    alg (Branch (TaggedInput ty n b :*: fork) p q)
      | m1 > m2  = tag (seqCost ty n m2) (Branch (guardJoin fork m2 b) (retag (subtract m2) m1 p') q')
      | m2 > m1  = tag (seqCost ty n m1) (Branch (guardJoin fork m1 b) p' (retag (subtract m1) m2 q'))
      | m1 == m2 = tag (seqCost ty n m1) (Branch (guardJoin fork m1 b) p' q')
      where (m1, p') = get p
            (m2, q') = get q
    alg (Match (TaggedInput ty n p :*: fork) fs qs d) =
      let mdqs = map get (d : qs)
          m = minimum (map fst mdqs)
          d' : qs' = map (uncurry (retag (subtract m))) mdqs
      in tag (seqCost ty n m) (Match (guardJoin fork m p) fs qs' d')
    alg (LookAhead (CostsInput n p :*: _)) = refunds n (LookAhead (free n p))
    alg (NotFollowedBy (CostsInput n p :*: _)) = refunds n (NotFollowedBy (free n p))
    alg (Debug name (CostsInput n p :*: _)) = tag n (Debug name p)
    alg p = imap (untag . ifst) p

pattern TaggedInput t n p = Op (MetaP (ConstInput t n) p)
pattern CostsInput n p = TaggedInput Costs n p

-- Termination Analysis (Generalised left-recursion checker)
data Consumption = Some | None | Never
data Prop = Prop {success :: Consumption, fails :: Consumption, indisputable :: Bool} | Unknown

looping (Prop Never Never _)          = True
looping _                             = False
strongLooping (Prop Never Never True) = True
strongLooping _                       = False
neverSucceeds (Prop Never _ _)        = True
neverSucceeds _                       = False
neverFails (Prop _ Never _)           = True
neverFails _                          = False

Never ||| _     = Never
_     ||| Never = Never
Some  ||| _     = Some
None  ||| p     = p

Some  &&& _    = Some
_     &&& Some = Some
None  &&& _    = None
Never &&& p    = p

Never ^^^ _     = Never
_     ^^^ Never = Never
None  ^^^ _     = None
Some  ^^^ p     = p

(==>) :: Prop -> Prop -> Prop
p ==> _ | neverSucceeds p            = p
_ ==> Prop Never Never True          = Prop Never Never True
Prop None _ _ ==> Prop Never Never _ = Prop Never Never False
Prop s1 f1 b1 ==> Prop s2 f2 b2      = Prop (s1 ||| s2) (f1 &&& (s1 ||| f2)) (b1 && b2)

branching :: Prop -> [Prop] -> Prop
branching b ps
  | neverSucceeds b = b
  | any strongLooping ps = Prop Never Never True
branching (Prop None f _) ps
  | any looping ps = Prop Never Never False
  | otherwise      = Prop (foldr1 (|||) (map success ps)) (f &&& (foldr1 (^^^) (map fails ps))) False
branching (Prop Some f _) ps = Prop (foldr (|||) Some (map success ps)) f False

--data InferredTerm = Loops | Safe | Undecidable
newtype Termination a = Termination {runTerm :: ReaderT (Set IMVar) (State (Map IMVar Prop)) Prop}
terminationAnalysis :: Free ParserF Void1 a -> Free ParserF Void1 a
terminationAnalysis p = if not (looping (evalState (runReaderT (runTerm (fold absurd (Termination . alg) p)) Set.empty) Map.empty)) then p
                        else error "Parser will loop indefinitely: either it is left-recursive or iterates over pure computations"
  where
    alg :: ParserF Termination a -> ReaderT (Set IMVar) (State (Map IMVar Prop)) Prop
    alg (Satisfy _)                          = return $! Prop Some None True
    alg (Pure _)                             = return $! Prop None Never True
    alg Empty                                = return $! Prop Never None True
    alg (Try p)                              =
      do x <- runTerm p
         return $! if looping x then x
                   else Prop (success x) None (indisputable x)
    alg (LookAhead p)                        =
      do x <- runTerm p
         return $! if looping x then x
                   else Prop None (fails x) (indisputable x)
    alg (NotFollowedBy p)                    =
      do x <- runTerm p
         return $! if looping x then x
                   else Prop None None True
    alg (p :<*>: q)                          = liftA2 (==>) (runTerm p) (runTerm q)
    alg (p :*>: q)                           = liftA2 (==>) (runTerm p) (runTerm q)
    alg (p :<*: q)                           = liftA2 (==>) (runTerm p) (runTerm q)
    alg (p :<|>: q)                          =
      do x <- runTerm p; case x of
           -- If we fail without consuming input then q governs behaviour
           Prop _ None _       -> runTerm q
           -- If p never fails then q is irrelevant
           x | neverFails x    -> return $! x
           -- If p never succeeds then q governs
           x | neverSucceeds x -> runTerm q
           Prop s1 Some i1     -> do ~(Prop s2 f i2) <- runTerm q; return $! Prop (s1 &&& s2) (Some ||| f) (i1 && i2)
    alg (Branch b p q)                       = liftA2 branching (runTerm b) (sequence [runTerm p, runTerm q])
    alg (Match p _ qs def)                   = liftA2 branching (runTerm p) (traverse runTerm (def:qs))
    alg (ChainPre op p)                      =
      do x <- runTerm op; case x of
           -- Never failing implies you must either loop or not consume input
           Prop _ Never _ -> return $! Prop Never Never True
           -- Reaching p can take a route that consumes no input, if op failed
           _ -> do y <- runTerm p
                   return $! if looping y then y
                             else y -- TODO Verify!
    alg (ChainPost p op)                     =
      do y <- runTerm op; case y of
           Prop None _ _ -> return $! Prop Never Never True
           y -> do x <- runTerm p; case (x, y) of
                     (Prop Some f _, Prop _ Never _) -> return $! Prop Some f False
                     (x, y)                          -> return $! Prop (success x) (fails x &&& fails y) False -- TODO Verify
    alg (Let True (MVar v) p)                =
      do props <- get
         seen <- ask
         case Map.lookup v props of
           Just prop -> return $! prop
           Nothing | Set.member v seen -> return $! Prop Never Never False
           Nothing -> do prop <- local (Set.insert v) (runTerm p)
                         let prop' = if looping prop then Prop Never Never True else prop
                         put (Map.insert v prop' props)
                         return $! prop'
    alg (Debug _ p)                          = runTerm p
    --alg _                                    = return $! Unknown