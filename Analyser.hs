{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}
module Analyser (constantInput, terminationAnalysis, constantInput') where

import ParserAST                  (ParserF(..), Meta(..))
import Machine                    (IMVar, MVar(..), IΣVar)
import Indexed                    (Free(..), History(Era), Void1, Const1(..), imap, fold, histo, present, (|>), absurd)
import Control.Applicative        (liftA2)
import Control.Monad.Reader       (ReaderT, ask, runReaderT, local)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Map.Strict            (Map)
import Data.Set                   (Set)
import Data.Monoid                ((<>))
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set

-- Constant Input Consumption Analysis
constantInput :: Free ParserF f a -> Maybe Int
constantInput = getConst1 . histo (const (Const1 Nothing)) (alg1 |> (Const1 . alg2 . imap present))
  where
    alg1 :: ParserF (History ParserF (Const1 (Maybe Int))) a -> Maybe (Const1 (Maybe Int) a)
    alg1 (Era (Const1 n) (Try _ _) :<|>: Era (Const1 q) _) = Just (Const1 (n <==> q))
    alg1 _ = Nothing
    alg2 :: ParserF (Const1 (Maybe Int)) a -> Maybe Int
    alg2 (Pure _)                                  = Just 0
    alg2 (Satisfy _)                               = Just 1
    alg2 (Const1 p :<*>: Const1 q)                 = p <+> q
    alg2 (Const1 p :*>: Const1 q)                  = p <+> q
    alg2 (Const1 p :<*: Const1 q)                  = p <+> q
    alg2 Empty                                     = Just 0
    alg2 (Try n _)                                 = n
    alg2 (LookAhead (Const1 p))                    = p
    alg2 (NotFollowedBy (Const1 p))                = p
    alg2 (Branch (Const1 b) (Const1 p) (Const1 q)) = b <+> (p <==> q)
    alg2 (Match (Const1 p) _ qs (Const1 def))      = p <+> (foldr (<==>) def (map getConst1 qs))
    alg2 (Debug _ (Const1 p))                      = p
    alg2 (Let False _ (Const1 p))                  = p
    alg2 _                                         = Nothing

(<+>) :: (Num a, Monad m) => m a -> m a -> m a
(<+>) = liftA2 (+)
(<==>) :: Eq a => Maybe a -> Maybe a -> Maybe a
(Just x) <==> (Just y)
  | x == y    = Just x
  | otherwise = Nothing
_ <==> _ = Nothing

constantInput' :: Free ParserF f a -> Free ParserF f a
constantInput' = untag . fold Var (Op . alg)
  where
    tag n = Meta (ConstInput n) . Op
    untag (TaggedInput 0 p) = p
    untag (TaggedInput 1 p) = p
    untag p = p
    get (TaggedInput n p) = (n, p)
    get p = (0, p)
    alg :: ParserF (Free ParserF f) a -> ParserF (Free ParserF f) a
    alg p@(Pure _) = tag 0 p
    alg p@(Satisfy _) = tag 1 p
    alg (TaggedInput n p :<*>: q) = let (m, q') = get q in tag (n + m) (p :<*>: q')
    alg (TaggedInput n p :*>: q) = let (m, q') = get q in tag (n + m) (p :*>: q')
    alg (TaggedInput n p :<*: q) = let (m, q') = get q in tag (n + m) (p :<*: q')
    alg (TaggedInput n p :<|>: TaggedInput m q) 
      | n > m  = tag m (TaggedInput (n - m) p :<|>: q)
      | m > n  = tag n (p :<|>: TaggedInput (m - n) q)
      | n == m = tag n (p :<|>: q)
    alg p@Empty = tag 0 p
    alg (Try _ (TaggedInput n p)) = tag n (Try (Just n) p)
    --alg (LookAhead (TaggedInput n p)) = tag n (LookAhead p) -- it is not safe to commute this... yet: coins need merging
    --alg (NotFollowedBy (TaggedInput n p)) = tag n (NotFollowedBy p) -- it is not safe to commute this... yet: coins need merging
    alg (Branch (TaggedInput n b) p q)
      | m1 > m2  = tag (n + m2) (Branch b (TaggedInput (m1 - m2) p') q')
      | m2 > m1  = tag (n + m1) (Branch b p' (TaggedInput (m2 - m1) q'))
      | m1 == m2 = tag (n + m1) (Branch b p' q')
      where (m1, p') = get p
            (m2, q') = get q
    -- How to do match?
    alg (Debug name (TaggedInput n p)) = tag n (Debug name p)
    alg p = imap untag p

pattern TaggedInput n p = Op (Meta (ConstInput n) p)

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
    alg (Try _ p)                            =
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