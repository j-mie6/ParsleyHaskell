{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeOperators #-}
module CombinatorAnalyser (analyse, compliance, Compliance(..), emptyFlags, AnalysisFlags(..)) where

import ParserAST                  (ParserF(..), MetaP(..))
import MachineAST                 (IMVar, MVar(..), IΣVar)
import Indexed                    (Fix(..), Const1(..), imap, cata, zygo, (:*:)(..), (/\), ifst, isnd)
import Control.Applicative        (liftA2)
import Control.Monad.Reader       (ReaderT, ask, runReaderT, local)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Map.Strict            (Map)
import Data.Set                   (Set)
import Data.Monoid                ((<>))
import Safe.Coerce                (coerce)
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set

data AnalysisFlags = AnalysisFlags {
  letBound :: Bool
}
emptyFlags = AnalysisFlags False

analyse :: AnalysisFlags -> Fix (ParserF q) a -> Fix (ParserF q) a
analyse flags = cutAnalysis (letBound flags) {-. terminationAnalysis-}

data Compliance k = DomComp | NonComp | Comp | FullPure deriving (Show, Eq)

seqCompliance :: Compliance a -> Compliance b -> Compliance c
seqCompliance c FullPure = coerce c
seqCompliance FullPure c = coerce c
seqCompliance Comp _     = Comp
seqCompliance _ _        = NonComp

caseCompliance :: Compliance a -> Compliance b -> Compliance c
caseCompliance c FullPure              = coerce c
caseCompliance FullPure c              = coerce c
caseCompliance c1 c2 | c1 == coerce c2 = coerce c1
caseCompliance _ _                     = NonComp

compliance :: ParserF q Compliance a -> Compliance a
compliance (Pure _)                 = FullPure
compliance (Satisfy _)              = NonComp
compliance Empty                    = FullPure
compliance (Let _ _ _)              = DomComp
compliance (Try _)                  = DomComp
compliance (NonComp :<|>: FullPure) = Comp
compliance (_ :<|>: _)              = NonComp
compliance (l :<*>: r)              = seqCompliance l r
compliance (l :<*: r)               = seqCompliance l r
compliance (l :*>: r)               = seqCompliance l r
compliance (LookAhead c)            = c -- Lookahead will consume input on failure, so its compliance matches that which is beneath it
compliance (NotFollowedBy _)        = FullPure
compliance (Debug _ c)              = c
compliance (ChainPre NonComp p)     = seqCompliance Comp p
compliance (ChainPre op p)          = seqCompliance NonComp p
compliance (ChainPost p NonComp)    = seqCompliance p Comp
compliance (ChainPost p op)         = seqCompliance p NonComp
compliance (Branch b p q)           = seqCompliance b (caseCompliance p q)
compliance (Match p _ qs def)       = seqCompliance p (foldr1 caseCompliance (def:qs))
compliance (MetaP _ c)              = c 

newtype CutAnalysis q a = CutAnalysis {cutOut :: Bool -> (Fix (ParserF q) a, Bool)}

biliftA2 :: (a -> b -> c) -> (x -> y -> z) -> (a, x) -> (b, y) -> (c, z)
biliftA2 f g (x1, y1) (x2, y2) = (f x1 x2, g y1 y2)

cutAnalysis :: Bool -> Fix (ParserF q) a -> Fix (ParserF q) a
cutAnalysis letBound = fst . ($ letBound) . cutOut . zygo (CutAnalysis . alg) compliance
  where
    mkCut True = In . MetaP Cut
    mkCut False = id

    requiresCut = In . MetaP RequiresCut

    seqAlg :: (Fix (ParserF q) a -> Fix (ParserF q) b -> ParserF q (Fix (ParserF q)) c) -> Bool -> CutAnalysis q a -> CutAnalysis q b -> (Fix (ParserF q) c, Bool)
    seqAlg con cut l r =
      let (l', handled) = cutOut l cut
          (r', handled') = cutOut r (cut && not handled)
      in (In (con l' r'), handled || handled')

    rewrap :: (Fix (ParserF q) a -> ParserF q (Fix (ParserF q)) b) -> Bool -> CutAnalysis q a -> (Fix (ParserF q) b, Bool)
    rewrap con cut p = let (p', handled) = cutOut p cut in (In (con p'), handled)

    alg :: ParserF q (CutAnalysis q :*: Compliance) a -> Bool -> (Fix (ParserF q) a, Bool)
    alg (Pure x) _ = (In (Pure x), False)
    alg (Satisfy f) cut = (mkCut cut (In (Satisfy f)), True)
    alg Empty _ = (In Empty, False)
    alg (Let r μ p) cut = (mkCut (not cut) (In (Let r μ (fst (cutOut (ifst p) True)))), False) -- If there is no cut, we generate a piggy for the continuation
    alg (Try p) _ = fmap (const False) $ rewrap Try False (ifst p)
    alg ((p :*: NonComp) :<|>: (q :*: FullPure)) _ = (requiresCut (In (fst (cutOut p True) :<|>: fst (cutOut q False))), True)
    alg (p :<|>: q) cut = 
      let (q', handled) = cutOut (ifst q) cut 
      in (In (fst (cutOut (ifst p) False) :<|>: q'), handled)
    alg (l :<*>: r) cut = seqAlg (:<*>:) cut (ifst l) (ifst r)
    alg (l :<*: r) cut = seqAlg (:<*:) cut (ifst l) (ifst r)
    alg (l :*>: r) cut = seqAlg (:*>:) cut (ifst l) (ifst r)
    alg (LookAhead p) cut = rewrap LookAhead cut (ifst p)
    alg (NotFollowedBy p) _ = fmap (const False) $ rewrap NotFollowedBy False (ifst p)
    alg (Debug msg p) cut = rewrap (Debug msg) cut (ifst p)
    alg (ChainPre (op :*: NonComp) p) _ = 
      let (op', _) = cutOut op True
          (p', _) = cutOut (ifst p) False
      in (requiresCut (In (ChainPre op' p')), True)
    alg (ChainPre op p) cut = 
      let (op', _) = cutOut (ifst op) False
          (p', handled) = cutOut (ifst p) cut
      in (mkCut (not cut) (In (ChainPre op' p')), handled)
    alg (ChainPost p (op :*: NonComp)) cut = 
      let (p', _) = cutOut (ifst p) cut
          (op', _) = cutOut op True
      in (requiresCut (In (ChainPost p' op')), True)
    alg (ChainPost p op) cut = 
      let (p', handled) = cutOut (ifst p) cut
          (op', _) = cutOut (ifst op) False
      in (mkCut (cut && handled) (In (ChainPost p' op')), handled)
    alg (Branch b p q) cut =
      let (b', handled) = cutOut (ifst b) cut
          (p', handled') = cutOut (ifst p) (cut && not handled)
          (q', handled'') = cutOut (ifst q) (cut && not handled)
      in (In (Branch b' p' q'), handled || (handled' && handled''))
    alg (Match p f qs def) cut = 
      let (p', handled) = cutOut (ifst p) cut
          (def', handled') = cutOut (ifst def) (cut && not handled)
          (qs', handled'') = foldr (\q -> biliftA2 (:) (&&) (cutOut (ifst q) (cut && not handled))) ([], handled') qs
      in (In (Match p' f qs' def'), handled || handled'')

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
terminationAnalysis :: Fix (ParserF q) a -> Fix (ParserF q) a
terminationAnalysis p = if not (looping (evalState (runReaderT (runTerm (cata (Termination . alg) p)) Set.empty) Map.empty)) then p
                        else error "Parser will loop indefinitely: either it is left-recursive or iterates over pure computations"
  where
    alg :: ParserF q Termination a -> ReaderT (Set IMVar) (State (Map IMVar Prop)) Prop
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