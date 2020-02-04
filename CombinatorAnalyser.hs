{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module CombinatorAnalyser (analyse) where

import ParserAST                  (ParserF(..), MetaP(..), CoinType(..))
import MachineAST                 (IMVar, MVar(..), IΣVar)
import Indexed                    (Fix(..), Cofree(..), Const1(..), imap, cata, histo, extract, (|>))
import Control.Applicative        (liftA2)
import Control.Monad.Reader       (ReaderT, ask, runReaderT, local)
import Control.Monad.State.Strict (State, get, put, evalState)
import Data.Map.Strict            (Map)
import Data.Set                   (Set)
import Data.Monoid                ((<>))
import Safe.Coerce                (coerce)
import qualified Data.Map.Strict as Map
import qualified Data.Set        as Set

analyse :: Fix ParserF a -> Fix ParserF a
analyse = id {-. terminationAnalysis-}

{-newtype (a :->: f) k = IFunc {run :: a -> f k}
send :: a -> (a :->: f) k -> f k
send = flip run-}

data Compliance k = DomComp | NonComp | Comp | FullPure deriving Show

seqCompliance :: Compliance a -> Compliance b -> Compliance c
seqCompliance c FullPure = coerce c
seqCompliance FullPure c = coerce c
seqCompliance Comp _     = Comp
seqCompliance _ _        = NonComp

compliance :: ParserF Compliance a -> Compliance a
compliance (Pure _) = FullPure
compliance (Satisfy _) = NonComp
compliance Empty = FullPure
compliance (Let _ _ _) = DomComp
compliance (Try _) = DomComp
compliance (NonComp :<|>: FullPure) = Comp
compliance (_ :<|>: _) = NonComp
compliance (l :<*>: r) = seqCompliance l r
compliance (l :<*: r) = seqCompliance l r
compliance (l :*>: r) = seqCompliance l r
compliance (LookAhead c) = c -- Lookahead will consume input on failure, so its compliance matches that which is beneath it
compliance (NotFollowedBy _) = FullPure
compliance (Debug _ c) = c
compliance (ChainPre _ _) = DomComp
compliance (ChainPost _ _) = DomComp
compliance _ = NonComp -- Match, Branch

{-constantInput :: Free ParserF f a -> Free ParserF f a
constantInput = untag . send True . fold (IFunc . const . Var) (IFunc . (Op .) . flip alg)
  where
    tyTag ty n = MetaP (ConstInput ty n) . Op
    tag = tyTag Costs
    refunds = tyTag Refunded
    free n  = Op . MetaP (ConstInput Free n)
    untag (TaggedInput _ 0 p) = p
    untag (TaggedInput _ 1 p) = p
    untag p = p
    retag f n p = untag (CostsInput (max (f n) 0) p)
    get cut (send cut -> TaggedInput _ n p) = (n, p)
    get cut (send cut -> p) = (0, p)

    -- This should be sufficient? Worse case we add more length checks than necessary
    seqCost Costs n m = n + m
    seqCost Refunded n m = max n m

    satisfyObligationsSeq cut cons ty n p q
      -- p failed to satisfy the obligation, so the burden is on q
      | cut && n == 0 = let (m, q') = get True q in tag m (cons p q')
      -- p has satisfied the obligation, so the node consumes 1 input and q is left untouched
      | cut && n == 1 = tag 1 (cons p (untag (send False q)))
      -- no cut obligation, so proceed as normal
      | otherwise     = let (m, q') = get False q in tag (seqCost ty n m) (cons p q')

    -- Lets focus on another problem for a minute, the join point problem is not appropriate
    -- to solve in this domain. The code generator has a better chance as it has the continuation
    -- We need to prevent semantic shift permitting more backtracking. This can be done by
    -- splitting out the first character from the left-branch of an <|> except where a try is present
    -- This will be done by passing a Bool down the tree to indicate whether to perform a split or
    -- not.
    alg :: Bool -> ParserF (Bool :->: Free ParserF f) a -> ParserF (Free ParserF f) a
    alg _ (Pure x) = tag 0 (Pure x)
    alg _ (Satisfy p) = tag 1 (Satisfy p)
    alg cut ((send cut -> TaggedInput ty n p) :<*>: q) = satisfyObligationsSeq cut (:<*>:) ty n p q
    alg cut ((send cut -> TaggedInput ty n p) :*>: q) = satisfyObligationsSeq cut (:*>:) ty n p q
    alg cut ((send cut -> TaggedInput ty n p) :<*: q) = satisfyObligationsSeq cut (:<*:) ty n p q
    alg cut ((send True -> CostsInput n p) :<|>: (send cut -> CostsInput m q)) -- TODO What about refunds?
      | n > m  = tag m (retag (subtract m) n p :<|>: q)
      | m > n  = tag n (p :<|>: retag (subtract n) m q)
      | n == m = tag n (p :<|>: q)
    alg _ Empty = tag 0 Empty
    alg _ (Try (send False -> TaggedInput ty n p)) = tyTag ty n (Try p)
    {-alg cut (Branch (send cut -> TaggedInput ty n b) p q)
      | m1 > m2  = tag (seqCost ty n m2) (Branch b (retag (subtract m2) m1 p') q')
      | m2 > m1  = tag (seqCost ty n m1) (Branch b p' (retag (subtract m1) m2 q'))
      | m1 == m2 = tag (seqCost ty n m1) (Branch b p' q')
      where (m1, p') = get p
            (m2, q') = get q
    alg cut (Match (send cut -> TaggedInput ty n p) fs qs d) =
      let mdqs = map get (d : qs)
          m = minimum (map fst mdqs)
          d' : qs' = map (uncurry (retag (subtract m))) mdqs
      in tag (seqCost ty n m) (Match p fs qs' d')-}
    alg cut (LookAhead (send cut -> CostsInput n p)) = refunds n (LookAhead (free n p))
    alg _ (NotFollowedBy (send False -> CostsInput n p)) = refunds n (NotFollowedBy (free n p))
    alg cut (Debug name (send cut -> CostsInput n p)) = tag n (Debug name p)
    alg cut p = imap (untag . send cut) p

pattern TaggedInput t n p = Op (MetaP (ConstInput t n) p)
pattern CostsInput n p = TaggedInput Costs n p

-}

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
terminationAnalysis :: Fix ParserF a -> Fix ParserF a
terminationAnalysis p = if not (looping (evalState (runReaderT (runTerm (cata (Termination . alg) p)) Set.empty) Map.empty)) then p
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