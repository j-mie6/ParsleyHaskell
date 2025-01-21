{-# LANGUAGE OverloadedStrings #-}

module Parsley.Internal.Frontend.Analysis.Liveness (tagCombinator) where
import Data.Set (Set)
import Parsley.Internal.Common (Fix(..), MonadFresh (..), intercalateDiff, HFresh)
import Parsley.Internal.Core.CombinatorAST (Combinator(..), PosSelector (..))
import Data.Kind (Type)
import qualified Data.Dependent.Map as DM
import Parsley.Internal.Backend.Machine.Identifiers (MVar)
import Parsley.Internal.Common.Fresh (runFresh)
import Parsley.Internal.Core.Identifiers (SomeΣVar)
import Control.Monad.ST.Lazy (ST, runST)
import Parsley.Internal.Common.Indexed (Const1(..), cata, IFunctor(..))
import qualified Data.Map as M
import Data.STRef.Lazy (STRef, newSTRef)
import Control.Monad.Fix (fix)
import Control.Monad (unless, when)

type NodeID = Integer

data Tag t f (k :: Type -> Type) a = Tag {tag :: t, tagged :: f k a}
instance IFunctor f => IFunctor (Tag t f) where
  imap f (Tag t k) = Tag t (imap f k)


data LivenessData = LivenessData { liveIn :: Set SomeΣVar, liveOut :: Set SomeΣVar }
type LivenessAnalysisResult = M.Map NodeID LivenessData
type TaggedCombinator = Tag NodeID Combinator

instance Show (Fix TaggedCombinator a) where
  show = ($ "") . getConst1 . cata (Const1 . alg)
    where
      alg (Tag t (Pure x))                                  = "{" . shows t . "} pure " . shows x
      alg (Tag t (Satisfy f))                               = "{" . shows t . "} satisfy " . shows f
      alg (Tag t (Const1 pf :<*>: Const1 px))               = "{" . shows t . "} (" . pf . " <*> " .  px . ")"
      alg (Tag t (Const1 p :*>: Const1 q))                  = "{" . shows t . "} (" . p . " *> " . q . ")"
      alg (Tag t (Const1 p :<*: Const1 q))                  = "{" . shows t . "} (" . p . " <* " . q . ")"
      alg (Tag t (Const1 p :<|>: Const1 q))                 = "{" . shows t . "} (" . p . " <|> " . q . ")"
      alg (Tag t Empty)                                     = "{" . shows t . "} empty"
      alg (Tag t (Try (Const1 p)))                          = "{" . shows t . "} try (". p . ")"
      alg (Tag t (LookAhead (Const1 p)))                    = "{" . shows t . "} lookAhead (" . p . ")"
      alg (Tag t (Let v))                                   = "{" . shows t . "} let-bound " . shows v
      alg (Tag t (NotFollowedBy (Const1 p)))                = "{" . shows t . "} notFollowedBy (" . p . ")"
      alg (Tag t (Branch (Const1 b) (Const1 p) (Const1 q))) = "{" . shows t . "} branch (" . b . ") (" . p . ") (" . q . ")"
      alg (Tag t (Match (Const1 p) fs qs (Const1 def)))     = "{" . shows t . "} match (" . p . ") " . shows fs . " [" . intercalateDiff ", " (map getConst1 qs) . "] ("  . def . ")"
      alg (Tag t (Loop (Const1 body) (Const1 exit)))        = "{" . shows t . "} loop (" . body . ") (" . exit . ")"
      alg (Tag t (MakeRegister σ (Const1 p) (Const1 q)))    = "{" . shows t . "} make " . shows σ . " (" . p . ") (" . q . ")"
      alg (Tag t (GetRegister σ))                           = "{" . shows t . "} get " . shows σ
      alg (Tag t (PutRegister σ (Const1 p)))                = "{" . shows t . "} put " . shows σ . " (" . p . ")"
      alg (Tag t (Position Line))                           = "{" . shows t . "} line"
      alg (Tag t (Position Col))                            = "{" . shows t . "} col"
      alg (Tag t (Debug _ (Const1 p)))                      = p
      alg (Tag t (MetaCombinator m (Const1 p)))             = p . " [" . shows m . "]"

{-| 
Given a forest of parsers, compute the liveIn and liveOut for each Combinator AST node and tag them with it. 
-}
livenessAnalysis :: Fix Combinator a -> DM.DMap MVar (Fix Combinator) -> ()
livenessAnalysis p ms = runST $ do
        sets <- newSTRef initSets
        fix $ \loop -> do
            change <- round sets pTagged -- TODO 
            when change loop
        return ()
    where
        initSets :: LivenessAnalysisResult
        initSets = undefined
        (pTagged, msTagged, maxID) = tagCombinator p ms
        round :: STRef s LivenessAnalysisResult -> Fix TaggedCombinator a -> ST s Bool
        round sets _ = undefined

{-|
Tag every node of the parser AST with a unique identifier of type `NodeID`. Returns tagged forest and max `NodeID` assigned.
-}
tagCombinator :: Fix Combinator a -> DM.DMap MVar (Fix Combinator) ->  (Fix TaggedCombinator a, DM.DMap MVar (Fix TaggedCombinator), NodeID)
tagCombinator p ps = (a, b, maxV')
    where
        init = 0
        (a, maxV) = runFresh (tagCombinatorNodes p) init
        (b, maxV') = runFresh (DM.traverseWithKey (\_ a -> tagCombinatorNodes a) ps) (succ maxV)

wrap p = newVar >>= (\t -> return $ In (Tag t p))

tagCombinatorNodes :: forall a. Fix Combinator a -> HFresh NodeID (Fix TaggedCombinator a)
tagCombinatorNodes (In (Pure x)) = wrap (Pure x)
tagCombinatorNodes (In (Satisfy f)) = wrap (Satisfy f)
tagCombinatorNodes (In Empty) = wrap Empty
tagCombinatorNodes (In (pf :<*>: px)) = do
    pft <- tagCombinatorNodes pf
    pxt <- tagCombinatorNodes px
    wrap (pft :<*>: pxt)
tagCombinatorNodes (In (p :*>: q) ) = do
    pt <- tagCombinatorNodes p
    qt <- tagCombinatorNodes q
    wrap (pt :*>: qt)
tagCombinatorNodes (In (p :<*: q) ) = do
    pt <- tagCombinatorNodes p
    qt <- tagCombinatorNodes q
    wrap (pt :<*: qt)
tagCombinatorNodes (In (p :<|>: q) ) = do
    pt <- tagCombinatorNodes p
    qt <- tagCombinatorNodes q
    wrap (pt :<|>: qt)
tagCombinatorNodes (In (Try p)) = tagCombinatorNodes p >>= wrap . Try
tagCombinatorNodes (In (LookAhead p)) = tagCombinatorNodes p >>= wrap . LookAhead
tagCombinatorNodes (In (Let v)) = wrap (Let v)
tagCombinatorNodes (In (NotFollowedBy p)) = tagCombinatorNodes p >>= wrap . NotFollowedBy
tagCombinatorNodes (In (Branch b p q)) = do
    bt <- tagCombinatorNodes b
    pt <- tagCombinatorNodes p
    qt <- tagCombinatorNodes q
    wrap (Branch bt pt qt)
tagCombinatorNodes (In (Match p fs qs def)) = do
    pt <- tagCombinatorNodes p
    qst <- traverse tagCombinatorNodes qs
    deft <- tagCombinatorNodes def
    wrap (Match pt fs qst deft)
tagCombinatorNodes (In (Loop body exit)) = do
    bodyt <- tagCombinatorNodes body
    exitt <- tagCombinatorNodes exit
    wrap (Loop bodyt exitt)
tagCombinatorNodes (In (MakeRegister σ p q)) =  do
    pt <- tagCombinatorNodes p
    qt <- tagCombinatorNodes q
    wrap (MakeRegister σ pt qt)
tagCombinatorNodes (In (GetRegister σ)) = wrap (GetRegister σ)
tagCombinatorNodes (In (PutRegister σ p)) = do
    pt <- tagCombinatorNodes p
    wrap (PutRegister σ pt)
tagCombinatorNodes (In (Position p)) = wrap (Position p)
tagCombinatorNodes (In (Debug d p)) = tagCombinatorNodes p >>= (wrap . Debug d)
tagCombinatorNodes (In (MetaCombinator m p)) = tagCombinatorNodes p >>= (wrap . MetaCombinator m)


