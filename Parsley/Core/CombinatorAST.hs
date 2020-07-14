{-# LANGUAGE GADTs,
             DataKinds,
             TypeOperators,
             RankNTypes,
             FlexibleInstances,
             FlexibleContexts,
             PolyKinds,
             OverloadedStrings #-}
module Parsley.Core.CombinatorAST (module Parsley.Core.CombinatorAST) where

import Parsley.Common           (IFunctor, Fix, Const1(..), imap, cata, intercalateDiff)
import Parsley.Core.Identifiers (MVar, ΣVar)
import Parsley.Core.Defunc      (Defunc)

-- Core datatype
data Combinator (k :: * -> *) (a :: *) where
  Pure           :: Defunc a -> Combinator k a
  Satisfy        :: Defunc (Char -> Bool) -> Combinator k Char
  (:<*>:)        :: k (a -> b) -> k a -> Combinator k b
  (:*>:)         :: k a -> k b -> Combinator k b
  (:<*:)         :: k a -> k b -> Combinator k a
  (:<|>:)        :: k a -> k a -> Combinator k a
  Empty          :: Combinator k a
  Try            :: k a -> Combinator k a
  LookAhead      :: k a -> Combinator k a
  Let            :: Bool -> MVar a -> k a -> Combinator k a
  NotFollowedBy  :: k a -> Combinator k ()
  Branch         :: k (Either a b) -> k (a -> c) -> k (b -> c) -> Combinator k c
  Match          :: k a -> [Defunc (a -> Bool)] -> [k b] -> k b -> Combinator k b
  ChainPre       :: k (a -> a) -> k a -> Combinator k a
  ChainPost      :: k a -> k (a -> a) -> Combinator k a
  MakeRegister   :: ΣVar a -> k a -> k b -> Combinator k b
  GetRegister    :: ΣVar a -> Combinator k a
  PutRegister    :: ΣVar a -> k a -> Combinator k ()
  Debug          :: String -> k a -> Combinator k a
  MetaCombinator :: MetaCombinator -> k a -> Combinator k a

data ScopeRegister (k :: * -> *) (a :: *) where
  ScopeRegister :: k a -> (forall r. Reg r a -> k b) -> ScopeRegister k b

newtype Reg (r :: *) a = Reg (ΣVar a)

data MetaCombinator where
  Cut         :: MetaCombinator
  RequiresCut :: MetaCombinator

-- Instances
instance IFunctor Combinator where
  imap _ (Pure x)             = Pure x
  imap _ (Satisfy p)          = Satisfy p
  imap f (p :<*>: q)          = f p :<*>: f q
  imap f (p :*>: q)           = f p :*>: f q
  imap f (p :<*: q)           = f p :<*: f q
  imap f (p :<|>: q)          = f p :<|>: f q
  imap _ Empty                = Empty
  imap f (Try p)              = Try (f p)
  imap f (LookAhead p)        = LookAhead (f p)
  imap f (Let r v p)          = Let r v (f p)
  imap f (NotFollowedBy p)    = NotFollowedBy (f p)
  imap f (Branch b p q)       = Branch (f b) (f p) (f q)
  imap f (Match p fs qs d)    = Match (f p) fs (map f qs) (f d)
  imap f (ChainPre op p)      = ChainPre (f op) (f p)
  imap f (ChainPost p op)     = ChainPost (f p) (f op)
  imap f (MakeRegister σ p q) = MakeRegister σ (f p) (f q)
  imap f (GetRegister σ)      = GetRegister σ
  imap f (PutRegister σ p)    = PutRegister σ (f p)
  imap f (Debug name p)       = Debug name (f p)
  imap f (MetaCombinator m p) = MetaCombinator m (f p)

instance Show (Fix Combinator a) where
  show = ($ "") . getConst1 . cata (Const1 . alg)
    where
      alg (Pure x)                                  = "(pure " . shows x . ")"
      alg (Satisfy f)                               = "(satisfy " . shows f . ")"
      alg (Const1 pf :<*>: Const1 px)               = "(" . pf . " <*> " .  px . ")"
      alg (Const1 p :*>: Const1 q)                  = "(" . p . " *> " . q . ")"
      alg (Const1 p :<*: Const1 q)                  = "(" . p . " <* " . q . ")"
      alg (Const1 p :<|>: Const1 q)                 = "(" . p . " <|> " . q . ")"
      alg Empty                                     = "empty"
      alg (Try (Const1 p))                          = "(try " . p . ")"
      alg (LookAhead (Const1 p))                    = "(lookAhead " . p . ")"
      alg (Let False v _)                           = "(let-bound " . shows v . ")"
      alg (Let True v _)                            = "(rec " . shows v . ")"
      alg (NotFollowedBy (Const1 p))                = "(notFollowedBy " . p . ")"
      alg (Branch (Const1 b) (Const1 p) (Const1 q)) = "(branch " . b . " " . p . " " . q . ")"
      alg (Match (Const1 p) fs qs (Const1 def))     = "(match " . p . " " . shows fs . " [" . intercalateDiff (", ") (map getConst1 qs) . "] "  . def . ")"
      alg (ChainPre (Const1 op) (Const1 p))         = "(chainPre " . op . " " . p . ")"
      alg (ChainPost (Const1 p) (Const1 op))        = "(chainPost " . p . " " . op . ")"
      alg (MakeRegister σ (Const1 p) (Const1 q))    = "(make " . shows σ . " " . p . " " . q . ")"
      alg (GetRegister σ)                           = "(get " . shows σ . ")"
      alg (PutRegister σ (Const1 p))                = "(put " . shows σ . " " . p . ")"
      alg (Debug _ (Const1 p))                      = p
      alg (MetaCombinator m (Const1 p))             = p . " [" . shows m . "]"

instance IFunctor ScopeRegister where
  imap f (ScopeRegister p g) = ScopeRegister (f p) (f . g)

instance Show MetaCombinator where
  show Cut = "coins after"
  show RequiresCut = "requires cut"