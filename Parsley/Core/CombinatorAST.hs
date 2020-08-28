{-# LANGUAGE ApplicativeDo,
             OverloadedStrings #-}
module Parsley.Core.CombinatorAST (module Parsley.Core.CombinatorAST) where

import Data.Kind                (Type)
import Parsley.Common           (IFunctor, Fix, Const1(..), imap, cata, intercalateDiff, (:+:))
import Parsley.Core.Identifiers (MVar, ΣVar)
import Parsley.Core.Defunc      (Defunc)

-- Parser wrapper type
newtype Parser t a = Parser {unParser :: Fix (Combinator t :+: ScopeRegister) a}

-- Core datatype
data Combinator (t :: Type) (k :: Type -> Type) (a :: Type) where
  Pure           :: Defunc a -> Combinator t k a
  Satisfy        :: Defunc (t -> Bool) -> Combinator t k t
  (:<*>:)        :: k (a -> b) -> k a -> Combinator t k b
  (:*>:)         :: k a -> k b -> Combinator t k b
  (:<*:)         :: k a -> k b -> Combinator t k a
  (:<|>:)        :: k a -> k a -> Combinator t k a
  Empty          :: Combinator t k a
  Try            :: k a -> Combinator t k a
  LookAhead      :: k a -> Combinator t k a
  Let            :: Bool -> MVar a -> k a -> Combinator t k a
  NotFollowedBy  :: k a -> Combinator t k ()
  Branch         :: k (Either a b) -> k (a -> c) -> k (b -> c) -> Combinator t k c
  Match          :: k a -> [Defunc (a -> Bool)] -> [k b] -> k b -> Combinator t k b
  ChainPre       :: k (a -> a) -> k a -> Combinator t k a
  ChainPost      :: k a -> k (a -> a) -> Combinator t k a
  MakeRegister   :: ΣVar a -> k a -> k b -> Combinator t k b
  GetRegister    :: ΣVar a -> Combinator t k a
  PutRegister    :: ΣVar a -> k a -> Combinator t k ()
  Debug          :: String -> k a -> Combinator t k a
  MetaCombinator :: MetaCombinator -> k a -> Combinator t k a

data ScopeRegister (k :: Type -> Type) (a :: Type) where
  ScopeRegister :: k a -> (forall r. Reg r a -> k b) -> ScopeRegister k b

newtype Reg (r :: Type) a = Reg (ΣVar a)

data MetaCombinator where
  Cut         :: MetaCombinator
  RequiresCut :: MetaCombinator

-- Instances
instance IFunctor (Combinator t) where
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
  imap _ (GetRegister σ)      = GetRegister σ
  imap f (PutRegister σ p)    = PutRegister σ (f p)
  imap f (Debug name p)       = Debug name (f p)
  imap f (MetaCombinator m p) = MetaCombinator m (f p)

instance Show (Fix (Combinator t) a) where
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

traverseCombinator :: Applicative m => (forall a. f a -> m (k a)) -> Combinator t f a -> m (Combinator t k a)
traverseCombinator expose (pf :<*>: px)        = do pf' <- expose pf; px' <- expose px; pure (pf' :<*>: px')
traverseCombinator expose (p :*>: q)           = do p' <- expose p; q' <- expose q; pure (p' :*>: q')
traverseCombinator expose (p :<*: q)           = do p' <- expose p; q' <- expose q; pure (p' :<*: q')
traverseCombinator expose (p :<|>: q)          = do p' <- expose p; q' <- expose q; pure (p' :<|>: q')
traverseCombinator _      Empty                = do pure Empty
traverseCombinator expose (Try p)              = do p' <- expose p; pure (Try p')
traverseCombinator expose (LookAhead p)        = do p' <- expose p; pure (LookAhead p')
traverseCombinator expose (NotFollowedBy p)    = do p' <- expose p; pure (NotFollowedBy p')
traverseCombinator expose (Branch b p q)       = do b' <- expose b; p' <- expose p; q' <- expose q; pure (Branch b' p' q')
traverseCombinator expose (Match p fs qs d)    = do p' <- expose p; qs' <- traverse expose qs; d' <- expose d; pure (Match p' fs qs' d')
traverseCombinator expose (ChainPre op p)      = do op' <- expose op; p' <- expose p; pure (ChainPre op' p')
traverseCombinator expose (ChainPost p op)     = do p' <- expose p; op' <- expose op; pure (ChainPost p' op')
traverseCombinator expose (MakeRegister σ p q) = do p' <- expose p; q' <- expose q; pure (MakeRegister σ p' q')
traverseCombinator _      (GetRegister σ)      = do pure (GetRegister σ)
traverseCombinator expose (PutRegister σ p)    = do p' <- expose p; pure (PutRegister σ p')
traverseCombinator expose (Debug name p)       = do p' <- expose p; pure (Debug name p')
traverseCombinator _      (Pure x)             = do pure (Pure x)
traverseCombinator _      (Satisfy f)          = do pure (Satisfy f)
traverseCombinator expose (Let r v p)          = do p' <- expose p; pure (Let r v p')
traverseCombinator expose (MetaCombinator m p) = do p' <- expose p; pure (MetaCombinator m p')