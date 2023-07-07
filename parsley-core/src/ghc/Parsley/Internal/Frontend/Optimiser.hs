{-# LANGUAGE ImplicitParams,
             LambdaCase,
             PatternSynonyms,
             ViewPatterns #-}
{-|
Module      : Parsley.Internal.Frontend.Optimiser
Description : Combinator law optimisation.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes the `optimise` algebra, which is used for optimisations based on the laws of parsers.

@since 1.0.0.0
-}
module Parsley.Internal.Frontend.Optimiser (optimise) where

import Prelude hiding                      ((<$>))
import Parsley.Internal.Common             (Fix(In), Quapplicative(..))
import Parsley.Internal.Core.CombinatorAST (Combinator(..))
import Parsley.Internal.Core.Defunc        (Defunc(..), pattern FLIP_H, pattern COMPOSE_H, pattern FLIP_CONST, pattern UNIT)

import qualified Parsley.Internal.Opt   as Opt

pattern (:<$>:) :: Defunc (a -> b) -> Fix Combinator a -> Combinator (Fix Combinator) b
pattern f :<$>: p = In (Pure f) :<*>: p
pattern (:$>:) :: Fix Combinator a -> Defunc b -> Combinator (Fix Combinator) b
pattern p :$>: x = p :*>: In (Pure x)
pattern (:<$:) :: Defunc a -> Fix Combinator b -> Combinator (Fix Combinator) a
pattern x :<$: p = In (Pure x) :<*: p

{-|
Optimises a `Combinator` tree according to the various laws of parsers. See the source
for which laws are being utilised.

@since 1.0.0.0
-}
optimise :: (?flags :: Opt.Flags) => Combinator (Fix Combinator) a -> Fix Combinator a
optimise
  | Opt.lawBasedOptimisations ?flags = opt
  | otherwise                        = In
  where
    opt :: Combinator (Fix Combinator) a -> Fix Combinator a
    -- DESTRUCTIVE OPTIMISATION
    -- Right Absorption Law: empty <*> u               = empty
    opt (In Empty :<*>: _)                             = In Empty
    -- Failure Weakening Law: u <*> empty              = u *> empty
    opt (u :<*>: In Empty)                             = opt (u :*>: In Empty)
    -- Right Absorption Law: empty *> u                = empty
    opt (In Empty :*>: _)                              = In Empty
    -- Right Absorption Law: empty <* u                = empty
    opt (In Empty :<*: _)                              = In Empty
    -- Failure Weakening Law: u <* empty               = u *> empty
    opt (u :<*: In Empty)                              = opt (u :*>: In Empty)
    -- Branch Absorption Law: branch empty p q          = empty
    opt (Branch (In Empty) _ _)                        = In Empty
    -- Branch Weakening Law: branch b empty empty      = b *> empty
    opt (Branch b (In Empty) (In Empty))               = opt (b :*>: In Empty)
    -- Match Absorption Law: match _ empty _ def       = def
    opt (Match (In Empty) _ _ def)                     = def
    -- Match Weakening Law: match _ p (const empty) empty = p *> empty
    opt (Match p _ qs (In Empty))
      | all (\case {In Empty -> True; _ -> False}) qs = opt (p :*>: In Empty)
    -- APPLICATIVE OPTIMISATION
    -- Identity Law: id <$> u                          = u
    opt (ID :<$>: u)                                   = u
    -- Flip const optimisation: flip const <$> u       = u *> pure id
    opt (FLIP_CONST :<$>: u)                           = opt (u :*>: In (Pure ID))
    -- Homomorphism Law: pure f <*> pure x             = pure (f x)
    opt (f :<$>: In (Pure x))                          = In (Pure (APP_H f x))
    -- NOTE: This is basically a shortcut, it can be caught by the Composition Law and Homomorphism law
    -- Functor Composition Law: f <$> (g <$> p)        = (f . g) <$> p
    opt (f :<$>: In (g :<$>: p))                       = opt (COMPOSE_H f g :<$>: p)
    -- Composition Law: u <*> (v <*> w)                = (.) <$> u <*> v <*> w
    opt (u :<*>: In (v :<*>: w))                       = opt (opt (opt (COMPOSE :<$>: u) :<*>: v) :<*>: w)
    -- Definition of *>
    opt (In (FLIP_CONST :<$>: p) :<*>: q)              = In (p :*>: q)
    -- Definition of <*
    opt (In (CONST :<$>: p) :<*>: q)                   = In (p :<*: q)
    -- Reassociation Law 1: (u *> v) <*> w             = u *> (v <*> w)
    opt (In (u :*>: v) :<*>: w)                        = opt (u :*>: opt (v :<*>: w))
    -- Interchange Law: u <*> pure x                   = pure ($ x) <*> u
    opt (u :<*>: In (Pure x))                          = opt (APP_H (FLIP_H ID) x :<$>: u)
    -- Right Absorption Law: (f <$> p) *> q            = p *> q
    opt (In (_ :<$>: p) :*>: q)                        = In (p :*>: q)
    -- Left Absorption Law: p <* (f <$> q)             = p <* q
    opt (p :<*: (In (_ :<$>: q)))                      = In (p :<*: q)
    -- Reassociation Law 2: u <*> (v <* w)             = (u <*> v) <* w
    opt (u :<*>: In (v :<*: w))                        = opt (opt (u :<*>: v) :<*: w)
    -- Reassociation Law 3: u <*> (v $> x)             = (u <*> pure x) <* v
    opt (u :<*>: In (v :$>: x))                        = opt (opt (u :<*>: In (Pure x)) :<*: v)
    -- ALTERNATIVE OPTIMISATION
    -- Left Catch Law: pure x <|> u                    = pure x
    opt (p@(In (Pure _)) :<|>: _)                      = p
    -- Left Neutral Law: empty <|> u                   = u
    opt (In Empty :<|>: u)                             = u
    -- Right Neutral Law: u <|> empty                  = u
    opt (u :<|>: In Empty)                             = u
    -- Associativity Law: (u <|> v) <|> w              = u <|> (v <|> w)
    opt (In (u :<|>: v) :<|>: w)                       = In (u :<|>: opt (v :<|>: w))
    -- SEQUENCING OPTIMISATION
    -- Identity law: pure x *> u                       = u
    opt (In (Pure _) :*>: u)                           = u
    -- Identity law: (u $> x) *> v                     = u *> v
    opt (In (u :$>: _) :*>: v)                         = In (u :*>: v)
    -- Associativity Law: u *> (v *> w)                = (u *> v) *> w
    opt (u :*>: In (v :*>: w))                         = opt (opt (u :*>: v) :*>: w)
    -- Identity law: u <* pure x                       = u
    opt (u :<*: In (Pure _))                           = u
    -- Identity law: u <* (v $> x)                     = u <* v
    opt (u :<*: In (v :$>: _))                         = opt (u :<*: v)
    -- Commutativity Law: x <$ u                       = u $> x
    opt (x :<$: u)                                     = opt (u :$>: x)
    -- Associativity Law (u <* v) <* w                 = u <* (v <* w)
    opt (In (u :<*: v) :<*: w)                         = opt (u :<*: opt (v :<*: w))
    -- Pure lookahead: lookAhead (pure x)              = pure x
    opt (LookAhead p@(In (Pure _)))                    = p
    -- Dead lookahead: lookAhead empty                 = empty
    opt (LookAhead p@(In Empty))                       = p
    -- Pure negative-lookahead: notFollowedBy (pure x) = empty
    opt (NotFollowedBy (In (Pure _)))                  = In Empty
    -- Dead negative-lookahead: notFollowedBy empty    = unit
    opt (NotFollowedBy (In Empty))                     = In (Pure UNIT)
    -- Double Negation Law: notFollowedBy . notFollowedBy = lookAhead . try . void
    opt (NotFollowedBy (In (NotFollowedBy p)))         = opt (LookAhead (In (In (Try p) :*>: In (Pure UNIT))))
    -- Zero Consumption Law: notFollowedBy (try p)     = notFollowedBy p
    opt (NotFollowedBy (In (Try p)))                   = opt (NotFollowedBy p)
    -- Idempotence Law: lookAhead . lookAhead          = lookAhead
    opt (LookAhead (In (LookAhead p)))                 = In (LookAhead p)
    -- Right Identity Law: notFollowedBy . lookAhead   = notFollowedBy
    opt (NotFollowedBy (In (LookAhead p)))             = opt (NotFollowedBy p)
    -- Left Identity Law: lookAhead . notFollowedBy    = notFollowedBy
    opt (LookAhead (In (NotFollowedBy p)))             = In (NotFollowedBy p)
    -- Transparency Law: notFollowedBy (try p <|> q)   = notFollowedBy p *> notFollowedBy q
    opt (NotFollowedBy (In (In (Try p) :<|>: q)))      = opt (opt (NotFollowedBy p) :*>: opt (NotFollowedBy q))
    -- Distributivity Law: lookAhead p <|> lookAhead q = lookAhead (try p <|> q)
    opt (In (LookAhead p) :<|>: In (LookAhead q))      = opt (LookAhead (opt (In (Try p) :<|>: q)))
    -- Interchange Law: lookAhead (p $> x)             = lookAhead p $> x
    opt (LookAhead (In (p :$>: x)))                    = opt (opt (LookAhead p) :$>: x)
    -- Interchange law: lookAhead (f <$> p)            = f <$> lookAhead p
    opt (LookAhead (In (f :<$>: p)))                   = opt (f :<$>: opt (LookAhead p))
    -- Absorption Law: p <*> notFollowedBy q           = (p <*> unit) <* notFollowedBy q
    opt (p :<*>: In (NotFollowedBy q))                 = opt (opt (p :<*>: In (Pure UNIT)) :<*: In (NotFollowedBy q))
    -- Idempotence Law: notFollowedBy (p $> x)         = notFollowedBy p
    opt (NotFollowedBy (In (p :$>: _)))                = opt (NotFollowedBy p)
    -- Idempotence Law: notFollowedBy (f <$> p)        = notFollowedBy p
    opt (NotFollowedBy (In (_ :<$>: p)))               = opt (NotFollowedBy p)
    -- Interchange Law: try (p $> x)                   = try p $> x
    opt (Try (In (p :$>: x)))                          = opt (opt (Try p) :$>: x)
    -- Interchange law: try (f <$> p)                  = f <$> try p
    opt (Try (In (f :<$>: p)))                         = opt (f :<$>: opt (Try p))
    -- pure Left law: branch (pure (Left x)) p q       = p <*> pure x
    opt (Branch (In (Pure l@(_val -> Left x))) p _)    = opt (p :<*>: In (Pure (makeQ x qx))) where qx = [||case $$(_code l) of Left x -> x||]
    -- pure Right law: branch (pure (Right x)) p q     = q <*> pure x
    opt (Branch (In (Pure r@(_val -> Right x))) _ q)   = opt (q :<*>: In (Pure (makeQ x qx))) where qx = [||case $$(_code r) of Right x -> x||]
    -- Generalised Identity law: branch b (pure f) (pure g) = either f g <$> b
    opt (Branch b (In (Pure f)) (In (Pure g)))         = opt (makeQ (either (_val f) (_val g)) [||either $$(_code f) $$(_code g)||] :<$>: b)
    -- Interchange law: branch (x *> y) p q            = x *> branch y p q
    opt (Branch (In (x :*>: y)) p q)                   = opt (x :*>: opt (Branch y p q))
    -- Negated Branch law: branch b p empty            = branch (swapEither <$> b) empty p
    opt (Branch b p (In Empty))                        = In (Branch (In (In (Pure (makeQ (either Right Left) [||either Right Left||])) :<*>: b)) (In Empty) p)
    -- Branch Fusion law: branch (branch b empty (pure f)) empty k     = branch (g <$> b) empty k where g is a monad transforming (>>= f)
    opt (Branch (In (Branch b (In Empty) (In (Pure f)))) (In Empty) k) = opt (Branch (opt (In (Pure (makeQ g qg)) :<*>: b)) (In Empty) k)
      where
        g (Left _) = Left ()
        g (Right x) = case _val f x of
          Left _ -> Left ()
          Right x -> Right x
        qg = [||\case Left _ -> Left ()
                      Right x -> case $$(_code f) x of
                                   Left _ -> Left ()
                                   Right y -> Right y||]
    -- Distributivity Law: f <$> branch b p q           = branch b ((f .) <$> p) ((f .) <$> q)
    opt (f :<$>: In (Branch b p q))                     = opt (Branch b (opt (APP_H COMPOSE f :<$>: p)) (opt (APP_H COMPOSE f :<$>: q)))
    -- pure Match law: match vs (pure x) f def          = if elem x vs then f x else def
    opt (Match (In (Pure x)) fs qs def)                 = foldr (\(f, q) k -> if _val f (_val x) then q else k) def (zip fs qs)
    -- Distributivity Law: f <$> match vs p g def       = match vs p ((f <$>) . g) (f <$> def)
    opt (f :<$>: (In (Match p fs qs def)))              = In (Match p fs (map (opt . (f :<$>:)) qs) (opt (f :<$>: def)))
    opt p                                               = In p
