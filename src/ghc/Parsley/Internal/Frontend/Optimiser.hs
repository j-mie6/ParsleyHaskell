{-# LANGUAGE LambdaCase,
             PatternSynonyms,
             ViewPatterns #-}
module Parsley.Internal.Frontend.Optimiser (optimise) where

import Prelude hiding                      ((<$>))
import Parsley.Internal.Common             (Fix(In), Quapplicative(..))
import Parsley.Internal.Core.CombinatorAST (Combinator(..))
import Parsley.Internal.Core.Defunc        (Defunc(..), pattern FLIP_H, pattern COMPOSE_H, pattern FLIP_CONST, pattern UNIT)

pattern (:<$>:) :: Defunc (a -> b) -> Fix Combinator a -> Combinator (Fix Combinator) b
pattern f :<$>: p = In (Pure f) :<*>: p
pattern (:$>:) :: Fix Combinator a -> Defunc b -> Combinator (Fix Combinator) b
pattern p :$>: x = p :*>: In (Pure x)
pattern (:<$:) :: Defunc a -> Fix Combinator b -> Combinator (Fix Combinator) a
pattern x :<$: p = In (Pure x) :<*: p

optimise :: Combinator (Fix Combinator) a -> Fix Combinator a
-- DESTRUCTIVE OPTIMISATION
-- Right Absorption Law: empty <*> u                    = empty
optimise (In Empty :<*>: _)                             = In Empty
-- Failure Weakening Law: u <*> empty                   = u *> empty
optimise (u :<*>: In Empty)                             = optimise (u :*>: In Empty)
-- Right Absorption Law: empty *> u                     = empty
optimise (In Empty :*>: _)                              = In Empty
-- Right Absorption Law: empty <* u                     = empty
optimise (In Empty :<*: _)                              = In Empty
-- Failure Weakening Law: u <* empty                    = u *> empty
optimise (u :<*: In Empty)                              = optimise (u :*>: In Empty)
-- Branch Absorption Law: branch empty p q              = empty
optimise (Branch (In Empty) _ _)                        = In Empty
-- Branch Weakening Law: branch b empty empty           = b *> empty
optimise (Branch b (In Empty) (In Empty))               = optimise (b :*>: In Empty)
-- Match Absorption Law: match _ empty _ def            = def
optimise (Match (In Empty) _ _ def)                     = def
-- Match Weakening Law: match _ p (const empty) empty   = p *> empty
optimise (Match p _ qs (In Empty))
  | all (\case {In Empty -> True; _ -> False}) qs = optimise (p :*>: In Empty)
-- APPLICATIVE OPTIMISATION
-- Identity Law: id <$> u                               = u
optimise (ID :<$>: u)                                   = u
-- Flip const optimisation: flip const <$> u            = u *> pure id
optimise (FLIP_CONST :<$>: u)                           = optimise (u :*>: In (Pure ID))
-- Homomorphism Law: pure f <*> pure x                  = pure (f x)
optimise (f :<$>: In (Pure x))                          = In (Pure (APP_H f x))
-- NOTE: This is basically a shortcut, it can be caught by the Composition Law and Homomorphism law
-- Functor Composition Law: f <$> (g <$> p)             = (f . g) <$> p
optimise (f :<$>: In (g :<$>: p))                       = optimise (COMPOSE_H f g :<$>: p)
-- Composition Law: u <*> (v <*> w)                     = (.) <$> u <*> v <*> w
optimise (u :<*>: In (v :<*>: w))                       = optimise (optimise (optimise (COMPOSE :<$>: u) :<*>: v) :<*>: w)
-- Definition of *>
optimise (In (FLIP_CONST :<$>: p) :<*>: q)              = In (p :*>: q)
-- Definition of <*
optimise (In (CONST :<$>: p) :<*>: q)                   = In (p :<*: q)
-- Reassociation Law 1: (u *> v) <*> w                  = u *> (v <*> w)
optimise (In (u :*>: v) :<*>: w)                        = optimise (u :*>: (optimise (v :<*>: w)))
-- Interchange Law: u <*> pure x                        = pure ($ x) <*> u
optimise (u :<*>: In (Pure x))                          = optimise (APP_H (FLIP_H ID) x :<$>: u)
-- Right Absorption Law: (f <$> p) *> q                 = p *> q
optimise (In (_ :<$>: p) :*>: q)                        = In (p :*>: q)
-- Left Absorption Law: p <* (f <$> q)                  = p <* q
optimise (p :<*: (In (_ :<$>: q)))                      = In (p :<*: q)
-- Reassociation Law 2: u <*> (v <* w)                  = (u <*> v) <* w
optimise (u :<*>: In (v :<*: w))                        = optimise (optimise (u :<*>: v) :<*: w)
-- Reassociation Law 3: u <*> (v $> x)                  = (u <*> pure x) <* v
optimise (u :<*>: In (v :$>: x))                        = optimise (optimise (u :<*>: In (Pure x)) :<*: v)
-- ALTERNATIVE OPTIMISATION
-- Left Catch Law: pure x <|> u                         = pure x
optimise (p@(In (Pure _)) :<|>: _)                      = p
-- Left Neutral Law: empty <|> u                        = u
optimise (In Empty :<|>: u)                             = u
-- Right Neutral Law: u <|> empty                       = u
optimise (u :<|>: In Empty)                             = u
-- Associativity Law: (u <|> v) <|> w                   = u <|> (v <|> w)
optimise (In (u :<|>: v) :<|>: w)                       = In (u :<|>: optimise (v :<|>: w))
-- SEQUENCING OPTIMISATION
-- Identity law: pure x *> u                            = u
optimise (In (Pure _) :*>: u)                           = u
-- Identity law: (u $> x) *> v                          = u *> v
optimise (In (u :$>: _) :*>: v)                         = In (u :*>: v)
-- Associativity Law: u *> (v *> w)                     = (u *> v) *> w
optimise (u :*>: In (v :*>: w))                         = optimise (optimise (u :*>: v) :*>: w)
-- Identity law: u <* pure x                            = u
optimise (u :<*: In (Pure _))                           = u
-- Identity law: u <* (v $> x)                          = u <* v
optimise (u :<*: In (v :$>: _))                         = optimise (u :<*: v)
-- Commutativity Law: x <$ u                            = u $> x
optimise (x :<$: u)                                     = optimise (u :$>: x)
-- Associativity Law (u <* v) <* w                      = u <* (v <* w)
optimise (In (u :<*: v) :<*: w)                         = optimise (u :<*: optimise (v :<*: w))
-- Pure lookahead: lookAhead (pure x)                   = pure x
optimise (LookAhead p@(In (Pure _)))                    = p
-- Dead lookahead: lookAhead empty                      = empty
optimise (LookAhead p@(In Empty))                       = p
-- Pure negative-lookahead: notFollowedBy (pure x)      = empty
optimise (NotFollowedBy (In (Pure _)))                  = In Empty
-- Dead negative-lookahead: notFollowedBy empty         = unit
optimise (NotFollowedBy (In Empty))                     = In (Pure UNIT)
-- Double Negation Law: notFollowedBy . notFollowedBy   = lookAhead . try . void
optimise (NotFollowedBy (In (NotFollowedBy p)))         = optimise (LookAhead (In (In (Try p) :*>: In (Pure UNIT))))
-- Zero Consumption Law: notFollowedBy (try p)          = notFollowedBy p
optimise (NotFollowedBy (In (Try p)))                   = optimise (NotFollowedBy p)
-- Idempotence Law: lookAhead . lookAhead               = lookAhead
optimise (LookAhead (In (LookAhead p)))                 = In (LookAhead p)
-- Right Identity Law: notFollowedBy . lookAhead        = notFollowedBy
optimise (NotFollowedBy (In (LookAhead p)))             = optimise (NotFollowedBy p)
-- Left Identity Law: lookAhead . notFollowedBy         = notFollowedBy
optimise (LookAhead (In (NotFollowedBy p)))             = In (NotFollowedBy p)
-- Transparency Law: notFollowedBy (try p <|> q)        = notFollowedBy p *> notFollowedBy q
optimise (NotFollowedBy (In (In (Try p) :<|>: q)))      = optimise (optimise (NotFollowedBy p) :*>: optimise (NotFollowedBy q))
-- Distributivity Law: lookAhead p <|> lookAhead q      = lookAhead (try p <|> q)
optimise (In (LookAhead p) :<|>: In (LookAhead q))      = optimise (LookAhead (optimise (In (Try p) :<|>: q)))
-- Interchange Law: lookAhead (p $> x)                  = lookAhead p $> x
optimise (LookAhead (In (p :$>: x)))                    = optimise (optimise (LookAhead p) :$>: x)
-- Interchange law: lookAhead (f <$> p)                 = f <$> lookAhead p
optimise (LookAhead (In (f :<$>: p)))                   = optimise (f :<$>: optimise (LookAhead p))
-- Absorption Law: p <*> notFollowedBy q                = (p <*> unit) <* notFollowedBy q
optimise (p :<*>: In (NotFollowedBy q))                 = optimise (optimise (p :<*>: In (Pure UNIT)) :<*: In (NotFollowedBy q))
-- Idempotence Law: notFollowedBy (p $> x)              = notFollowedBy p
optimise (NotFollowedBy (In (p :$>: _)))                = optimise (NotFollowedBy p)
-- Idempotence Law: notFollowedBy (f <$> p)             = notFollowedBy p
optimise (NotFollowedBy (In (_ :<$>: p)))               = optimise (NotFollowedBy p)
-- Interchange Law: try (p $> x)                        = try p $> x
optimise (Try (In (p :$>: x)))                          = optimise (optimise (Try p) :$>: x)
-- Interchange law: try (f <$> p)                       = f <$> try p
optimise (Try (In (f :<$>: p)))                         = optimise (f :<$>: optimise (Try p))
-- pure Left law: branch (pure (Left x)) p q            = p <*> pure x
optimise (Branch (In (Pure (l@(_val -> Left x)))) p _)  = optimise (p :<*>: In (Pure (makeQ x qx))) where qx = [||case $$(_code l) of Left x -> x||]
-- pure Right law: branch (pure (Right x)) p q          = q <*> pure x
optimise (Branch (In (Pure (r@(_val -> Right x)))) _ q) = optimise (q :<*>: In (Pure (makeQ x qx))) where qx = [||case $$(_code r) of Right x -> x||]
-- Generalised Identity law: branch b (pure f) (pure g) = either f g <$> b
optimise (Branch b (In (Pure f)) (In (Pure g)))         = optimise (makeQ (either (_val f) (_val g)) [||either $$(_code f) $$(_code g)||] :<$>: b)
-- Interchange law: branch (x *> y) p q                 = x *> branch y p q
optimise (Branch (In (x :*>: y)) p q)                   = optimise (x :*>: optimise (Branch y p q))
-- Negated Branch law: branch b p empty                 = branch (swapEither <$> b) empty p
optimise (Branch b p (In Empty))                        = In (Branch (In (In (Pure (makeQ (either Right Left) [||either Right Left||])) :<*>: b)) (In Empty) p)
-- Branch Fusion law: branch (branch b empty (pure f)) empty k                  = branch (g <$> b) empty k where g is a monad transforming (>>= f)
optimise (Branch (In (Branch b (In Empty) (In (Pure f)))) (In Empty) k) = optimise (Branch (optimise (In (Pure (makeQ g qg)) :<*>: b)) (In Empty) k)
  where
    g (Left _) = Left ()
    g (Right x) = case _val f x of
      Left _ -> Left ()
      Right x -> Right x
    qg = [||\case Left _ -> Left ()
                  Right x -> case $$(_code f) x of
                               Left _ -> Left ()
                               Right y -> Right y||]
-- Distributivity Law: f <$> branch b p q                = branch b ((f .) <$> p) ((f .) <$> q)
optimise (f :<$>: In (Branch b p q))                     = optimise (Branch b (optimise (APP_H COMPOSE f :<$>: p)) (optimise (APP_H COMPOSE f :<$>: q)))
-- pure Match law: match vs (pure x) f def               = if elem x vs then f x else def
optimise (Match (In (Pure x)) fs qs def)                 = foldr (\(f, q) k -> if _val f (_val x) then q else k) def (zip fs qs)
-- TODO I'm not actually sure this one is a good optimisation? might have some size constraint on it
-- Generalised Identity Match law: match vs p (pure . f) def = f <$> (p >?> flip elem vs) <|> def
{-optimise (Match p fs qs def)
  | all (\case {In (Pure _) -> True; _ -> False}) qs     = optimise (optimise (makeQ apply qapply :<$>: (p >?> (makeQ validate qvalidate))) :<|>: def)
    where apply x    = foldr (\(f, In (Pure y)) k -> if _val f x then _val y else k) (error "whoopsie") (zip fs qs)
          qapply     = [||\x -> $$(foldr (\(f, In (Pure y)) k -> [||if $$(_code f) x then $$(_code y) else $$k||]) ([||error "whoopsie"||]) (zip fs qs))||]
          validate x = foldr (\f b -> _val f x || b) False fs
          qvalidate  = [||\x -> $$(foldr (\f k -> [||$$(_code f) x || $$k||]) [||False||] fs)||]-}
-- Distributivity Law: f <$> match vs p g def            = match vs p ((f <$>) . g) (f <$> def)
optimise (f :<$>: (In (Match p fs qs def)))              = In (Match p fs (map (optimise . (f :<$>:)) qs) (optimise (f :<$>: def)))
-- Trivial let-bindings - NOTE: These will get moved when Let nodes no longer have the "source" in them
optimise (Let False _ p@(In (Pure _)))                               = p
optimise (Let False _ p@(In Empty))                                  = p
optimise (Let False _ p@(In (Satisfy _)))                            = p
optimise (Let False _ p@(In (In (Satisfy _) :$>: _)))                = p
optimise (Let False _ p@(In (GetRegister _)))                        = p
optimise (Let False _ p@(In (In (Pure _) :<*>: In (GetRegister _)))) = p
optimise p                                                           = In p

-- try (lookAhead p *> p *> lookAhead q) = lookAhead (p *> q) <* try p

{-(>?>) :: Fix Combinator a -> Defunc (a -> Bool) -> Fix Combinator a
p >?> f = In (Branch (In (makeQ g qg :<$>: p)) (In Empty) (In (Pure ID)))
  where
    g x = if _val f x then Right x else Left ()
    qg = [||\x -> if $$(_code f) x then Right x else Left ()||]-}