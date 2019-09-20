{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
module Optimiser (optimise) where

import Prelude hiding ((<$>))
import ParserAST (ParserF(..))
import Analyser  (constantInput)
import Indexed   (Free(Op))
import Utils     (lift', (>*<), WQ(..))

optimise :: ParserF (Free ParserF f) a -> Free ParserF f a
-- DESTRUCTIVE OPTIMISATION
-- Right Absorption Law: empty <*> u                    = empty
optimise (Op Empty :<*>: _)                             = Op Empty
-- Failure Weakening Law: u <*> empty                   = u *> empty
optimise (u :<*>: Op Empty)                             = Op (u :*>: Op Empty)
-- Right Absorption Law: empty *> u                     = empty
optimise (Op Empty :*>: _)                              = Op Empty
-- Right Absorption Law: empty <* u                     = empty
optimise (Op Empty :<*: _)                              = Op Empty
-- Failure Weakening Law: u <* empty                    = u *> empty
optimise (u :<*: Op Empty)                              = Op (u :*>: Op Empty)
-- APPLICATIVE OPTIMISATION
-- Homomorphism Law: pure f <*> pure x                  = pure (f x)
optimise (Op (Pure f) :<*>: Op (Pure x))                = Op (Pure (f >*< x))
-- NOTE: This is basically a shortcut, it can be caught by the Composition Law and Homomorphism law
-- Functor Composition Law: f <$> (g <$> p)             = (f . g) <$> p
optimise (Op (Pure f) :<*>: Op (Op (Pure g) :<*>: p))   = optimise (lift' (.) >*< f >*< g <$> p)
-- Composition Law: u <*> (v <*> w)                     = pure (.) <*> u <*> v <*> w
optimise (u :<*>: Op (v :<*>: w))                       = optimise (optimise (optimise (lift' (.) <$> u) :<*>: v) :<*>: w)
-- Reassociation Law 1: (u *> v) <*> w                  = u *> (v <*> w)
optimise (Op (u :*>: v) :<*>: w)                        = optimise (u :*>: (optimise (v :<*>: w)))
-- Interchange Law: u <*> pure x                        = pure ($ x) <*> u
optimise (u :<*>: Op (Pure x))                          = optimise (lift' flip >*< lift' ($) >*< x <$> u)
-- Right Absorption Law: (f <$> p) *> q                 = p *> q
optimise (Op (Op (Pure f) :<*>: p) :*>: q)              = Op (p :*>: q)
-- Left Absorption Law: p <* (f <$> q)                  = p <* q
optimise (p :<*: (Op (Op (Pure f) :<*>: q)))            = Op (p :<*: q)
-- Reassociation Law 2: u <*> (v <* w)                  = (u <*> v) <* w
optimise (u :<*>: Op (v :<*: w))                        = optimise (optimise (u :<*>: v) :<*: w)
-- Reassociation Law 3: u <*> (v *> pure x)             = (u <*> pure x) <* v
optimise (u :<*>: Op (v :*>: Op (Pure x)))              = optimise (optimise (u :<*>: Op (Pure x)) :<*: v)
-- ALTERNATIVE OPTIMISATION
-- Left Catch Law: pure x <|> u                         = pure x
optimise (p@(Op (Pure x)) :<|>: _)                      = p
-- Left Neutral Law: empty <|> u                        = u
optimise (Op Empty :<|>: u)                             = u
-- Right Neutral Law: u <|> empty                       = u
optimise (u :<|>: Op Empty)                             = u
-- Associativity Law: (u <|> v) <|> w                   = u <|> (v <|> w)
optimise (Op (u :<|>: v) :<|>: w)                       = Op (u :<|>: optimise (v :<|>: w))
-- SEQUENCING OPTIMISATION
-- Identity law: pure x *> u                            = u
optimise (Op (Pure _) :*>: u)                           = u
-- Identity law: (u *> pure x) *> v                     = u *> v
optimise (Op (u :*>: Op (Pure _)) :*>: v)               = Op (u :*>: v)
-- Associativity Law: u *> (v *> w)                     = (u *> v) *> w
optimise (u :*>: Op (v :*>: w))                         = optimise (optimise (u :*>: v) :*>: w)
-- Identity law: u <* pure x                            = u
optimise (u :<*: Op (Pure _))                           = u
-- Identity law: u <* (v *> pure x)                     = u <* v
optimise (u :<*: Op (v :*>: Op (Pure _)))               = optimise (u :<*: v)
-- Commutativity Law: pure x <* u                       = u *> pure x
optimise (Op (Pure x) :<*: u)                           = optimise (u :*>: Op (Pure x))
-- Associativity Law (u <* v) <* w                      = u <* (v <* w)
optimise (Op (u :<*: v) :<*: w)                         = optimise (u :<*: optimise (v :<*: w))
-- Pure lookahead: lookAhead (pure x)                   = pure x
optimise (LookAhead p@(Op (Pure x)))                    = p
-- Dead lookahead: lookAhead empty                      = empty
optimise (LookAhead p@(Op Empty))                       = p
-- Pure negative-lookahead: notFollowedBy (pure x)      = empty
optimise (NotFollowedBy (Op (Pure _)))                  = Op Empty
-- Dead negative-lookahead: notFollowedBy empty         = unit
optimise (NotFollowedBy (Op Empty))                     = Op (Pure (lift' ()))
-- Double Negation Law: notFollowedBy . notFollowedBy   = lookAhead . try . void
optimise (NotFollowedBy (Op (NotFollowedBy p)))         = optimise (LookAhead (Op (Op (Try (constantInput p) p) :*>: Op (Pure (lift' ())))))
-- Zero Consumption Law: notFollowedBy (try p)          = notFollowedBy p
optimise (NotFollowedBy (Op (Try _ p)))                 = optimise (NotFollowedBy p)
-- Idempotence Law: lookAhead . lookAhead               = lookAhead
optimise (LookAhead (Op (LookAhead p)))                 = Op (LookAhead p)
-- Right Identity Law: notFollowedBy . lookAhead        = notFollowedBy
optimise (NotFollowedBy (Op (LookAhead p)))             = optimise (NotFollowedBy p)
-- Left Identity Law: lookAhead . notFollowedBy         = notFollowedBy
optimise (LookAhead (Op (NotFollowedBy p)))             = Op (NotFollowedBy p)
-- Transparency Law: notFollowedBy (try p <|> q)        = notFollowedBy p *> notFollowedBy q
optimise (NotFollowedBy (Op (Op (Try _ p) :<|>: q)))    = optimise (optimise (NotFollowedBy p) :*>: optimise (NotFollowedBy q))
-- Distributivity Law: lookAhead p <|> lookAhead q      = lookAhead (p <|> q)
optimise (Op (LookAhead p) :<|>: Op (LookAhead q))      = optimise (LookAhead (optimise (p :<|>: q)))
-- Interchange Law: lookAhead (p *> pure x)             = lookAhead p *> pure x
optimise (LookAhead (Op (p :*>: Op (Pure x))))          = optimise (optimise (LookAhead p) :*>: Op (Pure x))
-- Interchange law: lookAhead (f <$> p)                 = f <$> lookAhead p
optimise (LookAhead (Op (Op (Pure f) :<*>: p)))         = optimise (f <$> optimise (LookAhead p))
-- Absorption Law: p <*> notFollowedBy q                = (p <*> unit) <* notFollowedBy q
optimise (p :<*>: Op (NotFollowedBy q))                 = optimise (optimise (p :<*>: Op (Pure (lift' ()))) :<*: Op (NotFollowedBy q))
-- Idempotence Law: notFollowedBy (p *> pure x)         = notFollowedBy p
optimise (NotFollowedBy (Op (p :*>: Op (Pure _))))      = optimise (NotFollowedBy p)
-- Idempotence Law: notFollowedBy (f <$> p)             = notFollowedBy p
optimise (NotFollowedBy (Op (Op (Pure _) :<*>: p)))     = optimise (NotFollowedBy p)
-- Interchange Law: try (p *> pure x)                   = try p *> pure x
optimise (Try n (Op (p :*>: Op (Pure x))))              = optimise (optimise (Try n p) :*>: Op (Pure x))
-- Interchange law: try (f <$> p)                       = f <$> try p
optimise (Try n (Op (Op (Pure f) :<*>: p)))             = optimise (f <$> optimise (Try n p))
optimise (Try Nothing p)                                = case constantInput p of
                                                            Just 0 -> p
                                                            -- This is a desirable thing to have, but we don't want to miss out
                                                            -- on possible constant input optimisations. It might be better to
                                                            -- perform global input size optimisation checks, potentially as a
                                                            -- separate instruction even? Or use strings, then this is unnecessary
                                                            --Just 1 -> p
                                                            ci -> Op (Try ci p)
-- pure Left law: branch (pure (Left x)) p q            = p <*> pure x
optimise (Branch (Op (Pure (WQ (Left x) ql))) p _)      = optimise (p :<*>: Op (Pure (WQ x qx))) where qx = [||case $$ql of Left x -> x||]
-- pure Right law: branch (pure (Right x)) p q          = q <*> pure x
optimise (Branch (Op (Pure (WQ (Right x) ql))) _ q)     = optimise (q :<*>: Op (Pure (WQ x qx))) where qx = [||case $$ql of Right x -> x||]
-- Generalised Identity law: branch b (pure f) (pure g) = either f g <$> b
optimise (Branch b (Op (Pure f)) (Op (Pure g)))         = optimise (lift' either >*< f >*< g <$> b)
-- Interchange law: branch (x *> y) p q                 = x *> branch y p q
optimise (Branch (Op (x :*>: y)) p q)                   = optimise (x :*>: optimise (Branch y p q))
-- Negated Branch law: branch b p empty                 = branch (swapEither <$> b) empty p
optimise (Branch b p (Op Empty))                        = Op (Branch (Op (Op (Pure (WQ (either Right Left) [||either Right Left||])) :<*>: b)) (Op Empty) p)
-- Branch Fusion law: branch (branch b empty (pure f)) empty k                  = branch (g <$> b) empty k where g is a monad transforming (>>= f)
optimise (Branch (Op (Branch b (Op Empty) (Op (Pure (WQ f qf))))) (Op Empty) k) = optimise (Branch (optimise (Op (Pure (WQ g qg)) :<*>: b)) (Op Empty) k)
  where
    g (Left _) = Left ()
    g (Right x) = case f x of
      Left _ -> Left ()
      Right x -> Right x
    qg = [||\case Left _ -> Left ()
                  Right x -> case $$qf x of
                               Left _ -> Left ()
                               Right y -> Right y||]
-- Distributivity Law: f <$> branch b p q                = branch b ((f .) <$> p) ((f .) <$> q)
optimise (Op (Pure f) :<*>: Op (Branch b p q))           = optimise (Branch b (optimise (lift' (.) >*< f <$> p)) (optimise (lift' (.) >*< f <$> q)))
-- pure Match law: match vs (pure x) f def               = if elem x vs then f x else def
optimise (Match (Op (Pure (WQ x _))) fs qs def)          = foldr (\(f, q) k -> if _val f x then q else k) def (zip fs qs)
-- Generalised Identity Match law: match vs p (pure . f) def = f <$> (p >?> flip elem vs) <|> def
optimise (Match p fs qs def)
  | all (\case {Op (Pure _) -> True; _ -> False}) qs     = optimise (optimise (WQ apply qapply <$> (p >?> (WQ validate qvalidate))) :<|>: def)
    where apply x    = foldr (\(f, Op (Pure y)) k -> if _val f x then _val y else k) (error "whoopsie") (zip fs qs)
          qapply     = foldr (\(f, Op (Pure y)) k -> [||\x -> if $$(_code f) x then $$(_code y) else $$k x||]) ([||const (error "whoopsie")||]) (zip fs qs)
          validate x = foldr (\f b -> _val f x || b) False fs
          qvalidate  = foldr (\f k -> [||\x -> $$(_code f) x || $$k x||]) [||const False||] fs
-- Distributivity Law: f <$> match vs p g def            = match vs p ((f <$>) . g) (f <$> def)
optimise (Op (Pure f) :<*>: (Op (Match p fs qs def)))    = Op (Match p fs (map (optimise . (f <$>)) qs) (optimise (f <$> def)))
-- Trivial let-bindings - NOTE: These will get moved when Let nodes no longer have the "source" in them
optimise (Let False _ p@(Op (Pure _)))                          = p
optimise (Let False _ p@(Op Empty))                             = p
optimise (Let False _ p@(Op (Satisfy _)))                       = p
optimise (Let False _ p@(Op (Op (Satisfy _) :*>: Op (Pure x)))) = p
-- Applicative-fusion across let boundary?
--optimise (Let _ p@(Op ()))
optimise p                                               = Op p

-- try (lookAhead p *> p *> lookAhead q) = lookAhead (p *> q) <* try p

(>?>) :: Free ParserF f a -> WQ (a -> Bool) -> Free ParserF f a
p >?> (WQ f qf) = Op (Branch (Op (WQ g qg <$> p)) (Op Empty) (Op (Pure (lift' id))))
  where
    g x = if f x then Right x else Left ()
    qg = [||\x -> if $$qf x then Right x else Left ()||]

(<$>) :: WQ (a -> b) -> Free ParserF f a -> ParserF (Free ParserF f) b
f <$> p = Op (Pure f) :<*>: p