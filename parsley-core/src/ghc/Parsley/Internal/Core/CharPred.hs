{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
module Parsley.Internal.Core.CharPred (
    CharPred(..), pattern Item, pattern Specific,
    apply, andPred, orPred, diffPred,
    members, nonMembers,
    lamTerm
  ) where

import Prelude hiding (null)

import Parsley.Internal.Common.RangeSet (RangeSet, elems, unelems, fromRanges, full, member, fold, null, union, extractSingle, singleton, intersection, difference)
import Parsley.Internal.Core.Lam        (Lam(Abs, App, Var, T, F, If))

data CharPred where
  UserPred :: (Char -> Bool) -> Lam (Char -> Bool) -> CharPred
  Ranges :: RangeSet Char -> CharPred

pattern Item :: CharPred
pattern Item <- Ranges (full -> True)
  where Item = Ranges (fromRanges [(minBound, maxBound)])

pattern Specific :: Char -> CharPred
pattern Specific c <- Ranges (extractSingle -> Just c)
  where Specific c = Ranges (singleton c)

apply :: CharPred -> Char -> Bool
apply (UserPred f _) c = f c
apply (Ranges rngs) c = member c rngs

andPred :: CharPred -> CharPred -> CharPred
andPred (UserPred f lf) p = UserPred (\c -> f c && apply p c) (Abs $ \c -> andLam (App lf c) (App (lamTerm p) c))
andPred p (UserPred f lf) = UserPred (\c -> apply p c && f c) (Abs $ \c -> andLam (App (lamTerm p) c) (App lf c))
andPred (Ranges rngs1) (Ranges rngs2) = Ranges (rngs1 `intersection` rngs2)

orPred :: CharPred -> CharPred -> CharPred
orPred (UserPred f lf) p = UserPred (\c -> f c || apply p c) (Abs $ \c -> orLam (App lf c) (App (lamTerm p) c))
orPred p (UserPred f lf) = UserPred (\c -> apply p c || f c) (Abs $ \c -> orLam (App (lamTerm p) c) (App lf c))
orPred (Ranges rngs1) (Ranges rngs2) = Ranges (rngs1 `union` rngs2)

diffPred :: CharPred -> CharPred -> CharPred
diffPred (UserPred f lf) p = UserPred (\c -> f c && not (apply p c)) (Abs $ \c -> andLam (App lf c) (notLam (App (lamTerm p) c)))
diffPred p (UserPred f lf) = UserPred (\c -> apply p c && not (f c)) (Abs $ \c -> andLam (App (lamTerm p) c) (notLam (App lf c)))
diffPred (Ranges rngs1) (Ranges rngs2) = Ranges (rngs1 `difference` rngs2)

andLam :: Lam Bool -> Lam Bool -> Lam Bool
andLam T y = y
andLam x T = x
andLam F _ = F
andLam _ F = F
andLam x y = App (App (Var True [||(&&)||]) x) y

orLam :: Lam Bool -> Lam Bool -> Lam Bool
orLam T _ = T
orLam _ T = T
orLam F y = y
orLam y F = y
orLam x y = App (App (Var True [||(||)||]) x) y

notLam :: Lam Bool -> Lam Bool
notLam T = F
notLam F = T
notLam x = App (Var True [||not||]) x

members :: CharPred -> [Char]
members (UserPred f _) = filter f [minBound..maxBound]
members (Ranges rngs)  = elems rngs

nonMembers :: CharPred -> [Char]
nonMembers (UserPred f _)      = filter (not . f) [minBound..maxBound]
nonMembers (Ranges rngs)       = unelems rngs

lamTerm :: CharPred -> Lam (Char -> Bool)
lamTerm (UserPred _ t) = t
lamTerm Item = Abs (const T)
lamTerm (Ranges (null -> True)) = Abs (const F)
lamTerm (Ranges rngs) =
  Abs $ \c ->
    fold (conv c) F rngs
  where
    conv c l u lb rb
    --  | l == u = eq c (Var True [||l||]) `or` (lb `or` rb)
    --  | otherwise = (lte (Var True [||l||]) c `and` lte c (Var True [||u||])) `or` (lb `or` rb)
      | l == u = eq c (Var True [||l||]) `or` if' (lt c (Var True [||l||])) lb rb
      | otherwise = if' (lte (Var True [||l||]) c) (lte c (Var True [||u||]) `or` rb) lb

    or = orLam
    and = andLam
    lte :: Lam Char -> Lam Char -> Lam Bool
    lte = App . App (Var True [||(<=)||])
    lt :: Lam Char -> Lam Char -> Lam Bool
    lt = App . App (Var True [||(<)||])
    eq :: Lam Char -> Lam Char -> Lam Bool
    eq = App . App (Var True [||(==)||])
    if' x y F = and x y
    if' c x y = If c x y

instance Show CharPred where
  show (UserPred _ f) = show f
  show Item = "const True"
  show (Specific c) = concat ["(== ", show c, ")"]
  show (Ranges rngs) = "elem " ++ show rngs