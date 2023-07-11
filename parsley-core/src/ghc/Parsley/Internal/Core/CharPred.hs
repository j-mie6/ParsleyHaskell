{-# LANGUAGE PatternSynonyms, ViewPatterns #-}
{-|
Module      : Parsley.Internal.Core.CharPred
Description : Packaging of offsets and positions.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains `CharPred`, a specialised defunctionalising for @Char -> Bool@ functions.
This can be used to efficiently query for character class membership.

@since 2.1.0.0
-}
module Parsley.Internal.Core.CharPred (
    CharPred(..), pattern Item, pattern Specific,
    apply, andPred, orPred, diffPred, optimisePredGiven, mergePreds,
    members, nonMembers,
    lamTerm
  ) where

import Prelude hiding (null)

import Data.RangeSet             (RangeSet, elems, unelems, fromRanges, full, member, fold, null, union, extractSingle, singleton, intersection, difference, isSubsetOf, sizeRanges, complement)
import Parsley.Internal.Core.Lam (Lam(Abs, App, Var, T, F, If), andLam, notLam, orLam)

{-|
Represents @Char -> Bool@ functions, potentially in a more inspectable way.

@since 2.1.0.0
-}
data CharPred where
  -- | This is a raw user-defined predicate, with little inspectability other than membership.
  UserPred :: (Char -> Bool) -> Lam (Char -> Bool) -> CharPred
  -- | This accounts for a character-class, implemented using a `RangeSet` for efficient querying and space.
  Ranges :: RangeSet Char -> CharPred

{-|
Represents @const True@.

@since 2.1.0.0
-}
pattern Item :: CharPred
pattern Item <- Ranges (full -> True)
  where Item = Ranges (fromRanges [(minBound, maxBound)])

{-|
Represents @(== c)@ for some specific @c@.

@since 2.1.0.0
-}
pattern Specific :: Char -> CharPred
pattern Specific c <- Ranges (extractSingle -> Just c)
  where Specific c = Ranges (singleton c)

{-|
Tests whether a given character falls within the predicate.

@since 2.1.0.0
-}
apply :: CharPred -> Char -> Bool
apply (UserPred f _) c = f c
apply (Ranges rngs) c = member c rngs

{-|
Merges two predicates by creating one which only returns true when a character
is in both original predicates.

@since 2.1.0.0
-}
andPred :: CharPred -> CharPred -> CharPred
andPred (UserPred f lf) p = UserPred (\c -> f c && apply p c) (Abs $ \c -> andLam (App lf c) (App (lamTerm p) c))
andPred p (UserPred f lf) = UserPred (\c -> apply p c && f c) (Abs $ \c -> andLam (App (lamTerm p) c) (App lf c))
andPred (Ranges rngs1) (Ranges rngs2) = Ranges (rngs1 `intersection` rngs2)

{-|
Occasionally, characters can pass through a predicate only to pass through another at a later point.
This given information can be used to optimise the new predicate the character is fed through.

This works as follows:

  * If the given knowledge is a subset of the new predicate, then we /know/ that any character check
    will have passed, because it already passed a stricter check. The predicate can, therefore, be
    optimised to `Item`.
  * Otherwise, the character can only pass through both predicates if it can pass through their
    intersection. If the intersection is smaller (in terms of the number of checks required to
    establish membership), then it should be used as it generates smaller code.
  * If neither of the above conditions are true, then the original predicate remains the most
    efficient for future tests.

@since 2.1.0.0
-}
optimisePredGiven :: CharPred -- ^ A predicate to be optimised with previous given knowledge.
                  -> CharPred -- ^ A predicate that is known to already be true.
                  -> CharPred
optimisePredGiven (Ranges pred) (Ranges given)
  | isSubsetOf given pred = Item
  | sizeRanges inter <= sizeRanges pred = Ranges inter
  | otherwise = Ranges pred
  where
    inter = intersection given pred
optimisePredGiven p _ = p

mergePreds :: CharPred -> CharPred -> CharPred
mergePreds (Ranges p1) (Ranges p2)
  | isSubsetOf p1 p2 = Ranges p2
  | isSubsetOf p2 p1 = Ranges p1
mergePreds _ _ = Item

{-|
Merges two predicates by creating one which only returns true when a character
is in either of the original predicates.

@since 2.1.0.0
-}
orPred :: CharPred -> CharPred -> CharPred
orPred (UserPred f lf) p = UserPred (\c -> f c || apply p c) (Abs $ \c -> orLam (App lf c) (App (lamTerm p) c))
orPred p (UserPred f lf) = UserPred (\c -> apply p c || f c) (Abs $ \c -> orLam (App (lamTerm p) c) (App lf c))
orPred (Ranges rngs1) (Ranges rngs2) = Ranges (rngs1 `union` rngs2)

{-|
Merges two predicates by creating one which only returns true when a character
is in the first but not the second predicate.

@since 2.1.0.0
-}
diffPred :: CharPred -> CharPred -> CharPred
diffPred (UserPred f lf) p = UserPred (\c -> f c && not (apply p c)) (Abs $ \c -> andLam (App lf c) (notLam (App (lamTerm p) c)))
diffPred p (UserPred f lf) = UserPred (\c -> apply p c && not (f c)) (Abs $ \c -> andLam (App (lamTerm p) c) (notLam (App lf c)))
diffPred (Ranges rngs1) (Ranges rngs2) = Ranges (rngs1 `difference` rngs2)

{-|
Given a predicate, returns the full range of characters it returns @True@ for.

@since 2.1.0.0
-}
members :: CharPred -> [Char]
members (UserPred f _) = filter f [minBound..maxBound]
members (Ranges rngs)  = elems rngs

{-|
Given a predicate, returns the full range of characters it returns @False@ for.

@since 2.1.0.0
-}
nonMembers :: CharPred -> [Char]
nonMembers (UserPred f _)      = filter (not . f) [minBound..maxBound]
nonMembers (Ranges rngs)       = unelems rngs

{-|
Converts this predicate into a `Lam` term represention. This representation can
be optimised.

@since 2.1.0.0
-}
-- TODO: Something to optimise /= or noneOf?
lamTerm :: CharPred -> Lam (Char -> Bool)
lamTerm (UserPred _ t) = t
lamTerm Item = Abs (const T)
lamTerm (Ranges (null -> True)) = Abs (const F)
lamTerm (Ranges (extractSingle . complement -> Just c)) = App (Var True [||(/=)||]) (Var True [||c||])
lamTerm (Ranges rngs) =
  Abs $ \c ->
    fold (conv c) F rngs
  where
    conv c l u lb rb
    --  | l == u = eq c (Var True [||l||]) `or` (lb `or` rb)
    --  | otherwise = (lte (Var True [||l||]) c `and` lte c (Var True [||u||])) `or` (lb `or` rb)
      | l == u        = eq c (Var True [||l||]) `or` If (lt c (Var True [||l||])) lb rb
      -- the left can be omitted here
      | l == minBound = lte c (Var True [||u||]) `or` rb
      -- the right can be omitted here
      | u == maxBound = lte (Var True [||l||]) c `or` lb
      | otherwise     = If (lte (Var True [||l||]) c) (lte c (Var True [||u||]) `or` rb) lb

    or = orLam
    lte :: Lam Char -> Lam Char -> Lam Bool
    lte = App . App (Var True [||(<=)||])
    lt :: Lam Char -> Lam Char -> Lam Bool
    lt = App . App (Var True [||(<)||])
    eq :: Lam Char -> Lam Char -> Lam Bool
    eq = App . App (Var True [||(==)||])

instance Show CharPred where
  show (UserPred _ f) = show f
  show Item = "const True"
  show (Specific c) = concat ["(== ", show c, ")"]
  show (Ranges rngs) = "elem " ++ show rngs
