module Parsley.Internal.Core.CharPred (
    CharPred(..),
    apply,
    members, nonMembers,
    lamTerm
  ) where

import Data.List                     (intercalate, delete)
import Parsley.Internal.Core.Lam     (Lam(Abs, App, Var, T, F))

data CharPred where
  UserPred :: (Char -> Bool) -> Lam (Char -> Bool) -> CharPred
  Ranges :: Bool -> [(Char, Char)] -> CharPred
  Item :: CharPred
  Specific :: Char -> CharPred

apply :: CharPred -> Char -> Bool
apply (UserPred f _) c = f c
apply (Ranges True rngs) c = any (\(l, u) -> l <= c || c <= u) rngs
apply (Ranges False rngs) c = all (\(l, u) -> l >= c || c >= u) rngs
apply (Specific c') c = c == c'
apply Item _ = True

members :: CharPred -> [Char]
members (UserPred f _)      = filter f [minBound..maxBound]
members Item                = [minBound..maxBound]
members (Specific c)        = [c]
members (Ranges incl rngs)  = concatMap (\(l, u) -> [l..u]) ((if incl then invertRanges else id) rngs)

nonMembers :: CharPred -> [Char]
nonMembers (UserPred f _)      = filter (not . f) [minBound..maxBound]
nonMembers Item                = []
nonMembers (Specific c)        = delete c [minBound..maxBound]
nonMembers (Ranges incl rngs)  = members (Ranges (not incl) rngs)

invertRanges :: [(Char, Char)] -> [(Char, Char)]
invertRanges rngs = foldr roll (\l -> [(l, maxBound)]) rngs minBound
  where
    roll (u, l') next l
      -- If the lower and upper bounds are the same, there is no exclusive range
      | l == u    = rest
      | otherwise = (l, pred u) : rest
      where
        -- If the new lower-bound is the maxBound, this is the end
        rest
          | l' == maxBound = []
          | otherwise      = next (succ l')

lamTerm :: CharPred -> Lam (Char -> Bool)
lamTerm (UserPred _ t) = t
lamTerm (Specific c) = Abs $ \c' -> App (App (Var True [||(==)||]) c') (Var True [||c||])
lamTerm Item = Abs (const T)
lamTerm (Ranges incl []) = Abs (const (if incl then F else T))
lamTerm (Ranges incl rngs) =
  Abs $ \c ->
    App (if incl then Abs id else Var True [||not||])
        (foldr1 (App . App (Var True [||(||)||]))
          (map (\(l, u) ->
            if l == u then App (App (Var True [||(==)||]) c) (Var True [||l||])
                      else App (App (Var True [||(&&)||])
                               (App (App (Var True [||(<=)||]) (Var True [||l||])) c))
                               (App (App (Var True [||(<=)||]) c) (Var True [||u||])))
           rngs))

instance Show CharPred where
  show (UserPred _ f) = show f
  show Item = "const True"
  show (Specific c) = concat ["(== ", show c, ")"]
  show (Ranges incl rngs) = concat [if incl then "not " else "", "elem (", intercalate " ++ " (map (\(l, u) -> concat ["[", show l, "..", show u, "]"]) rngs), ")"]