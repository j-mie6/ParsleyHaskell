module Parsley.Internal.Core.Lam (reduceAndGen, Lam(..)) where

import Parsley.Internal.Common.Utils (Code)

data Lam a where
    Abs :: (Lam a -> Lam b) -> Lam (a -> b)
    App :: Lam (a -> b) -> Lam a -> Lam b
    Var :: Code a -> Lam a
    If  :: Lam Bool -> Lam a -> Lam a -> Lam a
    Let :: Lam a -> (Lam a -> Lam b) -> Lam b

instance Show (Lam a) where
    show (Abs _) = "(Abs f)"
    show (App f x) = "(App " ++ show f ++ " " ++ show x ++ ")"
    show (Var _) = "(Var x)"
    show (If c t e) = "(If " ++ show c ++ " " ++ show t ++ " " ++ show e ++ ")"
    show (Let x _) = "(Let " ++ show x ++ " f)"

-- TODO: This needs improving, it's quite brittle at the moment!
reduce :: Lam a -> Lam a
reduce = fst . reduce'
  where
      reduce' :: Lam a -> (Lam a, Bool)
      reduce' (App (Abs f) x)       = reduce' (f x)
      reduce' (App (Var f) (Var x)) = (App (Var f) (Var x), True)
      reduce' (App (Var f) x)       = let (x', stuck) = reduce' x in (App (Var f) x', stuck)
      reduce' (App f x)             = let (f', stuck) = reduce' f in if stuck then (App f' x, True) else reduce' (App f' x)
      reduce' (Abs f)               = (Abs f, False)
      reduce' x                     = (x, True)

generate :: Lam a -> Code a
generate (Abs f) = [||\x -> $$(reduceAndGen (f (Var [||x||])))||]
-- These have already been reduced, since we only expose `reduceAndGen`
generate (App f x) = [||$$(generate f) $$(generate x)||]
generate (Var x) = x
generate (If c t e) = [||if $$(reduceAndGen c) then $$(reduceAndGen t) else $$(reduceAndGen e)||]
generate (Let b i) = [||let x = $$(reduceAndGen b) in $$(reduceAndGen (i (Var [||x||])))||]

reduceAndGen :: Lam a -> Code a
reduceAndGen = generate . reduce