module Parsley.Internal.Core.Lam (normaliseGen, normalise, Lam(..)) where

import Parsley.Internal.Common.Utils (Code)

data Lam a where
    Abs :: (Lam a -> Lam b) -> Lam (a -> b)
    App :: Lam (a -> b) -> Lam a -> Lam b
    Var :: Bool {- Simple -} -> Code a -> Lam a
    If  :: Lam Bool -> Lam a -> Lam a -> Lam a
    Let :: Lam a -> (Lam a -> Lam b) -> Lam b
    T   :: Lam Bool
    F   :: Lam Bool

normalise :: Lam a -> Lam a
normalise x = reduce x
  where
    reduce :: Lam a -> Lam a
    reduce x
      | normal x = x
      | otherwise = reduce (reduceStep x)

    reduceStep :: Lam a -> Lam a
    reduceStep (App (Abs f) x) = f x
    reduceStep (App f x)
      | normal f = App f (reduceStep x)
      | otherwise = App (reduceStep f) x
    reduceStep (If T x _) = x
    reduceStep (If F _ y) = y
    reduceStep x = x

    normal :: Lam a -> Bool
    normal (App (Abs _) _) = False
    normal (App f x) = normal f && normal x
    normal (If T _ _) = False
    normal (If F _ _) = False
    normal _ = True

generate :: Lam a -> Code a
generate (Abs f)    = [||\x -> $$(normaliseGen (f (Var True [||x||])))||]
-- These have already been reduced, since we only expose `normaliseGen`
generate (App f x)  = [||$$(generate f) $$(generate x)||]
generate (Var _ x)  = x
generate (If c t e) = [||if $$(normaliseGen c) then $$(normaliseGen t) else $$(normaliseGen e)||]
generate (Let b i)  = [||let x = $$(normaliseGen b) in $$(normaliseGen (i (Var True [||x||])))||]
generate T          = [||True||]
generate F          = [||False||]

normaliseGen :: Lam a -> Code a
normaliseGen = generate . normalise

instance Show (Lam a) where
  show = show' . normalise

show' :: Lam a -> String
show' (Abs f) = concat ["(\\x -> ", show (f (Var True undefined)), ")"]
show' (App f x) = concat ["(", show' f, " ", show' x, ")"]
show' (Var True _) = "x"
show' (Var False _) = "complex"
show' (If c t e) = concat ["if ", show' c, " then ", show t, " else ", show e]
show' (Let x f) = concat ["let x = ", show x, " in ", show' (f (Var True undefined))]
show' T = "True"
show' F = "False"