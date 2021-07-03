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
normalise x = if normal x then x else reduce x
  where
    reduce :: Lam a -> Lam a
    reduce (App (Abs f) x) = case f x of
      x | normal x -> x
      x            -> reduce x
    reduce (App f x) = case reduce f of
      f@(Abs _) -> reduce (App f x)
      f         -> App f x
    reduce (If c x y) = case reduce c of
      T -> x
      F -> y
      c -> If c x y
    reduce x = x

    normal :: Lam a -> Bool
    normal (App (Abs _) _) = False
    normal (App f _) = normal f
    normal (If T _ _) = False
    normal (If F _ _) = False
    normal (If x _ _) = normal x
    normal _ = True

generate :: Lam a -> Code a
generate (Abs f)    = [||\x -> $$(normaliseGen (f (Var True [||x||])))||]
-- f has already been reduced, since we only expose `normaliseGen`
generate (App f x)  = [||$$(generate f) $$(normaliseGen x)||]
generate (Var _ x)  = x
-- c has already been reduced, since we only expose `normaliseGen`
generate (If c t e) = [||if $$(generate c) then $$(normaliseGen t) else $$(normaliseGen e)||]
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