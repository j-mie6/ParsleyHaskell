{-# LANGUAGE ImplicitParams #-}
{-|
Module      : Parsley.Internal.Core.Lam
Description : Generic defunctionalised abstraction.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains `Lam`, which is a defunctionalised lambda calculus.
This serves as a more easy to work with form of defunctionalisation moving
into the backend and machine where it is no longer necessary to inspect function
values. It permits for the generation of efficient terms, with some inspection
of values.

@since 1.0.1.0
-}
module Parsley.Internal.Core.Lam (normaliseGen, normalise, Lam(..), andLam, orLam, notLam) where

import Parsley.Internal.Common.Utils   (Code)
import Parsley.Internal.Common.THUtils (eta)

import qualified Parsley.Internal.Opt   as Opt

{-|
Defunctionalised lambda calculus in HOAS form. Supports basic inspection
of values, but not functions.

@since 1.0.1.0
-}
data Lam a where
    -- | Function abstraction.
    Abs :: (Lam a -> Lam b) -> Lam (a -> b)
    -- | Function application.
    App :: Lam (a -> b) -> Lam a -> Lam b
    -- | Variable. The boolean represents whether it is "simple" or "complex", i.e. the size of the term.
    Var :: Bool {- Simple -} -> Code a -> Lam a
    -- | Conditional expression.
    If  :: Lam Bool -> Lam a -> Lam a -> Lam a
    -- | Let-binding.
    Let :: Lam a -> (Lam a -> Lam b) -> Lam b
    -- | Value representing true.
    T   :: Lam Bool
    -- | Value representing false.
    F   :: Lam Bool

andLam :: Lam Bool -> Lam Bool -> Lam Bool
andLam x y = If x y F

orLam :: Lam Bool -> Lam Bool -> Lam Bool
orLam x = If x T

notLam :: Lam Bool -> Lam Bool
notLam x = If x F T

{-|
Optimises a `Lam` expression, reducing it until the outmost lambda, let, or if statement.

@since 1.0.1.0
-}
normalise :: (?flags :: Opt.Flags) => Lam a -> Lam a
normalise x = if normal x || not (Opt.termNormalisation ?flags) then x else reduce x
  where
    reduce :: Lam a -> Lam a
    reduce (App (Abs f) x) = normalise (f x)
    reduce (App f x) = case reduce f of
      f@Abs{} -> reduce (App f x)
      f       -> App f x
    reduce (If T t _) = normalise t
    reduce (If F _ f) = normalise f
    reduce (If _ T T) = T
    reduce (If _ F F) = F
    reduce (If c T F) = normalise c
    -- one of them must be not in normal form
    reduce (If c t f) = normalise (If (normalise c) (normalise t) (normalise f))
    -- Reduction rule found courtesy of David Davies, forever immortalised
    reduce (Let v@(Var True _) f) = normalise (f v)
    reduce x = x

    normal :: Lam a -> Bool
    normal (App (Abs _) _) = False
    normal (App f _) = normal f
    normal (If T _ _) = False
    normal (If F _ _) = False
    normal (If _ T T) = False
    normal (If _ F F) = False
    normal (If _ T F) = False
    normal (If c t f) = normal c && normal t && normal f
    normal (Let (Var True _) _) = False
    normal _ = True

generate :: (?flags :: Opt.Flags) => Lam a -> Code a
generate (Abs f)    = [|| \x -> $$(normaliseGen (f (Var True [||x||]))) ||]
-- f has already been reduced, since we only expose `normaliseGen`
generate (App f x)  = [|| $$(generate f) $$(normaliseGen x) ||]
generate (Var _ x)  = x
-- all parts are reduced
generate (If c T e) = [|| $$(generate c) || $$(generate e) ||]
generate (If c t F) = [|| $$(generate c) && $$(generate t) ||]
generate (If c F T) = [|| not $$(generate c) ||]
generate (If c t e) = [|| if $$(generate c) then $$(generate t) else $$(generate e) ||]
generate (Let b i)  = [|| let x = $$(normaliseGen b) in $$(normaliseGen (i (Var True [||x||]))) ||]
generate T          = [|| True ||]
generate F          = [|| False ||]

{-|
Generates Haskell code that represents a `Lam` value, but normalising it first to ensure the
term is minimal.

@since 1.0.1.0
-}
normaliseGen :: (?flags :: Opt.Flags) => Lam a -> Code a
normaliseGen = eta . generate . normalise

instance Show (Lam a) where
  show = let ?flags = Opt.none { Opt.termNormalisation = True } in show' . normalise

show' :: Lam a -> String
show' (Abs f) = concat ["(\\x -> ", show (f (Var True undefined)), ")"]
show' (App f x) = concat ["(", show' f, " ", show' x, ")"]
show' (Var True _) = "x"
show' (Var False _) = "complex"
show' (If c t e) = concat ["if ", show' c, " then ", show t, " else ", show e]
show' (Let x f) = concat ["let x = ", show x, " in ", show' (f (Var True undefined))]
show' T = "True"
show' F = "False"
