{-# LANGUAGE PatternSynonyms #-}
module Parsley.Internal.Core.Defunc (module Parsley.Internal.Core.Defunc) where

import Language.Haskell.TH.Syntax (Lift(..))
import Parsley.Internal.Common.Utils (WQ(..), Code, Quapplicative(..))

{-|
This datatype is useful for providing an /inspectable/ representation of common Haskell functions.
These can be provided in place of `WQ` to any combinator that requires it. The only difference is
that the Parsley compiler is able to manipulate and match on the constructors, which might lead to
optimisations. They can also be more convenient than constructing the `WQ` object itself:

> ID ~= WQ id [||id||]
> APP_H f x ~= WQ (f x) [||f x||]

@since 0.1.0.0
-}
data Defunc a where
  -- | Corresponds to the standard @id@ function
  ID      :: Defunc (a -> a)
  -- | Corresponds to the standard @(.)@ function applied to no arguments
  COMPOSE :: Defunc ((b -> c) -> (a -> b) -> (a -> c))
  -- | Corresponds to the standard @flip@ function applied to no arguments
  FLIP    :: Defunc ((a -> b -> c) -> b -> a -> c)
  -- | Corresponds to function application of two other `Defunc` values
  APP_H   :: Defunc (a -> b) -> Defunc a -> Defunc b
  -- | Corresponds to the partially applied @(== x)@ for some `Defunc` value @x@
  EQ_H    :: Eq a => Defunc a -> Defunc (a -> Bool)
  -- | Represents a liftable, showable value
  LIFTED  :: (Show a, Lift a) => a -> Defunc a
  -- | Represents the standard @(:)@ function applied to no arguments
  CONS    :: Defunc (a -> [a] -> [a])
  -- | Represents the standard @const@ function applied to no arguments
  CONST   :: Defunc (a -> b -> a)
  -- | Represents the empty list @[]@
  EMPTY   :: Defunc [a]
  -- | Wraps up any value of type `WQ`
  BLACK   :: WQ a -> Defunc a

  -- Syntax constructors
  {-|
  Represents the regular Haskell @if@ syntax

  @since 0.1.1.0
  -}
  IF_S    :: Defunc Bool -> Defunc a -> Defunc a -> Defunc a
  {-|
  Represents a Haskell lambda abstraction

  @since 0.1.1.0
  -}
  LAM_S   :: (Defunc a -> Defunc b) -> Defunc (a -> b)
  {-|
  Represents a Haskell let binding

  @since 0.1.1.0
  -}
  LET_S   :: Defunc a -> (Defunc a -> Defunc b) -> Defunc b

{-|
This instance is used to manipulate values of `Defunc`.

@since 0.1.0.0
-}
instance Quapplicative Defunc where
  makeQ x qx        = BLACK (makeQ x qx)
  _val ID           = id
  _val COMPOSE      = (.)
  _val FLIP         = flip
  _val (APP_H f x)  = (_val f) (_val x)
  _val (LIFTED x)   = x
  _val (EQ_H x)     = ((_val x) ==)
  _val CONS         = (:)
  _val CONST        = const
  _val EMPTY        = []
  _val (BLACK f)    = _val f
  -- Syntax
  _val (IF_S c t e) = if _val c then _val t else _val e
  _val (LAM_S f)    = \x -> _val (f (makeQ x undefined))
  _val (LET_S x f)  = let y = _val x in _val (f (makeQ y undefined))
  _code = genDefunc
  (>*<) = APP_H

{-|
This pattern represents fully applied composition of two `Defunc` values

@since 0.1.0.0
-}
pattern COMPOSE_H     :: () => ((x -> y -> z) ~ ((b -> c) -> (a -> b) -> a -> c)) => Defunc x -> Defunc y -> Defunc z
pattern COMPOSE_H f g = APP_H (APP_H COMPOSE f) g
{-|
This pattern corresponds to the standard @flip@ function applied to a single argument

@since 0.1.0.0
-}
pattern FLIP_H        :: () => ((x -> y) ~ ((a -> b -> c) -> b -> a -> c)) => Defunc x -> Defunc y
pattern FLIP_H f      = APP_H FLIP f
{-|
Represents the flipped standard @const@ function applied to no arguments

@since 0.1.0.0
-}
pattern FLIP_CONST    :: () => (x ~ (a -> b -> b)) => Defunc x
pattern FLIP_CONST    = FLIP_H CONST
{-|
This pattern represents the unit value @()@

@since 0.1.0.0
-}
pattern UNIT          :: Defunc ()
pattern UNIT          = LIFTED ()

ap :: Defunc (a -> b) -> Defunc a -> Defunc b
ap f x = APP_H f x

genDefunc :: Defunc a -> Code a
genDefunc ID                        = [|| \x -> x ||]
genDefunc COMPOSE                   = [|| \f g x -> f (g x) ||]
genDefunc FLIP                      = [|| \f x y -> f y x ||]
genDefunc (COMPOSE_H f g)           = [|| \x -> $$(genDefunc1 (COMPOSE_H f g) [||x||]) ||]
genDefunc CONST                     = [|| \x _ -> x ||]
genDefunc FLIP_CONST                = [|| \_ y -> y ||]
genDefunc (FLIP_H f)                = [|| \x -> $$(genDefunc1 (FLIP_H f) [||x||]) ||]
genDefunc (APP_H f x)               = genDefunc1 f (genDefunc x)
genDefunc (LIFTED x)                = [|| x ||]
genDefunc (EQ_H x)                  = [|| \y -> $$(genDefunc1 (EQ_H x) [||y||]) ||]
genDefunc CONS                      = [|| \x xs -> x : xs ||]
genDefunc EMPTY                     = [|| [] ||]
genDefunc (IF_S (LIFTED True) t _)  = genDefunc t
genDefunc (IF_S (LIFTED False) _ e) = genDefunc e
genDefunc (IF_S c t e)              = [|| if $$(genDefunc c) then $$(genDefunc t) else $$(genDefunc e) ||]
genDefunc (LAM_S f)                 = [|| \x -> $$(genDefunc1 (LAM_S f) [||x||]) ||]
genDefunc (LET_S x f)               = [|| let y = $$(genDefunc x) in $$(genDefunc (f (makeQ undefined [||y||]))) ||]
genDefunc (BLACK f)                 = _code f

genDefunc1 :: Defunc (a -> b) -> Code a -> Code b
genDefunc1 ID              qx = qx
genDefunc1 COMPOSE         qf = [|| \g x -> $$qf (g x) ||]
genDefunc1 FLIP            qf = [|| \x y -> $$qf y x ||]
genDefunc1 (COMPOSE_H f g) qx = genDefunc1 f (genDefunc1 g qx)
genDefunc1 (APP_H ID f)    qx = genDefunc1 f qx
genDefunc1 (APP_H f x)     qy = genDefunc2 f (genDefunc x) qy
genDefunc1 CONST           qx = [|| \_ -> $$qx ||]
genDefunc1 FLIP_CONST      _  = genDefunc ID
genDefunc1 (FLIP_H f)      qx = [|| \y -> $$(genDefunc2 (FLIP_H f) qx [||y||]) ||]
genDefunc1 (EQ_H x)        qy = [|| $$(genDefunc x)  == $$qy ||]
genDefunc1 (LAM_S f)       qx = genDefunc (f (makeQ undefined qx))
genDefunc1 f               qx = [|| $$(genDefunc f) $$qx ||]

genDefunc2 :: Defunc (a -> b -> c) -> Code a -> Code b -> Code c
genDefunc2 ID              qf qx  = [|| $$qf $$qx ||]
genDefunc2 COMPOSE         qf qg  = [|| \x -> $$qf ($$qg x) ||]
genDefunc2 FLIP            qf qx  = [|| \y -> $$qf y $$qx ||]
genDefunc2 (COMPOSE_H f g) qx qy  = genDefunc2 f (genDefunc1 g qx) qy
genDefunc2 CONST           qx _   = qx
genDefunc2 FLIP_CONST      _  qy  = qy
genDefunc2 (FLIP_H f)      qx qy  = genDefunc2 f qy qx
genDefunc2 CONS            qx qxs = [|| $$qx : $$qxs ||]
genDefunc2 f               qx qy  = [|| $$(genDefunc1 f qx) $$qy ||]

instance Show (Defunc a) where
  show COMPOSE = "(.)"
  show FLIP = "flip"
  show (FLIP_H f) = concat ["(flip ", show f, ")"]
  show (COMPOSE_H f g) = concat ["(", show f, " . ", show g, ")"]
  show (APP_H f x) = concat ["(", show f, " ", show x, ")"]
  show (LIFTED x) = show x
  show (EQ_H x) = concat ["(== ", show x, ")"]
  show ID  = "id"
  show EMPTY = "[]"
  show CONS = "(:)"
  show CONST = "const"
  show (IF_S c b e) = concat ["(if ", show c, " then ", show b, " else ", show e, ")"]
  show (LAM_S _) = "f"
  show _ = "x"