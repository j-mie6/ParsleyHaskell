{-# LANGUAGE PatternSynonyms, TypeApplications #-}
module Parsley.Internal.Core.Defunc (module Parsley.Internal.Core.Defunc) where

--import Data.Typeable                 (Typeable, (:~:)(Refl), eqT)
import Language.Haskell.TH.Syntax    (Lift(..))
import Parsley.Internal.Common.Utils (WQ(..), Code, Quapplicative(..))
import Parsley.Internal.Core.Lam     (normaliseGen, Lam(..))

{-
  TODO: We should support Typeable in LIFTED to be more general, but I don't want changes to
  Defunc to impact back-compat in parsley itself. We should consider not exposing the datatype
  anymore, but exposing smart-constructors in Parsley.Defunctionalized.
  This will come in parsley-2.0.0.0.
-}


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
  LIFTED  :: (Show a, Lift a{-, Typeable a-}) => a -> Defunc a
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
  _code = normaliseGen . lamTerm
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
ap = APP_H

-- TODO: This is deprecated in favour of Typeable as of parsley 2.0.0.0
lamTermBool :: Defunc (a -> Bool) -> Lam (a -> Bool)
lamTermBool (APP_H CONST (LIFTED True)) = Abs (const T)
lamTermBool (APP_H CONST (LIFTED False)) = Abs (const F)
lamTermBool f = lamTerm f

lamTerm :: forall a. Defunc a -> Lam a
lamTerm ID = Abs id
lamTerm COMPOSE = Abs (\f -> Abs (\g -> Abs (App f . App g)))
lamTerm FLIP = Abs (\f -> Abs (\x -> Abs (\y -> App (App f y) x)))
lamTerm (APP_H f x) = App (lamTerm f) (lamTerm x)
{-lamTerm (LIFTED b) | Just Refl <- eqT @a @Bool = case b of
  False -> F
  True -> T-}
lamTerm (LIFTED x) = Var True [||x||]
lamTerm (EQ_H x) = Abs (App (App (Var True [||(==)||]) (lamTerm x)))
lamTerm CONS = Var True [||(:)||]
lamTerm EMPTY = Var True [||[]||]
lamTerm CONST = Abs (Abs . const)
lamTerm (BLACK x) = Var False (_code x)
lamTerm (LAM_S f) = Abs (adaptLam f)
lamTerm (IF_S c t e) = If (lamTerm c) (lamTerm t) (lamTerm e)
lamTerm (LET_S x f) = Let (lamTerm x) (adaptLam f)

adaptLam :: (Defunc a -> Defunc b) -> (Lam a -> Lam b)
adaptLam f = lamTerm . f . defuncTerm
  where
    defuncTerm :: Lam a -> Defunc a
    defuncTerm (Abs f)    = LAM_S (defuncTerm . f . lamTerm)
    defuncTerm (App f x)  = APP_H (defuncTerm f) (defuncTerm x)
    defuncTerm (Var _ x)  = unsafeBLACK x
    defuncTerm (If c t e) = IF_S (defuncTerm c) (defuncTerm t) (defuncTerm e)
    defuncTerm (Let x f)  = LET_S (defuncTerm x) (defuncTerm . f . lamTerm)
    defuncTerm T          = LIFTED True
    defuncTerm F          = LIFTED False

genDefunc :: Defunc a -> Code a
genDefunc = normaliseGen . lamTerm

genDefunc1 :: Defunc (a -> b) -> Code a -> Code b
genDefunc1 f x = genDefunc (APP_H f (unsafeBLACK x))

genDefunc2 :: Defunc (a -> b -> c) -> Code a -> Code b -> Code c
genDefunc2 f x y = genDefunc (APP_H (APP_H f (unsafeBLACK x)) (unsafeBLACK y))

unsafeBLACK :: Code a -> Defunc a
unsafeBLACK = BLACK . WQ undefined

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