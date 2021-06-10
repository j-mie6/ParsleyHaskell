{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE UndecidableInstances,
             CPP #-}
#if __GLASGOW_HASKELL__ >= 810
{-# LANGUAGE StandaloneKindSignatures #-}
#endif
module Parsley.Internal.Common.Utils (WQ(..), Code, Quapplicative(..), intercalate, intercalateDiff) where

import Data.List (intersperse)
import Data.String (IsString(..))

#if __GLASGOW_HASKELL__ >= 810
import Data.Kind    (Type)
import GHC.Exts    (TYPE, RuntimeRep)
#endif

#if __GLASGOW_HASKELL__ < 900
import Language.Haskell.TH (TExp, Q)
#else
import qualified Language.Haskell.TH as TH (Code, Q)
#endif

{-|
A type alias for typed template haskell code, which represents the Haskell AST for a given value.

@since 0.1.0.0
-}
#if __GLASGOW_HASKELL__ >= 810
type Code :: forall (r :: RuntimeRep). TYPE r -> Type
#endif
#if __GLASGOW_HASKELL__ < 900
type Code a = Q (TExp a)
#else
type Code a = TH.Code TH.Q a
#endif

{-|
Pronounced \"with code\", this datatype is the representation for user-land values. It pairs
a value up with its representation as Haskell @Code@. It should be manipulated using
`Quapplicative`.

@since 0.1.0.0
-}
data WQ a = WQ { __val :: a, __code :: Code a }

{-|
This class is used to manipulate the representations of both user-land values and defunctionalised
representations. It can be used to construct these values as well as extract their underlying value
and code representation on demand.

It is named after the @Applicative@ class, with the @Q@ standing for \"code\". The @(`>*<`)@ operator
is analogous to @(\<*>)@ and `makeQ` analogous to @pure@.

@since 0.1.0.0
-}
class Quapplicative q where
  {-|
  Combines a value with its representation to build one of the representation types.

  @since 0.1.0.0
  -}
  makeQ :: a -> Code a -> q a

  {-|
  Extracts the regular value out of the representation.

  @since 0.1.0.0
  -}
  _val :: q a -> a

  {-|
  Extracts the representation of the value as code.

  @since 0.1.0.0
  -}
  _code :: q a -> Code a

  {-|
  Pronounced \"quapp\", this can be used to combine the code of a function with the code of a value.

  > const5 = makeQ const [||const||] >*< makeQ 5 [||5||]

  is the same as saying

  > const5 = makeQ (const 5) [||const 5||]

  It is more idiomatically found as the output to the @IdiomsPlugin@.

  @since 0.1.0.0
  -}
  (>*<) :: q (a -> b) -> q a -> q b
  f >*< x = makeQ ((_val f) (_val x)) [||$$(_code f) $$(_code x)||]
infixl 9 >*<

{-|
This instance is used to manipulate values of `WQ`.

@since 0.1.0.0
-}
instance Quapplicative WQ where
  makeQ = WQ
  _code = __code
  _val = __val

intercalate :: Monoid w => w -> [w] -> w
intercalate xs xss = mconcat (intersperse xs xss)

instance IsString (String -> String) where
  fromString = showString

newtype Id a = Id {unId :: a -> a}
instance Semigroup (Id a) where f <> g = Id $ unId f . unId g
instance Monoid (Id a) where mempty = Id $ id

intercalateDiff :: (a -> a) -> [(a -> a)] -> a -> a
intercalateDiff sep xs = unId $ intercalate (Id sep) (map Id xs)