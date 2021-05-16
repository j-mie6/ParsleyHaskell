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

#if __GLASGOW_HASKELL__ == 810
type Code :: forall (r :: RuntimeRep). TYPE r -> Type
#endif
#if __GLASGOW_HASKELL__ < 900
type Code a = Q (TExp a)
#else
type Code a = TH.Code TH.Q a
#endif

data WQ a = WQ { __val :: a, __code :: Code a }

class Quapplicative q where
  makeQ :: a -> Code a -> q a
  _val :: q a -> a
  _code :: q a -> Code a
  -- pronounced quapp
  (>*<) :: q (a -> b) -> q a -> q b
  f >*< x = makeQ ((_val f) (_val x)) [||$$(_code f) $$(_code x)||]
infixl 9 >*<

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