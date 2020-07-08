{-# LANGUAGE TemplateHaskell,
             FlexibleInstances,
             UndecidableInstances #-}
module Parsley.Common.Utils (code, WQ(..), Code, Quapplicative(..), intercalate, intercalateDiff) where

import LiftPlugin (LiftTo, code)
import Language.Haskell.TH (TExpQ)
import Data.List (intersperse)
import Data.String (IsString(..))

type Code a = TExpQ a
data WQ a = WQ { __val :: a, __code :: Code a }
instance Quapplicative q => LiftTo q where code x = makeQ x [||x||]

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