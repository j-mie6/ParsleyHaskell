{-# LANGUAGE TemplateHaskell,
             FlexibleInstances,
             UndecidableInstances #-}
module Utils (code, WQ(..), Code, Quapplicative(..)) where

import LiftPlugin (LiftTo, code)
import Language.Haskell.TH (TExpQ)

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