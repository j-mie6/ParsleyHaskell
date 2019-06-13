{-# LANGUAGE TemplateHaskell #-}
module Utils (lift', (>*<), WQ(..), TExpQ) where

import LiftPlugin (Pure, lift')
import Language.Haskell.TH (TExpQ)

data WQ a = WQ { _val :: a, _code :: TExpQ a }
instance Pure WQ where lift' x = WQ x [||x||]

-- pronounced quapp
(>*<) :: WQ (a -> b) -> WQ a -> WQ b
WQ f qf >*< WQ x qx = WQ (f x) [||$$qf $$qx||]
infixl 9 >*<