{-# LANGUAGE TemplateHaskell #-}
module Utils (code, (>*<), WQ(..), Code) where

import LiftPlugin (LiftTo, code)
import Language.Haskell.TH (TExpQ)

data WQ a = WQ { _val :: a, _code :: TExpQ a }
instance LiftTo WQ where code x = WQ x [||x||]

type Code a = TExpQ a

-- pronounced quapp
(>*<) :: WQ (a -> b) -> WQ a -> WQ b
WQ f qf >*< WQ x qx = WQ (f x) [||$$qf $$qx||]
infixl 9 >*<