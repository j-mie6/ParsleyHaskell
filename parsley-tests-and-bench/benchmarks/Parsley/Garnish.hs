{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Parsley.Garnish (module LiftPlugin) where

import LiftPlugin (LiftTo(..), Syntax(..), overload)
import Parsley (Quapplicative(makeQ, _val, _code, (>*<)), Code)

instance Quapplicative q => LiftTo q where code x = makeQ x [||x||]

mkVal :: Quapplicative q => a -> q a
mkVal x = makeQ x undefined

mkCode :: Quapplicative q => Code a -> q a
mkCode qx = makeQ undefined qx

instance Quapplicative q => Syntax q where
  _if cond _then _else = makeQ
      (if    _val  cond  then    _val  _then  else    _val  _else)
    [||if $$(_code cond) then $$(_code _then) else $$(_code _else)||]
  _lam f = makeQ
      (\x ->    _val  (f (mkVal     x)))
    [||\x -> $$(_code (f (mkCode [||x||]))) ||]
  _let bndr body = makeQ
      (let x =    _val  bndr  in    _val  (body (mkVal     x)))
    [||let x = $$(_code bndr) in $$(_code (body (mkCode [||x||])))||]
  _ap = (>*<)

  -- Case overloading
  _uncons qxs nil cons = makeQ
      (case   (_val  qxs) of { x:xs ->    _val  (cons (mkVal     x)    (mkVal     xs));     [] ->    _val  nil})
    [||case $$(_code qxs) of { x:xs -> $$(_code (cons (mkCode [||x||]) (mkCode [||xs||]))); [] -> $$(_code nil)}||]
  _elim_prod pair f = makeQ
      (let (x, y) =    _val  pair  in    _val  (f (mkVal     x)    (mkVal     y)))
    [||let (x, y) = $$(_code pair) in $$(_code (f (mkCode [||x||]) (mkCode [||y||])))||]