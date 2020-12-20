{-# LANGUAGE PatternSynonyms #-}
module Parsley.Internal.Core.Defunc (module Parsley.Internal.Core.Defunc) where

import Parsley.Internal.Common.Utils (WQ(..), Code, Quapplicative(..))

data Defunc a where
  APP     :: Defunc ((a -> b) -> a -> b)
  COMPOSE :: Defunc ((b -> c) -> (a -> b) -> (a -> c))
  FLIP    :: Defunc ((a -> b -> c) -> b -> a -> c)
  APP_H   :: Defunc (a -> b) -> Defunc a -> Defunc b
  EQ_H    :: Eq a => Defunc a -> Defunc (a -> Bool)
  CHAR    :: Char -> Defunc Char
  ID      :: Defunc (a -> a)
  CONS    :: Defunc (a -> [a] -> [a])
  CONST   :: Defunc (a -> b -> a)
  EMPTY   :: Defunc [a]
  UNIT    :: Defunc ()
  BLACK   :: WQ a -> Defunc a

instance Quapplicative Defunc where
  makeQ x qx       = BLACK (makeQ x qx)
  _val APP         = ($)
  _val COMPOSE     = (.)
  _val FLIP        = flip
  _val (APP_H f x) = (_val f) (_val x)
  _val (CHAR c)    = c
  _val (EQ_H x)    = ((_val x) ==)
  _val ID          = id
  _val CONS        = (:)
  _val CONST       = const
  _val EMPTY       = []
  _val UNIT        = ()
  _val (BLACK f)   = _val f
  _code = genDefunc

pattern COMPOSE_H :: () => ((x -> y -> z) ~ ((b -> c) -> (a -> b) -> a -> c)) => Defunc x -> Defunc y -> Defunc z
pattern COMPOSE_H f g = APP_H (APP_H COMPOSE f) g
pattern FLIP_H :: () => ((x -> y) ~ ((a -> b -> c) -> b -> a -> c)) => Defunc x -> Defunc y
pattern FLIP_H f      = APP_H FLIP f
pattern FLIP_CONST :: () => (x ~ (a -> b -> b)) => Defunc x
pattern FLIP_CONST    = FLIP_H CONST

ap :: Defunc (a -> b) -> Defunc a -> Defunc b
ap f x = APP_H f x

genDefunc :: Defunc a -> Code a
genDefunc APP             = [|| \f x -> f x ||]
genDefunc COMPOSE         = [|| \f g x -> f (g x) ||]
genDefunc FLIP            = [|| \f x y -> f y x ||]
genDefunc (COMPOSE_H f g) = [|| \x -> $$(genDefunc1 (COMPOSE_H f g) [||x||]) ||]
genDefunc CONST           = [|| \x _ -> x ||]
genDefunc FLIP_CONST      = [|| \_ y -> y ||]
genDefunc (FLIP_H f)      = [|| \x -> $$(genDefunc1 (FLIP_H f) [||x||]) ||]
genDefunc (APP_H f x)     = genDefunc1 f (genDefunc x)
genDefunc (CHAR c)        = [|| c ||]
genDefunc (EQ_H x)        = [|| \y -> $$(genDefunc1 (EQ_H x) [||y||]) ||]
genDefunc ID              = [|| \x -> x ||]
genDefunc CONS            = [|| \x xs -> x : xs ||]
genDefunc EMPTY           = [|| [] ||]
genDefunc UNIT            = [|| () ||]
genDefunc (BLACK f)       = _code f

genDefunc1 :: Defunc (a -> b) -> Code a -> Code b
genDefunc1 APP             qf = [|| \x -> $$qf x ||]
genDefunc1 COMPOSE         qf = [|| \g x -> $$qf (g x) ||]
genDefunc1 FLIP            qf = [|| \x y -> $$qf y x ||]
genDefunc1 (COMPOSE_H f g) qx = genDefunc1 f (genDefunc1 g qx)
genDefunc1 (APP_H APP f)   qx = genDefunc1 f qx
genDefunc1 (APP_H f x)     qy = genDefunc2 f (genDefunc x) qy
genDefunc1 CONST           qx = [|| \_ -> $$qx ||]
genDefunc1 FLIP_CONST      _  = genDefunc ID
genDefunc1 (FLIP_H f)      qx = [|| \y -> $$(genDefunc2 (FLIP_H f) qx [||y||]) ||]
genDefunc1 (EQ_H x)        qy = [|| $$(genDefunc x)  == $$qy ||]
genDefunc1 ID              qx = qx
genDefunc1 f               qx = [|| $$(genDefunc f) $$qx ||]

genDefunc2 :: Defunc (a -> b -> c) -> Code a -> Code b -> Code c
genDefunc2 APP             qf qx  = [|| $$qf $$qx ||]
genDefunc2 COMPOSE         qf qg  = [|| \x -> $$qf ($$qg x) ||]
genDefunc2 FLIP            qf qx  = [|| \y -> $$qf y $$qx ||]
genDefunc2 (COMPOSE_H f g) qx qy  = genDefunc2 f (genDefunc1 g qx) qy
genDefunc2 CONST           qx _   = qx
genDefunc2 FLIP_CONST      _  qy  = qy
genDefunc2 (FLIP_H f)      qx qy  = genDefunc2 f qy qx
genDefunc2 CONS            qx qxs = [|| $$qx : $$qxs ||]
genDefunc2 f               qx qy  = [|| $$(genDefunc f) $$qx $$qy ||]

instance Show (Defunc a) where
  show APP = "($)"
  show COMPOSE = "(.)"
  show FLIP = "flip"
  show (FLIP_H f) = concat ["(flip ", show f, ")"]
  show (COMPOSE_H f g) = concat ["(", show f, " . ", show g, ")"]
  show (APP_H f x) = concat ["(", show f, " ", show x, ")"]
  show (CHAR c) = show c
  show (EQ_H x) = concat ["(== ", show x, ")"]
  show ID  = "id"
  show EMPTY = "[]"
  show CONS = "(:)"
  show CONST = "const"
  show UNIT = "()"
  show _ = "x"