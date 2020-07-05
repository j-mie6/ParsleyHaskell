{-# LANGUAGE PatternSynonyms,
             TemplateHaskell,
             GADTs,
             UndecidableInstances,
             TypeApplications,
             ScopedTypeVariables #-}
module Defunc where

import Utils (WQ(..), Code, Quapplicative(..))
import Input (PositionOps(same))

data DefuncUser q a where
  APP     :: DefuncUser q ((a -> b) -> a -> b)
  COMPOSE :: DefuncUser q ((b -> c) -> (a -> b) -> (a -> c))
  FLIP    :: DefuncUser q ((a -> b -> c) -> b -> a -> c)
  APP_H   :: DefuncUser q (a -> b) -> DefuncUser q a -> DefuncUser q b
  EQ_H    :: Eq a => DefuncUser q a -> DefuncUser q (a -> Bool)
  CHAR    :: Char -> DefuncUser q Char
  ID      :: DefuncUser q (a -> a)
  CONS    :: DefuncUser q (a -> [a] -> [a])
  EMPTY   :: DefuncUser q [a]
  UNIT    :: DefuncUser q ()
  BLACK   :: q a -> DefuncUser q a

instance Quapplicative q => Quapplicative (DefuncUser q) where
  makeQ x qx       = BLACK (makeQ x qx)
  _val APP         = ($)
  _val COMPOSE     = (.)
  _val FLIP        = flip
  _val (APP_H f x) = (_val f) (_val x)
  _val (CHAR c)    = c
  _val (EQ_H x)    = (== (_val x))
  _val ID          = id
  _val CONS        = (:)
  _val EMPTY       = []
  _val UNIT        = ()
  _val (BLACK f)   = _val f
  _code = genDefuncUser

data Defunc q o a where
  USER :: DefuncUser q a -> Defunc q o a
  SAME :: Defunc q o (o -> o -> Bool)

pattern COMPOSE_H :: () => ((x -> y -> z) ~ ((b -> c) -> (a -> b) -> a -> c)) => DefuncUser q x -> DefuncUser q y -> DefuncUser q z
pattern COMPOSE_H f g = APP_H (APP_H COMPOSE f) g
pattern FLIP_H :: () => ((x -> y) ~ ((a -> b -> c) -> b -> a -> c)) => DefuncUser q x -> DefuncUser q y
pattern FLIP_H f      = APP_H FLIP f

genDefuncUser :: forall q a. Quapplicative q => DefuncUser q a -> Code a
genDefuncUser APP             = [|| \f x -> f x ||]
genDefuncUser COMPOSE         = [|| \f g x -> f (g x) ||]
genDefuncUser FLIP            = [|| \f x y -> f y x ||]
genDefuncUser (COMPOSE_H f g) = [|| \x -> $$(genDefuncUser1 (COMPOSE_H f g) [||x||]) ||]
genDefuncUser (FLIP_H f)      = [|| \x -> $$(genDefuncUser1 (FLIP_H f) [||x||]) ||]
genDefuncUser (APP_H f x)     = genDefuncUser2 @q APP (genDefuncUser f) (genDefuncUser x)
genDefuncUser (CHAR c)        = [|| c ||]
genDefuncUser (EQ_H x)        = [|| \y -> $$(genDefuncUser x) == y ||]
genDefuncUser ID              = [|| \x -> x ||]
genDefuncUser CONS            = [|| \x xs -> x : xs ||]
genDefuncUser EMPTY           = [|| [] ||]
genDefuncUser UNIT            = [|| () ||]
genDefuncUser (BLACK f)       = _code f

genDefuncUser1 :: Quapplicative q => DefuncUser q (a -> b) -> Code a -> Code b
genDefuncUser1 APP             qf = [|| \x -> $$qf x ||]
genDefuncUser1 COMPOSE         qf = [|| \g x -> $$qf (g x) ||]
genDefuncUser1 FLIP            qf = [|| \x y -> $$qf y x ||]
genDefuncUser1 (COMPOSE_H f g) qx = [|| $$(genDefuncUser1 f (genDefuncUser1 g qx)) ||]
genDefuncUser1 (FLIP_H f)      qx = [|| \y -> $$(genDefuncUser2 (FLIP_H f) qx [||y||]) ||]
genDefuncUser1 (EQ_H x)        qy = [|| $$qy == $$(genDefuncUser x) ||]
genDefuncUser1 ID              qx = qx
genDefuncUser1 f               qx = [|| $$(genDefuncUser f) $$qx ||]

genDefuncUser2 :: Quapplicative q => DefuncUser q (a -> b -> c) -> Code a -> Code b -> Code c
genDefuncUser2 APP        qf qx  = [|| $$qf $$qx ||]
genDefuncUser2 COMPOSE    qf qg  = [|| \x -> $$qf ($$qg x) ||]
genDefuncUser2 FLIP       qf qx  = [|| \y -> $$qf y $$qx ||]
genDefuncUser2 (FLIP_H f) qx qy  = genDefuncUser2 f qy qx
genDefuncUser2 CONS       qx qxs = [|| $$qx : $$qxs ||]
genDefuncUser2 f          qx qy  = [|| $$(genDefuncUser f) $$qx $$qy ||]

genDefunc :: (PositionOps o, Quapplicative q) => Defunc q o a -> Code a
genDefunc (USER x) = genDefuncUser x
genDefunc SAME     = same

genDefunc1 :: (PositionOps o, Quapplicative q) => Defunc q o (a -> b) -> Code a -> Code b
genDefunc1 (USER f) qx = genDefuncUser1 f qx
genDefunc1 f qx        = [|| $$(genDefunc f) $$qx ||]

genDefunc2 :: (PositionOps o, Quapplicative q) => Defunc q o (a -> b -> c) -> Code a -> Code b -> Code c
genDefunc2 (USER f) qx qy = genDefuncUser2 f qx qy
genDefunc2 f qx qy        = [|| $$(genDefunc f) $$qx $$qy ||]

instance Show (DefuncUser q a) where
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
  show UNIT = "()"
  show _ = "x"

instance Show (Defunc q o a) where
  show (USER x) = show x
  show SAME = "same"