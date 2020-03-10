{-# LANGUAGE PatternSynonyms,
             TemplateHaskell,
             GADTs,
             UndecidableInstances,
             TypeApplications,
             ScopedTypeVariables #-}
module Defunc where
import Utils (WQ(..), Code, Quapplicative(..))
import LiftPlugin (LiftTo, code)

data Defunc q a where
  APP     :: Defunc q ((a -> b) -> a -> b)
  COMPOSE :: Defunc q ((b -> c) -> (a -> b) -> (a -> c))
  FLIP    :: Defunc q ((a -> b -> c) -> b -> a -> c)
  APP_H   :: Defunc q (a -> b) -> Defunc q a -> Defunc q b
  EQ_H    :: Eq a => Defunc q a -> Defunc q (a -> Bool)
  CHAR    :: Char -> Defunc q Char
  ID      :: Defunc q (a -> a)
  CONS    :: Defunc q (a -> [a] -> [a])
  EMPTY   :: Defunc q [a]
  UNIT    :: Defunc q ()
  BLACK   :: q a -> Defunc q a

instance Quapplicative q => Quapplicative (Defunc q) where
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
  _code = genDefunc

pattern COMPOSE_H :: () => ((x -> y -> z) ~ ((b -> c) -> (a -> b) -> a -> c)) => Defunc q x -> Defunc q y -> Defunc q z
pattern COMPOSE_H f g = APP_H (APP_H COMPOSE f) g
pattern FLIP_H :: () => ((x -> y) ~ ((a -> b -> c) -> b -> a -> c)) => Defunc q x -> Defunc q y
pattern FLIP_H f      = APP_H FLIP f

genDefunc :: forall q a. Quapplicative q => Defunc q a -> Code a
genDefunc APP             = [|| \f x -> f x ||]
genDefunc COMPOSE         = [|| \f g x -> f (g x) ||]
genDefunc FLIP            = [|| \f x y -> f y x ||]
genDefunc (COMPOSE_H f g) = [|| \x -> $$(genDefunc1 (COMPOSE_H f g) [||x||]) ||]
genDefunc (FLIP_H f)      = [|| \x -> $$(genDefunc1 (FLIP_H f) [||x||]) ||]
genDefunc (APP_H f x)     = genDefunc2 @q APP (genDefunc f) (genDefunc x)
genDefunc (CHAR c)        = [|| c ||]
genDefunc (EQ_H x)        = [|| \y -> $$(genDefunc x) == y ||]
genDefunc ID              = [|| \x -> x ||]
genDefunc CONS            = [|| \x xs -> x : xs ||]
genDefunc EMPTY           = [|| [] ||]
genDefunc UNIT            = [|| () ||]
genDefunc (BLACK f)       = _code f

genDefunc1 :: Quapplicative q => Defunc q (a -> b) -> Code a -> Code b
genDefunc1 APP             qf = [|| \x -> $$qf x ||]
genDefunc1 COMPOSE         qf = [|| \g x -> $$qf (g x) ||]
genDefunc1 FLIP            qf = [|| \x y -> $$qf y x ||]
genDefunc1 (COMPOSE_H f g) qx = [|| $$(genDefunc1 f (genDefunc1 g qx)) ||]
genDefunc1 (FLIP_H f)      qx = [|| \y -> $$(genDefunc2 (FLIP_H f) qx [||y||]) ||]
genDefunc1 (EQ_H x)        qy = [|| $$qy == $$(genDefunc x) ||]
genDefunc1 ID              qx = qx
genDefunc1 f               qx = [|| $$(genDefunc f) $$qx ||]

genDefunc2 :: Quapplicative q => Defunc q (a -> b -> c) -> Code a -> Code b -> Code c
genDefunc2 APP        qf qx  = [|| $$qf $$qx ||]
genDefunc2 COMPOSE    qf qg  = [|| \x -> $$qf ($$qg x) ||]
genDefunc2 FLIP       qf qx  = [|| \y -> $$qf y $$qx ||]
genDefunc2 (FLIP_H f) qx qy  = genDefunc2 f qy qx
genDefunc2 CONS       qx qxs = [|| $$qx : $$qxs ||]
genDefunc2 f          qx qy  = [|| $$(genDefunc f) $$qx $$qy ||]

instance Show (Defunc a q) where
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