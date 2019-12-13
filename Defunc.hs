{-# LANGUAGE PatternSynonyms,
             TemplateHaskell,
             GADTs #-}
module Defunc where
import Utils (WQ(..), Code)

data Defunc a where
  APP       :: Defunc ((a -> b) -> a -> b)
  COMPOSE   :: Defunc ((b -> c) -> (a -> b) -> (a -> c))
  FLIP      :: Defunc ((a -> b -> c) -> b -> a -> c)
  APP_H     :: Defunc (a -> b) -> Defunc a -> Defunc b
  BLACK     :: WQ a -> Defunc a

pattern COMPOSE_H :: () => ((x -> y -> z) ~ ((b -> c) -> (a -> b) -> a -> c)) => Defunc x -> Defunc y -> Defunc z
pattern COMPOSE_H f g = APP_H (APP_H COMPOSE f) g
pattern FLIP_H :: () => ((x -> y) ~ ((a -> b -> c) -> b -> a -> c)) => Defunc x -> Defunc y
pattern FLIP_H f      = APP_H FLIP f

genDefunc :: Defunc a -> Code a
genDefunc APP             = [|| \f x -> f x ||]
genDefunc COMPOSE         = [|| \f g x -> f (g x) ||]
genDefunc FLIP            = [|| \f x y -> f y x ||]
genDefunc (COMPOSE_H f g) = [|| \x -> $$(genDefunc1 (COMPOSE_H f g) [||x||]) ||]
genDefunc (FLIP_H f)      = [|| \x -> $$(genDefunc1 (FLIP_H f) [||x||]) ||]
genDefunc (APP_H f x)     = genDefunc2 APP (genDefunc f) (genDefunc x)
genDefunc (BLACK f)       = _code f

genDefunc1 :: Defunc (a -> b) -> Code a -> Code b
genDefunc1 APP             qf = [|| \x -> $$qf x ||]
genDefunc1 COMPOSE         qf = [|| \g x -> $$qf (g x) ||]
genDefunc1 FLIP            qf = [|| \x y -> $$qf y x ||]
genDefunc1 (COMPOSE_H f g) qx = [|| $$(genDefunc1 f (genDefunc1 g qx)) ||]
genDefunc1 (FLIP_H f)      qx = [|| \y -> $$(genDefunc2 (FLIP_H f) qx [||y||]) ||]
genDefunc1 f               qx = [|| $$(genDefunc f) $$qx ||]

genDefunc2 :: Defunc (a -> b -> c) -> Code a -> Code b -> Code c
genDefunc2 APP        qf qx = [|| $$qf $$qx ||]
genDefunc2 COMPOSE    qf qg = [|| \x -> $$qf ($$qg x) ||]
genDefunc2 FLIP       qf qx = [|| \y -> $$qf y $$qx ||]
genDefunc2 (FLIP_H f) qx qy = genDefunc2 f qy qx
genDefunc2 f          qx qy = [|| $$(genDefunc f) $$qx $$qy ||]

instance Show (Defunc a) where
  show APP = "($)"
  show COMPOSE = "(.)"
  show FLIP = "flip"
  show (FLIP_H f) = concat ["(flip ", show f, ")"]
  show (COMPOSE_H f g) = concat ["(", show f, " . ", show g, ")"]
  show (APP_H f x) = concat [" ", show f, " ", show x]
  show _ = "x"