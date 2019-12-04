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
genDefunc APP             = [|| ($) ||]
genDefunc COMPOSE         = [|| (.) ||]
genDefunc FLIP            = [|| flip ||]
genDefunc (COMPOSE_H f g) = genDefunc2 COMPOSE (genDefunc f) (genDefunc g)
genDefunc (FLIP_H f)      = [|| \x y -> $$(genDefunc f) y x ||]
genDefunc (APP_H f x)     = genDefunc2 APP (genDefunc f) (genDefunc x)
genDefunc (BLACK f)       = _code f

genDefunc2 :: Defunc (x -> y -> z) -> Code x -> Code y -> Code z
genDefunc2 APP qf qx        = [|| $$qf $$qx ||]
genDefunc2 COMPOSE qf qg    = [|| \x -> $$qf ($$qg x) ||]
genDefunc2 FLIP qf qx       = [|| \y -> $$qf y $$qx ||]
genDefunc2 (FLIP_H f) qx qy = genDefunc2 f qy qx
genDefunc2 f qx qy          = [|| $$(genDefunc f) $$qx $$qy ||]

instance Show (Defunc a) where
  show APP = "($)"
  show COMPOSE = "(.)"
  show FLIP = "flip"
  show (FLIP_H f) = concat ["(flip ", show f, ")"]
  show (COMPOSE_H f g) = concat ["(", show f, " . ", show g, ")"]
  show (APP_H f x) = concat [" ", show f, " ", show x]
  show _ = "x"