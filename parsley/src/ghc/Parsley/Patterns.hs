module Parsley.Patterns (
    deriveSubtype, deriveSubtypeUsing
  ) where

import Data.List     (intercalate)
import Language.Haskell.TH (Name, Q, reify, Info(TyConI), varE, varP, conE, conP, conT, newName)
import Language.Haskell.TH.Syntax (Type(ConT), Con(NormalC, RecC, GadtC, RecGadtC), Dec(TySynD, NewtypeD, DataD))
import Parsley.Precedence (Subtype(..))

-- Builder Generators

-- Subtype Generators
deriveSubtype :: Name -> Name -> Q [Dec]
deriveSubtype sub sup = determineWrap sub sup >>= deriveSubtypeUsing sub sup

data WrapCon = Single Name | Missing | Duplicates [Name]

determineWrap :: Name -> Name -> Q Name
determineWrap sub sup = do
  TyConI subDec <- reify sup
  case subDec of
    DataD _ _ _ _ cons _ -> findRightCon cons
    NewtypeD _ _ _ _ con _ -> findRightCon [con]
    TySynD {} -> fail ("type synonym " ++ show sup ++ " cannot be used for Subtype deriving")
    _         -> fail "Subtype derivation only works for data and newtype"
  where
    findRightCon :: [Con] -> Q Name
    findRightCon = getWrappedCon . foldr testCon Missing

    testCon :: Con -> WrapCon -> WrapCon
    testCon (NormalC con [(_, ConT ty)])
      | ty == sub = addWrappedCon con
    testCon (RecC con [(_, _, ConT ty)])
      | ty == sub = addWrappedCon con
    testCon (GadtC [con] [(_, ConT ty)] (ConT ty'))
      | ty == sub, ty' == sup = addWrappedCon con
    testCon (RecGadtC [con] [(_, _, ConT ty)] (ConT ty'))
      | ty == sub, ty' == sup = addWrappedCon con
    testCon _ = id

    addWrappedCon :: Name -> WrapCon -> WrapCon
    addWrappedCon con Missing = Single con
    addWrappedCon con (Single con') = Duplicates [con, con']
    addWrappedCon con (Duplicates cons) = Duplicates (con : cons)

    getWrappedCon :: WrapCon -> Q Name
    getWrappedCon Missing = fail missingConstructor
    getWrappedCon (Duplicates cons) = fail (tooManyConstructors cons)
    getWrappedCon (Single con) = return con

    missingConstructor =
      "type " ++ show sup ++ " does not have a constructor Con :: " ++ pretty sub ++ " -> " ++ pretty sup
    tooManyConstructors cons =
      "type " ++ show sup ++ " has conflicting constructors that could wrap " ++ show sub ++
      " namely " ++ conjunct cons
    conjunct [con1, con2] = pretty con1 ++ " and " ++ pretty con2
    conjunct others =
      intercalate ", " (map pretty (init others)) ++ ", and " ++ pretty (last others)
    pretty :: Name -> String
    pretty = reverse . takeWhile (/= '.') . reverse . show

deriveSubtypeUsing :: Name -> Name -> Name -> Q [Dec]
deriveSubtypeUsing sub sup wrap = do
  x <- newName "x"
  [d|
    instance Subtype $(conT sub) $(conT sup) where
      upcast = $(conE wrap)
      downcast $(conP wrap [varP x]) = Just $(varE x)
      downcast _ = Nothing |]