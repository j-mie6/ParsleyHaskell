{-# LANGUAGE CPP,
             PatternSynonyms,
             ViewPatterns #-}
module Parsley.Patterns (
    deriveLiftedConstructors, deriveSingletonConstuctors,
    deriveSubtype, deriveSubtypeUsing
  ) where

import Prelude hiding ((<$>), pure, (<*>))

import Data.List     (intercalate, elemIndex)
import Language.Haskell.TH (Name, Q, reify, Info(TyConI, DataConI), Extension(KindSignatures), newName, mkName, isExtEnabled)
import Language.Haskell.TH.Syntax (Type(ConT, AppT, TupleT, ArrowT, ForallT, StarT), Con(NormalC, RecC, GadtC, RecGadtC), Dec(TySynD, NewtypeD, DataD), TyVarBndr(PlainTV, KindedTV), Exp(VarE, AppE), Lift(..))
import Language.Haskell.TH.Lib (varE, varP, conE, conP, conT, forallT, funD, sigD, clause, normalB)
import Parsley (Parser)
import Parsley.Combinator (pos)
import Parsley.Precedence (Subtype(..))
import Parsley.Applicative (pure, (<$>), (<*>), (<**>))

-- Can't use the Lift typeclass for this because GHC 9 added polymorphic code...
liftQ :: Lift a => Q a -> Q Exp
liftQ qe = do
    e <- qe
    [|return $(lift e)|]

{- Builder Generators -}
deriveLiftedConstructors :: String -> [Name] -> Q [Dec]
deriveLiftedConstructors prefix = fmap concat . traverse deriveCon
  where
    deriveCon :: Name -> Q [Dec]
    deriveCon con = do
      DataConI _ ty _ <- reify con
      (forall, tys) <- splitFun ty
      posIdx <- findPosIdx con tys
      let tys' = maybe id deleteAt posIdx tys
      --ty' <- buildType forall (map return tys')
      --fail (show (posIdx, ty'))
      args <- sequence (replicate (length tys' - 1) (newName "x"))
      let posAp = maybe [|id|] (const [|(pos <**>)|]) posIdx
      let con' = mkName (prefix ++ pretty con)
      sequence [ sigD con' (buildType forall (map return tys'))
               , funD con' [clause (map varP args) (normalB [e|$posAp undefined|]) []]
               ]

deleteAt :: Int -> [a] -> [a]
deleteAt 0 (_:xs) = xs
deleteAt n (x:xs) = x : deleteAt (n-1) xs
deleteAt _ []     = []

deriveSingletonConstuctors :: String -> [Name] -> Q [Dec]
deriveSingletonConstuctors prefix cons = undefined

pattern PosTy :: Type
pattern PosTy <- AppT (AppT (TupleT 2) (ConT ((== ''Int) -> True))) (ConT ((== ''Int) -> True))
  where
    PosTy = AppT (AppT (TupleT 2) (ConT ''Int)) (ConT ''Int)

pattern FunTy :: Type -> Type -> Type
pattern FunTy x y = AppT (AppT ArrowT x) y

data PosIdx = Idx Int | Ambiguous | Absent deriving Show
findPosIdx :: Name -> [Type] -> Q (Maybe Int)
findPosIdx con tys = case maybe
  Absent
  (\idx -> if length (filter (== PosTy) tys) > 1 then Ambiguous else Idx idx)
  (elemIndex PosTy tys) of
     Ambiguous -> fail ("constructor " ++ pretty con ++ " has multiple occurrences of (Int, Int)")
     Absent -> return Nothing
     Idx idx -> return (Just idx)

splitFun :: Type -> Q (Q Type -> Q Type, [Type])
splitFun (ForallT bndrs ctx ty) = do
  kindSigs <- isExtEnabled KindSignatures
  let bndrs' = if kindSigs then bndrs else map sanitiseStarT bndrs
  return (forallT bndrs' (return ctx), splitFun' ty)
splitFun ty                     = return (id, splitFun' ty)

splitFun' :: Type -> [Type]
splitFun' (FunTy a b) = a : splitFun' b
splitFun' ty          = [ty]

buildType :: (Q Type -> Q Type) -> [Q Type] -> Q Type
buildType forall tys = forall (foldr (\ty rest -> [t|Parser $ty -> $rest|]) [t|Parser $(last tys)|] (init tys))

-- When KindSignatures is off, the default (a :: *) that TH generates is broken!
#if __GLASGOW_HASKELL__ < 900
sanitiseStarT (KindedTV ty StarT) = PlainTV ty
#else
sanitiseStarT (KindedTV ty flag StarT) = PlainTV ty flag
#endif
sanitiseStarT ty = ty

{- Subtype Generators -}
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