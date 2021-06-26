{-# LANGUAGE CPP,
             PatternSynonyms,
             ViewPatterns #-}
module Parsley.Patterns (
    Pos,
    deriveLiftedConstructors, deriveSingletonConstructors,
    deriveSubtype, deriveSubtypeUsing
  ) where

import Prelude hiding (pure, (<*>))

import Data.List     (intercalate, elemIndex)
import Language.Haskell.TH (Name, Q, reify, Info(TyConI, DataConI), Extension(KindSignatures), newName, mkName, isExtEnabled)
import Language.Haskell.TH.Syntax (Type(ConT, AppT, ArrowT, ForallT, StarT),
                                   Con(NormalC, RecC, GadtC, RecGadtC),
                                   Dec(TySynD, NewtypeD, DataD),
                                   TyVarBndr(PlainTV, KindedTV),
                                   Exp(VarE, AppE, ConE, LamE),
                                   Pat(VarP),
                                   Name(Name), OccName(OccName), NameFlavour(NameU, NameQ, NameG),
                                   ModName(ModName), NameSpace(DataName), PkgName(PkgName),
                                   Lift(lift))
#if __GLASGOW_HASKELL__ >= 900
import Language.Haskell.TH.Syntax (Type(MulArrowT), unsafeCodeCoerce)
#else
import Language.Haskell.TH.Syntax (unsafeTExpCoerce)
#endif
import Language.Haskell.TH.Lib (varE, varP, conE, conP, conT, forallT, funD, sigD, clause, normalB, lamE)
import Parsley (Parser, makeQ)
import Parsley.Combinator (pos)
import Parsley.Precedence (Subtype(..))
import Parsley.Applicative (pure, (<*>), (<**>))

type Pos = (Int, Int)

{- Builder Generators -}
deriveLiftedConstructors :: String -> [Name] -> Q [Dec]
deriveLiftedConstructors prefix = fmap concat . traverse deriveCon
  where
    deriveCon :: Name -> Q [Dec]
    deriveCon con = do
      (con', tys', func, posIdx, nargs, forall) <- buildMeta True prefix con
      args <- sequence (replicate nargs (newName "x"))
      let posAp = maybe [e|id|] (const [e|(pos <**>)|]) posIdx
      sequence [ sigD con' (buildType forall (map return tys'))
               , funD con' [clause (map varP args) (normalB [e|$posAp $(applyArgs [|pure $func|] (map varE args)) |]) []]
               ]

    applyArgs :: Q Exp -> [Q Exp] -> Q Exp
    applyArgs rest [] = rest
    applyArgs rest (arg:args) = applyArgs [e|$rest <*> $arg|] args

    buildType :: (Q Type -> Q Type) -> [Q Type] -> Q Type
    buildType forall tys = forall (foldr (\ty rest -> [t|Parser $ty -> $rest|]) [t|Parser $(last tys)|] (init tys))

deriveSingletonConstructors :: String -> [Name] -> Q [Dec]
deriveSingletonConstructors prefix = fmap concat . traverse deriveCon
  where
    deriveCon :: Name -> Q [Dec]
    deriveCon con = do
      (con', tys', func, posIdx, _, forall) <- buildMeta False prefix con
      let posAp = maybe [e|id|] (const [e|(<*> pos)|]) posIdx
      sequence [ sigD con' (buildType forall (map return tys'))
               , funD con' [clause [] (normalB [e|$posAp (pure $func)|]) []]
               ]

    buildType :: (Q Type -> Q Type) -> [Q Type] -> Q Type
    buildType forall tys = forall [t|Parser $(foldr1 (\ty rest -> [t| $ty -> $rest |]) tys)|]

buildMeta :: Bool -> String -> Name -> Q (Name, [Type], Q Exp, Maybe Int, Int, Q Type -> Q Type)
buildMeta posLast prefix con = do
  DataConI _ ty _ <- reify con
  (forall, tys) <- splitFun ty
  posIdx <- findPosIdx con tys
  let tys' = maybe id deleteAt posIdx tys
  let nargs = length tys' - 1
  let con' = mkName (prefix ++ pretty con)
  let func = buildLiftedLambda posLast con nargs posIdx
  return (con', tys', func, posIdx, nargs, forall)

buildLiftedLambda :: Bool -> Name -> Int -> Maybe Int -> Q Exp
buildLiftedLambda posLast con nargs posIdx = do
  args <- sequence (replicate nargs (newName "x"))
  posArg <- newName "pos"
  let args' = map varP args
  let posArg' = maybe [] (const [varP posArg]) posIdx
  let lam = lamE
        (if posLast then args' ++ posArg' else posArg' ++ args')
        (applyArgs (conE con) (varE posArg) (map varE args) posIdx)
#if __GLASGOW_HASKELL__ >= 900
  [e|makeQ $lam (unsafeCodeCoerce $(liftQ lam))|]
#else
  [e|makeQ $lam (unsafeTExpCoerce $(liftQ lam))|]
#endif
  where
    applyArgs :: Q Exp -> Q Exp -> [Q Exp] -> Maybe Int -> Q Exp
    applyArgs acc posArg args (Just 0) = applyArgs [e|$acc $posArg|] posArg args Nothing
    applyArgs acc _ [] _ = acc
    applyArgs acc posArg (arg:args) idx = applyArgs [e|$acc $arg|] posArg args (fmap pred idx)

deleteAt :: Int -> [a] -> [a]
deleteAt 0 (_:xs) = xs
deleteAt n (x:xs) = x : deleteAt (n-1) xs
deleteAt _ []     = []

pattern PosTy :: Type
pattern PosTy <- ConT ((== ''Pos) -> True)
  where
    PosTy = ConT ''Pos

pattern FunTy :: Type -> Type -> Type
pattern FunTy x y = AppT (AppT ArrowT x) y

#if __GLASGOW_HASKELL__ >= 900
pattern LinearFunTy :: Type -> Type -> Type
pattern LinearFunTy x y <- AppT (AppT (AppT MulArrowT _) x) y
#endif

data PosIdx = Idx Int | Ambiguous | Absent
findPosIdx :: Name -> [Type] -> Q (Maybe Int)
findPosIdx con tys = case maybe
  Absent
  (\idx -> if length (filter (== PosTy) tys) > 1 then Ambiguous else Idx idx)
  (elemIndex PosTy tys) of
     Ambiguous -> fail ("constructor " ++ pretty con ++ " has multiple occurrences of Parsley.Pattern.Pos")
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
#if __GLASGOW_HASKELL__ >= 900
splitFun' (LinearFunTy a b) = a : splitFun' b
#endif
splitFun' ty          = [ty]

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

-- Template Haskell Madness :(
-- Can't use the Lift typeclass for this because GHC 9 added polymorphic code...
liftQ :: Q Exp -> Q Exp
liftQ qe = do
    e <- qe
    [|return $(liftOurExp e)|]

-- These release us from having to orphan a bunch of Lift instances (and reduces compile time)
-- We should only need these constructors to do our work :)

liftOurExp :: Exp -> Q Exp
liftOurExp (VarE name) = [e|VarE $(liftOurName name)|]
liftOurExp (ConE name) = [e|ConE $(liftOurName name)|]
liftOurExp (AppE e1 e2) = [e|AppE $(liftOurExp e1) $(liftOurExp e2)|]
liftOurExp (LamE args body) = [e|LamE $(liftOurArgs args) $(liftOurExp body)|]
liftOurExp _ = error "well these aren't meant to exist..."

liftOurName :: Name -> Q Exp
liftOurName (Name (OccName v) (NameU x)) = [e|Name (OccName $(lift v)) (NameU $(lift x))|]
liftOurName (Name (OccName v) (NameQ (ModName mod))) = [e|Name (OccName $(lift v)) (NameQ (ModName $(lift mod)))|]
liftOurName (Name (OccName v) (NameG DataName (PkgName pkg) (ModName mod))) = [e|Name (OccName $(lift v)) (NameG DataName (PkgName $(lift pkg)) (ModName $(lift mod)))|]
liftOurName _ = error "well these aren't meant to exist..."

liftOurVarP :: Pat -> Q Exp
liftOurVarP (VarP name) = [e|VarP $(liftOurName name)|]
liftOurVarP _ = error "well these aren't meant to exist..."

liftOurArgs :: [Pat] -> Q Exp
liftOurArgs [] = [e|[]|]
liftOurArgs (p:ps) = [e|$(liftOurVarP p) : $(liftOurArgs ps)|]