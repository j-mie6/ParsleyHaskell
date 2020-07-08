{-# LANGUAGE RankNTypes, TemplateHaskell #-}
module Parsley.Backend.Machine.LetRecBuilder where

import Parsley.Common.Utils       (Code)
import Data.Dependent.Map         (DMap, DSum(..))
import Data.GADT.Compare          (GCompare)
import Language.Haskell.TH        (runQ, Q, newName, Name)
import Language.Haskell.TH.Syntax (unTypeQ, unsafeTExpCoerce, Exp(VarE, LetE), Dec(FunD), Clause(Clause), Body(NormalB))
import Data.Functor.Const         (Const(..), getConst)
import Data.Dependent.Map as DMap ((!), map, toList, traverseWithKey)

letRec :: GCompare key => {-bindings-}   DMap key named
                       -> {-nameof-}     (forall a. key a -> named a -> String)
                       -> {-wrap-}       (forall x. Code ((x -> y) -> z) -> q x)
                       -> {-genBinding-} (forall x. named x -> DMap key q -> Code ((x -> y) -> z))
                       -> {-expr-}       (DMap key q -> Code a)
                       -> Code a
letRec bindings nameOf wrap genBinding expr = unsafeTExpCoerce $
  do -- Make a bunch of names
     names <- traverseWithKey (\k v -> Const <$> newName (nameOf k v)) bindings
     -- Wrap them up so that they are valid typed template haskell names
     let typedNames = DMap.map (wrap . unsafeTExpCoerce . return . VarE . getConst) names
     -- Generate each binding providing them with the names
     let makeDecl (k :=> v) =
          do let Const name = names ! k
             body <- unTypeQ (genBinding v typedNames)
             return (FunD name [Clause [] (NormalB body) []])
     decls <- traverse makeDecl (toList bindings)
     -- Generate the main expression using the same names
     exp <- unTypeQ (expr typedNames)
     -- Construct the let expression
     return (LetE decls exp)