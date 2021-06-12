{-# LANGUAGE TupleSections,
             CPP #-}
module Parsley.Internal.Backend.Machine.LetRecBuilder (letRec) where

import Data.Dependent.Sum                           (DSum((:=>)))
import Data.Functor.Const                           (Const(..))
import Data.GADT.Compare                            (GCompare)
import Data.Some                                    (Some(Some))
import Language.Haskell.TH                          (newName, Name)
#if __GLASGOW_HASKELL__ < 900
import Language.Haskell.TH.Syntax                   (Q, unTypeQ, unsafeTExpCoerce, Exp(VarE, LetE), Dec(FunD), Clause(Clause), Body(NormalB))
#else
import Language.Haskell.TH.Syntax                   (unTypeCode, unsafeCodeCoerce, Exp(VarE, LetE), Dec(FunD), Clause(Clause), Body(NormalB))
#endif
import Parsley.Internal.Backend.Machine.LetBindings (LetBinding(..), Binding, Regs)
import Parsley.Internal.Backend.Machine.State       (QSubRoutine(..), Func)
import Parsley.Internal.Common.Utils                (Code)

import Data.Dependent.Map as DMap (DMap, (!), map, toList, traverseWithKey)

#if __GLASGOW_HASKELL__ < 900
unsafeCodeCoerce :: Q Exp -> Code a
unsafeCodeCoerce = unsafeTExpCoerce
unTypeCode :: Code a -> Q Exp
unTypeCode = unTypeQ
#endif

letRec :: GCompare key => {-bindings-}   DMap key (LetBinding o a)
                       -> {-nameof-}     (forall x. key x -> String)
                       -> {-genBinding-} (forall x rs. Binding o a x -> Regs rs -> DMap key (QSubRoutine s o a) -> Code (Func rs s o a x))
                       -> {-expr-}       (DMap key (QSubRoutine s o a) -> Code b)
                       -> Code b
letRec bindings nameOf genBinding expr = unsafeCodeCoerce $
  do -- Make a bunch of names
     names <- traverseWithKey (\k (LetBinding _ rs) -> Const . (, Some rs) <$> newName (nameOf k)) bindings
     -- Wrap them up so that they are valid typed template haskell names
     let typedNames = DMap.map makeTypedName names
     -- Generate each binding providing them with the names
     let makeDecl (k :=> LetBinding body frees) =
          do let Const (name, _) = names ! k
             func <- unTypeCode (genBinding body frees typedNames)
             return (FunD name [Clause [] (NormalB func) []])
     decls <- traverse makeDecl (toList bindings)
     -- Generate the main expression using the same names
     exp <- unTypeCode (expr typedNames)
     -- Construct the let expression
     return (LetE decls exp)
  where
     makeTypedName :: Const (Name, Some Regs) x -> QSubRoutine s o a x
     makeTypedName (Const (name, Some frees)) = QSubRoutine (unsafeCodeCoerce (return (VarE name))) frees