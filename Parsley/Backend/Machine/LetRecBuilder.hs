module Parsley.Backend.Machine.LetRecBuilder (letRec) where

import Data.Dependent.Sum                  (DSum((:=>)))
import Data.Functor.Const                  (Const(..))
import Data.GADT.Compare                   (GCompare)
import Data.Some                           (Some(Some))
import Language.Haskell.TH                 (newName, Name)
import Language.Haskell.TH.Syntax          (unTypeQ, unsafeTExpCoerce, Exp(VarE, LetE), Dec(ValD), Pat(VarP), Body(NormalB))
import Parsley.Backend.Machine.LetBindings (LetBinding(..), Binding, Regs)
import Parsley.Backend.Machine.State       (QSubRoutine(..), Func)
import Parsley.Common.Utils                (Code)

import Data.Dependent.Map as DMap (DMap, (!), map, toList, traverseWithKey)

letRec :: GCompare key => {-bindings-}   DMap key (LetBinding o)
                       -> {-nameof-}     (forall x. key x -> String)
                       -> {-genBinding-} (forall x rs. Binding o x -> Regs rs -> DMap key (QSubRoutine s o r) -> Code (Func rs s o r x))
                       -> {-expr-}       (DMap key (QSubRoutine s o r) -> Code b)
                       -> Code b
letRec bindings nameOf genBinding expr = unsafeTExpCoerce $
  do -- Make a bunch of names
     names <- traverseWithKey (\k (LetBinding _ rs) -> Const . (, Some rs) <$> newName (nameOf k)) bindings
     -- Wrap them up so that they are valid typed template haskell names
     let typedNames = DMap.map makeTypedName names
     -- Generate each binding providing them with the names
     let makeDecl (k :=> LetBinding body frees) =
          do let Const (name, _) = names ! k
             func <- unTypeQ (genBinding body frees typedNames)
             return (ValD (VarP name) (NormalB func) [])
     decls <- traverse makeDecl (toList bindings)
     -- Generate the main expression using the same names
     exp <- unTypeQ (expr typedNames)
     -- Construct the let expression
     return (if null decls then exp else LetE decls exp)
  where
     makeTypedName :: Const (Name, Some Regs) x -> QSubRoutine s o r x
     makeTypedName (Const (name, Some frees)) = QSubRoutine (unsafeTExpCoerce (return (VarE name))) frees