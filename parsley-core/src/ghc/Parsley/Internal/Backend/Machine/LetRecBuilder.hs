{-# LANGUAGE TupleSections,
             CPP #-}
{-|
Module      : Parsley.Internal.Backend.Machine.LetRecBuilder
Description : Function for building recursive groups.
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

Exposes the `letRec` function, used to provide a recursive /group/ of bindings
for the top level of a parser.

@since 1.0.0.0
-}
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
import Parsley.Internal.Backend.Machine.Types       (QSubroutine, qSubroutine, Func)

import Parsley.Internal.Common.Utils                (Code)

import Data.Dependent.Map as DMap (DMap, (!), map, toList, traverseWithKey)

#if __GLASGOW_HASKELL__ < 900
unsafeCodeCoerce :: Q Exp -> Code a
unsafeCodeCoerce = unsafeTExpCoerce
unTypeCode :: Code a -> Q Exp
unTypeCode = unTypeQ
#endif

{-|
Given a collection of bindings, generates a recursive binding group where each is allowed to
refer to every other. These are then in scope for the top-level parser.

@since 1.0.0.0
-}
letRec :: GCompare key 
       => {-bindings-}  DMap key (LetBinding o a)   -- ^ The bindings that should form part of the recursive group
      -> {-nameof-}     (forall x. key x -> String) -- ^ A function which can give a name to a key in the map
      -> {-genBinding-} (forall x rs. key x -> Binding o a x -> Regs rs -> DMap key (QSubroutine s o a) -> Code (Func rs s o a x)) 
      -- ^ How a binding - and their free registers - should be converted into code
      -> {-expr-}       (DMap key (QSubroutine s o a) -> Code b) 
      -- ^ How to produce the top-level binding given the compiled bindings, i.e. the @in@ for the @let@
      -> Code b
letRec bindings nameOf genBinding expr = unsafeCodeCoerce $
  do -- Make a bunch of names
     names <- traverseWithKey (\k (LetBinding _ rs) -> Const . (, rs) <$> newName (nameOf k)) bindings
     -- Wrap them up so that they are valid typed template haskell names
     let typedNames = DMap.map makeTypedName names
     -- Generate each binding providing them with the names
     let makeDecl (k :=> LetBinding body (Some frees)) =
          do let Const (name, _) = names ! k
             func <- unTypeCode (genBinding k body frees typedNames)
             return (FunD name [Clause [] (NormalB func) []])
     decls <- traverse makeDecl (toList bindings)
     -- Generate the main expression using the same names
     exp <- unTypeCode (expr typedNames)
     -- Construct the let expression
     return (LetE decls exp)
  where
     makeTypedName :: Const (Name, Some Regs) x -> QSubroutine s o a x
     makeTypedName (Const (name, Some frees)) = qSubroutine (unsafeCodeCoerce (return (VarE name))) frees