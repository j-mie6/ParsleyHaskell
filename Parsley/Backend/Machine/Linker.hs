{-# LANGUAGE ImplicitParams,
             MagicHash,
             UnboxedTuples #-}
module Parsley.Backend.Machine.Linker (
    staticLink,
    dynamicLink,
    InputPolymorphic(..)
  ) where

import Data.Dependent.Map                    (DMap)
import Data.List                             (unzip4)
import Data.Text                             (Text)
import Debug.Trace                           (trace)
import Control.Monad                         (forM)
import Control.Monad.ST                      (ST, runST)
import Language.Haskell.TH                   -- TODO Import list...
import Language.Haskell.TH.Syntax            (unTypeQ, unsafeTExpCoerce, lift)
import Parsley.Backend.Machine.Eval          (eval)
import Parsley.Backend.Machine.Identifiers   (MVar(..))
import Parsley.Backend.Machine.InputOps      (InputDependant(..), InputOps(InputOps), BoxOps(box))
import Parsley.Backend.Machine.InputRep      (Stream, UnpackedLazyByteString, OffWith)
import Parsley.Backend.Machine.LetBindings   (LetBinding(..), Binding(..))
import Parsley.Backend.Machine.LetRecBuilder (letRec)
import Parsley.Backend.Machine.Ops           (Ops, buildRec, halt, fatal)
import Parsley.Backend.Machine.State         (Γ(..), run, emptyCtx, OpStack(Empty), Handler, Cont)
import Parsley.Common                        (Code, Vec(..))
import Parsley.Core.Interface                (QParsley(..), Interface)

newtype InputPolymorphic x = InputPolymorphic (forall o. Ops o => (LetBinding o x, DMap MVar (LetBinding o)))
type InternalRepresentation s o x = forall r. Code (o -> (# Char, o #)) -> Code (o -> Bool) -> Code o -> Code (Cont s o r x) -> Code (Handler s o r) -> Code (ST s r)

link :: Ops o => LetBinding o x -> DMap MVar (LetBinding o) -> InternalRepresentation s o x
link (LetBinding (Binding !p) _) fs next more offset ret handle =
  let ?ops = InputOps more next
  in letRec fs
        nameLet
        (\(Binding exp) rs names -> buildRec rs (emptyCtx names) (eval exp))
        (\names -> run (eval p) (Γ Empty ret offset (VCons handle VNil)) (emptyCtx names))
  where
    nameLet :: MVar x -> String
    nameLet (MVar i) = "sub" ++ show i

staticLink :: forall o a. Ops o => (LetBinding o a, DMap MVar (LetBinding o)) -> Code (InputDependant o) -> Code (Maybe a)
staticLink (main, subs) input = trace ("STATICALLY LINKING") [|| runST $
  do let !(InputDependant next more offset) = $$input
     $$(link main subs [||next||] [||more||] [||offset||] (halt @o) (fatal @o))
  ||]

-- TODO more inlineable pragmas?
dynamicLink :: forall x. String -> Q Type -> InputPolymorphic x -> Q [Dec]
dynamicLink loadName qtyX m = trace ("DYNAMICALLY LINKING") $
  do let name = mkName loadName
     clsName <- newName ("Dispatcher_" ++ loadName)
     methodName <- newName (loadName ++ "_Inst")
     tyX <- qtyX
     let methodType = mkSig (return tyX)
     let partials = [ (untypeFunctionQ (linkMono @Int m),                    [t|Int|])
                    , (untypeFunctionQ (linkMono @(OffWith [Char]) m),       [t|OffWith [Char]|])
                    , (untypeFunctionQ (linkMono @(OffWith Stream) m),       [t|OffWith Stream|])
                    , (untypeFunctionQ (linkMono @UnpackedLazyByteString m), [t|UnpackedLazyByteString|])
                    , (untypeFunctionQ (linkMono @Text m),                   [t|Text|])
                    ]
     (quotes, repTys, typeSigs, impls) <- unzip4 <$> forM partials (uncurry (mkConcrete loadName methodType))
     cls <- mkClass clsName methodName methodType
     let insts = map (uncurry (mkInstance clsName methodName)) (zip repTys quotes)
     let mainInlinable = PragmaD (InlineP name Inlinable FunLike AllPhases)
     let mainTy = SigD name (AppT (ConT ''QParsley) tyX)
     mainImpl <- flip (ValD (VarP name)) [] . NormalB <$> [| QParsley . unsafeTExpCoerce $
         do Just parsley <- lookupValueName "Parsley"
            Just name <- lookupValueName $(lift (show methodName))
            return (AppE (ConE parsley) (VarE name))
       |]
     return (concat [typeSigs, impls, [cls, mainInlinable, mainTy, mainImpl], insts])
  where
    linkMono :: forall o s. Ops o => InputPolymorphic x -> InternalRepresentation s o x
    linkMono (InputPolymorphic (main, subs)) = link @o main subs

    untypeFunctionQ :: forall o s. BoxOps o => InternalRepresentation s o x -> Q Exp -> Q Exp -> Q Exp -> Q Exp -> Q Exp -> Q Exp
    untypeFunctionQ f next more offset ret handler = [|
        runST $ $(unTypeQ (f
                    (unsafeTExpCoerce next)
                    (unsafeTExpCoerce more)
                    (unsafeTExpCoerce offset)
                    [||\x o# -> return $ $$ret' x ($$box o#)||]
                    [||\o# -> return $ $$handler' ($$box o#)||]))
      |]
      where
        ret' :: Code (x -> o -> ST s r)
        ret' = unsafeTExpCoerce ret
        handler' :: Code (o -> ST s r)
        handler' = unsafeTExpCoerce handler

    mkSig :: Q Type -> Q Type -> Q Type
    mkSig x o = [t|Interface $o $x|]

    mkClass :: Name -> Name -> (Q Type -> Q Type) -> Q Dec
    mkClass clsName exposedName exposedType =
      do repTy <- newName "rep"
         sigTy <- exposedType (return (VarT repTy))
         let exposedMethod = SigD exposedName sigTy
         return (ClassD [] clsName [PlainTV repTy] [] [exposedMethod])

    mkConcrete :: String -> (Q Type -> Q Type) -> (Q Exp -> Q Exp -> Q Exp -> Q Exp -> Q Exp -> Q Exp) -> Q Type -> Q (Exp, Type, Dec, Dec)
    mkConcrete prefix partialSig qbody repTy =
      do name <- newUniqueName ("_" ++ prefix ++ "_Impl")
         repTy' <- repTy
         sigTy <- partialSig repTy
         next <- newName "next"
         more <- newName "more"
         offset <- newName "offset"
         ret <- newName "good"
         handler <- newName "bad"
         body <- qbody (return (VarE next)) (return (VarE more)) (return (VarE offset)) (return (VarE ret)) (return (VarE handler))
         return (VarE name, repTy', SigD name sigTy, FunD name [Clause [VarP next, VarP more, VarP offset, VarP ret, VarP handler] (NormalB body) []])

    mkInstance :: Name -> Name -> Type -> Exp -> Dec
    mkInstance clsName methodName repTy body = InstanceD Nothing [] (AppT (ConT clsName) repTy) [ValD (VarP methodName) (NormalB body) []]

    newUniqueName :: String -> Q Name
    newUniqueName name = newName name >>= newName . show
