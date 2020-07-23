{-# LANGUAGE ImplicitParams,
             UnboxedTuples #-}
module Parsley.Backend.Machine.Linker (
    staticLink,
    dynamicLink,
    LinkedParser(..),
    InputPolymorphic(..)
  ) where

import Data.Dependent.Map                    (DMap)
import Data.List                             (unzip4)
import Data.Text                             (Text)
import Debug.Trace                           (trace)
import Control.Monad                         (forM)
import Control.Monad.ST                      (ST, runST)
import Language.Haskell.TH                   -- TODO Import list...
import Language.Haskell.TH.Syntax            (unTypeQ, unsafeTExpCoerce)
import Parsley.Backend.Machine.Eval          (eval)
import Parsley.Backend.Machine.Identifiers   (MVar(..))
import Parsley.Backend.Machine.InputOps      (InputDependant(..), InputOps(InputOps))
import Parsley.Backend.Machine.InputRep      (Stream, UnpackedLazyByteString, OffWith)
import Parsley.Backend.Machine.LetBindings   (LetBinding(..))
import Parsley.Backend.Machine.LetRecBuilder (letRec)
import Parsley.Backend.Machine.Ops           (Ops, buildRec, halt, fatal)
import Parsley.Backend.Machine.State         (Γ(..), run, emptyCtx, OpStack(Empty), Handler, Cont)
import Parsley.Common                        (Code, Vec(..))

link :: Ops o => LetBinding o a x -> DMap MVar (LetBinding o a) -> Code (o -> (# Char, o #)) -> Code (o -> Bool) -> Code o -> Code (Cont s o a x) -> Code (Handler s o a) -> Code (ST s (Maybe a))
link (LetBinding !p _) fs next more offset ret handle =
  let ?ops = InputOps more next
  in letRec fs
        nameLet
        (\exp rs names -> buildRec rs (emptyCtx names) (eval exp))
        (\names -> run (eval p) (Γ Empty ret offset (VCons handle VNil)) (emptyCtx names))
  where
    nameLet :: MVar x -> String
    nameLet (MVar i) = "sub" ++ show i

staticLink :: forall o a. Ops o => (LetBinding o a a, DMap MVar (LetBinding o a)) -> Code (InputDependant o) -> Code (Maybe a)
staticLink (main, subs) input = trace ("STATICALLY LINKING") [|| runST $
  do let !(InputDependant next more offset) = $$input
     $$(link main subs [||next||] [||more||] [||offset||] (halt @o) (fatal @o))
  ||]

newtype InputPolymorphic a x = InputPolymorphic (forall o. Ops o => (LetBinding o a x, DMap MVar (LetBinding o a)))
type CallingConvention s o a x = Code (o -> (# Char, o #)) -> Code (o -> Bool) -> Code o -> Code (Cont s o a x) -> Code (Handler s o a) -> Code (ST s (Maybe a))
newtype LinkedParser x = LinkedParser (Q Exp) -- TODO Can we make this better?

dynamicLink :: forall a x. String -> Q Type -> InputPolymorphic a x -> Q [Dec]
dynamicLink loadName qtyX m =
  do let name = mkName loadName
     clsName <- newName ("Dispatcher_" ++ loadName)
     methodName <- newName (loadName ++ "_Inst")
     tyX <- qtyX
     let methodType = mkSig (return tyX)
     let partials = [ (convertLambda (linkMono @Int m),                    [t|Int|])
                    , (convertLambda (linkMono @(OffWith [Char]) m),       [t|OffWith [Char]|])
                    , (convertLambda (linkMono @(OffWith Stream) m),       [t|OffWith Stream|])
                    , (convertLambda (linkMono @UnpackedLazyByteString m), [t|UnpackedLazyByteString|])
                    , (convertLambda (linkMono @Text m),                   [t|Text|])
                    ]
     (quotes, repTys, typeSigs, impls) <- unzip4 <$> forM partials (uncurry (mkConcrete loadName methodType))
     cls <- mkClass clsName methodName methodType
     let insts = map (uncurry (mkInstance clsName methodName)) (zip repTys quotes)
     repTy <- newName "rep"
     let mainInlinable = PragmaD (InlineP name Inlinable FunLike AllPhases)
     let mainTy = SigD name (ForallT [PlainTV repTy] [AppT (ConT clsName) (VarT repTy)] (AppT (ConT ''LinkedParser) tyX))
     mainImpl <- FunD name . pure . flip (Clause []) [] . NormalB <$> [| LinkedParser $
         do Just name <- lookupValueName (loadName ++ "_Inst")
            return (VarE name)
       |]
     return (concat [typeSigs, impls, [cls, mainInlinable, mainTy, mainImpl], insts])
  where
    linkMono :: forall o s. Ops o => InputPolymorphic a x -> CallingConvention s o a x
    linkMono (InputPolymorphic (main, subs)) = link @o main subs

    convertLambda :: forall s o. CallingConvention s o a x -> Q Exp
    convertLambda f = [|\more next offset ret handler ->
        $(unTypeQ (f
          (unsafeTExpCoerce [|more|])
          (unsafeTExpCoerce [|next|])
          (unsafeTExpCoerce [|offset|])
          (unsafeTExpCoerce [|ret|])
          (unsafeTExpCoerce [|handler|])))
      |]

    mkSig :: Q Type -> Q Type -> Q Type -> Q Type -> Q Type
    mkSig x o s a = [t|($o -> (# Char, $o #)) -> ($o -> Bool) -> $o -> Cont $s $o $a $x -> Handler $s $o $a -> ST $s (Maybe $a) |]

    mkClass :: Name -> Name -> (Q Type -> Q Type -> Q Type -> Q Type) -> Q Dec
    mkClass clsName exposedName exposedType =
      do repTy <- newName "rep"
         sigTy <- genAbsType (exposedType (return (VarT repTy)))
         let exposedMethod = SigD exposedName sigTy
         return (ClassD [] clsName [PlainTV repTy] [] [exposedMethod])

    genAbsType :: (Q Type -> Q Type -> Q Type) -> Q Type
    genAbsType partialType =
      do s <- VarT <$> newName "s"
         a <- VarT <$> newName "a"
         partialType (return s) (return a)

    mkConcrete :: String -> (Q Type -> Q Type -> Q Type -> Q Type) -> Q Exp -> Q Type -> Q (Exp, Type, Dec, Dec)
    mkConcrete prefix partialSig qbody repTy =
      do name <- newUniqueName ("_" ++ prefix ++ "_Impl")
         repTy' <- repTy
         sigTy <- genAbsType (partialSig repTy)
         body <- qbody
         return (VarE name, repTy', SigD name sigTy, FunD name [Clause [] (NormalB body) []])

    mkInstance :: Name -> Name -> Type -> Exp -> Dec
    mkInstance clsName methodName repTy body = InstanceD Nothing [] (AppT (ConT clsName) repTy) [FunD methodName [Clause [] (NormalB body) []]]

    newUniqueName :: String -> Q Name
    newUniqueName name = newName name >>= newName . show
