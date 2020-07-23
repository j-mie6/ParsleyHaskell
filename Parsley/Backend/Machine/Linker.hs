{-# LANGUAGE ImplicitParams,
             UnboxedTuples #-}
module Parsley.Backend.Machine.Linker (
    staticLink
  ) where

import Data.Dependent.Map                    (DMap)
import Debug.Trace                           (trace)
import Control.Monad.ST                      (ST, runST)
import Parsley.Backend.Machine.Eval          (eval)
import Parsley.Backend.Machine.Identifiers   (MVar(..))
import Parsley.Backend.Machine.InputOps      (InputDependant(..), InputOps(InputOps))
import Parsley.Backend.Machine.LetBindings   (LetBinding(..))
import Parsley.Backend.Machine.LetRecBuilder (letRec)
import Parsley.Backend.Machine.Ops           (Ops, buildRec, halt, fatal)
import Parsley.Backend.Machine.State         (Γ(..), run, emptyCtx, OpStack(Empty), Handler, Cont)
import Parsley.Common                        (Code, Vec(..))

staticLink :: forall o a. Ops o => (LetBinding o a a, DMap MVar (LetBinding o a)) -> Code (InputDependant o) -> Code (Maybe a)
staticLink (main, subs) input = trace ("STATICALLY LINKING") [|| runST $
  do let !(InputDependant next more offset) = $$input
     $$(link main subs [||next||] [||more||] [||offset||] (halt @o) (fatal @o))
  ||]

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