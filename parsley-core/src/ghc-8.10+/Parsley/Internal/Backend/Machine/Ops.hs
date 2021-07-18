{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
{-# LANGUAGE AllowAmbiguousTypes,
             ConstrainedClassMethods,
             ConstraintKinds,
             ImplicitParams,
             MagicHash,
             NamedFieldPuns,
             PatternSynonyms,
             RecordWildCards,
             TypeApplications #-}
module Parsley.Internal.Backend.Machine.Ops (
    module Parsley.Internal.Backend.Machine.Ops,
    HandlerOps, JoinBuilder, RecBuilder, PositionOps, MarshalOps, LogOps
  ) where

import Control.Monad                                   (liftM2)
import Control.Monad.Reader                            (ask, local)
import Control.Monad.ST                                (ST)
import Data.STRef                                      (writeSTRef, readSTRef, newSTRef)
import Data.Void                                       (Void)
import Debug.Trace                                     (trace)
import GHC.Exts                                        (Int(..), (-#))
import Language.Haskell.TH.Syntax                      (liftTyped)
import Parsley.Internal.Backend.Machine.BindingOps
import Parsley.Internal.Backend.Machine.Defunc         (Defunc(OFFSET), genDefunc, _if, pattern FREEVAR)
import Parsley.Internal.Backend.Machine.Identifiers    (MVar, ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.InputOps       (PositionOps(..), LogOps(..), InputOps, next, more)
import Parsley.Internal.Backend.Machine.InputRep       (Rep)
import Parsley.Internal.Backend.Machine.Instructions   (Access(..))
import Parsley.Internal.Backend.Machine.LetBindings    (Regs(..))
import Parsley.Internal.Backend.Machine.Types          (MachineMonad, Machine(..), run)
import Parsley.Internal.Backend.Machine.Types.Context
import Parsley.Internal.Backend.Machine.Types.Dynamics (DynFunc, DynCont, DynHandler)
import Parsley.Internal.Backend.Machine.Types.Offset   (Offset(..), moveOne, mkOffset)
import Parsley.Internal.Backend.Machine.Types.State    (Γ(..), OpStack(..))
import Parsley.Internal.Backend.Machine.Types.Statics
import Parsley.Internal.Common                         (One, Code, Vec(..), Nat(..))
import System.Console.Pretty                           (color, Color(Green, White, Red, Blue))


type Ops o = (HandlerOps o, JoinBuilder o, RecBuilder o, PositionOps (Rep o), MarshalOps o, LogOps (Rep o))
type StaHandlerBuilder s o a = Offset o -> StaHandler s o a

{- Input Operations -}
sat :: (?ops :: InputOps (Rep o)) => (Defunc Char -> Defunc Bool) -> (Γ s o (Char : xs) n r a -> Code b) -> Code b -> Γ s o xs n r a -> Code b
sat p k bad γ@Γ{..} = next (offset input) $ \c offset' -> let v = FREEVAR c in _if (p v) (k (γ {operands = Op v operands, input = moveOne input offset'})) bad

emitLengthCheck :: forall s o xs n r a b. (?ops :: InputOps (Rep o), PositionOps (Rep o)) => Int -> (Γ s o xs n r a -> Code b) -> Code b -> Γ s o xs n r a -> Code b
emitLengthCheck 0 good _ γ   = good γ
emitLengthCheck 1 good bad γ = [|| if $$more $$(offset (input γ)) then $$(good γ) else $$bad ||]
emitLengthCheck (I# n) good bad γ = [||
  if $$more $$(shiftRight (offset (input γ)) (liftTyped (n -# 1#))) then $$(good γ)
  else $$bad ||]

{- General Operations -}
dup :: Defunc x -> (Defunc x -> Code r) -> Code r
dup (FREEVAR x) k = k (FREEVAR x)
dup (OFFSET o) k = k (OFFSET o)
dup x k = [|| let !dupx = $$(genDefunc x) in $$(k (FREEVAR [||dupx||])) ||]

{-# INLINE returnST #-}
returnST :: forall s a. a -> ST s a
returnST = return @(ST s)

{- Register Operations -}
newΣ :: ΣVar x -> Access -> Defunc x -> (Ctx s o a -> Code (ST s r)) -> Ctx s o a -> Code (ST s r)
newΣ σ Soft x k ctx = dup x $ \dupx -> k (insertNewΣ σ Nothing dupx ctx)
newΣ σ Hard x k ctx = dup x $ \dupx -> [||
    do ref <- newSTRef $$(genDefunc dupx)
       $$(k (insertNewΣ σ (Just [||ref||]) dupx ctx))
  ||]

writeΣ :: ΣVar x -> Access -> Defunc x -> (Ctx s o a -> Code (ST s r)) -> Ctx s o a -> Code (ST s r)
writeΣ σ Soft x k ctx = dup x $ \dupx -> k (cacheΣ σ dupx ctx)
writeΣ σ Hard x k ctx = let ref = concreteΣ σ ctx in dup x $ \dupx -> [||
    do writeSTRef $$ref $$(genDefunc dupx)
       $$(k (cacheΣ σ dupx ctx))
  ||]

readΣ :: ΣVar x -> Access -> (Defunc x -> Ctx s o a -> Code (ST s r)) -> Ctx s o a -> Code (ST s r)
readΣ σ Soft k ctx = k (cachedΣ σ ctx) ctx
readΣ σ Hard k ctx = let ref = concreteΣ σ ctx in [||
    do x <- readSTRef $$ref
       $$(let fv = FREEVAR [||x||] in k fv (cacheΣ σ fv ctx))
  ||]

{- Handler Operations -}
buildHandler :: Γ s o xs n r a
             -> (Γ s o (o : xs) n r a -> Code (ST s (Maybe a)))
             -> Word
             -> StaHandlerBuilder s o a
buildHandler γ h u c = mkStaHandler c $ \o# -> h (γ {operands = Op (OFFSET c) (operands γ), input = mkOffset o# u})

buildYesHandler :: Γ s o xs n r a
                -> (Γ s o xs n r a -> Code (ST s (Maybe a)))
                -> Word
                -> StaHandler s o a
buildYesHandler γ h u = staHandlerUnknown $ \o# -> h (γ {input = mkOffset o# u})

fatal :: StaHandler s o a
fatal = staHandlerUnknown (const [|| returnST Nothing ||])

bindAlwaysHandler :: HandlerOps o => Γ s o xs n r a
                  -> StaHandlerBuilder s o a
                  -> (Γ s o xs (Succ n) r a -> Code b) -> Code b
bindAlwaysHandler γ h k = bindHandler# (h (input γ)) $ \qh ->
  k (γ {handlers = VCons (staHandler (Just (input γ)) qh) (handlers γ)})

bindSameHandler :: (HandlerOps o, PositionOps (Rep o)) => Γ s o xs n r a
                -> StaHandler s o a
                -> StaHandlerBuilder s o a
                -> (Γ s o xs (Succ n) r a -> Code b)
                -> Code b
bindSameHandler γ yes no k = [||
    let yesSame = $$(staHandler# yes (offset (input γ)))
    in $$(bindHandler# (no (input γ)) $ \qno ->
            let handler = mkStaHandler (input γ) $ \o ->
                  [||if $$(same (offset (input γ)) o) then yesSame else $$qno $$o||]
            in bindHandler# handler $ \qhandler ->
                k (γ {handlers = VCons (staHandlerFull (Just (input γ)) qhandler [||yesSame||] qno) (handlers γ)}))
  ||]

raise :: Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))
raise γ = let VCons h _ = handlers γ in staHandlerEval h (input γ)

{- Control Flow Operations -}
suspend :: (Γ s o (x : xs) n r a -> Code (ST s (Maybe a))) -> Γ s o xs n r a -> Word -> StaCont s o a x
suspend m γ u = mkStaCont $ \x o# -> m (γ {operands = Op (FREEVAR x) (operands γ), input = mkOffset o# u})

halt :: StaCont s o a a
halt = mkStaCont $ \x _ -> [||returnST (Just $$x)||]

noreturn :: StaCont s o a Void
noreturn = mkStaCont $ \_ _ -> [||error "Return is not permitted here"||]

callWithContinuation :: MarshalOps o => StaSubRoutine s o a x -> StaCont s o a x -> Code (Rep o) -> Vec (Succ n) (StaHandler s o a) -> Code (ST s (Maybe a))
callWithContinuation sub ret input (VCons h _) = sub (dynCont ret) input (dynHandler h)

resume :: StaCont s o a x -> Γ s o (x : xs) n r a -> Code (ST s (Maybe a))
resume k γ = let Op x _ = operands γ in staCont# k (genDefunc x) (offset (input γ))

{- Builder Operations -}
setupJoinPoint :: forall s o xs n r a x. JoinBuilder o => ΦVar x -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a
setupJoinPoint φ (Machine k) mx = freshUnique $ \u ->
    liftM2 (\mk ctx γ ->
      setupJoinPoint# @o
        (\qx qo# -> mk (γ {operands = Op (FREEVAR qx) (operands γ), input = mkOffset qo# u}))
        (\qjoin -> run mx γ (insertΦ φ (staCont qjoin) ctx)))
      (local voidCoins k) ask

buildIterAlways :: forall s o a. RecBuilder o => Ctx s o a -> MVar Void -> Machine s o '[] One Void a
                -> StaHandlerBuilder s o a -> Offset o -> Word -> Code (ST s (Maybe a))
buildIterAlways ctx μ l h o u =
  bindIterHandler# @o (\qc# -> staHandler# (h (mkOffset qc# u))) $ \qhandler ->
    buildIter# @o (offset o) $ \qloop qo# ->
      let off = mkOffset qo# u
      in run l (Γ Empty noreturn off (VCons (staHandler (Just off) [||$$qhandler $$(qo#)||]) VNil))
                (voidCoins (insertSub μ (\_ o# _ -> [|| $$qloop $$(o#) ||]) ctx))

buildIterSame :: forall s o a. (RecBuilder o, HandlerOps o, PositionOps (Rep o)) => Ctx s o a -> MVar Void -> Machine s o '[] One Void a
                -> StaHandler s o a -> StaHandlerBuilder s o a -> Offset o -> Word -> Code (ST s (Maybe a))
buildIterSame ctx μ l yes no o u =
  bindHandler# @o yes $ \qyes ->
    bindIterHandler# @o (\qc# -> staHandler# (no (mkOffset qc# u))) $ \qno ->
      let handler qc# = mkStaHandler (mkOffset @o qc# u) $ \o ->
            [||if $$(same qc# o) then $$qyes $$(qc#) else $$qno $$(qc#) $$o||]
      in bindIterHandler# @o (staHandler# . handler) $ \qhandler ->
        buildIter# @o (offset o) $ \qloop qo# ->
          let off = mkOffset qo# u
          in run l (Γ Empty noreturn off (VCons (staHandlerFull (Just off) [||$$qhandler $$(qo#)||] [||$$qyes $$(qo#)||] [||$$qno $$(qo#)||]) VNil))
                   (voidCoins (insertSub μ (\_ o# _ -> [|| $$qloop $$(o#) ||]) ctx))

buildRec :: forall rs s o a r. RecBuilder o => MVar r
         -> Regs rs
         -> Ctx s o a
         -> Machine s o '[] One r a
         -> DynFunc rs s o a r
buildRec μ rs ctx k =
  takeFreeRegisters rs ctx $ \ctx ->
    buildRec# @o $ \qself qret qo# qh ->
      run k (Γ Empty (staCont qret) (mkOffset qo# 0) (VCons (staHandler Nothing qh) VNil))
            (insertSub μ (\k o# h -> [|| $$qself $$k $$(o#) $$h ||]) (nextUnique ctx))

{- Marshalling Operations -}
dynHandler :: forall s o a. MarshalOps o => StaHandler s o a -> DynHandler s o a
dynHandler (StaHandler _ sh Nothing) = dynHandler# @o (unknown sh)
dynHandler (StaHandler _ _ (Just dh)) = dh

dynCont :: forall s o a x. MarshalOps o => StaCont s o a x -> DynCont s o a x
dynCont (StaCont sk Nothing) = dynCont# @o sk
dynCont (StaCont _ (Just dk)) = dk

{- Debugger Operations -}
type LogHandler o = (PositionOps (Rep o), LogOps (Rep o))

logHandler :: (?ops :: InputOps (Rep o), LogHandler o) => String -> Ctx s o a -> Γ s o xs (Succ n) ks a -> Word -> StaHandlerBuilder s o a
logHandler name ctx γ u o = let VCons h _ = handlers γ in mkStaHandler o $ \o# -> [||
    trace $$(preludeString name '<' (γ {input = mkOffset o# u}) ctx (color Red " Fail")) $$(staHandler# h o#)
  ||]

preludeString :: forall s o xs n r a. (?ops :: InputOps (Rep o), LogHandler o) => String -> Char -> Γ s o xs n r a -> Ctx s o a -> String -> Code String
preludeString name dir γ ctx ends = [|| concat [$$prelude, $$eof, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    Offset {offset} = input γ
    indent          = replicate (debugLevel ctx * 2) ' '
    start           = shiftLeft offset [||5#||]
    end             = shiftRight offset [||5#||]
    inputTrace      = [|| let replace '\n' = color Green "↙"
                              replace ' '  = color White "·"
                              replace c    = return c
                              go i#
                                | $$(same [||i#||] end) || not ($$more i#) = []
                                | otherwise = $$(next [||i#||] (\qc qi' -> [||replace $$qc ++ go $$qi'||]))
                          in go $$start ||]
    eof             = [|| if $$more $$end then $$inputTrace else $$inputTrace ++ color Red "•" ||]
    prelude         = [|| concat [indent, dir : name, dir : " (", show $$(offToInt offset), "): "] ||]
    caretSpace      = [|| replicate (length $$prelude + $$(offToInt offset) - $$(offToInt start)) ' ' ||]