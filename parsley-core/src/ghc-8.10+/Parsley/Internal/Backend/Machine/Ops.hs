{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
{-# LANGUAGE AllowAmbiguousTypes,
             ConstrainedClassMethods,
             ConstraintKinds,
             CPP,
             ImplicitParams,
             MagicHash,
             NamedFieldPuns,
             PatternSynonyms,
             RecordWildCards,
             TypeApplications #-}
module Parsley.Internal.Backend.Machine.Ops (module Parsley.Internal.Backend.Machine.Ops) where

import Control.Monad                                 (liftM2)
import Control.Monad.Reader                          (ask, local)
import Control.Monad.ST                              (ST)
import Data.Array.Unboxed                            (UArray)
import Data.ByteString.Internal                      (ByteString)
import Data.STRef                                    (writeSTRef, readSTRef, newSTRef)
import Data.Proxy                                    (Proxy(Proxy))
import Data.Text                                     (Text)
import Data.Void                                     (Void)
import Debug.Trace                                   (trace)
import GHC.Exts                                      (Int(..), (-#))
import Language.Haskell.TH.Syntax                    (liftTyped)
import Parsley.Internal.Backend.Machine.Defunc       (Defunc(OFFSET), genDefunc, _if, pattern FREEVAR)
import Parsley.Internal.Backend.Machine.Identifiers  (MVar, ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.InputOps     (PositionOps(..), LogOps(..), InputOps, next, more)
import Parsley.Internal.Backend.Machine.InputRep     (Rep{-, representationTypes-})
import Parsley.Internal.Backend.Machine.Instructions (Access(..))
import Parsley.Internal.Backend.Machine.LetBindings  (Regs(..))
import Parsley.Internal.Backend.Machine.Offset       (Offset(..), moveOne, mkOffset)
import Parsley.Internal.Backend.Machine.State        (Γ(..), Ctx, Machine(..), MachineMonad, StaSubRoutine, OpStack(..), DynFunc,
                                                      StaHandler(..), StaCont(..), DynHandler, DynCont, staHandler#, mkStaHandler, staCont#, mkStaCont,
                                                      run, voidCoins, insertSub, insertΦ, insertNewΣ, cacheΣ, cachedΣ, concreteΣ, debugLevel,
                                                      takeFreeRegisters)
import Parsley.Internal.Common                       (One, Code, Vec(..), Nat(..))
import Parsley.Internal.Core.InputTypes              (Text16, CharList, Stream)
import System.Console.Pretty                         (color, Color(Green, White, Red, Blue))

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString)

#define inputInstances(derivation) \
derivation([Char])                 \
derivation((UArray Int Char))      \
derivation(Text16)                 \
derivation(ByteString)             \
derivation(CharList)               \
derivation(Stream)                 \
derivation(Lazy.ByteString)        \
derivation(Text)

type Ops o = (HandlerOps o, JoinBuilder o, RecBuilder o, PositionOps o, MarshalOps o, LogOps (Rep o))

{- Input Operations -}
sat :: (?ops :: InputOps (Rep o)) => (Defunc Char -> Defunc Bool) -> (Γ s o (Char : xs) n r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a)) -> Γ s o xs n r a -> Code (ST s (Maybe a))
sat p k bad γ@Γ{..} = next (offset input) $ \c offset' -> let v = FREEVAR c in _if (p v) (k (γ {operands = Op v operands, input = moveOne input offset'})) bad

emitLengthCheck :: forall s o xs n r a. (?ops :: InputOps (Rep o), PositionOps o) => Int -> (Γ s o xs n r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a)) -> Γ s o xs n r a -> Code (ST s (Maybe a))
emitLengthCheck 0 good _ γ   = good γ
emitLengthCheck 1 good bad γ = [|| if $$more $$(offset (input γ)) then $$(good γ) else $$bad ||]
emitLengthCheck (I# n) good bad γ = [||
  if $$more $$(shiftRight (Proxy @o) (offset (input γ)) (liftTyped (n -# 1#))) then $$(good γ)
  else $$bad ||]

{- General Operations -}
dup :: Defunc x -> (Defunc x -> Code r) -> Code r
dup (FREEVAR x) k = k (FREEVAR x)
dup x k = [|| let !dupx = $$(genDefunc x) in $$(k (FREEVAR [||dupx||])) ||]

{-# INLINE returnST #-}
returnST :: forall s a. a -> ST s a
returnST = return @(ST s)

{- Register Operations -}
newΣ :: ΣVar x -> Access -> Defunc x -> (Ctx s o a -> Code (ST s (Maybe a))) -> Ctx s o a -> Code (ST s (Maybe a))
newΣ σ Soft x k ctx = dup x $ \dupx -> k $! insertNewΣ σ Nothing dupx ctx
newΣ σ Hard x k ctx = dup x $ \dupx -> [||
    do ref <- newSTRef $$(genDefunc dupx)
       $$(k $! insertNewΣ σ (Just [||ref||]) dupx ctx)
  ||]

writeΣ :: ΣVar x -> Access -> Defunc x -> (Ctx s o a -> Code (ST s (Maybe a))) -> Ctx s o a -> Code (ST s (Maybe a))
writeΣ σ Soft x k ctx = dup x $ \dupx -> k $! cacheΣ σ dupx ctx
writeΣ σ Hard x k ctx = let ref = concreteΣ σ ctx in dup x $ \dupx -> [||
    do writeSTRef $$ref $$(genDefunc dupx)
       $$(k $! cacheΣ σ dupx ctx)
  ||]

readΣ :: ΣVar x -> Access -> (Defunc x -> Ctx s o a -> Code (ST s (Maybe a))) -> Ctx s o a -> Code (ST s (Maybe a))
readΣ σ Soft k ctx = (k $! cachedΣ σ ctx) $! ctx
readΣ σ Hard k ctx = let ref = concreteΣ σ ctx in [||
    do x <- readSTRef $$ref
       $$(let fv = FREEVAR [||x||] in k fv $! cacheΣ σ fv ctx)
  ||]

{- Handler Operations -}
buildHandler :: Γ s o xs n r a
             -> (Γ s o (o : xs) n r a -> Code (ST s (Maybe a)))
             -> Offset o -> StaHandler s o a
buildHandler γ h c = mkStaHandler $ \o# -> h (γ {operands = Op (OFFSET c) (operands γ), input = mkOffset o# 0})

fatal :: forall o s a. StaHandler s o a
fatal = mkStaHandler $ const [|| returnST Nothing ||]

class HandlerOps o where
  bindHandler :: Γ s o xs n r a
              -> (Offset o -> StaHandler s o a)
              -> (Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))

#define deriveHandlerOps(_o)                                                    \
instance HandlerOps _o where                                                    \
{                                                                               \
  bindHandler γ h k = [||                                                       \
    let handler (o# :: Rep _o) = $$(staHandler# (h (input γ)) [||o#||])         \
    in $$(k (γ {handlers = VCons (staHandler @_o [||handler||]) (handlers γ)})) \
  ||]                                                                           \
};
inputInstances(deriveHandlerOps)

raise :: Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))
raise γ = let VCons h _ = handlers γ in staHandler# h (offset (input γ))

{- Control Flow Operations -}
suspend :: (Γ s o (x : xs) n r a -> Code (ST s (Maybe a))) -> Γ s o xs n r a -> StaCont s o a x
suspend m γ = mkStaCont $ \x o# -> m (γ {operands = Op (FREEVAR x) (operands γ), input = mkOffset o# 0})

halt :: forall o s a. StaCont s o a a
halt = mkStaCont $ \x _ -> [||returnST $! Just $$x||]

noreturn :: forall o s a. StaCont s o a Void
noreturn = mkStaCont $ \_ _ -> [||error "Return is not permitted here"||]

callWithContinuation :: forall o s a x n. MarshalOps o => StaSubRoutine s o a x -> StaCont s o a x -> Offset o -> Vec (Succ n) (StaHandler s o a) -> Code (ST s (Maybe a))
callWithContinuation sub ret input (VCons h _) = sub (dynCont @o ret) (offset input) (dynHandler @o h)

resume :: StaCont s o a x -> Γ s o (x : xs) n r a -> Code (ST s (Maybe a))
resume k γ = let Op x _ = operands γ in staCont# k (genDefunc x) (offset (input γ))

{- Builder Operations -}
class JoinBuilder o where
  setupJoinPoint :: ΦVar x -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a

class RecBuilder o where
  buildIter :: Ctx s o a -> MVar Void -> Machine s o '[] One Void a
            -> (Offset o -> StaHandler s o a) -> Offset o -> Code (ST s (Maybe a))
  buildRec  :: MVar r
            -> Regs rs
            -> Ctx s o a
            -> Machine s o '[] One r a
            -> DynFunc rs s o a r

#define deriveJoinBuilder(_o)                                                                  \
instance JoinBuilder _o where                                                                  \
{                                                                                              \
  setupJoinPoint φ (Machine k) mx =                                                            \
    liftM2 (\mk ctx γ -> [||                                                                   \
      let join x !(o# :: Rep _o) =                                                             \
        $$(mk (γ {operands = Op (FREEVAR [||x||]) (operands γ), input = mkOffset [||o#||] 0})) \
      in $$(run mx γ (insertΦ φ (staCont @_o [||join||]) ctx))                                 \
    ||]) (local voidCoins k) ask;                                                              \
};
inputInstances(deriveJoinBuilder)

#define deriveRecBuilder(_o)                                                                                \
instance RecBuilder _o where                                                                                \
{                                                                                                           \
  buildIter ctx μ l h o = [||                                                                               \
      let handler (c# :: Rep _o) !(o# :: Rep _o) = $$(staHandler# (h (mkOffset [||c#||] 0)) [||o#||]);      \
          loop !(o# :: Rep _o) =                                                                            \
        $$(run l                                                                                            \
            (Γ Empty (noreturn @_o) (mkOffset [||o#||] 0) (VCons (staHandler @_o [||handler o#||]) VNil))   \
            (voidCoins (insertSub μ (\_ o# _ -> [|| loop $$(o#) ||]) ctx)))                                 \
      in loop $$(offset o)                                                                                  \
    ||];                                                                                                    \
  buildRec μ rs ctx k = takeFreeRegisters rs ctx (\ctx ->                                                   \
    {- The idea here is to try and reduce the number of times registers have to be passed around -}         \
    {-[|| \ ret !(o# :: Rep _o) h ->                                                                        \
      $$(run k (Γ Empty (staCont @_o [||ret||]) [||o#||] (VCons (staHandler @_o [||h||]) VNil)) ctx) ||]-}  \
    [|| let self ret !(o# :: Rep _o) h =                                                                    \
          $$(run k                                                                                          \
              (Γ Empty (staCont @_o [||ret||]) (mkOffset [||o#||] 0) (VCons (staHandler @_o [||h||]) VNil)) \
              (insertSub μ (\k o# h -> [|| self $$k $$(o#) $$h ||]) ctx)) in self ||]  );                   \
};
inputInstances(deriveRecBuilder)

{- Marshalling Operations -}
class MarshalOps o where
  dynHandler :: StaHandler s o a -> DynHandler s o a
  dynCont :: StaCont s o a x -> DynCont s o a x

staHandler :: forall o s a. DynHandler s o a -> StaHandler s o a
staHandler dh = StaHandler (\o# -> [|| $$dh $$(o#) ||]) (Just dh)

staCont :: forall o s a x. DynCont s o a x -> StaCont s o a x
staCont dk = StaCont (\x o# -> [|| $$dk $$x $$(o#) ||]) (Just dk)

#define deriveMarshalOps(_o)                                                            \
instance MarshalOps _o where                                                            \
{                                                                                       \
  dynHandler (StaHandler sh Nothing) = [||\ !(o# :: Rep _o) -> $$(sh [||o#||]) ||];     \
  dynHandler (StaHandler _ (Just dh)) = dh;                                             \
  dynCont (StaCont sk Nothing) = [||\ x (o# :: Rep _o) -> $$(sk [||x||] [||o#||]) ||]; \
  dynCont (StaCont _ (Just dk)) = dk;                                                   \
};
inputInstances(deriveMarshalOps)

{- Debugger Operations -}
type LogHandler o = (PositionOps o, LogOps (Rep o))

logHandler :: (?ops :: InputOps (Rep o), LogHandler o) => String -> Ctx s o a -> Γ s o xs (Succ n) ks a -> Offset o -> StaHandler s o a
logHandler name ctx γ _ = let VCons h _ = handlers γ in mkStaHandler $ \o# -> [||
    trace $$(preludeString name '<' (γ {input = mkOffset o# 0}) ctx (color Red " Fail")) $$(staHandler# h o#)
  ||]

preludeString :: forall s o xs n r a. (?ops :: InputOps (Rep o), LogHandler o) => String -> Char -> Γ s o xs n r a -> Ctx s o a -> String -> Code String
preludeString name dir γ ctx ends = [|| concat [$$prelude, $$eof, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    Offset {offset} = input γ
    proxy           = Proxy @o
    indent          = replicate (debugLevel ctx * 2) ' '
    start           = shiftLeft offset [||5#||]
    end             = shiftRight proxy offset [||5#||]
    inputTrace      = [|| let replace '\n' = color Green "↙"
                              replace ' '  = color White "·"
                              replace c    = return c
                              go i#
                                | $$(same proxy [||i#||] end) || not ($$more i#) = []
                                | otherwise = $$(next [||i#||] (\qc qi' -> [||replace $$qc ++ go $$qi'||]))
                          in go $$start ||]
    eof             = [|| if $$more $$end then $$inputTrace else $$inputTrace ++ color Red "•" ||]
    prelude         = [|| concat [indent, dir : name, dir : " (", show ($$(offToInt offset)), "): "] ||]
    caretSpace      = [|| replicate (length $$prelude + $$(offToInt offset) - $$(offToInt start)) ' ' ||]

-- RIP Dream :(
{-$(let derive _o = [d|
        instance HandlerOps _o where
          fatal = [||\(!o#) -> return Nothing :: ST s (Maybe a)||]
        |] in traverse derive representationTypes)-}