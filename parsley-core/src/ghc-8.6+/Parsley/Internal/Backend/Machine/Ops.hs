{-# OPTIONS_GHC -Wno-monomorphism-restriction #-}
{-# LANGUAGE AllowAmbiguousTypes,
             ConstrainedClassMethods,
             ConstraintKinds,
             CPP,
             ImplicitParams,
             MagicHash,
             PatternSynonyms,
             RecordWildCards,
             TypeApplications,
             UnboxedTuples #-}
module Parsley.Internal.Backend.Machine.Ops (module Parsley.Internal.Backend.Machine.Ops) where

import Control.Monad                                 (liftM2)
import Control.Monad.Reader                          (ask, local)
import Control.Monad.ST                              (ST)
import Data.Bits                                     ((.&.), (.|.))
import Data.STRef                                    (writeSTRef, readSTRef, newSTRef)
import Data.Text                                     (Text)
import Data.Void                                     (Void)
import Debug.Trace                                   (trace)
import Parsley.Internal.Backend.Machine.Defunc       (Defunc(LAM, INPUT), pattern FREEVAR, genDefunc, ap, _if)
import Parsley.Internal.Backend.Machine.Identifiers  (MVar, ΦVar, ΣVar)
import Parsley.Internal.Backend.Machine.InputOps     (PositionOps(..), BoxOps(..), LogOps(..), InputOps, next, more)
import Parsley.Internal.Backend.Machine.InputRep     (Unboxed, OffWith, UnpackedLazyByteString, Stream{-, representationTypes-})
import Parsley.Internal.Backend.Machine.Instructions (Access(..))
import Parsley.Internal.Backend.Machine.LetBindings  (Regs(..))
import Parsley.Internal.Backend.Machine.Types.State  (Γ(..), Ctx, Handler, Machine(..), MachineMonad, Cont, Subroutine, OpStack(..), Func,
                                                      run, voidCoins, insertSub, insertΦ, insertNewΣ, insertScopedΣ, cacheΣ, cachedΣ, concreteΣ, debugLevel)
import Parsley.Internal.Common                       (One, Code, Vec(..), Nat(..))
import Parsley.Internal.Core.CharPred                (CharPred, lamTerm)
import System.Console.Pretty                         (color, Color(Green, White, Red, Blue))

#define inputInstances(derivation) \
derivation(Int)                    \
derivation((OffWith [Char]))       \
derivation((OffWith Stream))       \
derivation(UnpackedLazyByteString) \
derivation(Text)

type Ops o = (LogHandler o, ContOps o, HandlerOps o, JoinBuilder o, RecBuilder o, ReturnOps o, PositionOps o, BoxOps o, LogOps o)

updatePos# :: Int -> Int -> Char -> (# Int, Int #)
updatePos# !line !_ '\n' = (# line + 1, 1 #)
updatePos# !line !col '\t' = (# line, ((col + 3) .&. (-4)) .|. 1 #) -- nearest tab boundary `c + (4 - (c - 1) % 4)`
updatePos# !line !col _    = (# line, col + 1 #)

updatePos :: (Code Int, Code Int) -> Code Char -> ((Code Int, Code Int) -> Code r) -> Code r
updatePos (qline, qcol) qc k = [|| case updatePos# $$qline $$qcol $$qc of (# line', col' #) -> $$(k ([||line'||], [||col'||])) ||]

{- Input Operations -}
sat :: (?ops :: InputOps o) => CharPred -> (Γ s o (Char : xs) n r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a)) -> Γ s o xs n r a -> Code (ST s (Maybe a))
sat p k bad γ@Γ{..} = next input $ \c input' -> let v = FREEVAR c in
                        updatePos pos c $ \pos' ->
                          _if (ap (LAM (lamTerm p)) v)
                              (k (γ {operands = Op v operands, input = input', pos = pos'}))
                              bad

emitLengthCheck :: (?ops :: InputOps o, PositionOps o) => Int -> (Γ s o xs n r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a)) -> Γ s o xs n r a -> Code (ST s (Maybe a))
emitLengthCheck 0 good _ γ   = good γ
emitLengthCheck 1 good bad γ = [|| if $$more $$(input γ) then $$(good (γ { deepestKnownChar = Just (input γ)})) else $$bad ||]
emitLengthCheck n good bad γ = [||
  let lookAheadInput = $$shiftRight $$(input γ) (n - 1) in
  if $$more lookAheadInput then $$(good (γ { deepestKnownChar = Just [||lookAheadInput||]}))
  else $$bad ||]

{- General Operations -}
dup :: Defunc x -> (Defunc x -> Code r) -> Code r
dup (FREEVAR x) k = k (FREEVAR x)
dup (INPUT o pos) k = k (INPUT o pos)
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
class HandlerOps o where
  buildHandler :: BoxOps o
               => Γ s o xs n r a
               -> (Γ s o (o : xs) n r a -> Code (ST s (Maybe a)))
               -> Code o -> (Code Int, Code Int) -> Code (Handler s o a)
  fatal :: Code (Handler s o a)
  raise :: BoxOps o => Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))

setupHandler :: Γ s o xs n r a
             -> (Code o -> (Code Int, Code Int) -> Code (Handler s o a))
             -> (Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))
setupHandler γ h k = [||
    let handler = $$(h (input γ) (pos γ))
    in $$(k (γ {handlers = VCons [||handler||] (handlers γ)}))
  ||]

#define deriveHandlerOps(_o)                         \
instance HandlerOps _o where                         \
{                                                    \
  buildHandler γ h c pos = [||\(o# :: Unboxed _o) !(line :: Int) !(col :: Int) ->     \
    $$(h (γ {operands = Op (INPUT c pos) (operands γ), \
             input = [||$$box o#||], deepestKnownChar = Nothing, pos = ([||line||], [||col||])}))||];           \
  fatal = [||\(!_) !_ !_ -> returnST Nothing ||];          \
  raise γ = let VCons h _ = handlers γ               \
            in [|| $$h ($$unbox $$(input γ)) $$(fst (pos γ)) $$(snd (pos γ)) ||];    \
};
inputInstances(deriveHandlerOps)

{- Control Flow Operations -}
class BoxOps o => ContOps o where
  suspend :: (Γ s o (x : xs) n r a -> Code (ST s (Maybe a))) -> Γ s o xs n r a -> Code (Cont s o a x)
  resume :: Code (Cont s o a x) -> Γ s o (x : xs) n r a -> Code (ST s (Maybe a))
  callWithContinuation :: Code (Subroutine s o a x) -> Code (Cont s o a x) -> Code o -> (Code Int, Code Int) -> Vec (Succ n) (Code (Handler s o a)) -> Code (ST s (Maybe a))

class ReturnOps o where
  halt :: Code (Cont s o a a)
  noreturn :: Code (Cont s o a Void)

#define deriveContOps(_o)                                                                      \
instance ContOps _o where                                                                      \
{                                                                                              \
  suspend m γ = [|| \x (!o#) !l !c -> $$(m (γ {operands = Op (FREEVAR [||x||]) (operands γ),         \
                                             input = [||$$box o#||], deepestKnownChar = Nothing, pos = ([||l||], [||c||])})) ||];                        \
  resume k γ = let Op x _ = operands γ in [|| $$k $$(genDefunc x) ($$unbox $$(input γ)) $$(fst (pos γ)) $$(snd (pos γ)) ||];   \
  callWithContinuation sub ret input (ql, qc) (VCons h _) = [||$$sub $$ret ($$unbox $$input) $$ql $$qc $! $$h||]; \
};
inputInstances(deriveContOps)

#define deriveReturnOps(_o)                                      \
instance ReturnOps _o where                                      \
{                                                                \
  halt = [||\x _ _ _ -> returnST $! Just x||];                       \
  noreturn = [||\_ _ _ _ -> error "Return is not permitted here"||]; \
};
inputInstances(deriveReturnOps)

{- Builder Operations -}
class BoxOps o => JoinBuilder o where
  setupJoinPoint :: ΦVar x -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a

class BoxOps o => RecBuilder o where
  buildIter :: ReturnOps o
            => Ctx s o a -> MVar Void -> Machine s o '[] One Void a
            -> (Code o -> (Code Int, Code Int) -> Code (Handler s o a)) -> Code o -> (Code Int, Code Int) -> Code (ST s (Maybe a))
  buildRec  :: MVar r
            -> Regs rs
            -> Ctx s o a
            -> Machine s o '[] One r a
            -> Code (Func rs s o a r)

#define deriveJoinBuilder(_o)                                                             \
instance JoinBuilder _o where                                                             \
{                                                                                         \
  setupJoinPoint φ (Machine k) mx =                                                       \
    liftM2 (\mk ctx γ -> [||                                                              \
      let join x !(o# :: Unboxed _o) !(line :: Int) !(col :: Int) =                                                    \
        $$(mk (γ {operands = Op (FREEVAR [||x||]) (operands γ), input = [||$$box o#||], deepestKnownChar = Nothing, pos = ([||line||], [||col||])})) \
      in $$(run mx γ (insertΦ φ [||join||] ctx))                                          \
    ||]) (local voidCoins k) ask;                                                         \
};
inputInstances(deriveJoinBuilder)

#define deriveRecBuilder(_o)                                                     \
instance RecBuilder _o where                                                     \
{                                                                                \
  buildIter ctx μ l h o (line, col) = let bx = box in [||                                    \
      let handler !o# !line !col = $$(h [||$$bx o#||] ([||line||], [||col||]));           \
          loop !o# !line !col =                                                             \
        $$(run l                                                                 \
            (Γ Empty (noreturn @_o) [||$$bx o#||] Nothing ([||line||], [||col||]) (VCons [||handler o# line col||] VNil)) \
            (voidCoins (insertSub μ [||\_ (!o#) !line !col _ -> loop o# line col||] ctx)))           \
      in loop ($$unbox $$o) $$line $$col                                                      \
    ||];                                                                         \
  buildRec _ rs ctx k = let bx = box in takeFreeRegisters rs ctx (\ctx ->        \
    [|| \(!ret) (!o#) !line !col h ->                                                       \
      $$(run k (Γ Empty [||ret||] [||$$bx o#||] Nothing ([||line||], [||col||]) (VCons [||h||] VNil)) ctx) ||]); \
};
inputInstances(deriveRecBuilder)

takeFreeRegisters :: Regs rs -> Ctx s o a -> (Ctx s o a -> Code (Subroutine s o a x)) -> Code (Func rs s o a x)
takeFreeRegisters NoRegs ctx body = body ctx
takeFreeRegisters (FreeReg σ σs) ctx body = [||\(!reg) -> $$(takeFreeRegisters σs (insertScopedΣ σ [||reg||] ctx) body)||]

{- Debugger Operations -}
class (BoxOps o, PositionOps o, LogOps o) => LogHandler o where
  logHandler :: (?ops :: InputOps o) => String -> Ctx s o a -> Γ s o xs (Succ n) ks a -> Code o -> (Code Int, Code Int) -> Code (Handler s o a)

preludeString :: (?ops :: InputOps o, PositionOps o, LogOps o) => String -> Char -> Γ s o xs n r a -> Ctx s o a -> String -> Code String
preludeString name dir γ ctx ends = [|| concat [$$prelude, $$eof, ends, '\n' : $$caretSpace, color Blue "^"] ||]
  where
    offset     = input γ
    indent     = replicate (debugLevel ctx * 2) ' '
    start      = [|| $$shiftLeft $$offset 5 ||]
    end        = [|| $$shiftRight $$offset 5 ||]
    inputTrace = [|| let replace '\n' = color Green "↙"
                         replace ' '  = color White "·"
                         replace c    = return c
                         go i
                           | $$same i $$end || not ($$more i) = []
                           | otherwise = $$(next [||i||] (\qc qi' -> [||replace $$qc ++ go $$qi'||]))
                     in go $$start ||]
    eof        = [|| if $$more $$end then $$inputTrace else $$inputTrace ++ color Red "•" ||]
    prelude    = [|| concat [indent, dir : name, dir : " (", show ($$offToInt $$offset), "): "] ||]
    caretSpace = [|| replicate (length $$prelude + $$offToInt $$offset - $$offToInt $$start) ' ' ||]

#define deriveLogHandler(_o)                                                                         \
instance LogHandler _o where                                                                         \
{                                                                                                    \
  logHandler name ctx γ _ _ = let VCons h _ = handlers γ in [||\(!o#) ->                             \
      trace $$(preludeString name '<' (γ {input = [||$$box o#||]}) ctx (color Red " Fail")) ($$h o#) \
    ||];                                                                                             \
};
inputInstances(deriveLogHandler)

-- RIP Dream :(
{-$(let derive _o = [d|
        instance HandlerOps _o where
          fatal = [||\(!o#) -> return Nothing :: ST s (Maybe a)||]
        |] in traverse derive representationTypes)-}
