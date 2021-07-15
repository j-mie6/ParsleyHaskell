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
                                                      takeFreeRegisters,
                                                      freshUnique, nextUnique)
import Parsley.Internal.Common                       (One, Code, Vec(..), Nat(..))
import Parsley.Internal.Core.InputTypes              (Text16, CharList, Stream)
import System.Console.Pretty                         (color, Color(Green, White, Red, Blue))

import qualified Data.ByteString.Lazy.Internal as Lazy (ByteString)











type Ops o = (HandlerOps o, JoinBuilder o, RecBuilder o, PositionOps o, MarshalOps o, LogOps (Rep o))
type StaHandlerBuilder s o a = Offset o -> StaHandler s o a

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
             -> Word
             -> StaHandlerBuilder s o a
buildHandler γ h u c = mkStaHandler $ \o# -> h (γ {operands = Op (OFFSET c) (operands γ), input = mkOffset o# u})

fatal :: forall o s a. StaHandler s o a
fatal = mkStaHandler $ const [|| returnST Nothing ||]

class HandlerOps o where
  bindHandler :: Γ s o xs n r a
              -> StaHandlerBuilder s o a
              -> (Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))) -> Code (ST s (Maybe a))









instance HandlerOps [Char] where                                                    {                                                                                 bindHandler γ h k = [||                                                           let handler (o# :: Rep [Char]) = $$(staHandler# (h (input γ)) [||o#||])             in $$(k (γ {handlers = VCons (staHandler @[Char] [||handler||]) (handlers γ)}))   ||]                                                                           };                 instance HandlerOps (UArray Int Char) where                                                    {                                                                                 bindHandler γ h k = [||                                                           let handler (o# :: Rep (UArray Int Char)) = $$(staHandler# (h (input γ)) [||o#||])             in $$(k (γ {handlers = VCons (staHandler @(UArray Int Char) [||handler||]) (handlers γ)}))   ||]                                                                           };      instance HandlerOps Text16 where                                                    {                                                                                 bindHandler γ h k = [||                                                           let handler (o# :: Rep Text16) = $$(staHandler# (h (input γ)) [||o#||])             in $$(k (γ {handlers = VCons (staHandler @Text16 [||handler||]) (handlers γ)}))   ||]                                                                           };                 instance HandlerOps ByteString where                                                    {                                                                                 bindHandler γ h k = [||                                                           let handler (o# :: Rep ByteString) = $$(staHandler# (h (input γ)) [||o#||])             in $$(k (γ {handlers = VCons (staHandler @ByteString [||handler||]) (handlers γ)}))   ||]                                                                           };             instance HandlerOps CharList where                                                    {                                                                                 bindHandler γ h k = [||                                                           let handler (o# :: Rep CharList) = $$(staHandler# (h (input γ)) [||o#||])             in $$(k (γ {handlers = VCons (staHandler @CharList [||handler||]) (handlers γ)}))   ||]                                                                           };               instance HandlerOps Stream where                                                    {                                                                                 bindHandler γ h k = [||                                                           let handler (o# :: Rep Stream) = $$(staHandler# (h (input γ)) [||o#||])             in $$(k (γ {handlers = VCons (staHandler @Stream [||handler||]) (handlers γ)}))   ||]                                                                           };                 instance HandlerOps Lazy.ByteString where                                                    {                                                                                 bindHandler γ h k = [||                                                           let handler (o# :: Rep Lazy.ByteString) = $$(staHandler# (h (input γ)) [||o#||])             in $$(k (γ {handlers = VCons (staHandler @Lazy.ByteString [||handler||]) (handlers γ)}))   ||]                                                                           };        instance HandlerOps Text where                                                    {                                                                                 bindHandler γ h k = [||                                                           let handler (o# :: Rep Text) = $$(staHandler# (h (input γ)) [||o#||])             in $$(k (γ {handlers = VCons (staHandler @Text [||handler||]) (handlers γ)}))   ||]                                                                           };

raise :: Γ s o xs (Succ n) r a -> Code (ST s (Maybe a))
raise γ = let VCons h _ = handlers γ in staHandler# h (offset (input γ))

{- Control Flow Operations -}
suspend :: (Γ s o (x : xs) n r a -> Code (ST s (Maybe a))) -> Γ s o xs n r a -> Word -> StaCont s o a x
suspend m γ u = mkStaCont $ \x o# -> m (γ {operands = Op (FREEVAR x) (operands γ), input = mkOffset o# u})

halt :: forall o s a. StaCont s o a a
halt = mkStaCont $ \x _ -> [||returnST $! Just $$x||]

noreturn :: forall o s a. StaCont s o a Void
noreturn = mkStaCont $ \_ _ -> [||error "Return is not permitted here"||]

callWithContinuation :: forall o s a x n. MarshalOps o => StaSubRoutine s o a x -> StaCont s o a x -> Code (Rep o) -> Vec (Succ n) (StaHandler s o a) -> Code (ST s (Maybe a))
callWithContinuation sub ret input (VCons h _) = sub (dynCont @o ret) input (dynHandler @o h)

resume :: StaCont s o a x -> Γ s o (x : xs) n r a -> Code (ST s (Maybe a))
resume k γ = let Op x _ = operands γ in staCont# k (genDefunc x) (offset (input γ))

{- Builder Operations -}
class JoinBuilder o where
  setupJoinPoint :: ΦVar x -> Machine s o (x : xs) n r a -> Machine s o xs n r a -> MachineMonad s o xs n r a

class RecBuilder o where
  buildIter :: Ctx s o a -> MVar Void -> Machine s o '[] One Void a
            -> StaHandlerBuilder s o a -> Code (Rep o) -> Word -> Code (ST s (Maybe a))
  buildRec  :: MVar r
            -> Regs rs
            -> Ctx s o a
            -> Machine s o '[] One r a
            -> DynFunc rs s o a r











instance JoinBuilder [Char] where                                                                  {                                                                                                setupJoinPoint φ (Machine k) mx = freshUnique $ \u ->                                            liftM2 (\mk ctx γ -> [||                                                                         let join x !(o# :: Rep [Char]) =                                                                     $$(mk (γ {operands = Op (FREEVAR [||x||]) (operands γ), input = mkOffset [||o#||] u}))       in $$(run mx γ (insertΦ φ (staCont @[Char] [||join||]) ctx))                                     ||]) (local voidCoins k) ask;                                                              };                 instance JoinBuilder (UArray Int Char) where                                                                  {                                                                                                setupJoinPoint φ (Machine k) mx = freshUnique $ \u ->                                            liftM2 (\mk ctx γ -> [||                                                                         let join x !(o# :: Rep (UArray Int Char)) =                                                                     $$(mk (γ {operands = Op (FREEVAR [||x||]) (operands γ), input = mkOffset [||o#||] u}))       in $$(run mx γ (insertΦ φ (staCont @(UArray Int Char) [||join||]) ctx))                                     ||]) (local voidCoins k) ask;                                                              };      instance JoinBuilder Text16 where                                                                  {                                                                                                setupJoinPoint φ (Machine k) mx = freshUnique $ \u ->                                            liftM2 (\mk ctx γ -> [||                                                                         let join x !(o# :: Rep Text16) =                                                                     $$(mk (γ {operands = Op (FREEVAR [||x||]) (operands γ), input = mkOffset [||o#||] u}))       in $$(run mx γ (insertΦ φ (staCont @Text16 [||join||]) ctx))                                     ||]) (local voidCoins k) ask;                                                              };                 instance JoinBuilder ByteString where                                                                  {                                                                                                setupJoinPoint φ (Machine k) mx = freshUnique $ \u ->                                            liftM2 (\mk ctx γ -> [||                                                                         let join x !(o# :: Rep ByteString) =                                                                     $$(mk (γ {operands = Op (FREEVAR [||x||]) (operands γ), input = mkOffset [||o#||] u}))       in $$(run mx γ (insertΦ φ (staCont @ByteString [||join||]) ctx))                                     ||]) (local voidCoins k) ask;                                                              };             instance JoinBuilder CharList where                                                                  {                                                                                                setupJoinPoint φ (Machine k) mx = freshUnique $ \u ->                                            liftM2 (\mk ctx γ -> [||                                                                         let join x !(o# :: Rep CharList) =                                                                     $$(mk (γ {operands = Op (FREEVAR [||x||]) (operands γ), input = mkOffset [||o#||] u}))       in $$(run mx γ (insertΦ φ (staCont @CharList [||join||]) ctx))                                     ||]) (local voidCoins k) ask;                                                              };               instance JoinBuilder Stream where                                                                  {                                                                                                setupJoinPoint φ (Machine k) mx = freshUnique $ \u ->                                            liftM2 (\mk ctx γ -> [||                                                                         let join x !(o# :: Rep Stream) =                                                                     $$(mk (γ {operands = Op (FREEVAR [||x||]) (operands γ), input = mkOffset [||o#||] u}))       in $$(run mx γ (insertΦ φ (staCont @Stream [||join||]) ctx))                                     ||]) (local voidCoins k) ask;                                                              };                 instance JoinBuilder Lazy.ByteString where                                                                  {                                                                                                setupJoinPoint φ (Machine k) mx = freshUnique $ \u ->                                            liftM2 (\mk ctx γ -> [||                                                                         let join x !(o# :: Rep Lazy.ByteString) =                                                                     $$(mk (γ {operands = Op (FREEVAR [||x||]) (operands γ), input = mkOffset [||o#||] u}))       in $$(run mx γ (insertΦ φ (staCont @Lazy.ByteString [||join||]) ctx))                                     ||]) (local voidCoins k) ask;                                                              };        instance JoinBuilder Text where                                                                  {                                                                                                setupJoinPoint φ (Machine k) mx = freshUnique $ \u ->                                            liftM2 (\mk ctx γ -> [||                                                                         let join x !(o# :: Rep Text) =                                                                     $$(mk (γ {operands = Op (FREEVAR [||x||]) (operands γ), input = mkOffset [||o#||] u}))       in $$(run mx γ (insertΦ φ (staCont @Text [||join||]) ctx))                                     ||]) (local voidCoins k) ask;                                                              };





















instance RecBuilder [Char] where                                                                                {                                                                                                             buildIter ctx μ l h o u = [||                                                                                   let handler (c# :: Rep [Char]) !(o# :: Rep [Char]) = $$(staHandler# (h (mkOffset [||c#||] u)) [||o#||]);                loop !(o# :: Rep [Char]) =                                                                                    $$(run l                                                                                                        (Γ Empty (noreturn @[Char]) (mkOffset [||o#||] u) (VCons (staHandler @[Char] [||handler o#||]) VNil))               (voidCoins (insertSub μ (\_ o# _ -> [|| loop $$(o#) ||]) ctx)))                                       in loop $$o                                                                                               ||];                                                                                                      buildRec μ rs ctx k = takeFreeRegisters rs ctx (\ctx ->                                                       {- The idea here is to try and reduce the number of times registers have to be passed around -}             {-[|| \ ret !(o# :: Rep [Char]) h ->                                                                              $$(run k (Γ Empty (staCont @[Char] [||ret||]) [||o#||] (VCons (staHandler @[Char] [||h||]) VNil)) ctx) ||]-}      [|| let self ret !(o# :: Rep [Char]) h =                                                                              $$(run k                                                                                                        (Γ Empty (staCont @[Char] [||ret||]) (mkOffset [||o#||] 0) (VCons (staHandler @[Char] [||h||]) VNil))               (insertSub μ (\k o# h -> [|| self $$k $$(o#) $$h ||]) (nextUnique ctx))) in self ||]  );      };                 instance RecBuilder (UArray Int Char) where                                                                                {                                                                                                             buildIter ctx μ l h o u = [||                                                                                   let handler (c# :: Rep (UArray Int Char)) !(o# :: Rep (UArray Int Char)) = $$(staHandler# (h (mkOffset [||c#||] u)) [||o#||]);                loop !(o# :: Rep (UArray Int Char)) =                                                                                    $$(run l                                                                                                        (Γ Empty (noreturn @(UArray Int Char)) (mkOffset [||o#||] u) (VCons (staHandler @(UArray Int Char) [||handler o#||]) VNil))               (voidCoins (insertSub μ (\_ o# _ -> [|| loop $$(o#) ||]) ctx)))                                       in loop $$o                                                                                               ||];                                                                                                      buildRec μ rs ctx k = takeFreeRegisters rs ctx (\ctx ->                                                       {- The idea here is to try and reduce the number of times registers have to be passed around -}             {-[|| \ ret !(o# :: Rep (UArray Int Char)) h ->                                                                              $$(run k (Γ Empty (staCont @(UArray Int Char) [||ret||]) [||o#||] (VCons (staHandler @(UArray Int Char) [||h||]) VNil)) ctx) ||]-}      [|| let self ret !(o# :: Rep (UArray Int Char)) h =                                                                              $$(run k                                                                                                        (Γ Empty (staCont @(UArray Int Char) [||ret||]) (mkOffset [||o#||] 0) (VCons (staHandler @(UArray Int Char) [||h||]) VNil))               (insertSub μ (\k o# h -> [|| self $$k $$(o#) $$h ||]) (nextUnique ctx))) in self ||]  );      };      instance RecBuilder Text16 where                                                                                {                                                                                                             buildIter ctx μ l h o u = [||                                                                                   let handler (c# :: Rep Text16) !(o# :: Rep Text16) = $$(staHandler# (h (mkOffset [||c#||] u)) [||o#||]);                loop !(o# :: Rep Text16) =                                                                                    $$(run l                                                                                                        (Γ Empty (noreturn @Text16) (mkOffset [||o#||] u) (VCons (staHandler @Text16 [||handler o#||]) VNil))               (voidCoins (insertSub μ (\_ o# _ -> [|| loop $$(o#) ||]) ctx)))                                       in loop $$o                                                                                               ||];                                                                                                      buildRec μ rs ctx k = takeFreeRegisters rs ctx (\ctx ->                                                       {- The idea here is to try and reduce the number of times registers have to be passed around -}             {-[|| \ ret !(o# :: Rep Text16) h ->                                                                              $$(run k (Γ Empty (staCont @Text16 [||ret||]) [||o#||] (VCons (staHandler @Text16 [||h||]) VNil)) ctx) ||]-}      [|| let self ret !(o# :: Rep Text16) h =                                                                              $$(run k                                                                                                        (Γ Empty (staCont @Text16 [||ret||]) (mkOffset [||o#||] 0) (VCons (staHandler @Text16 [||h||]) VNil))               (insertSub μ (\k o# h -> [|| self $$k $$(o#) $$h ||]) (nextUnique ctx))) in self ||]  );      };                 instance RecBuilder ByteString where                                                                                {                                                                                                             buildIter ctx μ l h o u = [||                                                                                   let handler (c# :: Rep ByteString) !(o# :: Rep ByteString) = $$(staHandler# (h (mkOffset [||c#||] u)) [||o#||]);                loop !(o# :: Rep ByteString) =                                                                                    $$(run l                                                                                                        (Γ Empty (noreturn @ByteString) (mkOffset [||o#||] u) (VCons (staHandler @ByteString [||handler o#||]) VNil))               (voidCoins (insertSub μ (\_ o# _ -> [|| loop $$(o#) ||]) ctx)))                                       in loop $$o                                                                                               ||];                                                                                                      buildRec μ rs ctx k = takeFreeRegisters rs ctx (\ctx ->                                                       {- The idea here is to try and reduce the number of times registers have to be passed around -}             {-[|| \ ret !(o# :: Rep ByteString) h ->                                                                              $$(run k (Γ Empty (staCont @ByteString [||ret||]) [||o#||] (VCons (staHandler @ByteString [||h||]) VNil)) ctx) ||]-}      [|| let self ret !(o# :: Rep ByteString) h =                                                                              $$(run k                                                                                                        (Γ Empty (staCont @ByteString [||ret||]) (mkOffset [||o#||] 0) (VCons (staHandler @ByteString [||h||]) VNil))               (insertSub μ (\k o# h -> [|| self $$k $$(o#) $$h ||]) (nextUnique ctx))) in self ||]  );      };             instance RecBuilder CharList where                                                                                {                                                                                                             buildIter ctx μ l h o u = [||                                                                                   let handler (c# :: Rep CharList) !(o# :: Rep CharList) = $$(staHandler# (h (mkOffset [||c#||] u)) [||o#||]);                loop !(o# :: Rep CharList) =                                                                                    $$(run l                                                                                                        (Γ Empty (noreturn @CharList) (mkOffset [||o#||] u) (VCons (staHandler @CharList [||handler o#||]) VNil))               (voidCoins (insertSub μ (\_ o# _ -> [|| loop $$(o#) ||]) ctx)))                                       in loop $$o                                                                                               ||];                                                                                                      buildRec μ rs ctx k = takeFreeRegisters rs ctx (\ctx ->                                                       {- The idea here is to try and reduce the number of times registers have to be passed around -}             {-[|| \ ret !(o# :: Rep CharList) h ->                                                                              $$(run k (Γ Empty (staCont @CharList [||ret||]) [||o#||] (VCons (staHandler @CharList [||h||]) VNil)) ctx) ||]-}      [|| let self ret !(o# :: Rep CharList) h =                                                                              $$(run k                                                                                                        (Γ Empty (staCont @CharList [||ret||]) (mkOffset [||o#||] 0) (VCons (staHandler @CharList [||h||]) VNil))               (insertSub μ (\k o# h -> [|| self $$k $$(o#) $$h ||]) (nextUnique ctx))) in self ||]  );      };               instance RecBuilder Stream where                                                                                {                                                                                                             buildIter ctx μ l h o u = [||                                                                                   let handler (c# :: Rep Stream) !(o# :: Rep Stream) = $$(staHandler# (h (mkOffset [||c#||] u)) [||o#||]);                loop !(o# :: Rep Stream) =                                                                                    $$(run l                                                                                                        (Γ Empty (noreturn @Stream) (mkOffset [||o#||] u) (VCons (staHandler @Stream [||handler o#||]) VNil))               (voidCoins (insertSub μ (\_ o# _ -> [|| loop $$(o#) ||]) ctx)))                                       in loop $$o                                                                                               ||];                                                                                                      buildRec μ rs ctx k = takeFreeRegisters rs ctx (\ctx ->                                                       {- The idea here is to try and reduce the number of times registers have to be passed around -}             {-[|| \ ret !(o# :: Rep Stream) h ->                                                                              $$(run k (Γ Empty (staCont @Stream [||ret||]) [||o#||] (VCons (staHandler @Stream [||h||]) VNil)) ctx) ||]-}      [|| let self ret !(o# :: Rep Stream) h =                                                                              $$(run k                                                                                                        (Γ Empty (staCont @Stream [||ret||]) (mkOffset [||o#||] 0) (VCons (staHandler @Stream [||h||]) VNil))               (insertSub μ (\k o# h -> [|| self $$k $$(o#) $$h ||]) (nextUnique ctx))) in self ||]  );      };                 instance RecBuilder Lazy.ByteString where                                                                                {                                                                                                             buildIter ctx μ l h o u = [||                                                                                   let handler (c# :: Rep Lazy.ByteString) !(o# :: Rep Lazy.ByteString) = $$(staHandler# (h (mkOffset [||c#||] u)) [||o#||]);                loop !(o# :: Rep Lazy.ByteString) =                                                                                    $$(run l                                                                                                        (Γ Empty (noreturn @Lazy.ByteString) (mkOffset [||o#||] u) (VCons (staHandler @Lazy.ByteString [||handler o#||]) VNil))               (voidCoins (insertSub μ (\_ o# _ -> [|| loop $$(o#) ||]) ctx)))                                       in loop $$o                                                                                               ||];                                                                                                      buildRec μ rs ctx k = takeFreeRegisters rs ctx (\ctx ->                                                       {- The idea here is to try and reduce the number of times registers have to be passed around -}             {-[|| \ ret !(o# :: Rep Lazy.ByteString) h ->                                                                              $$(run k (Γ Empty (staCont @Lazy.ByteString [||ret||]) [||o#||] (VCons (staHandler @Lazy.ByteString [||h||]) VNil)) ctx) ||]-}      [|| let self ret !(o# :: Rep Lazy.ByteString) h =                                                                              $$(run k                                                                                                        (Γ Empty (staCont @Lazy.ByteString [||ret||]) (mkOffset [||o#||] 0) (VCons (staHandler @Lazy.ByteString [||h||]) VNil))               (insertSub μ (\k o# h -> [|| self $$k $$(o#) $$h ||]) (nextUnique ctx))) in self ||]  );      };        instance RecBuilder Text where                                                                                {                                                                                                             buildIter ctx μ l h o u = [||                                                                                   let handler (c# :: Rep Text) !(o# :: Rep Text) = $$(staHandler# (h (mkOffset [||c#||] u)) [||o#||]);                loop !(o# :: Rep Text) =                                                                                    $$(run l                                                                                                        (Γ Empty (noreturn @Text) (mkOffset [||o#||] u) (VCons (staHandler @Text [||handler o#||]) VNil))               (voidCoins (insertSub μ (\_ o# _ -> [|| loop $$(o#) ||]) ctx)))                                       in loop $$o                                                                                               ||];                                                                                                      buildRec μ rs ctx k = takeFreeRegisters rs ctx (\ctx ->                                                       {- The idea here is to try and reduce the number of times registers have to be passed around -}             {-[|| \ ret !(o# :: Rep Text) h ->                                                                              $$(run k (Γ Empty (staCont @Text [||ret||]) [||o#||] (VCons (staHandler @Text [||h||]) VNil)) ctx) ||]-}      [|| let self ret !(o# :: Rep Text) h =                                                                              $$(run k                                                                                                        (Γ Empty (staCont @Text [||ret||]) (mkOffset [||o#||] 0) (VCons (staHandler @Text [||h||]) VNil))               (insertSub μ (\k o# h -> [|| self $$k $$(o#) $$h ||]) (nextUnique ctx))) in self ||]  );      };

{- Marshalling Operations -}
class MarshalOps o where
  dynHandler :: StaHandler s o a -> DynHandler s o a
  dynCont :: StaCont s o a x -> DynCont s o a x

staHandler :: forall o s a. DynHandler s o a -> StaHandler s o a
staHandler dh = StaHandler (\o# -> [|| $$dh $$(o#) ||]) (Just dh)

staCont :: forall o s a x. DynCont s o a x -> StaCont s o a x
staCont dk = StaCont (\x o# -> [|| $$dk $$x $$(o#) ||]) (Just dk)









instance MarshalOps [Char] where                                                           {                                                                                        dynHandler (StaHandler sh Nothing) = [||\ !(o# :: Rep [Char]) -> $$(sh [||o#||]) ||];      dynHandler (StaHandler _ (Just dh)) = dh;                                              dynCont (StaCont sk Nothing) = [||\ x (o# :: Rep [Char]) -> $$(sk [||x||] [||o#||]) ||];   dynCont (StaCont _ (Just dk)) = dk;                                                  };                 instance MarshalOps (UArray Int Char) where                                                           {                                                                                        dynHandler (StaHandler sh Nothing) = [||\ !(o# :: Rep (UArray Int Char)) -> $$(sh [||o#||]) ||];      dynHandler (StaHandler _ (Just dh)) = dh;                                              dynCont (StaCont sk Nothing) = [||\ x (o# :: Rep (UArray Int Char)) -> $$(sk [||x||] [||o#||]) ||];   dynCont (StaCont _ (Just dk)) = dk;                                                  };      instance MarshalOps Text16 where                                                           {                                                                                        dynHandler (StaHandler sh Nothing) = [||\ !(o# :: Rep Text16) -> $$(sh [||o#||]) ||];      dynHandler (StaHandler _ (Just dh)) = dh;                                              dynCont (StaCont sk Nothing) = [||\ x (o# :: Rep Text16) -> $$(sk [||x||] [||o#||]) ||];   dynCont (StaCont _ (Just dk)) = dk;                                                  };                 instance MarshalOps ByteString where                                                           {                                                                                        dynHandler (StaHandler sh Nothing) = [||\ !(o# :: Rep ByteString) -> $$(sh [||o#||]) ||];      dynHandler (StaHandler _ (Just dh)) = dh;                                              dynCont (StaCont sk Nothing) = [||\ x (o# :: Rep ByteString) -> $$(sk [||x||] [||o#||]) ||];   dynCont (StaCont _ (Just dk)) = dk;                                                  };             instance MarshalOps CharList where                                                           {                                                                                        dynHandler (StaHandler sh Nothing) = [||\ !(o# :: Rep CharList) -> $$(sh [||o#||]) ||];      dynHandler (StaHandler _ (Just dh)) = dh;                                              dynCont (StaCont sk Nothing) = [||\ x (o# :: Rep CharList) -> $$(sk [||x||] [||o#||]) ||];   dynCont (StaCont _ (Just dk)) = dk;                                                  };               instance MarshalOps Stream where                                                           {                                                                                        dynHandler (StaHandler sh Nothing) = [||\ !(o# :: Rep Stream) -> $$(sh [||o#||]) ||];      dynHandler (StaHandler _ (Just dh)) = dh;                                              dynCont (StaCont sk Nothing) = [||\ x (o# :: Rep Stream) -> $$(sk [||x||] [||o#||]) ||];   dynCont (StaCont _ (Just dk)) = dk;                                                  };                 instance MarshalOps Lazy.ByteString where                                                           {                                                                                        dynHandler (StaHandler sh Nothing) = [||\ !(o# :: Rep Lazy.ByteString) -> $$(sh [||o#||]) ||];      dynHandler (StaHandler _ (Just dh)) = dh;                                              dynCont (StaCont sk Nothing) = [||\ x (o# :: Rep Lazy.ByteString) -> $$(sk [||x||] [||o#||]) ||];   dynCont (StaCont _ (Just dk)) = dk;                                                  };        instance MarshalOps Text where                                                           {                                                                                        dynHandler (StaHandler sh Nothing) = [||\ !(o# :: Rep Text) -> $$(sh [||o#||]) ||];      dynHandler (StaHandler _ (Just dh)) = dh;                                              dynCont (StaCont sk Nothing) = [||\ x (o# :: Rep Text) -> $$(sk [||x||] [||o#||]) ||];   dynCont (StaCont _ (Just dk)) = dk;                                                  };

{- Debugger Operations -}
type LogHandler o = (PositionOps o, LogOps (Rep o))

logHandler :: (?ops :: InputOps (Rep o), LogHandler o) => String -> Ctx s o a -> Γ s o xs (Succ n) ks a -> Word -> StaHandlerBuilder s o a
logHandler name ctx γ u _ = let VCons h _ = handlers γ in mkStaHandler $ \o# -> [||
    trace $$(preludeString name '<' (γ {input = mkOffset o# u}) ctx (color Red " Fail")) $$(staHandler# h o#)
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
    prelude         = [|| concat [indent, dir : name, dir : " (", show $$(offToInt offset), "): "] ||]
    caretSpace      = [|| replicate (length $$prelude + $$(offToInt offset) - $$(offToInt start)) ' ' ||]

-- RIP Dream :(
{-$(let derive _o = [d|
        instance HandlerOps _o where
          fatal = [||\(!o#) -> return Nothing :: ST s (Maybe a)||]
        |] in traverse derive representationTypes)-}