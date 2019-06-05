{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}
module Compiler(compile) where

import ParserAST            (ParserF(..), Parser(..))
import Optimiser            (optimise)
import Analyser             (terminationAnalysis)
import CodeGenerator        (codeGen)
import Machine              (Machine(..), ΣVars, IMVar(..))
import Indexed              (Free(Op), Void, fold', absurd)
import Control.Applicative  (liftA2, liftA3)
import Control.Monad.Reader (ReaderT, ask, runReaderT, local, lift)
import System.IO.Unsafe     (unsafePerformIO)
import Data.IORef           (IORef, writeIORef, readIORef, newIORef)
import GHC.StableName       (StableName(..), makeStableName, hashStableName, eqStableName)
import Data.Hashable        (Hashable, hashWithSalt, hash)
import Data.HashMap.Lazy    (HashMap)
import GHC.Prim             (StableName#)
import Safe.Coerce          (coerce)
import Debug.Trace          (traceShow)
import qualified Data.HashMap.Lazy as HashMap

compile :: Parser a -> (Machine a, ΣVars)
compile (Parser p) = let (m, σs) = codeGen (terminationAnalysis (preprocess p)) in (Machine m, σs)

data StableParserName xs ks i = forall a. StableParserName (StableName# (Free ParserF Void xs ks a i))
data GenParser xs ks i = forall a. GenParser (Free ParserF Void xs ks a i)

newtype Carrier xs ks a i = Carrier {unCarrier :: ReaderT (HashMap (StableParserName xs ks i) (IMVar, GenParser xs ks i, IORef Bool), IMVar) IO (Free ParserF Void xs ks a i)}
preprocess :: Free ParserF Void '[] '[] a i -> Free ParserF Void '[] '[] a i
preprocess !p = unsafePerformIO (runReaderT (unCarrier (fold' absurd alg p)) (HashMap.empty, 0))
  where
    alg :: Free ParserF Void xs ks a i -> ParserF Carrier xs ks a i -> Carrier xs ks a i
    -- Force evaluation of p to ensure that the stableName is correct first time
    alg !p q = Carrier $ do
      !(seen, v) <- ask
      (StableName _name) <- lift (makeStableName p)
      let !name = StableParserName _name
      case HashMap.lookup name seen of
        Just (v', GenParser q, used) -> do lift (writeIORef used True)
                                           return $! (Op (Rec v' (coerce q)))
        Nothing -> mdo usedVar <- lift (newIORef False)
                       q' <- local (HashMap.insert name (v, GenParser q', usedVar) >< (+1)) (unCarrier $ subalg q)
                       used <- lift (readIORef usedVar)
                       if used then return $! (Op (Rec v q'))
                       else         return $! q'
    subalg :: ParserF Carrier xs ks a i -> Carrier xs ks a i
    subalg !(pf :<*>: px)     = Carrier (fmap optimise (liftA2 (:<*>:) (unCarrier pf) (unCarrier px)))
    subalg !(p :*>: q)        = Carrier (fmap optimise (liftA2 (:*>:)  (unCarrier p)  (unCarrier q)))
    subalg !(p :<*: q)        = Carrier (fmap optimise (liftA2 (:<*:)  (unCarrier p)  (unCarrier q)))
    subalg !(p :<|>: q)       = Carrier (fmap optimise (liftA2 (:<|>:) (unCarrier p)  (unCarrier q)))
    subalg !Empty             = Carrier (return (Op Empty))
    subalg !(Try n p)         = Carrier (fmap optimise (fmap (Try n) (unCarrier p)))
    subalg !(LookAhead p)     = Carrier (fmap optimise (fmap LookAhead (unCarrier p)))
    subalg !(NotFollowedBy p) = Carrier (fmap optimise (fmap NotFollowedBy (unCarrier p)))
    subalg !(Branch b p q)    = Carrier (fmap optimise (liftA3 Branch (unCarrier b) (unCarrier p) (unCarrier q)))
    subalg !(Match p fs qs)   = Carrier (fmap optimise (liftA3 Match (unCarrier p) (return fs) (traverse unCarrier qs)))
    subalg !(ChainPre op p)   = Carrier (liftA2 (\op p -> Op (ChainPre op p)) (unCarrier op) (unCarrier p))
    subalg !(ChainPost p op)  = Carrier (liftA2 (\p op -> Op (ChainPost p op)) (unCarrier p) (unCarrier op))
    subalg !(Debug name p)    = Carrier (fmap (Op . Debug name) (unCarrier p))
    subalg !(Pure x)          = Carrier (return (Op (Pure x)))
    subalg !(Satisfy f)       = Carrier (return (Op (Satisfy f)))

    (><) :: (a -> x) -> (b -> y) -> (a, b) -> (x, y)
    (f >< g) (x, y) = (f x, g y)

instance Eq (StableParserName xs ks i) where 
  (StableParserName n) == (StableParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable (StableParserName xs ks i) where
  hash (StableParserName n) = hashStableName (StableName n)
  hashWithSalt salt (StableParserName n) = hashWithSalt salt (StableName n)