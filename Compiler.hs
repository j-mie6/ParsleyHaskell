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
preprocess !p = unsafePerformIO (runReaderT (unCarrier (fold' absurd findRecursion p)) (HashMap.empty, 0))

findRecursion :: Free ParserF Void xs ks a i -> ParserF Carrier xs ks a i -> Carrier xs ks a i
-- Force evaluation of p to ensure that the stableName is correct first time
findRecursion !p q = Carrier $ do
  !(seen, v) <- ask
  (StableName _name) <- lift (makeStableName p)
  let !name = StableParserName _name
  case HashMap.lookup name seen of
    Just (v', GenParser q, used) -> do lift (writeIORef used True)
                                       return $! (Op (Rec v' (coerce q)))
    Nothing -> mdo usedVar <- lift (newIORef False)
                   q' <- local (HashMap.insert name (v, GenParser q', usedVar) >< (+1)) (unCarrier $ postprocess q)
                   used <- lift (readIORef usedVar)
                   if used then return $! (Op (Rec v q'))
                   else         return $! q'

postprocess :: ParserF Carrier xs ks a i -> Carrier xs ks a i
postprocess !(pf :<*>: px)     = Carrier (fmap optimise (liftA2 (:<*>:) (unCarrier pf) (unCarrier px)))
postprocess !(p :*>: q)        = Carrier (fmap optimise (liftA2 (:*>:)  (unCarrier p)  (unCarrier q)))
postprocess !(p :<*: q)        = Carrier (fmap optimise (liftA2 (:<*:)  (unCarrier p)  (unCarrier q)))
postprocess !(p :<|>: q)       = Carrier (fmap optimise (liftA2 (:<|>:) (unCarrier p)  (unCarrier q)))
postprocess !Empty             = Carrier (return        (Op Empty))
postprocess !(Try n p)         = Carrier (fmap optimise (fmap (Try n) (unCarrier p)))
postprocess !(LookAhead p)     = Carrier (fmap optimise (fmap LookAhead (unCarrier p)))
postprocess !(NotFollowedBy p) = Carrier (fmap optimise (fmap NotFollowedBy (unCarrier p)))
postprocess !(Branch b p q)    = Carrier (fmap optimise (liftA3 Branch (unCarrier b) (unCarrier p) (unCarrier q)))
postprocess !(Match p fs qs)   = Carrier (fmap optimise (liftA3 Match (unCarrier p) (return fs) (traverse unCarrier qs)))
postprocess !(ChainPre op p)   = Carrier (fmap Op       (liftA2 ChainPre (unCarrier op) (unCarrier p)))
postprocess !(ChainPost p op)  = Carrier (fmap Op       (liftA2 ChainPost (unCarrier p) (unCarrier op)))
postprocess !(Debug name p)    = Carrier (fmap Op       (fmap (Debug name) (unCarrier p)))
postprocess !(Pure x)          = Carrier (return        (Op (Pure x)))
postprocess !(Satisfy f)       = Carrier (return        (Op (Satisfy f)))

(><) :: (a -> x) -> (b -> y) -> (a, b) -> (x, y)
(f >< g) (x, y) = (f x, g y)

showM :: Parser a -> String
showM = show . fst . compile

instance Eq (StableParserName xs ks i) where 
  (StableParserName n) == (StableParserName m) = eqStableName (StableName n) (StableName m)
instance Hashable (StableParserName xs ks i) where
  hash (StableParserName n) = hashStableName (StableName n)
  hashWithSalt salt (StableParserName n) = hashWithSalt salt (StableName n)