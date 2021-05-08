{-# LANGUAGE DeriveFunctor,
             MultiParamTypeClasses,
             DerivingStrategies,
             CPP #-}
module Parsley.Internal.Common.State (
    State, StateT,
    runState, evalState, execState,
    runStateT, evalStateT, execStateT,
    module Control.Monad.State.Class
  ) where

import Control.Applicative       (liftA2, Alternative(..))
#if __GLASGOW_HASKELL__ < 808
import Control.Monad.Fail        (MonadFail(..))
#endif
import Control.Monad.Fix         (MonadFix(..))
import Control.Monad.Identity    (Identity, runIdentity)
import Control.Monad.State.Class
import Control.Monad.Trans       (MonadTrans(..), MonadIO(..))

#if __GLASGOW_HASKELL__ < 808
import qualified Control.Monad.Fail as Fail (MonadFail(fail))
#endif

type State s = StateT s Identity
{-# INLINE runState #-}
runState :: State s a -> s -> (a, s)
runState mx = runIdentity . runStateT mx

{-# INLINE evalState #-}
evalState :: State s a -> s -> a
evalState mx = runIdentity . evalStateT mx

{-# INLINE execState #-}
execState :: State s a -> s -> s
execState mx = runIdentity . execStateT mx

newtype StateT s m a = StateT {unStateT :: forall r. s -> (a -> s -> m r) -> m r} deriving stock Functor

{-# INLINE runStateT #-}
runStateT :: Monad m => StateT s m a -> s -> m (a, s)
runStateT (StateT f) s = f s (curry return)

{-# INLINE evalStateT #-}
evalStateT :: Monad m => StateT s m a -> s -> m a
evalStateT (StateT f) s = f s (const . return)

{-# INLINE execStateT #-}
execStateT :: Monad m => StateT s m a -> s -> m s
execStateT (StateT f) s = f s (const return)

instance Applicative (StateT s m) where
  {-# INLINE pure #-}
  pure x = StateT (flip ($ x))
  {-# INLINE liftA2 #-}
  liftA2 f (StateT mx) (StateT my) = StateT (\s k -> mx s (\x s' -> my s' (\y s'' -> k (f x y) s'')))

instance Monad (StateT s m) where
  {-# INLINE return #-}
  return = pure
  {-# INLINE (>>=) #-}
  StateT mx >>= f = StateT (\s k -> mx s (\x s' -> unStateT (f x) s' k))

instance MonadFix m => MonadFix (StateT s m) where
  {-# INLINE mfix #-}
  mfix f = StateT (\s k -> mfix (\ ~(x, _) -> runStateT (f x) s) >>= uncurry k)

instance MonadTrans (StateT s) where
  {-# INLINE lift #-}
  lift m = StateT (\s k -> m >>= (`k` s))

instance MonadIO m => MonadIO (StateT s m) where liftIO = lift . liftIO

instance MonadFail m => MonadFail (StateT s m) where
#if __GLASGOW_HASKELL__ < 808
  fail msg = StateT (\_ _ -> Fail.fail msg)
#else
  fail msg = StateT (\_ _ -> fail msg)
#endif

instance Alternative m => Alternative (StateT s m) where
  empty = StateT (\_ _ -> empty)
  StateT mx <|> StateT my = StateT (\s k -> mx s k <|> my s k)

instance MonadState s (StateT s m) where
  get = StateT (\s k -> k s s)
  put s = StateT (\_ k -> k () s)