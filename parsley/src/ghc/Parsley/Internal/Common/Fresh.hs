{-# LANGUAGE FunctionalDependencies,
             GeneralisedNewtypeDeriving,
             DerivingStrategies,
             UndecidableInstances #-}
module Parsley.Internal.Common.Fresh (
    VFreshT, HFreshT, VFresh, HFresh,
    runFreshT, runFresh,
    evalFreshT, evalFresh,
    execFreshT, execFresh,
    MonadFresh(..), construct, mapVFreshT,
    RunFreshT
  ) where

import Control.Applicative        (liftA2)
import Control.Monad.Fix          (MonadFix(..))
import Control.Monad.Identity     (Identity, runIdentity)
import Control.Monad.Reader.Class (MonadReader(..))
import Control.Monad.State.Class  (MonadState(..))
import Control.Monad.Trans        (MonadTrans(..), MonadIO(..))

-- Fresh operations
class Monad m => MonadFresh x m | m -> x where
  newVar :: m x
  newScope :: m a -> m a

construct :: MonadFresh x m => (x -> a) -> m a
construct f = fmap f newVar

mapVFreshT :: (m (a, x, x) -> n (b, x, x)) -> VFreshT x m a -> VFreshT x n b
mapVFreshT f m = vFreshT (\cur max -> f (unVFreshT m cur max))

class (Monad n, Monad m) => RunFreshT x n m | m -> x, m -> n where
  runFreshT :: m a -> x -> n (a, x)

evalFreshT :: RunFreshT x n m => m a -> x -> n a
evalFreshT m init = fst <$> runFreshT m init

execFreshT :: RunFreshT x n m => m a -> x -> n x
execFreshT m init = snd <$> runFreshT m init

-- Fresh type
type HFresh x = HFreshT x Identity
type VFresh x = VFreshT x Identity
-- TODO Nominals
newtype VFreshT x m a = VFreshT (FreshT x m a) deriving newtype (Functor, Applicative, Monad, MonadFix, MonadTrans, MonadIO, MonadReader r, MonadState s, RunFreshT x m)
newtype HFreshT x m a = HFreshT (FreshT x m a) deriving newtype (Functor, Applicative, Monad, MonadFix, MonadTrans, MonadIO, MonadReader r, MonadState s, RunFreshT x m)
newtype FreshT x m a = FreshT {unFreshT :: x -> x -> m (a, x, x)}

instance Monad n => RunFreshT x n (FreshT x n) where
  runFreshT k init =
    do (x, _, max) <- unFreshT k init init
       return $! (x, max)

runFresh :: RunFreshT x Identity m => m a -> x -> (a, x)
runFresh mx = runIdentity . runFreshT mx

evalFresh :: RunFreshT x Identity m => m a -> x -> a
evalFresh mx = runIdentity . evalFreshT mx

execFresh :: RunFreshT x Identity m => m a -> x -> x
execFresh mx = runIdentity . execFreshT mx

vFreshT :: (x -> x -> m (a, x, x)) -> VFreshT x m a
vFreshT = VFreshT . FreshT

unVFreshT :: VFreshT x m a -> x -> x -> m (a, x, x)
unVFreshT (VFreshT f) = unFreshT f

hFreshT :: (x -> x -> m (a, x, x)) -> HFreshT x m a
hFreshT = HFreshT . FreshT

unHFreshT :: HFreshT x m a -> x -> x -> m (a, x, x)
unHFreshT (HFreshT f) = unFreshT f

instance Functor f => Functor (FreshT x f) where
  {-# INLINE fmap #-}
  fmap f (FreshT k) = FreshT (\cur max -> fmap (\(x, cur', max') -> (f x, cur', max')) (k cur max))

instance Monad m => Applicative (FreshT x m) where
  {-# INLINE pure #-}
  pure x = FreshT (\cur max -> pure (x, cur, max))
  {-# INLINE liftA2 #-}
  liftA2 f (FreshT mx) (FreshT my) = FreshT (\cur max ->
    do (x, cur', max') <- mx cur max
       (y, cur'', max'') <- my cur' max'
       return $! (f x y, cur'', max''))

instance Monad m => Monad (FreshT x m) where
  {-# INLINE return #-}
  return = pure
  {-# INLINE (>>=) #-}
  (FreshT mx) >>= f = FreshT (\cur max ->
    do (x, cur', max') <- mx cur max
       unFreshT (f x) cur' max')

instance MonadFix m => MonadFix (FreshT x m) where
  {-# INLINE mfix #-}
  mfix f = FreshT (\cur max -> mfix (\ ~(x, _, _) -> unFreshT (f x) cur max))

instance MonadTrans (FreshT x) where
  {-# INLINE lift #-}
  lift m = FreshT (\cur max ->
    do x <- m
       return (x, cur, max))

instance (Monad m, Ord x, Enum x) => MonadFresh x (VFreshT x m) where
  newVar = vFreshT (\cur m -> return (cur, cur, max m cur))
  newScope scoped = vFreshT (\cur max ->
    do (x, _, max') <- unVFreshT scoped (succ cur) max
       return $! (x, cur, max'))

instance (Monad m, Ord x, Enum x) => MonadFresh x (HFreshT x m) where
  newVar = hFreshT (\cur m -> return (cur, succ cur, max m cur))
  newScope scoped = hFreshT (\cur max ->
    do (x, _, max') <- unHFreshT scoped cur max
       return $! (x, cur, max'))

instance MonadIO m => MonadIO (FreshT x m) where liftIO = lift . liftIO
instance MonadReader r m => MonadReader r (FreshT x m) where
  ask = lift ask
  local f m = FreshT (\cur next -> local f (unFreshT m cur next))
instance MonadState s m => MonadState s (FreshT x m) where
  get = lift get
  put = lift . put