{-# LANGUAGE MultiParamTypeClasses #-}
module Parsley.Internal.Trace (Trace, trace, traceShow) where

class Trace where
  trace :: String -> a -> a

traceShow :: (Trace, Show a) => a -> a
traceShow = show >>= trace
