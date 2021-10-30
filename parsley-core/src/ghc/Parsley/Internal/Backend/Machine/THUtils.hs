{-# LANGUAGE CPP #-}
{-|
Module      : Parsley.Internal.Backend.Machine.THUtils
Description : Functions for low-level template haskell manipulation
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains some Template Haskell related functions for manipulating
template haskell as a lower, combinator-based, level.

@since 1.7.0.0
-}
module Parsley.Internal.Backend.Machine.THUtils (eta, unsafeCodeCoerce, unTypeCode) where

import GHC.Types                     (TYPE)
import Control.Arrow                 (first)
import Language.Haskell.TH.Syntax    ( Exp(AppE, LamE, VarE), Pat(VarP, BangP, SigP)
#if __GLASGOW_HASKELL__ < 900
                                     , Q, unTypeQ, unsafeTExpCoerce
#else
                                     , unTypeCode, unsafeCodeCoerce
#endif
                                     )
import Parsley.Internal.Common.Utils (Code)

{-|
Given a function (of arbitrarily many arguments, but it must at /least/ have 1), eta-reduces
it to remove redundant arguments.

@since 1.7.0.0
-}
eta :: forall r1 r2 (a :: TYPE r1) (b :: TYPE r2). Code (a -> b) -> Code (a -> b)
eta = unsafeCodeCoerce . fmap checkEtaMulti . unTypeCode
  where
    --     \       x                  ->      f       x              = f
    checkEta (VarP x)                  (AppE qf (VarE x')) | x == x' = (Nothing, qf)
    --     \       (x ::    t)        ->      f       x              = f
    checkEta (SigP (VarP x) _)         (AppE qf (VarE x')) | x == x' = (Nothing, qf)
    --     \ (!           x)          ->      f       x              = f
    checkEta (BangP (VarP x))          (AppE qf (VarE x')) | x == x' = (Nothing, qf)
    --     \ (!            x ::    t) ->      f       x              = f
    checkEta (BangP (SigP (VarP x) _)) (AppE qf (VarE x')) | x == x' = (Nothing, qf)
    --     \ x -> body                                               = \ x -> body
    checkEta qarg qbody                                              = (Just qarg, qbody)

    checkEtaMulti (LamE args body)  = uncurry LamE $
      foldr (\arg (args, body) -> first (maybe args (: args)) (checkEta arg body))
            ([], body)
            args
    checkEtaMulti qf = qf

#if __GLASGOW_HASKELL__ < 900
unsafeCodeCoerce :: Q Exp -> Code a
unsafeCodeCoerce = unsafeTExpCoerce

unTypeCode :: Code a -> Q Exp
unTypeCode = unTypeQ
#endif