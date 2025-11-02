{-# LANGUAGE CPP #-}
{-|
Module      : Parsley.Internal.Common.THUtils
Description : Functions for low-level template haskell manipulation
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains some Template Haskell related functions for manipulating
template haskell as a lower, combinator-based, level.

@since 2.3.0.0
-}
module Parsley.Internal.Common.THUtils (eta, unsafeCodeCoerce, unTypeCode, debugTH) where

import Control.Arrow                 (first)
import Data.Generics                 (everything, mkQ)
import Language.Haskell.TH           (Q, Exp(AppE, LamE, VarE), Pat(VarP, BangP, SigP), unTypeCode, unsafeCodeCoerce, runQ)
import Parsley.Internal.Common.Utils (Code)
import GHC.IO                        (unsafePerformIO)

{-|
Given a function (of arbitrarily many arguments, but it must at /least/ have 1), eta-reduces
it to remove redundant arguments.

@since 2.3.0.0
-}
eta :: Code a -> Code a
eta = unsafeCodeCoerce . fmap checkEtaMulti . unTypeCode
  where
    --     \       x                  ->              x                                    = id
    checkEta (VarP x)                           (VarE x')  | x == x'                       = (Nothing, VarE 'id)
    --     \       x                  ->      f       x                                    = f
    checkEta (VarP x)                  (AppE qf (VarE x')) | x == x', checkOccurrence x qf = (Nothing, qf)
    --     \       (x ::    t)        ->      f       x                                    = f
    checkEta (SigP (VarP x) _)         (AppE qf (VarE x')) | x == x', checkOccurrence x qf = (Nothing, qf)
    --     \ (!           x)          ->      f       x                                    = f
    checkEta (BangP (VarP x))          (AppE qf (VarE x')) | x == x', checkOccurrence x qf = (Nothing, qf)
    --     \ (!            x ::    t) ->      f       x                                    = f
    checkEta (BangP (SigP (VarP x) _)) (AppE qf (VarE x')) | x == x', checkOccurrence x qf = (Nothing, qf)
    --     \ x -> body                                                                     = \ x -> body
    checkEta qarg qbody                                                                    = (Just qarg, qbody)

    checkOccurrence x body = everything (&&) (mkQ True (/= x)) body

    checkEtaMulti (LamE args body) = if null args' then body' else LamE args' body'
      where
        (args', body') = foldr (\arg (args, body) -> first (maybe args (: args)) (checkEta arg body))
                         ([], body)
                         args
    checkEtaMulti qf = qf

-- Debug: print TH AST at "pure" site
debugTH :: Q Exp -> a -> a
debugTH qexp result =
  unsafePerformIO $ do
    expr <- runQ qexp
    print expr
    return result