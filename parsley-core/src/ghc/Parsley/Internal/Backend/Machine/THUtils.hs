{-# LANGUAGE CPP #-}
module Parsley.Internal.Backend.Machine.THUtils (eta, unsafeCodeCoerce, unTypeCode) where

import GHC.Types                     (TYPE)
#if __GLASGOW_HASKELL__ < 900
import Language.Haskell.TH.Syntax    (Q, unTypeQ, unsafeTExpCoerce, Exp(AppE, LamE, VarE), Pat(VarP, BangP, SigP))
#else
import Language.Haskell.TH.Syntax    (unTypeCode, unsafeCodeCoerce, Exp(AppE, LamE, VarE), Pat(VarP, BangP, SigP))
#endif
import Parsley.Internal.Common.Utils (Code)

import Debug.Trace (trace)

eta :: forall r1 r2 (a :: TYPE r1) (b :: TYPE r2). Code (a -> b) -> Code (a -> b)
eta = unsafeCodeCoerce . fmap checkEta . unTypeCode
  where
    checkEta (LamE [VarP x] (AppE qf (VarE x')))                  | x == x' = trace "reduced non-bang" qf
    checkEta (LamE [SigP (VarP x) _] (AppE qf (VarE x')))         | x == x' = trace "reduced non-bang (ascript)" qf
    checkEta (LamE [BangP (VarP x)] (AppE qf (VarE x')))          | x == x' = trace "reduced bang" qf
    checkEta (LamE [BangP (SigP (VarP x) _)] (AppE qf (VarE x'))) | x == x' = trace "reduced bang (ascript)" qf
    checkEta qf                                                             = trace ("not reduced" ++ show qf) qf

#if __GLASGOW_HASKELL__ < 900
unsafeCodeCoerce :: Q Exp -> Code a
unsafeCodeCoerce = unsafeTExpCoerce

unTypeCode :: Code a -> Q Exp
unTypeCode = unTypeQ
#endif