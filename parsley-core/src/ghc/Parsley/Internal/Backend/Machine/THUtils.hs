{-# LANGUAGE CPP #-}
module Parsley.Internal.Backend.Machine.THUtils (eta, unsafeCodeCoerce, unTypeCode) where

import GHC.Types                     (TYPE)
#if __GLASGOW_HASKELL__ < 900
import Language.Haskell.TH.Syntax    (Q, unTypeQ, unsafeTExpCoerce
#else
import Language.Haskell.TH.Syntax    (unTypeCode, unsafeCodeCoerce
#endif
                                     , Exp(AppE, LamE, VarE), Pat(VarP, BangP, SigP))
import Parsley.Internal.Common.Utils (Code)

eta :: forall r1 r2 (a :: TYPE r1) (b :: TYPE r2). Code (a -> b) -> Code (a -> b)
eta = unsafeCodeCoerce . fmap checkEta . unTypeCode
  where
    checkEta (LamE [VarP x] (AppE qf (VarE x')))                  | x == x' = qf
    checkEta (LamE [SigP (VarP x) _] (AppE qf (VarE x')))         | x == x' = qf
    checkEta (LamE [BangP (VarP x)] (AppE qf (VarE x')))          | x == x' = qf
    checkEta (LamE [BangP (SigP (VarP x) _)] (AppE qf (VarE x'))) | x == x' = qf
    checkEta qf                                                             = qf

#if __GLASGOW_HASKELL__ < 900
unsafeCodeCoerce :: Q Exp -> Code a
unsafeCodeCoerce = unsafeTExpCoerce

unTypeCode :: Code a -> Q Exp
unTypeCode = unTypeQ
#endif