{-# LANGUAGE MagicHash,
             TypeFamilies #-}
{-|
Module      : Parsley.Internal.Backend.Machine.Types.Base
Description : Base types representing core machine components
License     : BSD-3-Clause
Maintainer  : Jamie Willis
Stability   : experimental

This module contains the core types of components that make up
the underlying machinery for compiled code.

@since 1.4.0.0
-}
module Parsley.Internal.Backend.Machine.Types.Base (
    module Parsley.Internal.Backend.Machine.Types.Base
  ) where

import Control.Monad.ST                          (ST)
import Data.STRef                                (STRef)
import Data.Kind                                 (Type)
import GHC.Prim                                  (Int#)
import Parsley.Internal.Backend.Machine.InputRep (Rep)

type Line = Int#
type Col = Int#

{-|
@Handler#@ represents the functions that handle failure within a
parser. For most of their life, handlers are represented as
`Parsley.Internal.Backend.Machine.Types.Statics.StaHandler`,
but @Handler#@ is used at the boundaries, such as for recursion.

@since 1.4.0.0
-}
type Handler# s o a =  Int#           -- ^ The current line
                    -> Int#           -- ^ The current column
                    -> Rep o          -- ^ The current input on failure
                    -> ST s (Maybe a)

{-|
@Cont#@ represents return continuation from recursive parsers. They
feed back their result @x@ back to the caller as well as the updated input.

@since 1.4.0.0
-}
type Cont# s o a x =  x              -- ^ The value to be returned to the caller
                   -> Int#           -- ^ The current line
                   -> Int#           -- ^ The current column
                   -> Rep o          -- ^ The new input after the call is executed
                   -> ST s (Maybe a)

{-|
@Subroutine#@ represents top-level parsers, which require a return continuation,
input, an error handler in order to produce (or contribute to) a result of type @a@.

@since 1.4.0.0
-}
type Subroutine# s o a x =  Cont# s o a x  -- ^ What to do when this parser returns
                         -> Handler# s o a -- ^ How to handle failure within the call
                         -> Int#           -- ^ The current line
                         -> Int#           -- ^ The current column
                         -> Rep o          -- ^ The input on entry to the call
                         -> ST s (Maybe a)

{-|
A @Func@ is a `Subroutine#` augmented with extra arguments with which to handle over
the required free-registers of the parser. These are registers that are not created
by the parser, but are used to execute it.

@since 1.4.0.0
-}
type family Func (rs :: [Type]) s o a x where
  Func '[] s o a x      = Subroutine# s o a x
  Func (r : rs) s o a x = STRef s r -> Func rs s o a x