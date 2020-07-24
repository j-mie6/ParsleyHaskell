{-# LANGUAGE AllowAmbiguousTypes,
             ConstraintKinds,
             UnboxedTuples #-}
module Parsley.Core.Interface (module Parsley.Core.Interface) where

import Parsley.Common.Utils (Code)

{- This module defines the interface for Parsley - essentially, the
   abstraction to which it adheres. Any implementation of Parsley
   must be able to work with this interface, allowing them to interact
   with each other. -}
type Good input a r = a -> input -> r
type Bad input r = input -> r
type Interface input a = forall r.
     {-next-}    (input -> (# Char, input #))
  -> {-more-}    (input -> Bool)
  -> {-input-}   input
  -> {-good-}    Good input a r
  -> {-bad-}     Bad input r
  -> {-result -} r

{- Parsley makes no attempt to document what types you can use with it.
   That being said, the interface does permit the implementation to
   restrict the set of inputs that it allows. This does not constrain
   all implementations to a fixed set that is supported by the staged
   version. This is the aim of the `allowed` constraint. -}
newtype Parsley a = Parsley (forall allowed input. allowed input => Interface input a)
newtype QParsley x = QParsley (Code (Parsley x))