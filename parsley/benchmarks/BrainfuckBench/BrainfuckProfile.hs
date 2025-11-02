{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             StandaloneDeriving,
             DeriveAnyClass,
             DeriveGeneric,
             TypeFamilies,
             UnboxedTuples,
             OverloadedStrings,
             TypeApplications, 
             FlexibleContexts #-}
module Main where

import Parsley hiding (pure)

import Data.ByteString               (ByteString)
import GHC.Generics                  (Generic)
import Control.DeepSeq               (deepseq,rnf,NFData, rwhnf)
import Control.Monad                 (replicateM_)
import BrainfuckBench.Parsley.Parser (brainfuck, brainfuck')
import BrainfuckBench.Shared         (BrainFuckOp(..))

import qualified Data.ByteString as BS


deriving instance Generic BrainFuckOp

parser :: ByteString -> Maybe [BrainFuckOp]
parser = $$(parse brainfuck')

main :: IO ()
main = do 
    let filename = "benchmarks/inputs/nonsense_big.bf"
    inp <- BS.readFile filename
    parser inp `deepseq` (pure ())
    
