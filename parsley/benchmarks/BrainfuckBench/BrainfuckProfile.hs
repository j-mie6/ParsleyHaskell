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
--{-# OPTIONS_GHC -prof #-}
module Main where 

import Parsley hiding (pure)
import Data.ByteString     (ByteString)
import qualified Data.ByteString as BS
import Control.DeepSeq (deepseq,rnf,NFData)
import GHC.Generics        (Generic)
import Control.Monad (replicateM_)

import BrainfuckBench.Parsley.Parser (brainfuck, brainfuck')
import BrainfuckBench.Shared (BrainFuckOp(..))


deriving instance Generic BrainFuckOp
deriving instance NFData BrainFuckOp

parser :: ByteString -> Maybe [BrainFuckOp]
parser = $$(parse brainfuck')

main :: IO ()
main = do 
    let filename = "benchmarks/inputs/nonsense_big.bf"
    inp <- BS.readFile filename
    parser inp `deepseq` (pure ())
    
