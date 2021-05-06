{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             TypeFamilies,
             UnboxedTuples,
             TypeApplications #-}
module Main where
import Criterion.Main         (Benchmark, bgroup, defaultMain)
import Control.DeepSeq        (NFData)
import Data.ByteString        (ByteString)
--import Parsley.Internal.Verbose ()
import qualified NandlangBench.Parsley.Parser
import qualified NandlangBench.Bison.Parser
import qualified Parsley
import Shared.BenchmarkUtils

main :: IO ()
main = defaultMain [nandlang]

nandParsleyB :: ByteString -> Maybe ()
nandParsleyB = $$(Parsley.runParser NandlangBench.Parsley.Parser.nandlang)

nandlang :: Benchmark
nandlang =
  let nandTest :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe ()) -> Benchmark
      nandTest = benchmark ["benchmarks/inputs/fibonacci.nand", "benchmarks/inputs/fizzbuzz.nand", "benchmarks/inputs/arrays.nand"]
  in bgroup "Nandlang"
       [ nandTest bytestring "Parsley" nandParsleyB
       , nandTest bytestring "Bison"   NandlangBench.Bison.Parser.nand ]