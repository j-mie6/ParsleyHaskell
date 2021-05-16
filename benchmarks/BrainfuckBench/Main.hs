{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             StandaloneDeriving,
             DeriveAnyClass,
             DeriveGeneric,
             TypeFamilies,
             UnboxedTuples,
             TypeApplications #-}
module Main where
import Criterion.Main         (Benchmark, bgroup, defaultMain)
import Control.DeepSeq        (NFData)
import GHC.Generics           (Generic)
import Data.ByteString        (ByteString)
import Parsley.InputExtras    (Text16(..), CharList(..))
--import Parsley.Internal.Verbose ()
import qualified BrainfuckBench.Parsley.Parser
import qualified BrainfuckBench.Parsec.Parser
import qualified BrainfuckBench.Megaparsec.Parser
import qualified BrainfuckBench.Attoparsec.Parser
import qualified BrainfuckBench.Handrolled.Parser
import qualified BrainfuckBench.Happy.Parser
import qualified Parsley
import qualified Data.ByteString.Lazy
import BrainfuckBench.Shared
import Shared.BenchmarkUtils

main :: IO ()
main = defaultMain [brainfuck]

deriving instance Generic BrainFuckOp
deriving instance NFData BrainFuckOp

brainfuckParsleyS :: String -> Maybe [BrainFuckOp]
brainfuckParsleyS = $$(Parsley.runParser BrainfuckBench.Parsley.Parser.brainfuck)

brainfuckParsleyT :: Text16 -> Maybe [BrainFuckOp]
brainfuckParsleyT = $$(Parsley.runParser BrainfuckBench.Parsley.Parser.brainfuck)

brainfuckParsleyB :: ByteString -> Maybe [BrainFuckOp]
brainfuckParsleyB = $$(Parsley.runParser BrainfuckBench.Parsley.Parser.brainfuck)

brainfuckParsleySS :: CharList -> Maybe [BrainFuckOp]
brainfuckParsleySS = $$(Parsley.runParser BrainfuckBench.Parsley.Parser.brainfuck)

brainfuckParsleyLB :: Data.ByteString.Lazy.ByteString -> Maybe [BrainFuckOp]
brainfuckParsleyLB = $$(Parsley.runParser BrainfuckBench.Parsley.Parser.brainfuck)

brainfuck :: Benchmark
brainfuck =
  let bfTest :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe [BrainFuckOp]) -> Benchmark
      bfTest = benchmark ["benchmarks/inputs/helloworld.bf", "benchmarks/inputs/helloworld_golfed.bf", "benchmarks/inputs/compiler.bf"]
  in bgroup "Brainfuck"
       [ {-bfTest string          "Parsley (Stream)"          (brainfuckParsleySS . CharList)
       ,-} bfTest string          "Happy"                     BrainfuckBench.Happy.Parser.brainfuck
       , bfTest string          "Parsley (String)"          brainfuckParsleyS
       , bfTest text            "Parsley (Text)"            (brainfuckParsleyT . Text16)
       --, bfTest bytestring      "Parsley (ByteString)"      brainfuckParsleyB
       --, bfTest lazy_bytestring "Parsley (Lazy ByteString)" brainfuckParsleyLB
       , bfTest string          "Parsec (String)"           (parsecParse BrainfuckBench.Parsec.Parser.brainfuck)
       , bfTest text            "Parsec (Text)"             (parsecParse BrainfuckBench.Parsec.Parser.brainfuck)
       , bfTest string          "Mega (String)"             (megaParse BrainfuckBench.Megaparsec.Parser.brainfuck)
       , bfTest text            "Mega (Text)"               (megaParse BrainfuckBench.Megaparsec.Parser.brainfuck)
       , bfTest text            "Atto (Text)"               (attoParse BrainfuckBench.Attoparsec.Parser.brainfuck)
       , bfTest string          "Handrolled"               BrainfuckBench.Handrolled.Parser.brainfuck
       ]