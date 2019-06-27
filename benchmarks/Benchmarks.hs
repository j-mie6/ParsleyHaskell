{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             StandaloneDeriving,
             DeriveAnyClass,
             DeriveGeneric,
             DataKinds, 
             TypeOperators #-}
module Main where
import Criterion.Main  (Benchmark, bgroup, bench, whnf, nf, defaultMain, env)
import Control.DeepSeq (NFData(rnf))
import GHC.Generics    (Generic)
import Data.Text       (Text)
import Data.ByteString (ByteString)
import qualified ParsleyParsers
import qualified YodaParsers
import qualified ParsecParsers
import qualified MegaparsecParsers
import qualified AttoparsecParsers
import qualified NativeParsers
import qualified Parsley
import qualified Text.Yoda                  as Yoda
import qualified Text.Parsec                as Parsec
import qualified Text.Megaparsec            as Megaparsec
import qualified Data.Attoparsec.Text       as AttoparsecText
import qualified Data.Attoparsec.ByteString as AttoparsecByteString
import qualified Data.Text.IO
import qualified Data.ByteString
import CommonFunctions

main :: IO ()
--main = rnf (tailTestP (replicate 10000000 'a' ++ "b")) `seq` return ()
main = --{-
  defaultMain [ brainfuck
                 --, tailTest 
              ]--}-}

-- Tail Recursion Benchmark
tailTestP :: String -> Maybe Char
tailTestP = $$(Parsley.runParser ParsleyParsers.phiTest)

tailTest :: Benchmark
tailTest = bgroup "tail-rec" [ bench "tail-rec 0"      $ nf tailTestP (replicate 0 'a' ++ "b")
                             , bench "tail-rec 1"      $ nf tailTestP (replicate 1 'a' ++ "b")
                             , bench "tail-rec 10"     $ nf tailTestP (replicate 10 'a' ++ "b")
                             , bench "tail-rec 100"    $ nf tailTestP (replicate 100 'a' ++ "b")
                             , bench "tail-rec 1000"   $ nf tailTestP (replicate 1000 'a' ++ "b")
                             , bench "tail-rec 10,000" $ nf tailTestP (replicate 10000 'a' ++ "b")
                             ]

-- BrainFuck Benchmark
deriving instance Generic BrainFuckOp
deriving instance NFData BrainFuckOp

brainfuckParsleyS :: String -> Maybe [BrainFuckOp]
brainfuckParsleyS = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsleyT :: Text -> Maybe [BrainFuckOp]
brainfuckParsleyT = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsleyB :: ByteString -> Maybe [BrainFuckOp]
brainfuckParsleyB = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuck :: Benchmark
brainfuck =
  let bfTest :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe [BrainFuckOp]) -> Benchmark
      bfTest = benchmark ["inputs/helloworld.bf", "inputs/helloworld_golfed.bf", "inputs/compiler.bf"]
  in bgroup "Brainfuck"
       [ bfTest string     "Parsley (String)"     brainfuckParsleyS
       , bfTest text       "Parsley (Text)"       brainfuckParsleyT
       , bfTest bytestring "Parsley (ByteString)" brainfuckParsleyB
       , bfTest string     "Parsec (String)"      (parsecParseS ParsecParsers.brainfuck)
       , bfTest text       "Parsec (Text)"        (parsecParseT ParsecParsers.brainfuck)
       , bfTest string     "Mega (String)"        (megaParseS MegaparsecParsers.brainfuck)
       , bfTest text       "Mega (Text)"          (megaParseT MegaparsecParsers.brainfuck)
       , bfTest string     "Native"               NativeParsers.brainfuck
       ]

-- Utils
parsecParseS :: ParsecParsers.Parser String a -> String -> Maybe a
parsecParseS p = either (const Nothing) Just . Parsec.parse p ""

parsecParseT :: ParsecParsers.Parser Text a -> Text -> Maybe a
parsecParseT p = either (const Nothing) Just  . Parsec.parse p ""

megaParseS :: MegaparsecParsers.Parser String a -> String -> Maybe a
megaParseS = Megaparsec.parseMaybe

megaParseT :: MegaparsecParsers.Parser Text a -> Text -> Maybe a
megaParseT = Megaparsec.parseMaybe

string     :: FilePath -> IO String
string     = readFile
text       :: FilePath -> IO Text
text       = Data.Text.IO.readFile
bytestring :: FilePath -> IO ByteString
bytestring = Data.ByteString.readFile

benchmark :: (NFData a, NFData rep) => [FilePath] -> (FilePath -> IO rep) -> String -> (rep -> Maybe a) -> Benchmark
benchmark filenames load lib parser = env (traverse load filenames) (bgroup lib . (tasks filenames))
  where
    tasks filenames inputs = foldr (\f ts n -> bench f (nf parser (inputs !! n)) : ts (n+1)) (const []) filenames 0
