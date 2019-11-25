{-# LANGUAGE TemplateHaskell,
             ScopedTypeVariables,
             StandaloneDeriving,
             DeriveAnyClass,
             DeriveGeneric,
             DataKinds, 
             TypeOperators,
             TypeFamilies,
             FlexibleContexts,
             NumericUnderscores,
             UnboxedTuples #-}
module Main where
import Criterion.Main         (Benchmark, bgroup, bench, whnf, nf, defaultMain, env)
import Control.DeepSeq        (NFData(rnf))
import GHC.Generics           (Generic)
import Control.Monad.Identity (Identity)
import Data.Text              (Text)
import Data.ByteString        (ByteString)
import Parsley                (Text16(..), CharList(..), Stream)
import qualified ParsleyParsers
import qualified YodaParsers
import qualified ParsecParsers
import qualified MegaparsecParsers
import qualified AttoparsecParsers
import qualified NativeParsers
import qualified HappyParsers
import qualified Parsley
import qualified Text.Yoda                  as Yoda
import qualified Text.Parsec                as Parsec
import qualified Text.Megaparsec            as Megaparsec
import qualified Data.Attoparsec.Text       as AttoparsecText
import qualified Data.Attoparsec.ByteString as AttoparsecByteString
import qualified Data.Text.IO
import qualified Data.ByteString
import qualified Data.ByteString.Lazy
import qualified Data.ByteString.Char8 (pack)
import CommonFunctions

main :: IO ()
main =
  defaultMain [ regex
              , brainfuck
              , tailTest 
              ]

as :: Data.ByteString.Lazy.ByteString -> Maybe ()
as = $$(Parsley.runParser (Parsley.skipMany (Parsley.char 'a') Parsley.<* Parsley.eof))

streams :: Data.ByteString.Lazy.ByteString -> Maybe String
streams = $$(Parsley.runParser (Parsley.token "abc" Parsley.<* Parsley.eof))

-- Tail Recursion Benchmark
tailTestP :: String -> Maybe Char
tailTestP = $$(Parsley.runParser ParsleyParsers.phiTest)

tailTest :: Benchmark
tailTest = bgroup "tail-rec" [ bench "tail-rec 0"      $ nf (tailTestP) (replicate 0 'a' ++ "b")
                             , bench "tail-rec 1"      $ nf (tailTestP) (replicate 1 'a' ++ "b")
                             , bench "tail-rec 10"     $ nf (tailTestP) (replicate 10 'a' ++ "b")
                             , bench "tail-rec 100"    $ nf (tailTestP) (replicate 100 'a' ++ "b")
                             , bench "tail-rec 1000"   $ nf (tailTestP) (replicate 1000 'a' ++ "b")
                             , bench "tail-rec 10,000" $ nf (tailTestP) (replicate 10_000 'a' ++ "b")
                             ]

-- Regex Wars 2019
regexP :: ByteString -> Maybe Bool
regexP = $$(Parsley.runParser ParsleyParsers.regex)

regex :: Benchmark
regex = env (return ( Data.ByteString.Char8.pack (concat (replicate 1000 "ab"))
                    , Data.ByteString.Char8.pack (concat (replicate 10_000 "ab"))
                    , Data.ByteString.Char8.pack (concat (replicate 100_000 "ab")))) $ \(~(i1, i2, i3)) -> 
          bgroup "regex" [ bench "regex 1000" $ nf regexP i1
                         , bench "regex 10000" $ nf regexP i2
                         , bench "regex 100000" $ nf regexP i3
                         ]

-- BrainFuck Benchmark
deriving instance Generic BrainFuckOp
deriving instance NFData BrainFuckOp

brainfuckParsleyS :: String -> Maybe [BrainFuckOp]
brainfuckParsleyS = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsleyT :: Text16 -> Maybe [BrainFuckOp]
brainfuckParsleyT = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsleyB :: ByteString -> Maybe [BrainFuckOp]
brainfuckParsleyB = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsleySS :: CharList -> Maybe [BrainFuckOp]
brainfuckParsleySS = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuckParsleyLB :: Data.ByteString.Lazy.ByteString -> Maybe [BrainFuckOp]
brainfuckParsleyLB = $$(Parsley.runParser ParsleyParsers.brainfuck)

brainfuck :: Benchmark
brainfuck =
  let bfTest :: NFData rep => (FilePath -> IO rep) -> String -> (rep -> Maybe [BrainFuckOp]) -> Benchmark
      bfTest = benchmark ["inputs/helloworld.bf", "inputs/helloworld_golfed.bf", "inputs/compiler.bf"]
  in bgroup "Brainfuck"
       [ bfTest string          "Parsley (Stream)"          (brainfuckParsleySS . CharList)
       , bfTest string          "Happy"                     HappyParsers.brainfuck
       , bfTest string          "Parsley (String)"          brainfuckParsleyS
       , bfTest text            "Parsley (Text)"            (brainfuckParsleyT . Text16)
       , bfTest bytestring      "Parsley (ByteString)"      brainfuckParsleyB
       , bfTest lazy_bytestring "Parsley (Lazy ByteString)" brainfuckParsleyLB
       , bfTest string          "Parsec (String)"           (parsecParse ParsecParsers.brainfuck)
       , bfTest text            "Parsec (Text)"             (parsecParse ParsecParsers.brainfuck)
       , bfTest string          "Mega (String)"             (megaParse MegaparsecParsers.brainfuck)
       , bfTest text            "Mega (Text)"               (megaParse MegaparsecParsers.brainfuck)
       , bfTest string          "Native"                    NativeParsers.brainfuck
       ]

-- Utils
parsecParse :: Parsec.Stream s Identity Char => ParsecParsers.Parser s a -> s -> Maybe a
parsecParse p = either (const Nothing) Just  . Parsec.parse p ""

megaParse :: (Megaparsec.Stream s, Megaparsec.Token s ~ Char) => MegaparsecParsers.Parser s a -> s -> Maybe a
megaParse = Megaparsec.parseMaybe

string          :: FilePath -> IO String
string          = readFile
text            :: FilePath -> IO Text
text            = Data.Text.IO.readFile
bytestring      :: FilePath -> IO ByteString
bytestring      = Data.ByteString.readFile
lazy_bytestring :: FilePath -> IO Data.ByteString.Lazy.ByteString
lazy_bytestring = Data.ByteString.Lazy.readFile

benchmark :: (NFData a, NFData rep) => [FilePath] -> (FilePath -> IO rep) -> String -> (rep -> Maybe a) -> Benchmark
benchmark filenames load lib parser = env (traverse load filenames) (bgroup lib . (tasks filenames))
  where
    tasks filenames inputs = foldr (\f ts n -> bench f (nf parser (inputs !! n)) : ts (n+1)) (const []) filenames 0
