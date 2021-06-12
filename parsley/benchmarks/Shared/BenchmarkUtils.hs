{-# LANGUAGE TypeFamilies
           , FlexibleContexts #-}
module Shared.BenchmarkUtils where

import Criterion.Main         (Benchmark, bgroup, bench, nf, defaultMain, env)
import Control.DeepSeq        (NFData)
import Control.Monad.Identity (Identity)
import Data.Text              (Text)
import Data.ByteString        (ByteString)
import qualified Text.Parsec                as Parsec
import qualified Text.Megaparsec            as Megaparsec
import qualified Data.Attoparsec.Text       as Attoparsec
import qualified Data.Text.IO
import qualified Data.ByteString
import qualified Data.ByteString.Lazy
import qualified Shared.Parsec.Extended
import qualified Shared.Megaparsec.Extended

parsecParse :: Parsec.Stream s Identity Char => Shared.Parsec.Extended.Parser s a -> s -> Maybe a
parsecParse p = either (const Nothing) Just  . Parsec.parse p ""

megaParse :: (Megaparsec.Stream s, Megaparsec.Token s ~ Char) => Shared.Megaparsec.Extended.Parser s a -> s -> Maybe a
megaParse = Megaparsec.parseMaybe

attoParse :: Attoparsec.Parser a -> Text -> Maybe a
attoParse p = Attoparsec.maybeResult . Attoparsec.parse p

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