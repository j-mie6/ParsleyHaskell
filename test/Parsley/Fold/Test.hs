{-# LANGUAGE TemplateHaskell, UnboxedTuples #-}
module Parsley.Fold.Test where
import Test.Tasty
import Test.Tasty.HUnit

import Prelude hiding ()
import Parsley (runParser, code)

tests :: TestTree
tests = testGroup "Fold" [ chainPreTests
                         , chainPostTests
                         , pfoldrTests
                         , pfoldlTests
                         , chainlTests
                         , chainrTests
                         , manyTests
                         , skipManyTests
                         , sepByTests
                         , endByTests
                         , sepEndByTests]

chainPreTests :: TestTree
chainPreTests = testGroup "chainPre should" [] -- chainPre

chainPostTests :: TestTree
chainPostTests = testGroup "chainPost should" [] -- chainPost

pfoldrTests :: TestTree
pfoldrTests = testGroup "pfoldr should" [] -- pfoldr pfoldr1

pfoldlTests :: TestTree
pfoldlTests = testGroup "pfoldl should" [] -- pfoldl pfoldl1

chainlTests :: TestTree
chainlTests = testGroup "chainl should" [] -- chainl1' chainl1 chainl

chainrTests :: TestTree
chainrTests = testGroup "chainr should" [] -- chainr1' chainr1 chainr

manyTests :: TestTree
manyTests = testGroup "many should" [] -- many manyN some

skipManyTests :: TestTree
skipManyTests = testGroup "skipMany should" [] -- skipMany skipManyN skipSome

sepByTests :: TestTree
sepByTests = testGroup "sepBy should" [] -- sepBy sepBy1

endByTests :: TestTree
endByTests = testGroup "endBy should" [] -- endBy endBy1

sepEndByTests :: TestTree
sepEndByTests = testGroup "sepEndBy should" [] -- sepEndBy sepEndBy1