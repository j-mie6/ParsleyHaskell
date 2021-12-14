{-# LANGUAGE StandaloneDeriving, DeriveAnyClass, DeriveGeneric, TypeApplications, BangPatterns #-}
{-# OPTIONS_GHC -ddump-simpl -ddump-to-file #-}
module Main where

import Gauge
import BenchmarkUtils

import Parsley.Internal.Common.RangeSet (RangeSet)
import Data.Set (Set)
import Test.QuickCheck

import Control.Monad
import Control.DeepSeq

import GHC.Generics (Generic)

import qualified Parsley.Internal.Common.RangeSet as RangeSet
import qualified Data.Set as Set
import qualified Data.List as List

deriving instance (Generic a, NFData a) => NFData (RangeSet a)
deriving instance Generic a => Generic (RangeSet a)
deriving instance Generic Int
deriving instance Generic Word
deriving instance Generic Char

main :: IO ()
main = do
  xss <- forM [1..10] $ \n -> generate (vectorOf (n * 10) (chooseInt (0, n * 20)))
  condensedMain [
      fromListBench xss,
      rangeMemberBench,
      setMemberBench
    ]

fromListBench :: [[Int]] -> Benchmark
fromListBench xss =
  bgroup "fromList" (map (makeBench (show . length)
                                    [ ("Set", nf Set.fromList)
                                    , ("RangeSet", nf RangeSet.fromList)
                                    ]) xss)

pi4_1 :: (a, b, c, d) -> a
pi4_1 (x, _, _, _) = x

pi4_2 :: (a, b, c, d) -> b
pi4_2 (_, x, _, _) = x

pi4_3 :: (a, b, c, d) -> c
pi4_3 (_, _, x, _) = x

pi4_4 :: (a, b, c, d) -> d
pi4_4 (_, _, _, x) = x

xs1, xs2, xs3 :: [Word]
xs1 = [0,2..2048]
xs2 = List.delete 1536 (List.delete 512 (List.delete 1024 [0..2048]))
xs3 = [1, 2, 3, 5, 6, 7, 8, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 23, 25]
xs4 = ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['_']

ys1 = [0..2048]
ys2 = [0..27]
ys3 = ['\x00'..'\xff']

rangeMemberBench :: Benchmark
rangeMemberBench =
  env (return (RangeSet.fromList xs1,
               RangeSet.fromList xs2,
               RangeSet.fromList xs3,
               RangeSet.fromList xs4)) $ \t ->
    bgroup "RangeSet.member" [
      bench "Pathological" $ nf (f (pi4_1 t)) ys1,
      bench "4 way split" $ nf (f (pi4_2 t)) ys1,
      bench "Small" $ nf (f (pi4_3 t)) ys2,
      bench "alphaNum" $ nf (f (pi4_4 t)) ys3
    ]
  where
    f t = List.foldl' (\ !_ y -> RangeSet.member y t) False

setMemberBench :: Benchmark
setMemberBench =
  env (return (Set.fromList xs1,
               Set.fromList xs2,
               Set.fromList xs3,
               Set.fromList xs4)) $ \t ->
    bgroup "Set.member" [
      bench "Pathological" $ nf (f (pi4_1 t)) ys1,
      bench "4 way split" $ nf (f (pi4_2 t)) ys1,
      bench "Small" $ nf (f (pi4_3 t)) ys2,
      bench "alphaNum" $ nf (f (pi4_4 t)) ys3
    ]
  where
    f t = List.foldl' (\ !_ y -> Set.member y t) False

makeBench :: NFData a => (a -> String) -> [(String, a -> Benchmarkable)] -> a -> Benchmark
makeBench caseName cases x = env (return x) (\x ->
  bgroup (caseName x) (map (\(name, gen) -> bench name $ gen x) cases))