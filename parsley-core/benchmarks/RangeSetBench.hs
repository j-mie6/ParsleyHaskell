{-# LANGUAGE StandaloneDeriving, DeriveAnyClass, DeriveGeneric, TypeApplications, BangPatterns, TemplateHaskell #-}
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
      rangeFromList,
      fromListBench xss,
      rangeMemberBench,
      setMemberBench
    ]

rangeFromList :: Benchmark
rangeFromList =
  env (return (xs1, xs2, xs3, xs4)) $ \xs ->bgroup "RangeSet.fromList" [
      bench "Pathological" $ nf RangeSet.fromList (pi4_1 xs),
      bench "4 way split" $ nf RangeSet.fromList (pi4_2 xs),
      bench "Small" $ nf RangeSet.fromList (pi4_3 xs),
      bench "alphaNum" $ nf RangeSet.fromList (pi4_4 xs)
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
    bgroup "RangeSet" [
      bgroup "member" [
        bench "Pathological" $ nf (f ys1) (pi4_1 t),
        bench "4 way split" $ nf (f ys1) (pi4_2 t),
        bench "Small" $ nf (f ys2) (pi4_3 t),
        bench "alphaNum" $ nf (f ys3) (pi4_4 t)
      ],
      bgroup "delete" [
        bench "Pathological" $ nf (g ys1) (pi4_1 t),
        bench "4 way split" $ nf (g ys1) (pi4_2 t),
        bench "Small" $ nf (g ys2) (pi4_3 t),
        bench "alphaNum" $ nf (g ys3) (pi4_4 t)
      ]
    ]
  where
    f ys t = List.foldl' (\ !_ y -> RangeSet.member y t) False ys
    g ys t = List.foldl' (\ !t y -> RangeSet.delete y t) t ys

setMemberBench :: Benchmark
setMemberBench =
  env (return (Set.fromList xs1,
               Set.fromList xs2,
               Set.fromList xs3,
               Set.fromList xs4)) $ \t ->
    bgroup "Set" [
            bgroup "member" [
        bench "Pathological" $ nf (f ys1) (pi4_1 t),
        bench "4 way split" $ nf (f ys1) (pi4_2 t),
        bench "Small" $ nf (f ys2) (pi4_3 t),
        bench "alphaNum" $ nf (f ys3) (pi4_4 t)
      ],
      bgroup "delete" [
        bench "Pathological" $ nf (g ys1) (pi4_1 t),
        bench "4 way split" $ nf (g ys1) (pi4_2 t),
        bench "Small" $ nf (g ys2) (pi4_3 t),
        bench "alphaNum" $ nf (g ys3) (pi4_4 t)
      ]
    ]
  where
    f ys t = List.foldl' (\ !_ y -> Set.member y t) False ys
    g ys t = List.foldl' (\ !t y -> Set.delete y t) t ys

makeBench :: NFData a => (a -> String) -> [(String, a -> Benchmarkable)] -> a -> Benchmark
makeBench caseName cases x = env (return x) (\x ->
  bgroup (caseName x) (map (\(name, gen) -> bench name $ gen x) cases))