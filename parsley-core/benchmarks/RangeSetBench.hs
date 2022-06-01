{-# LANGUAGE StandaloneDeriving, DeriveAnyClass, DeriveGeneric, BangPatterns, TypeApplications, ScopedTypeVariables, BlockArguments, AllowAmbiguousTypes, CPP #-}
{-# OPTIONS_GHC -ddump-simpl -ddump-to-file #-}
module Main where

-- #define USE_ENUM

import Gauge
import BenchmarkUtils

import Parsley.Internal.Common.RangeSet (RangeSet)
#ifdef USE_ENUM
import Data.EnumSet (Set)
#else
import Data.Set (Set)
#endif
import Test.QuickCheck

import Control.Monad
import Control.DeepSeq

import Data.Array.IO

import Data.List
import Data.Maybe

import Data.Bifunctor (bimap)

import Control.Selective (whileS)

import GHC.Generics (Generic)

import qualified Parsley.Internal.Common.RangeSet as RangeSet
#ifdef USE_ENUM
import qualified Data.EnumSet as Set
#else
import qualified Data.Set as Set
#endif
import qualified Data.List as List
import GHC.Real (Fractional, (%))

deriving instance (Generic a, NFData a) => NFData (RangeSet a)
deriving instance Generic a => Generic (RangeSet a)
deriving instance Generic Int
deriving instance Generic Word
deriving instance Generic Char

main :: IO ()
main = do
  xss <- forM [1..10] $ \n -> generate (vectorOf (n * 10) (chooseInt (0, n * 20)))
  (ratios, bins) <- unzip <$> fillBins @Word
  --print bins

  condensedMain [
      contiguityBench ratios bins,
      rangeFromList,
      rangeMemberDeleteBench,
      rangeUnionBench,
      rangeDiffBench,
      rangeIntersectBench,
      setMemberDeleteBench,
      fromListBench xss
    ]

rangeFromList :: Benchmark
rangeFromList =
  env (return (xs1, xs2, xs3, xs4)) $ \xs -> bgroup "RangeSet.fromList" [
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

rangeMemberDeleteBench :: Benchmark
rangeMemberDeleteBench =
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

setMemberDeleteBench :: Benchmark
setMemberDeleteBench =
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

zs1, zs2, zs3, zs4 :: RangeSet Word
zs1 = RangeSet.fromRanges [(0, 50), (100, 150), (200, 250), (300, 350), (400, 450), (475, 500)]
zs2 = RangeSet.fromRanges [(25, 75), (125, 175), (225, 275), (325, 375), (425, 475), (485, 500)]
zs3 = RangeSet.fromRanges [(51, 99), (151, 199), (251, 299), (351, 399), (451, 474)]
zs4 = RangeSet.fromRanges [(0, 125), (140, 222), (230, 240), (310, 351), (373, 381), (462, 491)]

rangeUnionBench :: Benchmark
rangeUnionBench =
  env (return (zs1, zs2, zs3, zs4)) $ \t -> bgroup "union" [
      bench "same" $ nf (RangeSet.union (pi4_1 t)) (pi4_1 t),
      bench "overlaps" $ nf (RangeSet.union (pi4_1 t)) (pi4_2 t),
      bench "disjoint" $ nf (RangeSet.union (pi4_1 t)) (pi4_3 t),
      bench "messy" $ nf (RangeSet.union (pi4_1 t)) (pi4_4 t)
  ]

rangeDiffBench :: Benchmark
rangeDiffBench =
  env (return (zs1, zs2, zs3, zs4)) $ \t -> bgroup "difference" [
      bench "same" $ nf (RangeSet.difference (pi4_1 t)) (pi4_1 t),
      bench "overlaps" $ nf (RangeSet.difference (pi4_1 t)) (pi4_2 t),
      bench "disjoint" $ nf (RangeSet.difference (pi4_1 t)) (pi4_3 t),
      bench "messy" $ nf (RangeSet.difference (pi4_1 t)) (pi4_4 t)
  ]

rangeIntersectBench :: Benchmark
rangeIntersectBench =
  env (return (zs1, zs2, zs3, zs4)) $ \t -> bgroup "intersection" [
      bench "same" $ nf (RangeSet.intersection (pi4_1 t)) (pi4_1 t),
      bench "overlaps" $ nf (RangeSet.intersection (pi4_1 t)) (pi4_2 t),
      bench "disjoint" $ nf (RangeSet.intersection (pi4_1 t)) (pi4_3 t),
      bench "messy" $ nf (RangeSet.intersection (pi4_1 t)) (pi4_4 t)
  ]

-- Density benchmark
-- This benchmark generates bunches of random data with a contiguity measure of 0.0 to 1.0
-- this is defined as $1 - m/n$ where $n$ is the number of elements in the set and $m$ the number
-- of ranges. For each of these random sets, each element is queried in turn, and the average
-- time is taken. This comparison is done between the rangeset and the data.set

contiguity :: Enum a => RangeSet a -> Rational
contiguity s = 1 - fromIntegral (RangeSet.sizeRanges s) % fromIntegral (RangeSet.size s)

numContBins :: Int
numContBins = 20

binSize :: Int
binSize = 50

approxSetSize :: Int
approxSetSize = 100

maxElem :: Enum a => a
maxElem = toEnum (approxSetSize - 1)

minElem :: Enum a => a
minElem = toEnum 0

elems :: forall a. Enum a => [a]
elems = [minElem @a .. maxElem @a]

fillBins :: forall a. (Ord a, Enum a) => IO [(Rational, [(RangeSet a, Set a, [a])])]
fillBins = do
  bins <- newArray (0, numContBins-1) [] :: IO (IOArray Int [(RangeSet a, [a])])
  let granulation = 1 % fromIntegral numContBins
  let toRatio = (* granulation) . fromIntegral
  let idxs = map toRatio [0..numContBins-1]
  print idxs

  whileS do
    shuffled <- generate (shuffle (elems @a))
    let sets = scanr (\x -> bimap (RangeSet.insert x) (x:)) (RangeSet.empty, []) shuffled
    forM_ (init sets) $ \set -> do
      let c = contiguity (fst set)
      let idx = fromMaybe 0 (findIndex (>= c) idxs)
      binC <- readArray bins idx
      writeArray bins idx (set : binC)
    szs <- map length <$> getElems bins
    print szs
    return (any (< binSize) szs)

  map (bimap toRatio (map (\(r, xs) -> (r, Set.fromList xs, sort xs)))) <$> getAssocs bins

contiguityBench :: forall a. (NFData a, Ord a, Enum a, Generic a) => [Rational] -> [[(RangeSet a, Set a, [a])]] -> Benchmark
contiguityBench ratios bins = es `deepseq` env (return (map unzip3 bins)) $ \dat ->
    bgroup "contiguity" (concatMap (mkBench dat) (zip ratios [0..]))

  where
    es = elems @a
    mkBench dat (ratio, i) = let ~(rs, ss, xss) = dat !! i in [
        bench ("overhead rangeset-all (" ++ show ratio ++ ")") $ nf (overheadRangeSetAllMember es) rs,
        bench ("overhead set-all (" ++ show ratio ++ ")") $ nf (overheadSetAllMember es) ss,
        bench ("rangeset-all (" ++ show ratio ++ ")") $ nf (rangeSetAllMember es) rs,
        bench ("set-all (" ++ show ratio ++ ")") $ nf (setAllMember es) ss,
        bench ("overhead rangeset-mem (" ++ show ratio ++ ")") $ nf (uncurry overheadRangeSetMember) (xss, rs),
        bench ("overhead set-mem (" ++ show ratio ++ ")") $ nf (uncurry overheadSetMember) (xss, ss),
        bench ("rangeset-mem (" ++ show ratio ++ ")") $ nf (uncurry rangeSetMember) (xss, rs),
        bench ("set-mem (" ++ show ratio ++ ")") $ nf (uncurry setMember) (xss, ss),
        bench ("overhead rangeset-ins (" ++ show ratio ++ ")") $ nf overheadRangeSetInsert xss,
        bench ("overhead set-ins (" ++ show ratio ++ ")") $ nf overheadSetInsert xss,
        bench ("rangeset-ins (" ++ show ratio ++ ")") $ nf rangeSetInsert xss,
        bench ("set-ins (" ++ show ratio ++ ")") $ nf setInsert xss
      ]

    overheadRangeSetAllMember :: [a] -> [RangeSet a] -> [Bool]
    overheadRangeSetAllMember !elems rs = [False | r <- rs, x <- elems]

    overheadSetAllMember :: [a] -> [Set a] -> [Bool]
    overheadSetAllMember !elems ss = [False | s <- ss, x <- elems]

    rangeSetAllMember :: [a] -> [RangeSet a] -> [Bool]
    rangeSetAllMember !elems rs = [RangeSet.member x r | r <- rs, x <- elems]

    setAllMember :: [a] -> [Set a] -> [Bool]
    setAllMember !elems ss = [Set.member x s | s <- ss, x <- elems]

    overheadRangeSetMember :: [[a]] -> [RangeSet a] -> [Bool]
    overheadRangeSetMember xss rs = [False | (r, xs) <- zip rs xss, x <- xs]

    overheadSetMember :: [[a]] -> [Set a] -> [Bool]
    overheadSetMember xss ss = [False | (s, xs) <- zip ss xss, x <- xs]

    rangeSetMember :: [[a]] -> [RangeSet a] -> [Bool]
    rangeSetMember xss rs = [RangeSet.member x r | (r, xs) <- zip rs xss, x <- xs]

    setMember :: [[a]] -> [Set a] -> [Bool]
    setMember xss ss = [Set.member x s | (s, xs) <- zip ss xss, x <- xs]

    overheadRangeSetInsert :: [[a]] -> [RangeSet a]
    overheadRangeSetInsert = map (foldr (flip const) RangeSet.empty)

    overheadSetInsert :: [[a]] -> [Set a]
    overheadSetInsert = map (foldr (flip const) Set.empty)

    rangeSetInsert :: [[a]] -> [RangeSet a]
    rangeSetInsert = map (foldr RangeSet.insert RangeSet.empty)

    setInsert :: [[a]] -> [Set a]
    setInsert = map (foldr Set.insert Set.empty)

makeBench :: NFData a => (a -> String) -> [(String, a -> Benchmarkable)] -> a -> Benchmark
makeBench caseName cases x = env (return x) (\x ->
  bgroup (caseName x) (map (\(name, gen) -> bench name $ gen x) cases))
