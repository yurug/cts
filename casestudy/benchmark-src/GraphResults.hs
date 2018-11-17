{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
module Main where


import Data.Inc.Bag.Generated (
  average, caverage, daverage)
import Data.Inc.Map.Generated (
  indexedJoin, cindexedJoin, dindexedJoin)
import Data.Inc.Sequence.Generated (
  cartesianProduct, ccartesianProduct, dcartesianProduct)

import Data.Inc.Bag (
  Bag, fromList, Changes(Changes), changeInsert)
import Data.Inc.Sequence (
  Sequence)
import qualified Data.Inc.Sequence as Seq (
  fromList, singleton, insert)
import Data.Inc.ChangeStruct (
  ChangeStruct(Dt, oplus), onil)


import Criterion.Main (
  defaultMainWith, defaultConfig, bench, whnf, env)
import Criterion.Types (
  Config(csvFile, reportFile))
import GHC.DataSize (
  recursiveSize)
import Control.DeepSeq (
  NFData(rnf))

import Data.Csv (
  decodeByName, encodeByName, Header,
  FromNamedRecord(parseNamedRecord), (.:),
  ToNamedRecord(toNamedRecord), namedRecord, (.=))
import Data.Vector (
  Vector)
import qualified Data.Vector as Vector (
  fromList, find)
import qualified Data.ByteString.Lazy as B (
  readFile, writeFile)

import System.Directory (
  createDirectoryIfMissing)
import Control.Monad (
  forM_, forM)
import Data.Proxy (
  Proxy(Proxy))


type BenchmarkName = String
type Size = Int

bagSizes :: [Size]
bagSizes = [2 ^ k | k <- [0 .. 20]]

mapSizes :: [Size]
mapSizes = [2 ^ k | k <- [0 .. 20]]

sequenceSizes :: [Size]
sequenceSizes = [2 ^ k | k <- [0 .. 10]]

main :: IO ()
main = do

  putStrLn "Checking ..."

  check "bag/average" bagSizes average caverage daverage initialBag bagChange

  check "map/indexedJoin" mapSizes (uncurry indexedJoin) cindexedJoin dindexedJoin initialTables tableChange

  check "sequence/nestedLoopOuter" sequenceSizes (uncurry cartesianProduct) ccartesianProduct dcartesianProduct initialSequences sequenceChangeOuter

  check "sequence/nestedLoopInner" sequenceSizes (uncurry cartesianProduct) ccartesianProduct dcartesianProduct initialSequences sequenceChangeInner

  benchmark "bag/average" bagSizes average caverage daverage initialBag bagChange

  benchmark "map/indexedJoin" mapSizes (uncurry indexedJoin) cindexedJoin dindexedJoin initialTables tableChange

  benchmark "sequence/nestedLoopOuter" sequenceSizes (uncurry cartesianProduct) ccartesianProduct dcartesianProduct initialSequences sequenceChangeOuter

  benchmark "sequence/nestedLoopInner" sequenceSizes (uncurry cartesianProduct) ccartesianProduct dcartesianProduct initialSequences sequenceChangeInner

  writeResults "bag/average" bagSizes

  writeResults "map/indexedJoin" mapSizes

  writeResults "sequence/nestedLoopOuter" sequenceSizes

  writeResults "sequence/nestedLoopInner" sequenceSizes

  measureCacheSize "bag/average" bagSizes caverage initialBag

  measureCacheSize "map/indexedJoin" mapSizes cindexedJoin initialTables

  measureCacheSize "sequence/nestedLoop" sequenceSizes ccartesianProduct initialSequences


configFile :: BenchmarkName -> Size -> Config
configFile name size =
  defaultConfig { csvFile = Just csvPath, reportFile = Just htmlPath } where
    path = resultsPath name size
    csvPath = path ++ "raw_results.csv"
    htmlPath = path ++ "raw_results.html"

resultsPath :: BenchmarkName -> Size -> FilePath
resultsPath name size =
  "benchmark-results/" ++ name ++ "/size" ++ show size ++ "/"


benchmark ::
  (ChangeStruct a, ChangeStruct b, NFData a, NFData b, NFData c) =>
  BenchmarkName -> [Size] ->
  (a -> b) -> (a -> (b, c)) -> (a -> Dt a -> c -> (Dt b, c)) ->
  (Size -> a) -> Dt a -> IO ()
benchmark name sizes f cf df inputOfSize da = do

  forM_ sizes (\size ->
    createDirectoryIfMissing True (resultsPath name size))

  forM_ sizes (\size -> do
    defaultMainWith (configFile name size) [
      (env (return (oplus (inputOfSize size) da))) (\ua ->
        bench "from_scratch" (whnf f ua)),
      (env (return (oplus (inputOfSize size) da))) (\ua ->
        bench "caching" (whnf (\ua' -> case cf ua' of (b, _) -> b) ua)),
      (env (return (inputOfSize size, cf (inputOfSize size)))) (\ ~(a, ~(b, c)) ->
        bench "incremental" (whnf (\da' -> case df a da' c of (db, _) -> oplus b db) da))])


check ::
  (ChangeStruct a, ChangeStruct b, Eq b) =>
  BenchmarkName -> [Size] ->
  (a -> b) -> (a -> (b, c)) -> (a -> Dt a -> c -> (Dt b, c)) ->
  (Size -> a) -> Dt a -> IO ()
check name sizes f cf df inputOfSize da = do

  let ok = and (do
        size <- sizes
        let a = inputOfSize size
            ua = oplus a da
            fromScratchResult = f ua
            cachingResult = fst (cf ua)
            (b, c) = cf a
            (db, _) = df a da c
            incrementalResult = oplus b db
        return (
          fromScratchResult == cachingResult &&
          fromScratchResult == incrementalResult))

  if ok
    then putStrLn (name ++ " ok")
    else putStrLn (name ++ " from scratch and incremental disagree")


initialBag :: Size -> Bag Int
initialBag size = fromList [1 .. size]

bagChange :: Dt (Bag Int)
bagChange = Changes [changeInsert 1]

initialTables :: Size -> (Bag (Int, Int), Bag (Int, Int))
initialTables size = (orders, lineItems) where

  orders = fromList (do
    ordk <- [1 .. size]
    let xch = ordk
    return (ordk, xch))

  lineItems = fromList (do
    ordk <- [1 .. size]
    let price = ordk
    return (ordk, price))

tableChange :: Dt (Bag (Int, Int), Bag (Int, Int))
tableChange =
  (Changes [changeInsert (1, 1)], Changes [])

initialSequences :: Size -> (Sequence Int, Sequence Int)
initialSequences size = (Seq.fromList [1 .. size], Seq.fromList [1 .. size])

sequenceChangeOuter :: Dt (Sequence Int, Sequence Int)
sequenceChangeOuter =
  (Seq.insert 1 (Seq.singleton 1), onil Proxy)

sequenceChangeInner :: Dt (Sequence Int, Sequence Int)
sequenceChangeInner =
  (onil Proxy, Seq.insert 1 (Seq.singleton 1))


data RawResult = RawResult {
  rawResultName :: String,
  rawResultMean :: Double }

instance FromNamedRecord RawResult where
  parseNamedRecord m = RawResult <$>
    m .: "Name" <*>
    m .: "Mean"


data Timing = Timing {
  timingSize :: Size,
  timingFromScratch :: Double,
  timingCaching :: Double,
  timingIncremental :: Double }

instance ToNamedRecord Timing where
  toNamedRecord (Timing {..}) = namedRecord [
    "size" .= timingSize,
    "from_scratch" .= timingFromScratch,
    "caching" .= timingCaching,
    "incremental" .= timingIncremental]


writeResults :: BenchmarkName -> [Size] -> IO ()
writeResults name sizes = do
  timings <- forM sizes (\size -> do
    let rawResultsPath = resultsPath name size ++ "raw_results.csv"
    parsed <- B.readFile rawResultsPath >>= return . decodeByName
    case parsed of
      Left errorMessage -> error (rawResultsPath ++ "\n" ++ errorMessage)
      Right (_, rawResults) -> do
        let timingSize = size
            timingFromScratch = findResult "from_scratch" rawResults
            timingCaching = findResult "caching" rawResults
            timingIncremental = findResult "incremental" rawResults
        return (Timing {..}))
  let timingsPath = "benchmark-results/" ++ name ++ ".csv"
  B.writeFile timingsPath (encodeByName timingHeader timings)

timingHeader :: Header
timingHeader = Vector.fromList ["size", "from_scratch", "caching", "incremental"]

findResult :: String -> Vector RawResult -> Double
findResult name rawResults =
  case Vector.find ((== name) . rawResultName) rawResults of
    Nothing -> error ("raw results not found " ++ name)
    Just (RawResult _ mean) -> mean


instance (NFData a, NFData b, NFData c, NFData d, NFData e, NFData f, NFData g,
          NFData h, NFData i, NFData j, NFData k, NFData l, NFData m, NFData n, NFData o, NFData p, NFData q, NFData r)
               => NFData (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r) where
  rnf (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r) =
    rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e `seq` rnf f `seq` rnf g `seq` rnf h `seq` rnf i `seq` rnf j `seq` rnf k `seq` rnf l `seq` rnf m `seq` rnf n `seq` rnf o `seq` rnf p `seq` rnf q `seq` rnf r


benchmarkSpace :: [Size] -> (a -> (b, c)) -> (Size -> a) -> IO [SpaceMeasurement]
benchmarkSpace sizes cf inputOfSize = forM sizes (\size -> do
  let a = inputOfSize size
      (_, c) = cf a
  bytes <- recursiveSize $! c
  return (SpaceMeasurement size bytes))


data SpaceMeasurement = SpaceMeasurement {
  spaceMeasurementSize :: Size,
  spaceMeasurementBytes :: Word }

instance ToNamedRecord SpaceMeasurement where
  toNamedRecord (SpaceMeasurement {..}) = namedRecord [
    "size" .= spaceMeasurementSize,
    "bytes" .= spaceMeasurementBytes]

measureCacheSize :: BenchmarkName -> [Size] -> (a -> (b, c)) -> (Size -> a) -> IO ()
measureCacheSize name sizes cf inputOfSize = do
  spaceMeasurements <- benchmarkSpace sizes cf inputOfSize
  let spaceMeasurementPath = "benchmark-results/" ++ name ++ "_space.csv"
  B.writeFile spaceMeasurementPath (encodeByName spaceMeasurementHeader spaceMeasurements)

spaceMeasurementHeader :: Header
spaceMeasurementHeader = Vector.fromList ["size", "bytes"]

