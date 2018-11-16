module Main where

import Prelude hiding (
  sum, length, concat, map)
import qualified Prelude (
  map)

import Data.Inc.Bag.Generated (
  sum, csum, dsum,
  length, clength, dlength,
  average, caverage, daverage)
import Data.Inc.Map.Generated (
  indexedJoin, cindexedJoin, dindexedJoin)
import Data.Inc.Sequence.Generated (
  cartesianProduct, ccartesianProduct, dcartesianProduct)

import Data.Inc.ChangeStruct (
  Dt, ChangeStruct(oplus), nil, onil, ocompose)
import Data.Inc.Function (
  Fun(Primitive, Closure), DFun(DPrimitive, DClosure),
  apply, dapply)
import Data.Inc.Int (
  PlusC, cplus, dplus)
import Data.Inc.Bag (
  Bag, Changes(Changes), fromList, changeInsert)
import Data.Inc.Sequence (
  Sequence,
  concat, cconcat, dconcat,
  map, MapC, cmap, dmap)
import qualified Data.Inc.Sequence as Sequence (
  fromList, singleton, insert, changeAt)

import Criterion.Main (
  defaultMain, Benchmark, bgroup, env, bench, whnf)
import Control.DeepSeq (
  NFData(rnf))
import Data.Proxy (
  Proxy(Proxy))


main :: IO ()
main = defaultMain [
  benchmark "sum" sum csum dsum exampleBag exampleBagChange,
  benchmark "length" length clength dlength exampleBag exampleBagChange,
  benchmark "average" average caverage daverage exampleBag exampleBagChange,
  benchmark "indexedJoin" (uncurry indexedJoin) cindexedJoin dindexedJoin exampleBags exampleBagChanges,
  benchmark "nestedLoopOuter" (uncurry cartesianProduct) ccartesianProduct dcartesianProduct exampleSequences outerSequenceChange,
  benchmark "nestedLoopInner" (uncurry cartesianProduct) ccartesianProduct dcartesianProduct exampleSequences innerSequenceChange,
  benchmark "concat" concat cconcat dconcat exampleNestedSequence exampleNestedSequenceChange,
  benchmark "mapIncrement" mapIncrement (apply cmapIncrement) (dapply cmapIncrement dmapIncrement) exampleSequence exampleSequenceChange,
  benchmark "mapIncrementPlus2" mapIncrementPlus2 (apply cmapIncrement) (dapply cmapIncrement dmapIncrementPlus2) exampleSequence exampleSequenceChange]


benchmark ::
  (ChangeStruct a, ChangeStruct b, NFData a, NFData b, NFData c) =>
  String -> (a -> b) -> (a -> (b, c)) -> (a -> Dt a -> c -> (Dt b, c)) ->
  (Int -> a) -> Dt a -> Benchmark
benchmark name f cf df na da = let
  nas = Prelude.map (\n -> (n, na n)) ns
  in bgroup name [

    bgroup "from_scratch" (do
      (n, a) <- nas
      return (env (return (oplus a da)) (\ua ->
        bench (show n) (whnf f ua)))),

    bgroup "caching" (do
      (n, a) <- nas
      return (env (return (oplus a da)) (\ua ->
        bench (show n) (whnf (\ua' ->
          case cf ua' of
            (b, _) -> b) ua)))),

    bgroup "incremental" (do
      (n, a) <- nas
      return (env (return (cf a)) (\ ~(b, c) ->
        bench (show n) (whnf (\da' ->
          case df a da' c of
            (db, _) -> oplus b db) da))))]

ns :: [Int]
ns = [0, 1, 2, 4, 8, 16, 32, 64, 128]

exampleBag :: Int -> Bag Int
exampleBag n = fromList [0 .. n]

exampleBagChange :: Dt (Bag Int)
exampleBagChange = Changes (Prelude.map changeInsert [0 .. 10])

exampleBags :: Int -> (Bag (Int, Int), Bag (Int, Int))
exampleBags n = (fromList (Prelude.map (\i -> (i, i)) [0 .. n]), fromList (Prelude.map (\i -> (i, i)) [0 .. n]))

exampleBagChanges :: Dt (Bag (Int, Int), Bag (Int, Int))
exampleBagChanges = (Changes (Prelude.map (\i -> changeInsert (i, i)) [0 .. 10]), Changes (Prelude.map (\i -> changeInsert (i, i)) [0 .. 10]))

exampleSequences :: Int -> (Sequence Int, Sequence Int)
exampleSequences size = (Sequence.fromList [0 .. size], Sequence.fromList [0 .. size])

innerSequenceChange :: Dt (Sequence Int, Sequence Int)
innerSequenceChange =
  (onil Proxy, Sequence.insert 0 (Sequence.singleton 0))

outerSequenceChange :: Dt (Sequence Int, Sequence Int)
outerSequenceChange =
  (Sequence.insert 0 (Sequence.singleton 0), onil Proxy)

exampleNestedSequence :: Int -> Sequence (Sequence Int)
exampleNestedSequence size = Sequence.fromList (replicate size (Sequence.fromList [0 .. size]))

exampleNestedSequenceChange :: Dt (Sequence (Sequence Int))
exampleNestedSequenceChange = Sequence.changeAt 0 (Sequence.insert 0 (Sequence.fromList [12]))

exampleSequence :: Int -> Sequence Int
exampleSequence size = Sequence.fromList [0 .. size]

exampleSequenceChange :: Dt (Sequence Int)
exampleSequenceChange = Sequence.insert 0 (Sequence.fromList [12]) `ocompose` Sequence.changeAt 0 3


mapIncrement :: Sequence Int -> Sequence Int
mapIncrement = map (+1)

cmapIncrement :: Fun (Sequence Int) (Sequence Int) (MapC IncrementC)
cmapIncrement = Closure (Primitive (uncurry cmap) (\(cf, cxs) (df, dxs) -> dmap cf df cxs dxs)) cincrement

dmapIncrement :: DFun (Sequence Int) (Sequence Int) (MapC IncrementC)
dmapIncrement = DClosure (Primitive (uncurry cmap) (\(cf, cxs) (df, dxs) -> dmap cf df cxs dxs)) (DPrimitive (\(cf, cxs) (df, dxs) -> dmap cf df cxs dxs)) cincrement dincrementNil

mapIncrementPlus2 :: Sequence Int -> Sequence Int
mapIncrementPlus2 = map (+3)

dmapIncrementPlus2 :: DFun (Sequence Int) (Sequence Int) (MapC IncrementC)
dmapIncrementPlus2 = DClosure (Primitive (uncurry cmap) (\(cf, cxs) (df, dxs) -> dmap cf df cxs dxs)) (DPrimitive (\(cf, cxs) (df, dxs) -> dmap cf df cxs dxs)) cincrement dincrementPlus2

type IncrementC = PlusC

increment :: Int -> Int
increment x = x + 1

cincrement :: Fun Int Int IncrementC
cincrement = Closure (Primitive cplus dplus) 1

dincrementNil :: DFun Int Int IncrementC
dincrementNil = DClosure
  (Primitive cplus dplus) (DPrimitive dplus) 1 (nil 1)

dincrementPlus2 :: DFun Int Int IncrementC
dincrementPlus2 = DClosure
  (Primitive cplus dplus) (DPrimitive dplus) 1 2



instance (NFData a, NFData b, NFData c, NFData d, NFData e, NFData f, NFData g,
          NFData h, NFData i, NFData j, NFData k, NFData l, NFData m, NFData n, NFData o, NFData p, NFData q, NFData r)
               => NFData (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r) where
  rnf (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r) =
    rnf a `seq` rnf b `seq` rnf c `seq` rnf d `seq` rnf e `seq` rnf f `seq` rnf g `seq` rnf h `seq` rnf i `seq` rnf j `seq` rnf k `seq` rnf l `seq` rnf m `seq` rnf n `seq` rnf o `seq` rnf p `seq` rnf q `seq` rnf r

