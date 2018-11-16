{-# LANGUAGE DataKinds #-}
module Examples.Map where

import Prelude hiding (map)

import StaticCaching

import Data.Inc.Bag (
  Bag)
import qualified Data.Inc.Bag as Bag (
  SingletonC, FoldMapGroupC)
import Data.Inc.Map (
  Map, FoldMapGroupWithKeyC, MergeC)
import qualified Data.Inc.Map as Map (
  SingletonC)
import Data.Inc.Int (
  MulC)
import Data.Inc.Function (
  Fun, ClosureC)

import Data.Monoid (
  Sum)


type IndexedJoinC = '[
  Fun (Int, Int) Int (Cache '[Int]),
  Fun (Fun (Int, Int) Int (Cache '[Int]), Bag (Int, Int)) (Map Int (Bag (Int, Int)))    (Cache (GroupByC Int (Int, Int) (Cache '[Int]))),
  Fun (Fun (Bag (Int, Int)) (Sum Int) (Cache FoldMapGroupSumSndC), Map Int (Bag (Int, Int))) (Map Int (Sum Int)) (Cache (MapC Int (Bag (Int, Int)) (Sum Int) (Cache FoldMapGroupSumSndC))),
  Fun (Bag (Int, Int)) (Sum Int) (Cache FoldMapGroupSumSndC),
  Fun (Fun (Sum Int, Sum Int) (Sum Int) (Cache MulSumC), Map Int (Sum Int, Sum Int)) (Sum Int) (Cache (FoldMapGroupC Int (Sum Int, Sum Int) (Sum Int) (Cache MulSumC))),
  Fun (Sum Int, Sum Int) (Sum Int) (Cache MulSumC),
  Map Int (Bag (Int, Int)),
  Cache (GroupByC Int (Int, Int) (Cache '[Int])), Map Int (Sum Int),
  Cache (MapC Int (Bag (Int, Int)) (Sum Int) (Cache FoldMapGroupSumSndC)),
  Map Int (Bag (Int, Int)),
  Cache (GroupByC Int (Int, Int) (Cache '[Int])), Map Int (Sum Int),
  Cache (MapC Int (Bag (Int, Int)) (Sum Int) (Cache FoldMapGroupSumSndC)),
  Map Int (Sum Int, Sum Int),
  MergeC,
  Sum Int,
  Cache (FoldMapGroupC Int (Sum Int, Sum Int) (Sum Int) (Cache MulSumC))]

indexedJoin :: v (Bag (Int, Int)) -> v (Bag (Int, Int)) -> Stm v IndexedJoinC (Sum Int)
indexedJoin orders lineItems =
  Bind (Lambda (\ab -> Bind (Fst ab) (\a -> Pure a))) (\frst ->
  Bind (Lambda2 groupBy) (\groupBy ->
  Bind (Lambda2 map) (\map ->
  Bind (Lambda foldMapGroupSumSnd) (\foldMapGroupSumSnd ->
  Bind (Lambda2 foldMapGroup) (\foldMapGroup ->
  Bind (Lambda mulSum) (\mulSum ->
  Call3 Apply2 groupBy frst orders (\orderIndex ->
  Call3 Apply2 map foldMapGroupSumSnd orderIndex (\orderSumIndex ->
  Call3 Apply2 groupBy frst lineItems (\lineItemIndex ->
  Call3 Apply2 map foldMapGroupSumSnd lineItemIndex (\lineItemSumIndex ->
  Call2 Merge orderSumIndex lineItemSumIndex (\joined ->
  Call3 Apply2 foldMapGroup mulSum joined (\r ->
  Pure r))))))))))))

type GroupByC k a c = '[
  Fun (Fun a k c, a) (Map k (Bag a)) (Cache '[k, c, Bag a, Bag.SingletonC, Map k (Bag a), Map.SingletonC]),
  Fun a (Map k (Bag a)) (Cache '[k, c, Bag a, Bag.SingletonC, Map k (Bag a), Map.SingletonC]),
  ClosureC,
  Map k (Bag a),
  Bag.FoldMapGroupC a (Map k (Bag a)) (Cache '[k, c, Bag a, Bag.SingletonC, Map k (Bag a), Map.SingletonC])]

groupBy :: v (Fun a k c) -> v (Bag a) -> Stm v (GroupByC k a c) (Map k (Bag a))
groupBy f bag =
  Bind (Lambda2 (\f a ->
    Call2 Apply1 f a (\k ->
    Call1 BagSingleton a (\as ->
    Call2 MapSingleton k as (\r ->
    Pure r))))) (\singletonKeyed ->
  Call2 Closure singletonKeyed f (\singletonKeyedClosure ->
  Call2 FoldMapGroup singletonKeyedClosure bag (\r ->
  Pure r)))

type MapC k a b c = '[
  Fun (Fun a b c, (k, a)) (Map k b) (Cache '[b, c, Map k b, Map.SingletonC]),
  Fun (k, a) (Map k b) (Cache '[b, c, Map k b, Map.SingletonC]),
  ClosureC,
  Map k b,
 FoldMapGroupWithKeyC k (Cache '[b, c, Map k b, Map.SingletonC])]

map :: v (Fun a b c) -> v (Map k a) -> Stm v (MapC k a b c) (Map k b)
map f m =
  Bind (Lambda3 (\f k a ->
    Call2 Apply1 f a (\b ->
    Call2 MapSingleton k b (\r ->
    Pure r)))) (\innerMap ->
  Call2 Closure innerMap f (\innerMapClosure ->
  Call2 FoldMapGroupWithKey innerMapClosure m (\r ->
  Pure r)))

type FoldMapGroupSumSndC = '[
  Fun (Int, Int) (Sum Int) (Cache '[Int, Sum Int]), Sum Int,
  Bag.FoldMapGroupC (Int, Int) (Sum Int) (Cache '[Int, Sum Int])]

foldMapGroupSumSnd :: v (Bag (Int, Int)) -> Stm v FoldMapGroupSumSndC (Sum Int)
foldMapGroupSumSnd bag =
  Bind (Lambda (\xy ->
    Bind (Snd xy) (\x ->
    Bind (ConSum x) (\sx ->
    Pure sx)))) (\sumSnd ->
  Call2 FoldMapGroup sumSnd bag (\r ->
  Pure r))

type FoldMapGroupC k a b c = '[
  Fun (Fun a b c, (k, a)) b (Cache '[b, c]),
  Fun (k, a) b (Cache '[b, c]),
  ClosureC,
  b,
  FoldMapGroupWithKeyC k (Cache '[b, c])]

foldMapGroup :: v (Fun a b c) -> v (Map k a) -> Stm v (FoldMapGroupC k a b c) b
foldMapGroup f m =
  Bind (Lambda3 (\f _ a ->
    Call2 Apply1 f a (\r ->
    Pure r))) (\innerFoldMapGroup ->
  Call2 Closure innerFoldMapGroup f (\innerFoldMapGroupClosure ->
  Call2 FoldMapGroupWithKey innerFoldMapGroupClosure m (\r ->
  Pure r)))

type MulSumC = '[
 Sum Int, Sum Int, Int, Int, Int, MulC, Sum Int]

mulSum :: v (Sum Int, Sum Int) -> Stm v MulSumC (Sum Int)
mulSum sxy =
  Bind (Fst sxy) (\sx ->
  Bind (Snd sxy) (\sy ->
  Bind (GetSum sx) (\x ->
  Bind (GetSum sy) (\y ->
  Call2 Mul x y (\r ->
  Bind (ConSum r) (\sr ->
  Pure sr))))))

