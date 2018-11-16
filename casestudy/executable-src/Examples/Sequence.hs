{-# LANGUAGE DataKinds #-}
module Examples.Sequence where

import Prelude hiding (concatMap, filter)

import StaticCaching

import Data.Inc.Sequence (
  Sequence, MapC, ConcatC, SingletonC)
import Data.Inc.Function (
  Fun, ClosureC)

type CartesianProductC = '[
  Fun (Fun Int (Sequence (Int, Int)) (Cache (MapPairC Int Int)), Sequence Int) (Sequence (Int, Int)) (Cache (ConcatMapC Int (Int, Int) (Cache (MapPairC Int Int)))),
  Fun (Sequence Int, Int) (Sequence (Int, Int)) (Cache (MapPairC Int Int)),
  Fun Int (Sequence (Int, Int)) (Cache (MapPairC Int Int)),
  ClosureC,
  Sequence (Int, Int),
  Cache (ConcatMapC Int (Int, Int) (Cache (MapPairC Int Int)))]

cartesianProduct :: v (Sequence Int) -> v (Sequence Int) -> Stm v CartesianProductC (Sequence (Int, Int))
cartesianProduct xs ys =
  Bind (Lambda2 concatMap) (\concatMap ->
  Bind (Lambda2 mapPair) (\mapPair ->
  Call2 Closure mapPair ys (\mapPairYs ->
  Call3 Apply2 concatMap mapPairYs xs (\r ->
  Pure r))))

type ConcatMapC a b c = '[
  Sequence (Sequence b),
  MapC c,
  Sequence b,
  ConcatC]

concatMap :: v (Fun a (Sequence b) c) -> v (Sequence a) -> Stm v (ConcatMapC a b c) (Sequence b)
concatMap f xs =
  Call2 Map f xs (\yss ->
  Call1 Concat yss (\r ->
  Pure r))

type MapPairC b a = '[
  Fun (a, b) (a, b) (Cache '[(a, b)]),
  Fun b (a, b) (Cache '[(a, b)]),
  ClosureC,
  Sequence (a, b),
  MapC (Cache '[(a, b)])]

mapPair :: v (Sequence b) -> v a -> Stm v (MapPairC b a) (Sequence (a, b))
mapPair ys x =
  Bind (Lambda2 (\x y -> Bind (Pair x y) (\xy -> Pure xy))) (\pair ->
  Call2 Closure pair x (\pairX ->
  Call2 Map pairX ys (\r ->
  Pure r)))


