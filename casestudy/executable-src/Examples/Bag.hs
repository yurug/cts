{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
module Examples.Bag where

import Prelude hiding (
  sum, length)

import StaticCaching

import Data.Inc.Function (
  Fun)

import Data.Inc.Int (
  DivC)
import Data.Inc.Bag (
  Bag, FoldMapGroupC)


import Data.Monoid (
  Sum)


type SumC = '[
  Fun Int (Sum Int) (Cache '[Sum Int]),
  Sum Int,
  FoldMapGroupC Int (Sum Int) (Cache '[Sum Int]),
  Int]

sum :: v (Bag Int) -> Stm v SumC Int
sum xs =
  Bind (Lambda (\a -> Bind (ConSum a) Pure)) (\inSum ->
  Call2 FoldMapGroup inSum xs (\s ->
  Bind (GetSum s) Pure))

type LengthC = '[
  Fun Int (Sum Int) (Cache '[Int, Sum Int]),
  Sum Int,
  FoldMapGroupC Int (Sum Int) (Cache '[Int, Sum Int]),
  Int]

length :: v (Bag Int) -> Stm v LengthC Int
length xs =
  Bind (Lambda (\_ -> Bind (Literal 1) (\one -> Bind (ConSum one) Pure))) (\inSumOne ->
  Call2 FoldMapGroup inSumOne xs (\n ->
  Bind (GetSum n) Pure))

type AverageC = '[
  Fun (Bag Int) Int (Cache SumC),
  Fun (Bag Int) Int (Cache LengthC),
  Int,
  Cache SumC,
  Int,
  Cache LengthC,
  Int,
  DivC]

average :: v (Bag Int) -> Stm v AverageC Int
average xs =
  Bind (Lambda sum) (\sum ->
  Bind (Lambda length) (\length ->
  Call2 Apply1 sum xs (\s ->
  Call2 Apply1 length xs (\n ->
  Call2 Div s n (\r ->
  Pure r)))))

