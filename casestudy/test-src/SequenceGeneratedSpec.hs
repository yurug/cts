{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-partial-type-signatures #-}
module SequenceGeneratedSpec where

import SequenceSpec ()
import CorrectnessProperty (
  correctnessProperty, fullyEvaluates, ValidChange(ValidChange))

import Data.Inc.Sequence.Generated (
  ccartesianProduct, dcartesianProduct)

import Data.Inc.ChangeStruct (
  Dt, onil)
import Data.Inc.Function (
  Fun(Primitive), DFun(DPrimitive))
import Data.Inc.Sequence (
  Sequence, fromList, insert, singleton)

import Test.Hspec (
  Spec, describe, it)
import Test.QuickCheck (
  property)

import Data.Proxy (
  Proxy(Proxy))


spec :: Spec
spec = describe "Sequence" $ do

  describe "cartesianProduct" $ do

    it "has the correctness property" $
      property (\(ValidChange xs dxs, ValidChange ys dys) -> correctnessProperty
        (Primitive ccartesianProduct dcartesianProduct) (DPrimitive dcartesianProduct)
        (xs, ys)
        (dxs, dys))

    it "fully evaluates the result and cache on changes to the inner sequence" $ do
      fullyEvaluates ccartesianProduct dcartesianProduct initialSequences sequenceChangeInner

    it "fully evaluates the result and cache on changes to the outer sequence" $ do
      fullyEvaluates ccartesianProduct dcartesianProduct initialSequences sequenceChangeOuter


size :: Int
size = 512

initialSequences :: (Sequence Int, Sequence Int)
initialSequences = (fromList [1 .. size], fromList [1 .. size])

sequenceChangeOuter :: Dt (Sequence Int, Sequence Int)
sequenceChangeOuter =
  (insert 1 (singleton 1), onil Proxy)

sequenceChangeInner :: Dt (Sequence Int, Sequence Int)
sequenceChangeInner =
  (onil Proxy, insert 1 (singleton 1))


