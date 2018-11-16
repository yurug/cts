{-# LANGUAGE BangPatterns #-}
module BagGeneratedSpec where

import Prelude hiding (length)

import BagSpec ()
import CorrectnessProperty (
  correctnessProperty, fullyEvaluates)

import Data.Inc.ChangeStruct (
  ChangeStruct(Dt, oplus))
import Data.Inc.Function (
  Fun(Primitive), DFun(DPrimitive))
import Data.Inc.Bag (
  Bag, fromList,
  Changes(Changes), changeInsert)
import Data.Inc.Bag.Generated (
  csum, dsum, length, clength, dlength, caverage, daverage)

import Test.Hspec (
  Spec, describe, it)
import Test.QuickCheck (
  property, (==>))


spec :: Spec
spec = describe "Bag" $ do

  describe "dsum" $ do
    it "has the correctness property" $
      property (correctnessProperty (Primitive csum dsum) (DPrimitive dsum))
    it "fully evaluates the result and cache" $ do
      fullyEvaluates csum dsum initialBag bagChange

  describe "dlength" $ do
    it "has the correctness property" $
      property (correctnessProperty (Primitive clength dlength) (DPrimitive dlength))
    it "fully evaluates the result and cache" $ do
      fullyEvaluates clength dlength initialBag bagChange

  describe "daverage" $ do
    it "has the correctness property" $
      property (\bag dbag ->
        not (length bag == 0) && not (length (oplus bag dbag) == 0) ==>
        correctnessProperty (Primitive caverage daverage) (DPrimitive daverage) bag dbag)
    it "fully evaluates the result and cache" $ do
      fullyEvaluates caverage daverage initialBag bagChange


size :: Int
size = 1024

initialBag :: Bag Int
initialBag = fromList [1 .. size]

bagChange :: Dt (Bag Int)
bagChange = Changes [changeInsert 1]

