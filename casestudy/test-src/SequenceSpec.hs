{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module SequenceSpec where

import Prelude hiding (length)

import BagSpec (
  cincrement, IncrementC, dincrementNil, dincrementPlus2)
import CorrectnessProperty (
  correctnessProperty, ValidChange(ValidChange))

import Data.Inc.ChangeStruct (
  ChangeStruct(Dt, oplus), DiffChangeStruct(ominus))
import Data.Inc.Sequence (
  Sequence(S), fromList, length, index, oplusSingle,
  AtomicChange(..),
  cconcat, dconcat,
  cmap, MapC, dmap)
import Data.Inc.Function (
  Fun(Primitive, Closure), DFun(DPrimitive, DClosure))

import Test.Hspec (
  Spec, describe, it)
import Test.QuickCheck (
  Arbitrary(arbitrary, shrink), Gen, genericShrink,
  oneof, choose, sized,
  property)

import qualified Data.DList as DList (
  fromList, toList)
import Data.List (
  inits)


spec :: Spec
spec = describe "Sequence" $ do

  describe "concat" $ do

    it "has the correctness property" $
      property (\(ValidChange ss dss) ->
        correctnessProperty @(Sequence (Sequence Int))
        (Primitive cconcat dconcat) (DPrimitive dconcat)
        ss dss)

  describe "map" $ do

    it "has the correctness property on nil function changes" $
      property (\(ValidChange ss dss) ->
        correctnessProperty @(Sequence Int)
        cmapIncrement dmapIncrement
        ss dss)

    it "has the correctness property on non-nil function changes" $
      property (\(ValidChange ss dss) ->
        correctnessProperty @(Sequence Int)
        cmapIncrement dmapIncrementPlus2
        ss dss)

  describe "ominus" $ do

    it "has its defining property" $
      property (\xs ys -> oplus ys (ominus xs ys) == (xs :: Sequence Int))


cmapIncrement :: Fun (Sequence Int) (Sequence Int) (MapC IncrementC)
cmapIncrement = Closure (Primitive (uncurry cmap) (\(cf, cxs) (df, dxs) -> dmap cf df cxs dxs)) cincrement

dmapIncrement :: DFun (Sequence Int) (Sequence Int) (MapC IncrementC)
dmapIncrement = DClosure (Primitive (uncurry cmap) (\(cf, cxs) (df, dxs) -> dmap cf df cxs dxs)) (DPrimitive (\(cf, cxs) (df, dxs) -> dmap cf df cxs dxs)) cincrement dincrementNil

dmapIncrementPlus2 :: DFun (Sequence Int) (Sequence Int) (MapC IncrementC)
dmapIncrementPlus2 = DClosure (Primitive (uncurry cmap) (\(cf, cxs) (df, dxs) -> dmap cf df cxs dxs)) (DPrimitive (\(cf, cxs) (df, dxs) -> dmap cf df cxs dxs)) cincrement dincrementPlus2


instance Arbitrary (ValidChange (Sequence Int)) where
  arbitrary = do
    s <- arbitrary
    ds <- validSequenceChanges (const arbitrary) s
    return (ValidChange s ds)
  shrink (ValidChange s ds) = do
    ds' <- init (inits (DList.toList ds))
    return (ValidChange s (DList.fromList ds'))

instance Arbitrary (ValidChange (Sequence (Sequence Int))) where
  arbitrary = do
    s <- arbitrary
    ds <- validSequenceChanges (validSequenceChanges (const arbitrary)) s
    return (ValidChange s ds)
  shrink (ValidChange s ds) = do
    ds' <- init (inits (DList.toList ds))
    return (ValidChange s (DList.fromList ds'))


validSequenceChanges :: (Arbitrary a, ChangeStruct a) => (a -> Gen (Dt a)) -> Sequence a -> Gen (Dt (Sequence a))
validSequenceChanges validChange s = do
  let loop _ 0 = do
        return []
      loop s' k = do
        ds <- validSequenceChange validChange s'
        let u = oplusSingle s' ds
        dss <- loop u (k - 1)
        return (ds : dss)
  fmap DList.fromList (sized (loop s))


validSequenceChange :: (Arbitrary a) => (a -> Gen (Dt a)) -> Sequence a -> Gen (AtomicChange a)
validSequenceChange validChange s = do
  let l = length s
  ds <- oneof [
    (do
      i <- choose (0, l)
      a <- arbitrary
      return (Insert i a)),
    (do
      i <- choose (0, l)
      n <- choose (0, l - i)
      return (Delete i n)),
    (do
      i <- choose (0, l)
      n <- choose (0, l - i)
      j <- choose (0, l - n)
      return (Shift i n j)),
    (case l of
      0 -> do
        return (Insert 0 (fromList []))
      _ -> do
        i <- choose (0, l - 1)
        da <- validChange (index s i)
        return (ChangeAt i da))]
  return ds


instance (Arbitrary a) => Arbitrary (Sequence a) where
  arbitrary = arbitrary >>= return . S
  shrink = genericShrink

