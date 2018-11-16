{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module MapSpec where

import CorrectnessProperty (
  correctnessProperty)

import Data.Inc.ChangeStruct (
  ChangeStruct(Dt, oplus))
import Data.Inc.Function (
  Fun(Primitive, Closure), DFun(DPrimitive, DClosure))
import Data.Inc.Int (
  mul, MulC, cmul, dmul)
import Data.Inc.Map (
  Map,
  foldMapGroupWithKey, cfoldMapGroupWithKey, dfoldMapGroupWithKey,
  MergeC, cmerge, dmerge,
  Change(Change), Changes(Changes))
import qualified Data.Inc.Map as Map (
  Map(Map, unMap), fromList)
import qualified Data.Map as Map (
  map)

import Test.Hspec (
  Spec, describe, it,
  shouldBe)
import Test.QuickCheck (
  Arbitrary(arbitrary, shrink), NonZero(NonZero, getNonZero), genericShrink,
  property)

import Data.Monoid (
  Sum(Sum, getSum))


spec :: Spec
spec = describe "Map" $ do

  describe "foldMapGroupWithKey" $ do
    it "fold maps the keys and elements" $
      foldMapGroupWithKey mulSum exampleMap `shouldBe`
        Sum 14

    it "has the correctness property on nil function changes" $
      property (correctnessProperty
        (Closure
          (Primitive (uncurry cfoldMapGroupWithKey) (\(cf, cm) (df, dm) -> dfoldMapGroupWithKey cf df cm dm))
          (Primitive cmulSum dmulSum))
        (DClosure
          (Primitive (uncurry cfoldMapGroupWithKey) (\(cf, cm) (df, dm) -> dfoldMapGroupWithKey cf df cm dm))
          (DPrimitive (\(cf, cm) (df, dm) -> dfoldMapGroupWithKey cf df cm dm))
          (Primitive cmulSum dmulSum)
          (DPrimitive dmulSum)))

    it "has the correctness property on non-nil function changes" $ do
      let mult3Closure = Closure (Primitive cmulSum3 dmulSum3) 4
          mult3Change = DClosure (Primitive cmulSum3 dmulSum3) (DPrimitive dmulSum3) 4 3
          foldMapGroupWithKeyClosure = Closure
            (Primitive (uncurry cfoldMapGroupWithKey) (\(cf, cm) (df, dm) -> dfoldMapGroupWithKey cf df cm dm))
            mult3Closure
          foldMapGroupWithKeyChange = DClosure
            (Primitive (uncurry cfoldMapGroupWithKey) (\(cf, cm) (df, dm) -> dfoldMapGroupWithKey cf df cm dm))
            (DPrimitive (\(cf, cm) (df, dm) -> dfoldMapGroupWithKey cf df cm dm))
            mult3Closure
            mult3Change
      property (correctnessProperty foldMapGroupWithKeyClosure foldMapGroupWithKeyChange)

  describe "mulSum" $ do
    it "has the correctness property" $
      property (correctnessProperty (Primitive cmulSum dmulSum) (DPrimitive dmulSum))

  describe "mulSum3" $ do
    it "has the correctness property" $
      property (correctnessProperty (Primitive cmulSum3 dmulSum3) (DPrimitive dmulSum3))

  describe "merge" $ do
    it "has the correctness property" $
      property (correctnessProperty
        (Primitive (uncurry cmerge) (\(cm1, cm2) (dm1, dm2) -> dmerge cm1 dm1 cm2 dm2) :: Fun (Map (Sum Int) (Sum Int), Map (Sum Int) (Sum Int)) (Map (Sum Int) (Sum Int, Sum Int)) MergeC) (DPrimitive (\(cm1, cm2) (dm1, dm2) -> dmerge cm1 dm1 cm2 dm2)))


exampleMap :: Map (Sum Int) (Sum Int)
exampleMap = Map.fromList [
  (1, 1),
  (2, 2),
  (3, 3)]


mulSum :: Sum Int -> Sum Int -> Sum Int
mulSum sx sy = let
  x = getSum sx
  y = getSum sy
  i = mul x y
  r = Sum i
  in r

type MulSumC = MulC

cmulSum :: (Sum Int, Sum Int) -> (Sum Int, MulSumC)
cmulSum (sx, sy) = let
  x = getSum sx
  y = getSum sy
  (i, ci) = cmul x y
  r = Sum i
  in (r, ci)

dmulSum :: (Sum Int, Sum Int) -> Dt (Sum Int, Sum Int) -> MulSumC -> (Dt (Sum Int), MulSumC)
dmulSum (csx, csy) (dsx, dsy) ci = let
  cx = getSum csx
  dx = getSum dsx
  cy = getSum csy
  dy = getSum dsy
  (di, ui) = dmul cx dx cy dy ci
  dr = Sum di
  in (dr, ui)


mulSum3 :: (Sum Int, (Sum Int, Sum Int)) -> Sum Int
mulSum3 (x, (y, z)) = let
  i = mulSum y z
  r = mulSum x i
  in r

type MulSum3C = (Sum Int, MulC, Sum Int, MulC)

cmulSum3 :: (Sum Int, (Sum Int, Sum Int)) -> (Sum Int, MulSum3C)
cmulSum3 (x, (y, z)) = let
  (i, ci) = cmulSum (y, z)
  (r, cr) = cmulSum (x, i)
  in (r, (i, ci, r, cr))

dmulSum3 :: (Sum Int, (Sum Int, Sum Int)) -> Dt (Sum Int, (Sum Int, Sum Int)) -> MulSum3C -> (Dt (Sum Int), MulSum3C)
dmulSum3 (cx, (cy, cz)) (dx, (dy, dz)) (ci, cci, cr, ccr) = let
  (di, uci) = dmulSum (cy, cz) (dy, dz) cci
  ui = oplus ci di
  (dr, ucr) = dmulSum (cx, ci) (dx, di) ccr
  ur = oplus cr dr
  in (dr, (ui, uci, ur, ucr))


instance (Arbitrary k, Ord k, Arbitrary a, Num a, Eq a) =>
  Arbitrary (Map k a) where
    arbitrary = arbitrary >>= return . Map.Map . Map.map getNonZero
    shrink = map (Map.Map . Map.map getNonZero) . shrink . Map.map NonZero . Map.unMap

instance Arbitrary (Change (Sum Int) (Sum Int)) where
  arbitrary = do
    a <- arbitrary
    da <- arbitrary
    n <- arbitrary
    dn <- arbitrary
    return (Change a da n dn)
  shrink = genericShrink

instance Arbitrary (Change Int (Sum Int)) where
  arbitrary = do
    a <- arbitrary
    da <- arbitrary
    n <- arbitrary
    dn <- arbitrary
    return (Change a da n dn)
  shrink = genericShrink

instance Arbitrary (Changes (Sum Int) (Sum Int)) where
  arbitrary = do
    changes <- arbitrary
    return (Changes changes)

instance Arbitrary (Changes Int (Sum Int)) where
  arbitrary = do
    changes <- arbitrary
    return (Changes changes)

