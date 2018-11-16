{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module BagSpec where

import CorrectnessProperty (
  correctnessProperty)

import Data.Inc.ChangeStruct (
  ChangeStruct(Dt, oplus), nil)
import Data.Inc.Int (
  cplus, PlusC, dplus)
import Data.Inc.Function (
  Fun(Primitive, Closure), DFun(DPrimitive, DClosure))
import Data.Inc.Bag (
  Bag, Changes(Changes),
  foldGroup, cfoldGroup, FoldGroupC(FoldGroupC), dfoldGroup,
  cmap, MapC(MapC), dmap,
  cfoldMapGroup, FoldMapGroupC(FoldMapGroupC), dfoldMapGroup,
  changeInsert, changeAt,
  Change(Change), oplusSingle)
import qualified Data.Inc.Bag as Bag (
  Bag(Bag, unBag), fromList, map)
import qualified Data.Map as Map (
  fromList, map)


import Test.Hspec (
  Spec, describe, it,
  shouldSatisfy, shouldBe)
import Test.QuickCheck (
  Arbitrary(arbitrary, shrink), NonZero(NonZero, getNonZero), genericShrink,
  property)

import Data.Monoid (
  Sum(Sum))

spec :: Spec
spec = describe "Bag" $ do

  describe "oplusSingle" $ do
    it "inserts an element" $
      oplusSingle smallBag (changeInsert 4) `shouldSatisfy` bagListEq [1, 1, 2, 4]
    it "changes an element" $
      oplusSingle smallBag (changeAt 1 8) `shouldSatisfy` bagListEq [9, 1, 2]

  describe "folding" $ do
    describe "foldGroup" $ do
      it "sums the elements" $
        foldGroup smallSumBag `shouldBe` Sum 3
    describe "cfoldGroup" $ do
      it "sums the elements and returns the cache" $
        cfoldGroup smallSumBag `shouldBe` (Sum 3, foldSumBagCache)
    describe "dfoldGroup" $ do
      it "computes the changeInsertFour in output" $
        dfoldGroup smallSumBag sumChange foldSumBagCache `shouldBe` (Sum 4, updatedFoldSumBagCache)
      it "has the correctness property" $
        property (correctnessProperty @(Bag (Sum Int)) (Primitive cfoldGroup dfoldGroup) (DPrimitive dfoldGroup))

  describe "mapping" $ do

    describe "map" $ do
      it "maps over the elements" $
        Bag.map increment smallBag `shouldBe`
          Bag.fromList [2, 2, 3]

    describe "cmap" $ do
      it "maps over the elements and returns the cache" $
        cmap cincrement smallBag `shouldBe`
          (Bag.fromList [2, 2, 3], mapBagCache)
      it "produces the expected cache after a bag update" $
        cmap cincrement (smallBag `oplus` changeInsertFour) `shouldBe`
          (Bag.fromList [2, 2, 3, 5], mapBagCache2)
      it "produces the expected cache after a function update" $
        cmap cincrementPlusY (smallBag `oplus` changeInsertFour) `shouldBe`
          (Bag.fromList [4, 4, 5, 7], mapBagCache3)
      it "produces the expected cache after an element changeInsertFour" $
        cmap cincrementPlusY (smallBag `oplus` changeElement) `shouldBe`
          (Bag.fromList [12, 4, 5], mapBagCache4)
      it "produces the expected cache after an existing element is inserted" $
        cmap cincrementPlusY (smallBag `oplus` changeExisting) `shouldBe`
          (Bag.fromList [4, 4, 5, 5], mapBagCache5)
      it "produces the expected cache after element changes to another element" $
        cmap cincrementPlusY (smallBag `oplus` changeExistingElement) `shouldBe`
          (Bag.fromList [4, 5, 5], mapBagCache6)

    describe "dmap" $ do
      it "maps the function over the changeInsertFour" $
        dmap cincrement dincrementNil smallBag changeInsertFour mapBagCache `shouldBe`
          (mapDIncrementChange, mapBagCache2)
      it "works with a changing function" $
        dmap cincrement dincrementPlus2 smallBag changeInsertFour mapBagCache `shouldBe`
          (mapDPlusYChange, mapBagCache3)
      it "handles changes to individual elements" $
        dmap cincrement dincrementPlus2 smallBag changeElement mapBagCache `shouldBe`
          (mapElementChange, mapBagCache4)
      it "works when inserting an element that already exists" $
        dmap cincrement dincrementPlus2 smallBag changeExisting mapBagCache `shouldBe`
          (mapExistingChange, mapBagCache5)
      it "works when changing an element that occurs multiple times" $
        dmap cincrement dincrementPlus2 smallBag changeExistingElement mapBagCache `shouldBe`
          (mapExistingElementChange, mapBagCache6)
      it "works even when the multiplicities of the changes disagree with the bag" $
        dmap cincrement dincrementPlus2 (Bag.fromList []) changeNonExistingElement (MapC (Map.fromList [])) `shouldBe`
          (mapNonExistingElementChange, mapBagCache7)
      it "works for counting" $
        dmap cinSumOne dinSumOne (Bag.fromList []) (Changes [Change 0 (-1) 1 0]) (MapC (Map.fromList [])) `shouldBe`
          (Changes [Change 1 0 1 0], MapC (Map.fromList [(-1, (Sum 1, (1, Sum 1))), (0, (Sum 1, (1, Sum 1)))]))
      it "has the correctness property" $
        property (correctnessProperty cmapIncrement dmapIncrementPlus2)
      it "has the correctness property on nil changes" $
        property (correctnessProperty cmapIncrement dmapIncrement)

  describe "dfoldMapGroup" $ do
    it "has the correctness property" $
      property (correctnessProperty cfoldMapGroupInSumOne dfoldMapGroupInSumOne)

  describe "cincrement" $ do
    it "has the correctness property" $
      property (correctnessProperty cincrement dincrementPlus2)



smallSumBag :: Bag (Sum Int)
smallSumBag = Bag.fromList (map Sum [1, 2, (-2), 2])

smallBag :: Bag Int
smallBag = Bag.fromList [1, 1, 2]


sumChange :: Dt (Bag (Sum Int))
sumChange = Changes [Change 4 (Sum 0) 0 1]

changeInsertFour :: Dt (Bag Int)
changeInsertFour = Changes [changeInsert 4]

changeElement :: Dt (Bag Int)
changeElement = Changes [changeAt 1 8]

changeExisting :: Dt (Bag Int)
changeExisting = Changes [changeInsert 2]

changeExistingElement :: Dt (Bag Int)
changeExistingElement = Changes [changeAt 1 1]

changeNonExistingElement :: Dt (Bag Int)
changeNonExistingElement = Changes [Change 0 0 1 2]


mapDIncrementChange :: Dt (Bag Int)
mapDIncrementChange = Changes [changeInsert 5]

mapDPlusYChange :: Dt (Bag Int)
mapDPlusYChange = Changes [Change 2 2 2 0, changeAt 3 2, Change 5 2 0 1]

mapElementChange :: Dt (Bag Int)
mapElementChange = Changes [Change 2 2 1 0,Change 3 2 1 0,Change 2 10 1 0]

mapExistingChange :: Dt (Bag Int)
mapExistingChange = Changes [Change 2 2 2 0, changeAt 3 2,Change 3 2 0 1]

mapExistingElementChange :: Dt (Bag Int)
mapExistingElementChange = Changes [Change 2 2 1 0,Change 3 2 1 0,Change 2 3 1 0]

mapNonExistingElementChange :: Dt (Bag Int)
mapNonExistingElementChange = Changes [Change 1 2 (-1) 0, Change 1 2 1 2]


foldSumBagCache :: FoldGroupC
foldSumBagCache = FoldGroupC

updatedFoldSumBagCache :: FoldGroupC
updatedFoldSumBagCache = FoldGroupC

mapBagCache :: MapC Int Int IncrementC
mapBagCache =
  MapC (Map.fromList [(1,(2,())), (2,(3,()))])

mapBagCache2 :: MapC Int Int IncrementC
mapBagCache2 =
  MapC (Map.fromList [(1,(2,())), (2,(3,())), (4,(5,()))])

mapBagCache3 :: MapC Int Int IncrementC
mapBagCache3 =
  MapC (Map.fromList [(1,(4,())), (2,(5,())), (4,(7,()))])

mapBagCache4 :: MapC Int Int IncrementC
mapBagCache4 =
  MapC (Map.fromList [(1,(4,())),(9,(12,())), (2,(5,()))])

mapBagCache5 :: MapC Int Int IncrementC
mapBagCache5 =
  MapC (Map.fromList [(1,(4,())), (2,(5,()))])

mapBagCache6 :: MapC Int Int IncrementC
mapBagCache6 =
  MapC (Map.fromList [(1,(4,())), (2,(5,()))])

mapBagCache7 :: MapC Int Int IncrementC
mapBagCache7 =
  MapC (Map.fromList [(0,(3,()))])


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

cincrementPlusY :: Fun Int Int IncrementC
cincrementPlusY = oplus cincrement dincrementPlus2


cmapIncrement :: Fun (Bag Int) (Bag Int) (MapC Int Int IncrementC)
cmapIncrement = Closure (Primitive (uncurry cmap) (\(cf, cm) (df, dm) -> dmap cf df cm dm)) cincrement

dmapIncrement :: DFun (Bag Int) (Bag Int) (MapC Int Int IncrementC)
dmapIncrement = DClosure
  (Primitive (uncurry cmap) (\(cf, cm) (df, dm) -> dmap cf df cm dm))
  (DPrimitive (\(cf, cm) (df, dm) -> dmap cf df cm dm))
  cincrement
  dincrementNil

dmapIncrementPlus2 :: DFun (Bag Int) (Bag Int) (MapC Int Int IncrementC)
dmapIncrementPlus2 = DClosure
  (Primitive (uncurry cmap) (\(cf, cm) (df, dm) -> dmap cf df cm dm))
  (DPrimitive (\(cf, cm) (df, dm) -> dmap cf df cm dm))
  cincrement
  dincrementPlus2


cfoldMapGroupInSumOne :: Fun (Bag Int) (Sum Int) (FoldMapGroupC Int (Sum Int) InSumOneC)
cfoldMapGroupInSumOne = Closure
  (Primitive (uncurry cfoldMapGroup) (uncurryDerivative2 dfoldMapGroup))
  cinSumOne

dfoldMapGroupInSumOne :: DFun (Bag Int) (Sum Int) (FoldMapGroupC Int (Sum Int) InSumOneC)
dfoldMapGroupInSumOne = DClosure
  (Primitive (uncurry cfoldMapGroup) (uncurryDerivative2 dfoldMapGroup))
  (DPrimitive (uncurryDerivative2 dfoldMapGroup))
  cinSumOne
  dinSumOne


cinSumOne :: Fun Int (Sum Int) InSumOneC
cinSumOne = Primitive (\x -> (Sum 1, (1, Sum 1))) (\x dx (ci, cc) -> (Sum 0, (ci, cc)))

type InSumOneC = (Int, Sum Int)

dinSumOne :: DFun Int (Sum Int) InSumOneC
dinSumOne = DPrimitive (\x dx (ci, cc) -> (Sum 0, (ci, cc)))


uncurryDerivative2 ::
  (a1 -> Dt a1 -> a2 -> Dt a2 -> c -> (Dt b, c)) ->
  ((a1, a2) -> Dt (a1, a2) -> c -> (Dt b, c))
uncurryDerivative2 df (a1, a2) (da1, da2) = df a1 da1 a2 da2


instance (Arbitrary a, Ord a) => Arbitrary (Bag a) where
  arbitrary = arbitrary >>= return . Bag.Bag . Map.map getNonZero
  shrink = map (Bag.Bag . Map.map getNonZero) . shrink . Map.map NonZero . Bag.unBag

instance Arbitrary (Change Int) where
  arbitrary = do
    a <- arbitrary
    da <- arbitrary
    n <- arbitrary
    dn <- arbitrary
    return (Change a da n dn)
  shrink = genericShrink

instance Arbitrary (Change (Sum Int)) where
  arbitrary = do
    a <- arbitrary
    da <- arbitrary
    n <- arbitrary
    dn <- arbitrary
    return (Change a da n dn)
  shrink = genericShrink

instance Arbitrary (Change (Int, Int)) where
  arbitrary = do
    a <- arbitrary
    da <- arbitrary
    n <- arbitrary
    dn <- arbitrary
    return (Change a da n dn)
  shrink = genericShrink

instance Arbitrary (Changes Int) where
  arbitrary = do
    changes <- arbitrary
    return (Changes changes)

instance Arbitrary (Changes (Sum Int)) where
  arbitrary = do
    changes <- arbitrary
    return (Changes changes)

instance Arbitrary (Changes (Int, Int)) where
  arbitrary = do
    changes <- arbitrary
    return (Changes changes)

bagListEq :: (Ord a) => [a] -> Bag a -> Bool
bagListEq as bag = (Bag.fromList as) == bag

