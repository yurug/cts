{-# LANGUAGE StandaloneDeriving #-}
module MapGeneratedSpec where

import BagSpec ()
import CorrectnessProperty (
  correctnessProperty, fullyEvaluates)

import Data.Inc.Map.Generated (
  cindexedJoin, dindexedJoin)

import Data.Inc.ChangeStruct (
  Dt)
import Data.Inc.Function (
  Fun(Primitive), DFun(DPrimitive))
import Data.Inc.Bag (
  Bag, fromList, Changes(Changes), changeInsert)

import Test.Hspec (
  Spec, describe, it)
import Test.QuickCheck (
  property)


spec :: Spec
spec = describe "Map" $ do

  describe "indexedJoin" $ do

    it "has the correctness property" $
      property (correctnessProperty (Primitive cindexedJoin dindexedJoin) (DPrimitive dindexedJoin))

    it "fully evaluates the result and cache" $ do
      fullyEvaluates cindexedJoin dindexedJoin initialTables tableChange


size :: Int
size = 1024

initialTables :: (Bag (Int, Int), Bag (Int, Int))
initialTables = (orders, lineItems) where

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


deriving instance (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f, Eq g,
                   Eq h, Eq i, Eq j, Eq k, Eq l, Eq m, Eq n, Eq o, Eq p, Eq q, Eq r)
               => Eq (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r)

deriving instance (Show a, Show b, Show c, Show d, Show e, Show f, Show g,
                   Show h, Show i, Show j, Show k, Show l, Show m, Show n, Show o, Show p, Show q, Show r)
               => Show (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r)


