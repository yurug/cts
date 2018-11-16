module Main where

import qualified BagSpec (
  spec)
import qualified BagGeneratedSpec (
  spec)
import qualified MapSpec (
  spec)
import qualified MapGeneratedSpec (
  spec)
import qualified SequenceSpec (
  spec)
import qualified SequenceGeneratedSpec (
  spec)

import Test.Hspec (
  hspec)


main :: IO ()
main = hspec (do
  BagSpec.spec
  BagGeneratedSpec.spec
  MapSpec.spec
  MapGeneratedSpec.spec
  SequenceSpec.spec
  SequenceGeneratedSpec.spec)

