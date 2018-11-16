{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Data.Inc.Int where

import Data.Inc.ChangeStruct (
  Dt)

import Control.DeepSeq (
  NFData)

import GHC.Generics (
  Generic)


type PlusC = ()

cplus :: (Int, Int) -> (Int, PlusC)
cplus (x, y) = let
  !r = x + y
  in (r, ())

dplus :: (Int, Int) -> Dt (Int, Int) -> PlusC -> (Dt Int, PlusC)
dplus _ (dx, dy) () = (dx + dy, ())


data DivC = DivC
  deriving (Show, Eq, Generic, NFData)

cdiv :: Int -> Int -> (Int, DivC)
cdiv a1 a2 = let
  !r = div a1 a2
  in (r, DivC)

ddiv :: Int -> Dt Int -> Int -> Dt Int -> DivC -> (Dt Int, DivC)
ddiv ca1 da1 ca2 da2 DivC = let
  r = (ca1 + da1) `div` (ca2 + da2) - (ca1 `div` ca2)
  in (r, DivC)


mul :: Int -> Int -> Int
mul x y = x * y

data MulC = MulC
  deriving (Show, Eq, Generic, NFData)

cmul :: Int -> Int -> (Int, MulC)
cmul x y = let
  !r = x * y
  in (r, MulC)

dmul :: Int -> Dt Int -> Int -> Dt Int -> MulC -> (Dt Int, MulC)
dmul cx dx cy dy MulC = let
  r  = (cx + dx) * (cy + dy) - cx * cy
  in (r, MulC)

