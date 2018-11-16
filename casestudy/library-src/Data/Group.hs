{-# LANGUAGE FlexibleInstances #-}
module Data.Group where

import Data.Monoid

class Monoid g => Group g where
  invert :: g -> g

instance Num a => Group (Sum a) where
  invert n = - n

-- Delete this instance after implementing intersectionWith
instance Group (Sum Int, Sum Int) where
  invert (a, b) = (invert a, invert b)

