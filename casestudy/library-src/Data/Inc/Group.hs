{-# LANGUAGE FlexibleInstances #-}
module Data.Inc.Group (GroupChangeStruct(..), module Data.Group) where

import Data.Group
import Data.Inc.ChangeStruct
import Data.Monoid (Sum(..))

class (Group a, ChangeStruct a) => GroupChangeStruct a where
  -- | Inject group elements into changes. Laws:
  -- a `oplus` inject b = a `mappend` b
  inject :: a -> Dt a
{-
Corollaries of the law:
1. a `oplus` inject mempty = a `mappend` mempty = a

2.
With change equivalence:
b `ominus` a == inject (invert a `mappend` b)
but that means:
a `oplus` (b `ominus` a) = a `oplus` inject (invert a `mappend` b)
and the LHS is a, while the RHS is a `mappend` (invert a `mappend` b),
which is |a| by associativity and properties of invert.
-}

instance GroupChangeStruct (Sum Int) where
  inject (Sum a) = Sum a

-- Delete this instance after implementing intersectionWith
instance GroupChangeStruct (Sum Int, Sum Int) where
  inject (a, b) = (inject a, inject b)

{-
TODO: group changes created by inject can be "translated", that it transported
to be applied to other base values. Should we require this to hold in general?
-}
