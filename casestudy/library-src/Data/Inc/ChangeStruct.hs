{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Inc.ChangeStruct where

import Data.Proxy (Proxy(Proxy))
import Data.Bits (xor)
import Data.Monoid (Sum(..))
import Control.Applicative (liftA2)

import Control.DeepSeq ()

class ChangeStruct t where
  type Dt t = r | r -> t
  oplus :: t -> Dt t -> t

class ChangeStruct t => DiffChangeStruct t where
  ominus :: t -> t -> Dt t

class ChangeStruct t => OnilChangeStruct t where
  -- Proxy is used to encode explicit type application.
  onil :: Proxy t -> Dt t

class ChangeStruct t => NilChangeStruct t where
  nil :: t -> Dt t

-- | Deprecated: only for internal use
class ChangeStruct a => CompChangeStruct a where
  -- | Compose change dx1 with dx2, so that
  -- x `oplus` (dx1 `ocompose` dx2) == x `oplus` dx1 `oplus` dx2.
  -- Beware: this is flipped relative to composition in the incremental-computing package.
  ocompose :: Dt a -> Dt a -> Dt a

-- This instance can't be defined as it triggers overlaps everywhere:

-- instance (ChangeStruct t, OnilChangeStruct t) => NilChangeStruct t where
--   nil (_ :: t) = onil (Proxy :: Proxy t)

-- | Useful for deriving NilChangeStruct instances from OnilChangeStruct instances. Stereotypical use:
-- instance OnilChangeStruct t where
--   onil = ...
--
-- instance NilChangeStruct t where
--   nil = nilFromOnil
nilFromOnil :: OnilChangeStruct t => t -> Dt t
nilFromOnil _ = onil (Proxy :: Proxy t)

class NilChangeStruct t => NilTestable t where
  isNil :: Dt t -> Bool

instance ChangeStruct () where
  type Dt () = ()
  oplus _ _ = ()
instance OnilChangeStruct () where
  onil _ = ()
instance NilChangeStruct () where
   nil = nilFromOnil
instance NilTestable () where
  isNil () = True

funIdChange :: (ChangeStruct a, DiffChangeStruct b) => (a -> b) -> a -> Dt a -> Dt b
funIdChange f = \x dx -> f (x `oplus` dx) `ominus` f x

instance (NilChangeStruct a, ChangeStruct b) => ChangeStruct (a -> b) where
  type Dt (a -> b) = a -> Dt a -> Dt b
  f `oplus` df = \x -> f x `oplus` df x (nil x)

instance (NilChangeStruct a, DiffChangeStruct b) => NilChangeStruct (a -> b) where
  nil = funIdChange

instance (NilChangeStruct a, DiffChangeStruct b) => DiffChangeStruct (a -> b) where
  g `ominus` f = \x dx -> g (x `oplus` dx) `ominus` f x

-- Booleans form a group (with xor) which gives rise to a change structure,
-- where `False` is the nil change and `True` is the only possible non-nil
-- change. Since we have a universal change structure, we can easily support
-- `onil`.
instance ChangeStruct Bool where
  type Dt Bool = Bool
  oplus = xor
instance OnilChangeStruct Bool where
  onil _ = False
instance DiffChangeStruct Bool where
  ominus = xor

instance ChangeStruct Int where
  type Dt Int = Int
  oplus = (+)
instance OnilChangeStruct Int where
  onil _ = 0
instance NilChangeStruct Int where
   nil = nilFromOnil
instance DiffChangeStruct Int where
  ominus = (-)
instance CompChangeStruct Int where
  ocompose = (+)
instance NilTestable Int where
  isNil = (== 0)

instance ChangeStruct Integer where
  type Dt Integer = Integer
  oplus = (+)
instance OnilChangeStruct Integer where
  onil _ = 0
instance DiffChangeStruct Integer where
  ominus = (-)
instance CompChangeStruct Integer where
  ocompose = (+)

instance ChangeStruct (Sum Int) where
  type Dt (Sum Int) = Sum (Dt Int)
  oplus = liftA2 oplus
instance OnilChangeStruct (Sum Int) where
  onil _ = Sum (onil (Proxy :: Proxy Int))
instance NilChangeStruct (Sum Int) where
  nil = nilFromOnil
instance DiffChangeStruct (Sum Int) where
  ominus = liftA2 ominus
instance CompChangeStruct (Sum Int) where
  ocompose = liftA2 ocompose
instance NilTestable (Sum Int) where
  isNil = (== 0)

instance ChangeStruct [a] where
  type Dt [a] = [a]
  oplus = (++)
instance OnilChangeStruct [a] where
  onil _ = []

instance (ChangeStruct a, ChangeStruct b) => ChangeStruct (a, b) where
  type Dt (a, b) = (Dt a, Dt b)
  oplus (a, b) (da, db) = let
    !ua = oplus a da
    !ub = oplus b db
    in (ua, ub)

instance (OnilChangeStruct a, OnilChangeStruct b) => OnilChangeStruct (a, b) where
  onil (_ :: Proxy (a, b)) = (onil (Proxy :: Proxy a), onil (Proxy :: Proxy b))

instance (NilChangeStruct a, NilChangeStruct b) => NilChangeStruct (a, b) where
  nil (a, b) = (nil a, nil b)

instance (DiffChangeStruct a, DiffChangeStruct b) => DiffChangeStruct (a, b) where
  (a2, b2) `ominus` (a1, b1) = (a2 `ominus` a1, b2 `ominus` b1)

errInvChange :: t
errInvChange = error "invalid change"


