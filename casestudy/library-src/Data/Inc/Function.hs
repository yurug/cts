{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
module Data.Inc.Function where

import Data.Inc.ChangeStruct (
  ChangeStruct(Dt, oplus), NilChangeStruct(nil),
  NilTestable(isNil))

import Control.DeepSeq (
  NFData(rnf))
import GHC.Generics (
  Generic)


-- | A function is either a primitive function or a partially applied function.
data Fun a b c where
  Primitive ::
    !(a -> (b, c)) -> !(a -> Dt a -> c -> (Dt b, c)) -> Fun a b c
  Closure :: (NilTestable e, NilChangeStruct e, NFData e) =>
    !(Fun (e, a) b c) -> !e -> Fun a b c

instance Eq (Fun a b c) where
  _ == _ = True

instance Show (Fun a b c) where
  show (Primitive _ _) = "<function>"
  show (Closure _ _) = "<closure>"

instance NFData (Fun a b c) where
  rnf (Primitive cf df) = rnf cf `seq` rnf df
  rnf (Closure cf e) = rnf cf `seq` rnf e


-- | A function change is either the nil change of a primitive function
-- or a change to a partial application.
-- A function change 'DPrimitive df' for a primitive function 'Primitive f'
-- is valid if df is the derivative of f.
-- A function change 'DClosure f1 df e1 de' for a function 'Closure f2 e2' is valid
-- iff 'f1 == f2' and 'e1 == e2'.
data DFun a b c where
  DPrimitive ::
    !(a -> Dt a -> c -> (Dt b, c)) -> DFun a b c
  DClosure :: (NilTestable e, NilChangeStruct e, NFData e) =>
    !(Fun (e, a) b c) -> !(DFun (e, a) b c) -> !e -> !(Dt e) -> DFun a b c

-- | A primitive function change is a nil change.
-- A closure is a nil change if the environment change is nil and
-- the function change is nil.
isNilDFun :: DFun a b c -> Bool
isNilDFun (DPrimitive _) = True
isNilDFun (DClosure _ dfc _ de) = isNil dfc && isNil de

-- | Apply a function
apply :: Fun a b c -> (a -> (b, c))
apply (Primitive cf _) a = cf a
apply (Closure cf e) a = apply cf (e, a)

-- | Apply a function to two arguments
apply2 :: Fun (a1, a2) b c -> (a1 -> a2 -> (b, c))
apply2 cf a1 a2 = apply cf (a1, a2)

-- | Apply an incremental function
dapply :: Fun a b c -> DFun a b c -> (a -> Dt a -> c -> (Dt b, c))
dapply _ (DPrimitive df) a da c = df a da c
dapply _ (DClosure cf df e de) a da c = dapply cf df (e, a) (de, da) c

-- | Apply an incremental function to two arguments
dapply2 :: Fun (a1, a2) b c -> DFun (a1, a2) b c -> (a1 -> Dt a1 -> a2 -> Dt a2 -> c -> (Dt b, c))
dapply2 cf df a1 da1 a2 da2 c = dapply cf df (a1, a2) (da1, da2) c

-- | Update a function
-- The only valid change for a primitive function is its nil change
-- For closures we have to update the environment. Problem:
-- We can't be sure that the environment and change's types match.
-- Solution: pack the environment together with change.
-- Here we use the fact that the function and environment in the base
-- value are the same as the function and environment in the function change.
oplusFun :: Fun a b c -> DFun a b c -> Fun a b c
oplusFun (Primitive cf df) (DPrimitive _) =
  Primitive cf df
oplusFun (Closure _ _) (DClosure cf dfc e de) =
  let !uf = oplusFun cf dfc
      !ue = oplus e de
  in Closure uf ue
oplusFun _ _ =
  error "invalid function update"

-- | The derivative of a function (its nil change)
derivFun :: Fun a b c -> DFun a b c
derivFun (Primitive _ df) = DPrimitive df
derivFun (Closure cf e) = DClosure cf (derivFun cf) e (nil e)

-- | We can compose two function changes.
-- When we compose two closure function changes we use the fact that in order for
-- the second function change to be valid it has to already contain the result of
-- applying the first function change.
composeDFun :: DFun a b c -> DFun a b c -> DFun a b c
composeDFun (DPrimitive dfc1) (DPrimitive _) =
  DPrimitive dfc1
composeDFun (DClosure _ _ _ _) (DClosure fc2 dfc2 e2 de2) =
  DClosure fc2 dfc2 e2 de2
composeDFun _ _ =
  error "invalid function composition"

-- | We can partially apply a function to get a closure
closure :: (e -> a -> b) -> (e -> (a -> b))
closure f e = f e

data ClosureC = ClosureC
  deriving (Eq, Show, Generic)

instance NFData ClosureC

-- | Caching version of closure creation.
-- The cache contains the original inputs i.e. creating a closure is not
-- self-maintaineable.
cclosure :: (NilTestable e, NFData e) =>
  Fun (e, a) b c -> e -> (Fun a b c, ClosureC)
cclosure cf ce =
  (Closure cf ce, ClosureC)

-- | Incremental version of closure creation
-- Here we pack the original function and environment together with their changes.
dclosure :: (NilChangeStruct e, NilTestable e, NFData e) =>
  Fun (e, a) b c -> DFun (e, a) b c -> e -> Dt e -> ClosureC -> (DFun a b c, ClosureC)
dclosure cf df ce de ClosureC =
  (DClosure cf df ce de, ClosureC)

instance ChangeStruct (Fun a b c) where
  type Dt (Fun a b c) = DFun a b c
  oplus = oplusFun

instance NilChangeStruct (Fun a b c) where
  nil = derivFun

instance NilTestable (Fun a b c) where
  isNil dfc = isNilDFun dfc

-- Since this composition function is problematic, do not export it through typeclasses, which allow using it implicitly.
-- instance CompChangeStruct (Fun a b c) where
--   ocompose = composeDFun






