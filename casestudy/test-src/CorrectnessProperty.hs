{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
module CorrectnessProperty where

import Data.Inc.ChangeStruct (
  ChangeStruct(Dt, oplus))
import Data.Inc.Function (
  apply, dapply, Fun)

import Test.Hspec (
  shouldReturn)
import Test.QuickCheck (
  Property, (===), (.&&.))

import Control.Exception (
  evaluate)
import GHC.AssertNF (
  isNF, assertNF)
import Control.DeepSeq (
  NFData, force)
import GHC.Generics (
  Generic)


correctnessProperty ::
  (ChangeStruct a, ChangeStruct b, Eq b, Show b, Eq c, Show c) =>
  Fun a b c -> Dt (Fun a b c) -> a -> Dt a -> Property
correctnessProperty cf df a da = let
  (initialResult, initialc) = apply cf a
  (changedResult, changedc) = apply (cf `oplus` df) (a `oplus` da)
  (dresult, changedc') = dapply cf df a da initialc
  in (changedResult === initialResult `oplus` dresult) .&&. (changedc === changedc')

data ValidChange a = ValidChange a (Dt a)
  deriving (Generic)

deriving instance (Show a, Show (Dt a)) => Show (ValidChange a)


fullyEvaluates ::
  (NFData a, NFData (Dt a), ChangeStruct b) =>
  (a -> (b, c)) -> (a -> Dt a -> c -> (Dt b, c)) -> a -> Dt a -> IO ()
fullyEvaluates cf df a da = do
  _ <- evaluate (force a)
  _ <- evaluate (force da)
  case cf a of
    (b, c) -> do
      _ <- evaluate b
      isNF b `shouldReturn` True
      isNF c `shouldReturn` True
      case df a da c of
        (db, u) -> do
          let ub = oplus b db
          _ <- evaluate ub
          isNF ub `shouldReturn` True
          isNF u `shouldReturn` True



