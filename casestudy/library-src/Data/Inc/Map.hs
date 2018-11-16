{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Inc.Map where

import Prelude hiding (map)

import Data.Inc.ChangeStruct (
  ChangeStruct(Dt, oplus),
  NilChangeStruct(nil), NilTestable(isNil))
import Data.Inc.Function (
  Fun, apply, dapply)
import Data.Inc.Group (
  Group(invert), GroupChangeStruct(inject))

import qualified Data.Map.Strict as Map (
  Map, fromList, fromListWith, empty, singleton,
  toList, keys, elems,
  union, unionWith, difference, mergeWithKey,
  map, foldMapWithKey, mapWithKey, filterWithKey,
  lookup, member, alter)

import Data.Maybe (
  fromMaybe)
import Control.Monad (
  guard)

import Control.DeepSeq (
  NFData)
import GHC.Generics (
  Generic)


newtype Map k a = Map { unMap :: Map.Map k a }
  deriving (Eq, Ord, Show, NFData)

-- API

instance (Ord k, Monoid a, Eq a) => Monoid (Map k a) where
  mempty = empty
  mappend = unionWithGroup

instance (Ord k, Group a, Eq a) => Group (Map k a) where
  invert = map invert

fromList :: (Ord k) => [(k, a)] -> Map k a
fromList = Map . Map.fromList

toList :: Map k a -> [(k, a)]
toList = Map.toList . unMap

-- (f k) has to be a group homomorphism
-- For example 'f k empty' has to be 'empty'
foldMapGroupWithKey :: (Monoid b) => (k -> a -> b) -> Map k a -> b
foldMapGroupWithKey f = Map.foldMapWithKey f . unMap

empty :: Map k a
empty = Map Map.empty

singleton :: (Monoid a, Eq a) => k -> a -> Map k a
singleton k a = Map (if a == mempty then Map.empty else Map.singleton k a)

unionWithGroup :: (Ord k, Monoid a, Eq a) => Map k a -> Map k a -> Map k a
unionWithGroup m1 m2 = Map (Map.mergeWithKey f id id (unMap m1) (unMap m2)) where
  f _ a1 a2 = let a = mappend a1 a2 in if a == mempty then Nothing else Just a

merge :: (Ord k, Monoid a, Monoid b) => Map k a -> Map k b -> Map k (a, b)
merge m1 m2 = Map (Map.mergeWithKey
  (\_ a b -> Just (a, b))
  (Map.map (\a -> (a, mempty)))
  (Map.map (\b -> (mempty, b)))
  (unMap m1)
  (unMap m2))

-- f has to be a group homomorphism
-- For example 'f empty' has to be 'empty'
map :: (Ord k, Monoid b, Eq b) => (a -> b) -> Map k a -> Map k b
map f = foldMapGroupWithKey (\k a -> singleton k (f a))

foldGroup :: (Monoid a) => Map k a -> a
foldGroup = foldMapGroupWithKey (\_ a -> a)

-- f has to be a group homomorphism
foldMapGroup :: (Monoid b) => (a -> b) -> Map k a -> b
foldMapGroup f = foldMapGroupWithKey (\_ a -> f a)

-- Caching API

cfoldMapGroupWithKey :: (Monoid b) =>
  Fun (k, a) b c -> Map k a -> (b, FoldMapGroupWithKeyC k c)
cfoldMapGroupWithKey cf m = let
  elementResultsWithCaches = Map.mapWithKey (curry (apply cf)) (unMap m)
  elementc = Map.mapWithKey (\_ (_, c) -> c) elementResultsWithCaches
  !r = Map.foldMapWithKey (\_ (b, _) -> b) elementResultsWithCaches
  in (r, FoldMapGroupWithKeyC elementc)

data FoldMapGroupWithKeyC k c =
  FoldMapGroupWithKeyC !(Map.Map k c)
    deriving (Show, Eq, Generic)

instance (NFData k, NFData c) => NFData (FoldMapGroupWithKeyC k c)


csingleton :: (Monoid a, Eq a) => k -> a -> (Map k a, SingletonC)
csingleton k a = let
  !r = singleton k a
  in (r, SingletonC)

data SingletonC = SingletonC
  deriving (Show, Eq, Ord, Generic)

instance NFData SingletonC


cmerge ::
  (Ord k, Monoid a, Monoid b) =>
  Map k a -> Map k b -> (Map k (a, b), MergeC)
cmerge m1 m2 = let
  !r = merge m1 m2
  in (r, MergeC)

data MergeC = MergeC
  deriving (Show, Eq, Ord, Generic)

instance NFData MergeC


-- Incremental API


dfoldMapGroupWithKey ::
  (Ord k, NilChangeStruct k,
   Eq a, NilChangeStruct a, GroupChangeStruct a, GroupChangeStruct b) =>
  Fun (k, a) b c -> Dt (Fun (k, a) b c) -> Map k a -> Dt (Map k a) ->
  FoldMapGroupWithKeyC k c -> (Dt b, FoldMapGroupWithKeyC k c)
dfoldMapGroupWithKey cf df cm dm = case isNil df of
  True -> dfoldMapGroupWithKeyNil cf df cm dm
  False -> dfoldMapGroupWithKeyNotNil cf df cm dm


dfoldMapGroupWithKeyNotNil ::
  (Ord k, NilChangeStruct k,
   Group a, Eq a, NilChangeStruct a, GroupChangeStruct a, GroupChangeStruct b) =>
  Fun (k, a) b c -> Dt (Fun (k, a) b c) -> Map k a -> Dt (Map k a) ->
  FoldMapGroupWithKeyC k c -> (Dt b, FoldMapGroupWithKeyC k c)
dfoldMapGroupWithKeyNotNil cf df cm (Changes changes) (FoldMapGroupWithKeyC elementc) = let

  -- XXX avoid this
  um = oplus cm (Changes changes)

  nilValueChanges = Map.map (\_ -> []) elementc
  changeValueChanges = Map.fromListWith (++) (do
    Change k dk a da <- changes
    [(k `oplus` dk, [inject (a `oplus` da)]), (k, [inject (invert a)])])
  valueChanges = Map.unionWith (++) changeValueChanges nilValueChanges

  changesAndCaches = Map.mapWithKey (\k das ->
    let a = fromMaybe mempty (Map.lookup k (unMap cm))
        c = fromMaybe (snd (apply cf (k, a))) (Map.lookup k elementc)
        (db, c') = dapply cf df (k, a) (nil k, inject (foldl oplus mempty das)) c
    in (db,c')) valueChanges

  elementc' = Map.map snd (
    Map.filterWithKey (\k _ -> Map.member k (unMap um)) changesAndCaches)
  dr = inject (
    foldl oplus mempty (Map.elems (Map.map fst changesAndCaches)))

  in (dr, FoldMapGroupWithKeyC elementc')


dfoldMapGroupWithKeyNil ::
  (Ord k, NilChangeStruct k,
   Group a, Eq a, NilChangeStruct a, GroupChangeStruct a, GroupChangeStruct b) =>
  Fun (k, a) b c -> Dt (Fun (k, a) b c) -> Map k a -> Dt (Map k a) ->
  FoldMapGroupWithKeyC k c -> (Dt b, FoldMapGroupWithKeyC k c)
dfoldMapGroupWithKeyNil cf df cm (Changes changes) (FoldMapGroupWithKeyC elementc) = let

  -- XXX avoid this
  um = cm `oplus` (Changes changes)

  valueChanges = Map.fromListWith (++) (do
    Change k dk a da <- changes
    [(k `oplus` dk, [inject (a `oplus` da)]), (k, [inject (invert a)])])

  changesAndCaches = Map.mapWithKey (\k das ->
    let a = fromMaybe mempty (Map.lookup k (unMap cm))
        c = fromMaybe (snd (apply cf (k, mempty))) (Map.lookup k elementc)
        (db, c') = dapply cf df (k, a) (nil k, inject (foldl oplus mempty das)) c
    in (db,c')) valueChanges

  invalidElements = Map.fromList (do
    k <- Map.keys changesAndCaches
    guard (not (Map.member k (unMap um)))
    return (k, ()))

  elementc' = Map.difference
    (Map.union (Map.map snd changesAndCaches) elementc) invalidElements
  dr = inject (
    foldl oplus mempty (Map.elems (Map.map fst changesAndCaches)))

  in (dr, FoldMapGroupWithKeyC elementc')


dsingleton ::
  (ChangeStruct k, ChangeStruct a) =>
  k -> Dt k -> a -> Dt a -> SingletonC -> (Dt (Map k a), SingletonC)
dsingleton ck dk ca da SingletonC =
  (Changes [Change ck dk ca da], SingletonC)


dmerge ::
  (Ord k, NilChangeStruct k,
   Eq a, NilChangeStruct a, GroupChangeStruct a,
   Eq b, NilChangeStruct b, GroupChangeStruct b,
   Group (a, b)) =>
  Map k a -> Dt (Map k a) -> Map k b -> Dt (Map k b) ->
  MergeC -> (Dt (Map k (a, b)), MergeC)
dmerge cma (Changes dma) cmb (Changes dmb) MergeC = let

  uma = cma `oplus` (Changes dma)
  umb = cmb `oplus` (Changes dmb)

  dra = do
    Change k dk a da <- dma
    let dra1 = do
          let b = fromMaybe mempty (Map.lookup k (unMap umb))
          return (Change k (nil k) (mempty, b) (inject (invert a), nil b))
    let dra2 = do
          let b = fromMaybe mempty (Map.lookup (k `oplus` dk) (unMap umb))
          return (Change (k `oplus` dk) (nil (k `oplus` dk)) (mempty, b) (inject (a `oplus` da), nil b))
    dra1 ++ dra2

  drb = do
    Change k dk b db <- dmb
    let drb1 = do
          let a = fromMaybe mempty (Map.lookup k (unMap uma))
          return (Change k (nil k) (a, mempty) (nil a, inject (invert b)))
    let drb2 = do
          let a = fromMaybe mempty (Map.lookup (k `oplus` dk) (unMap uma))
          return (Change (k `oplus` dk) (nil (k `oplus` dk)) (a, mempty) (nil a, inject (b `oplus` db)))
    drb1 ++ drb2

  dr = Changes (dra ++ drb)

  in (dr, MergeC)


-- Changes

data Change k a =
  Change k (Dt k) a (Dt a)
    deriving Generic

deriving instance (Show k, Show (Dt k), Show a, Show (Dt a)) => Show (Change k a)
deriving instance (Eq k, Eq (Dt k), Eq a, Eq (Dt a)) => Eq (Change k a)
instance (NFData k, NFData (Dt k), NFData a, NFData (Dt a)) => NFData (Change k a)

change :: k -> Dt k -> a -> Dt a -> Change k a
change = Change

newtype Changes k a = Changes [Change k a]
  deriving (Generic)

deriving instance (Show k, Show (Dt k), Show a, Show (Dt a)) => Show (Changes k a)
deriving instance (Eq k, Eq (Dt k), Eq a, Eq (Dt a)) => Eq (Changes k a)
deriving instance (NFData k, NFData (Dt k), NFData a, NFData (Dt a)) => NFData (Changes k a)

-- Change struct

oplusSingle :: (Ord k, ChangeStruct k, GroupChangeStruct a, Eq a) =>
  Map k a -> Change k a -> Map k a
oplusSingle m (Change k dk a da) =
  insertNormalize (k `oplus` dk) (a `oplus` da) (insertNormalize k (invert a) m)

insertNormalize :: (Ord k, Monoid a, GroupChangeStruct a, Eq a) => k -> a -> Map k a -> Map k a
insertNormalize k a1 m = Map (Map.alter f k (unMap m)) where
  f ma = let a = oplus a1 (inject (fromMaybe mempty ma)) in
    if a == mempty then Nothing else Just a

oplusMap :: (Ord k, ChangeStruct k, GroupChangeStruct a, Eq a) =>
  Map k a -> Changes k a -> Map k a
oplusMap m (Changes changes) = foldl oplusSingle m changes

instance (Ord k, ChangeStruct k, GroupChangeStruct a, Eq a) =>
  ChangeStruct (Map k a) where
    type Dt (Map k a) = Changes k a
    oplus = oplusMap

instance (Ord k, ChangeStruct k, GroupChangeStruct a, Eq a) =>
  NilChangeStruct (Map k a) where
    nil _ = Changes []

instance (Ord k, NilChangeStruct k, Eq a, GroupChangeStruct a) => GroupChangeStruct (Map k a) where
  inject m = Changes (do
    (k, a) <- toList m
    return (Change k (nil k) mempty (inject a)))


