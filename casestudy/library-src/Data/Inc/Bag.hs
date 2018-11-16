{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
module Data.Inc.Bag where

import Prelude hiding (map)
import qualified Prelude (map)

import Data.Inc.ChangeStruct (
  ChangeStruct(Dt, oplus),
  NilChangeStruct(nil), NilTestable(isNil))
import Data.Inc.Function (
  Fun, apply, DFun, dapply)
import Data.Group (
  Group(invert))
import Data.Inc.Group (
  GroupChangeStruct(inject))


import Data.Map.Strict (
  Map)
import qualified Data.Map.Strict as Map (
  fromListWith, fromList, empty, singleton,
  toList, keys, foldrWithKey',
  map, mapKeysWith, mapWithKey, filter,
  alter, lookup, member,
  union, unionWith, mergeWithKey, difference)
import Data.Maybe (
  fromMaybe)
import Data.List (
  foldl')
import Control.Monad (
  guard)


import Control.DeepSeq (
  NFData)

import GHC.Generics (
  Generic)


newtype Bag a = Bag { unBag :: Map a Int }
  deriving (Show, Eq, Ord, Generic, NFData)

-- API

instance (Ord a) => Monoid (Bag a) where
  mempty = empty
  mappend = union

instance (Ord a) => Group (Bag a) where
  invert cbag = Bag (Map.map negate (unBag cbag))

fromList :: (Ord a) => [a] -> Bag a
fromList as = Bag (Map.fromListWith (+) (zip as (repeat 1)))

toList :: Bag a -> [a]
toList (Bag as) = Prelude.concatMap (\(a,n) -> replicate n a) (Map.toList as)


foldGroup :: (Group g) =>  Bag g -> g
foldGroup (Bag gs) = Map.foldrWithKey' reduce mempty gs where
  reduce element n acc = case compare n 0 of
    LT -> reduce (invert element) (negate n) acc
    EQ -> acc
    GT -> mappend element (reduce element (n - 1) acc)


map :: (Ord b) => (a -> b) -> Bag a -> Bag b
map f (Bag as) = Bag (Map.filter (not . (== 0)) (Map.mapKeysWith (+) f as))


foldMapGroup :: (Ord b, Group b) => (a -> b) -> Bag a -> b
foldMapGroup f cbag = let
  m = map f cbag
  b = foldGroup m
  in b


empty :: Bag a
empty = Bag Map.empty


singleton :: a -> Bag a
singleton a = Bag (Map.singleton a 1)


union :: (Ord a) => Bag a -> Bag a -> Bag a
union bag1 bag2 = Bag (Map.mergeWithKey f id id (unBag bag1) (unBag bag2)) where
  f _ n m = if n + m == 0 then Nothing else Just (n + m)


insert :: (Ord a) => a -> Bag a -> Bag a
insert = insertN 1

insertN :: (Ord a) => Int -> a -> Bag a -> Bag a
insertN n a (Bag as) = Bag (Map.alter (
  (\m -> if m + n == 0 then Nothing else Just (m + n)) . fromMaybe 0) a as)


delete :: (Ord a) => a -> Bag a -> Bag a
delete = deleteN 1

deleteN :: (Ord a) => Int -> a -> Bag a -> Bag a
deleteN n = insertN (negate n)


-- Caching API

data FoldGroupC = FoldGroupC
  deriving (Show, Eq, Ord, Generic, NFData)

cfoldGroup :: (Group g) => Bag g -> (g, FoldGroupC)
cfoldGroup cbag = let
  !r = foldGroup cbag
  in (r, FoldGroupC)


data MapC a b c = MapC !(Map a (b, c))
  deriving (Show, Eq, Generic, NFData)

cmap :: (Ord b) => Fun a b c -> Bag a -> (Bag b, MapC a b c)
cmap !cf !cbag = let
  !r = map (fst . apply cf) cbag
  !elementc = Map.mapWithKey (\a _ -> case apply cf a of
    !(!b, c) -> (b, c)) (unBag cbag)
  in (r, MapC elementc) where

data FoldMapGroupC a b c = FoldMapGroupC !(Bag b) !(MapC a b c) !b !FoldGroupC
  deriving (Show, Eq, Generic, NFData)

cfoldMapGroup :: (Ord b, Group b) => Fun a b c -> Bag a -> (b, FoldMapGroupC a b c)
cfoldMapGroup cf cbag = let
  !(!m, !mc) = cmap cf cbag
  !(!b, !bc) = cfoldGroup m
  in (b, FoldMapGroupC m mc b bc)


data SingletonC = SingletonC
  deriving (Show, Eq, Ord, Generic)

instance NFData SingletonC

csingleton :: a -> (Bag a, SingletonC)
csingleton a = let
  !r = singleton a
  in (r, SingletonC)


-- Incremental API

dfoldGroup :: (GroupChangeStruct g, Ord g) => Bag g -> Dt (Bag g) -> FoldGroupC -> (Dt g, FoldGroupC)
dfoldGroup _ (Changes changes) FoldGroupC = let

  g = foldMap (\(Change a da n dn) ->
    power (n `oplus` dn) (a `oplus` da) `mappend` invert (power n a)) changes

  in (inject g, FoldGroupC)


power :: (Group a) => Int -> a -> a
power n a
  | n < 0 = invert (power (negate n) a)
  | otherwise = mconcat (replicate n a)


-- | Incremental and caching map function.
dmap ::
  (NilChangeStruct a, ChangeStruct b, Ord a, Ord b) =>
  Fun a b c -> DFun a b c -> Bag a -> Dt (Bag a) -> MapC a b c -> (Dt (Bag b), MapC a b c)
dmap cf df cbag dbag c = case isNil df of
  True -> dmapNil cf df cbag dbag c
  False -> dmapNotNil cf df cbag dbag c

dmapNotNil ::
  (NilChangeStruct a, ChangeStruct b, Ord a, Ord b) =>
  Fun a b c -> DFun a b c -> Bag a -> Dt (Bag a) -> MapC a b c -> (Dt (Bag b), MapC a b c)
dmapNotNil cf df cbag (Changes changes) (MapC elementc) = let

  !ubag = oplus cbag (Changes changes)

  negativeChangeMultiplicities = Map.fromListWith (+) (do
    Change a _ n _ <- changes
    return (a, negate n))

  nilChanges = do
    (a, n) <- Map.toList (Map.unionWith (+) (unBag cbag) negativeChangeMultiplicities)
    guard (not (n == 0))
    return (Change a (nil a) n (nil n))

  elementChangesAndCaches = do
    Change a da n dn <- nilChanges ++ changes
    let (b, c) = fromMaybe (apply cf a) (Map.lookup a elementc)
        (db, c') = dapply cf df a da c
    return (a `oplus` da, (Change b db n dn, c'))

  dr = Prelude.map (fst . snd) elementChangesAndCaches

  !elementc' = Map.fromList (do
    (a, (Change b db _ _, c)) <- elementChangesAndCaches
    guard (Map.member a (unBag ubag))
    let !ub = b `oplus` db
        !uc = c
    return (a, (ub, uc)))

  in (Changes dr, MapC elementc')

dmapNil ::
  (NilChangeStruct a, ChangeStruct b, Ord a, Ord b) =>
  Fun a b c -> DFun a b c -> Bag a -> Dt (Bag a) -> MapC a b c -> (Dt (Bag b), MapC a b c)
dmapNil cf df cbag (Changes changes) (MapC elementc) = let

  changeElementc = Map.fromList (do
    Change a _ _ _ <- changes
    return (a, apply cf a))

  elementcWithUnseenElements =
    Map.union elementc changeElementc

  elementChangesAndCaches = do
    Change a da n dn <- changes
    let (b, c) = fromMaybe (error "element not in cache") (
          Map.lookup a elementcWithUnseenElements)
        (db, c') = dapply cf df a da c
    return (a `oplus` da, (Change b db n dn, c'))

  dr = Prelude.map (fst . snd) elementChangesAndCaches

  freshElementc = Map.fromList (do
    (a, (Change b db _ _, c)) <- elementChangesAndCaches
    let !ub = b `oplus` db
        !uc = c
    return (a, (ub, uc)))

  -- XXX avoid this
  ubag = oplus cbag (Changes changes)

  invalidElements = Map.fromList (do
    a <- Map.keys changeElementc ++ Map.keys freshElementc
    guard (not (Map.member a (unBag ubag)))
    return (a, ()))

  !elementc' = Map.difference
    (Map.union elementcWithUnseenElements freshElementc) invalidElements

  in (Changes dr, MapC elementc')


dfoldMapGroup ::
  (NilChangeStruct a, Ord a, Ord b, GroupChangeStruct b) =>
  Fun a b c -> DFun a b c -> Bag a -> Changes a -> FoldMapGroupC a b c -> (Dt b, FoldMapGroupC a b c)
dfoldMapGroup cf df cbag dbag (FoldMapGroupC cm ccm cb ccb) =let
  !(dm, !ucm) = dmap cf df cbag dbag ccm
  !um = oplus cm dm
  !(db, !ucb) = dfoldGroup cm dm ccb
  !ub = oplus cb db
  in (db, FoldMapGroupC um ucm ub ucb)


dsingleton :: (ChangeStruct a) =>
  a -> Dt a -> SingletonC -> (Dt (Bag a), SingletonC)
dsingleton ca da SingletonC =
  (Changes [Change ca da 1 0], SingletonC)


-- Changes
data Change a =
  Change a (Dt a) Int (Dt Int)
    deriving (Generic)

deriving instance (Show a, Show (Dt a)) => Show (Change a)
deriving instance (Eq a, Eq (Dt a)) => Eq (Change a)
deriving instance (NFData a, NFData (Dt a)) => NFData (Change a)

newtype Changes a = Changes [Change a]
  deriving (Generic)

deriving instance (Show a, Show (Dt a)) => Show (Changes a)
deriving instance (Eq a, Eq (Dt a)) => Eq (Changes a)
deriving instance (NFData a, NFData (Dt a)) => NFData (Changes a)


changeInsert :: (NilChangeStruct a) => a -> Change a
changeInsert a = Change a (nil a) 0 1

changeDelete :: (NilChangeStruct a) => a -> Change a
changeDelete a = Change a (nil a) 0 (-1)

changeAt :: a -> Dt a -> Change a
changeAt a da = Change a da 1 (nil 1)


-- Change struct

oplusSingle :: (ChangeStruct a, Ord a) => Bag a -> Change a -> Bag a
oplusSingle cbag (Change a da n dn) =
  insertN (n `oplus` dn) (a `oplus` da) (deleteN n a cbag)

oplusBag :: (ChangeStruct a, Ord a) => Bag a -> Changes a -> Bag a
oplusBag cbag (Changes changes) = foldl' oplusSingle cbag changes

instance (ChangeStruct a, Ord a) => ChangeStruct (Bag a) where
  type Dt (Bag a) = Changes a
  oplus = oplusBag

instance (ChangeStruct a, Ord a) => NilChangeStruct (Bag a) where
  nil _ = Changes []

instance (Ord a, NilChangeStruct a) => GroupChangeStruct (Bag a) where
  inject cbag = Changes (do
    (a, n) <- Map.toList (unBag cbag)
    return (Change a (nil a) 0 n))

