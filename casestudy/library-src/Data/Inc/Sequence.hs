{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Inc.Sequence where

import           Control.DeepSeq
import           Control.Monad
import           Data.DList (DList)
import qualified Data.DList as D
import           HaskellWorks.Data.FingerTree.Strict (FingerTree, Measured (measure))
import qualified HaskellWorks.Data.FingerTree.Strict as FingerTree
import           Data.Foldable hiding (concat, length)
import           Data.Monoid
import           Data.Sequence (Seq, (><))
import qualified Data.Sequence as S
import           GHC.Generics (Generic)
import           Prelude hiding (concat, concatMap, length, map, unzip, zip)
import qualified Prelude (map, unzip)

import           Data.Inc.ChangeStruct
import           Data.Inc.Function

-- This module is based off "Purely Functional Incremental Computing" and the incremental-computing package.

-- Newtype to avoid orphan instances :-(
newtype Sequence a = S {unS :: S.Seq a}
  deriving (Eq, Show, Functor, Applicative, Monad, Foldable, Monoid, NFData, Generic)

lift0 :: (a -> Seq b) -> a -> Sequence b
lift0 = (S .)

lift1 :: (Seq a -> Seq b) -> Sequence a -> Sequence b
lift1 f = S . f . unS

subseq :: Sequence a -> Int -> Int -> Sequence a
subseq xs src len = S $ S.take len $ S.drop src (unS xs)

index :: Sequence a -> Int -> a
index (S xs) = S.index xs

length :: Sequence a -> Int
length = S.length . unS

unzip :: Sequence (a, b) -> (Sequence a, Sequence b)
unzip asbs = let
  (as, bs) = Prelude.unzip (toList asbs)
  sas = S (S.fromList as)
  sbs = S (S.fromList bs)
  in foldr seq () sas `seq` foldr seq () sbs `seq` (sas, sbs)

zip :: Sequence a -> Sequence b -> Sequence (a, b)
zip (S xs) (S ys) = S $ S.zip xs ys

------------------------
-- The rest of the code deals with Sequence, not Seq.
------------------------

-- API (Primitives)

fromList :: [a] -> Sequence a
fromList = S . S.fromList

empty :: Sequence a
empty = S $ S.empty

singleton :: b -> Sequence b
singleton = lift0 S.singleton

concat :: Sequence (Sequence a) -> Sequence a
concat xss = let
  xs = join xss
  in foldr seq () xs `seq` xs

map :: (a -> b) -> Sequence a -> Sequence b
map f xs = let
  ys = fmap f xs
  in foldr seq () ys `seq` ys


-- Caching API


csingleton :: a -> (Sequence a, SingletonC)
csingleton a = let
  !r = singleton a
  in (r, SingletonC)

data SingletonC = SingletonC
  deriving (Show, Eq)


-- Taken (with credit) from the incremental-computing package.
cconcat :: Sequence (Sequence a) -> (Sequence a, ConcatC)
cconcat xss = let
  !r = concat xss
  in (r, ConcatC $ seqToConcatState xss)

-- | Cache lengths of the subvectors.
seqToConcatState :: Sequence (Sequence a) -> ConcatState
seqToConcatState = FingerTree.fromList . toList .
                   fmap (ConcatStateElement . length) . unS

newtype ConcatC = ConcatC ConcatState
  deriving (Show, Eq, NFData)

type ConcatState = FingerTree ConcatStateMeasure ConcatStateElement

data ConcatStateMeasure =
  ConcatStateMeasure
  { sourceLength :: !Int
  , targetLength :: !Int
  } deriving (Show)

instance Monoid ConcatStateMeasure where
  mempty = ConcatStateMeasure 0 0
  mappend (ConcatStateMeasure srcLen1 tgtLen1) (ConcatStateMeasure srcLen2 tgtLen2) = measure'
    where
      measure' = ConcatStateMeasure (srcLen1 + srcLen2) (tgtLen1 + tgtLen2)

newtype ConcatStateElement = ConcatStateElement Int
  deriving (Show, Eq, NFData)

instance Measured ConcatStateMeasure ConcatStateElement where
  measure (ConcatStateElement elemLen) = ConcatStateMeasure 1 elemLen

instance (NFData a) => NFData (FingerTree v a) where
  rnf = foldr (seq . rnf) ()


cmap :: Fun a b c -> Sequence a -> (Sequence b, MapC c)
cmap cf xs = let
  !(!ys, !cc) = unzip $ map (apply cf) xs
  in (ys, MapC cc)

data MapC c = MapC !(Sequence c)
  deriving (Show, Eq, Generic)

instance (NFData c) => NFData (MapC c)


-- Incremental API

dsingleton :: a -> Dt a -> SingletonC -> (Dt (Sequence a), SingletonC)
dsingleton _ da SingletonC = (changeAt 0 da, SingletonC)


dconcat :: ChangeStruct a => Sequence (Sequence a) -> Dt (Sequence (Sequence a)) -> ConcatC -> (Dt (Sequence a), ConcatC)
dconcat _ changes c = go [] c (toList changes) where
  go !dys !c0 [] =
    (D.fromList (reverse dys), c0)
  go !dys !c0 (dxs : dxss) = let
    (dy, c1) = dconcatSingle dxs c0
    in go (dy ++ dys) c1 dxss

-- Beware: list of output changes is in reverse order
dconcatSingle :: AtomicChange (Sequence a) -> ConcatC -> ([AtomicChange a], ConcatC)
dconcatSingle (Insert ix xs) (ConcatC lens) = (change', ConcatC lens')
  where
    (ix', front, rear) = splitAndTranslate ix lens
    change' = [Insert ix' (join xs)]
    lens' = front <> seqToConcatState xs <> rear
-- TODO: rename state to lens.
dconcatSingle (Delete ix len) (ConcatC state) = (change', ConcatC state')
  where
    (ix', front, rest) = splitAndTranslate ix state
    (len', _, rear) = splitAndTranslate len rest
    change' = [Delete ix' len']
    state' = front <> rear
dconcatSingle (Shift src len tgt) (ConcatC state) = (change', ConcatC state')
  where
    (src', front, rest) = splitAndTranslate src state
    (len', mid, rear) = splitAndTranslate len rest
    (tgt', front', rear') = splitAndTranslate tgt (front <> rear)
    change' = [Shift src' len' tgt']
    state' = front' <> mid <> rear'
dconcatSingle (ChangeAt ix change) (ConcatC state)
  | indexInBounds len ix = (change', ConcatC state')
  | otherwise            = (mempty, ConcatC state)
  where
    len = sourceLength (measure state)
    (ix', front, rest) = splitAndTranslate ix state
    (ConcatStateElement elemLen FingerTree.:< rear) = FingerTree.viewl rest
    -- XXX Suffixes like 0 and 1 here prevent shadowing
    ChangeAndLength change' elemLen' = foldl' next init0 change where
      init0 = ChangeAndLength [] elemLen
      next (ChangeAndLength curChanges curElemLen) atomic = result where
        result = ChangeAndLength curChange' curElemLen'
        normAtomic = normalizeAtomicChange curElemLen atomic
        shiftedNormAtomic = case normAtomic of
          Insert elemIx xs
            -> [Insert (ix' + elemIx) xs]
          Delete elemIx curElemLen1
            -> [Delete (ix' + elemIx) curElemLen1]
          Shift elemSrc curElemLen1 elemTgt
            -> [Shift (ix' + elemSrc) curElemLen1 (ix' + elemTgt)]
          ChangeAt elemIx change1
            -> if indexInBounds curElemLen elemIx
               then [ChangeAt (ix' + elemIx) change1]
               else []

        curChange' = shiftedNormAtomic ++ curChanges
        curElemLen' = changeLength normAtomic curElemLen

    state' = front <> (ConcatStateElement elemLen' FingerTree.<| rear)

-- List of changes is in reverse order
data ChangeAndLength a = ChangeAndLength [AtomicChange a] !Int

splitAndTranslate :: Int -> ConcatState -> (Int, ConcatState, ConcatState)
splitAndTranslate ix state = (ix', front, rear) where
  (front, rear) = FingerTree.split ((> ix) . sourceLength) state
  ix' = targetLength (measure front)

changeLength :: AtomicChange a -> Int -> Int
changeLength (Insert _ xs) totalLength = totalLength + length xs
changeLength (Delete _ len) totalLength = totalLength - len
changeLength (Shift _ _ _)  totalLength = totalLength
changeLength (ChangeAt _ _) totalLength = totalLength

normalizeAtomicChange :: Int -> AtomicChange a -> AtomicChange a
normalizeAtomicChange totalLen (Insert ix xs) = Insert ix' xs where
  ix' = normalizeIx totalLen ix

normalizeAtomicChange totalLen (Delete ix len) = Delete ix' len' where
  (ix', len') = normalizeIxAndLen totalLen ix len

normalizeAtomicChange totalLen (Shift src len tgt) = Shift src' len' tgt' where
  (src', len') = normalizeIxAndLen totalLen src len
  tgt' = normalizeIx (totalLen - len') tgt

normalizeAtomicChange totalLen (ChangeAt ix change) = ChangeAt ix' change where
  ix' | indexInBounds totalLen ix = ix
      | otherwise                 = totalLen

normalizeIxAndLen :: Int -> Int -> Int -> (Int, Int)
normalizeIxAndLen totalLen ix len = (ix', len') where
  ix' = normalizeIx totalLen ix
  len' = (len `max` 0) `min` (totalLen - ix')

indexInBounds :: Int -> Int -> Bool
indexInBounds len ix = ix >= 0 && ix < len

normalizeIx :: Int -> Int -> Int
normalizeIx totalLen ix = (ix `max` 0) `min` totalLen


-- | Caching derivative for cmap.
dmap ::
  (ChangeStruct b, NilChangeStruct a) =>
  Fun a b c -> DFun a b c -> Sequence a -> Dt (Sequence a) -> MapC c -> (Dt (Sequence b), MapC c)
dmap cf df cxs dxs cm = case isNil df of
  False -> dmapNonNil cf df cxs dxs cm
  True -> dmapNil cf df cxs dxs cm

dmapNonNil ::
  (ChangeStruct b, NilChangeStruct a) =>
  Fun a b c -> DFun a b c -> Sequence a -> Dt (Sequence a) -> MapC c -> (Dt (Sequence b), MapC c)
dmapNonNil cf df cxs dxs cm = let

  -- first we incorporate sequence changes
  (dr1, MapC cc) = dmapNil cf (nil cf) cxs dxs cm

  -- rerun the function change on updated elements
  uxs = oplus cxs dxs

  (dys, ccs) = Prelude.unzip (Prelude.zipWith3
    (dapply cf df) (toList uxs) (Prelude.map nil (toList uxs)) (toList cc))

  uc = fromList ccs

  dr2 = D.fromList (zipWith ChangeAt [0..] dys)

  dr = D.append dr1 dr2

  in (dr, MapC uc)

dmapNil ::
  (ChangeStruct b, NilChangeStruct a) =>
  Fun a b c -> DFun a b c -> Sequence a -> Dt (Sequence a) -> MapC c -> (Dt (Sequence b), MapC c)
dmapNil cf df cxs dxs cm = go cxs [] cm (toList dxs) where

  go !cxs' !drs' !cm' [] =
    (D.fromList (reverse drs'), cm')
  go !cxs' !drs' !cm' (dx : dxs) = let
    (dr', um') = dmapSingle cf df cxs' dx cm'
    in go (oplusSingle cxs' dx) (dr' : drs') um' dxs

-- | Derivative of cmap for a single input change.
-- This function is always called with a nil function change
dmapSingle ::
  (ChangeStruct b, NilChangeStruct a) =>
  Fun a b c -> DFun a b c -> Sequence a -> AtomicChange a -> MapC c -> (AtomicChange b, MapC c)
dmapSingle cf _ _ (Insert ix nxs) (MapC cc) = let

  (nys, ncc) = unzip $ fmap (apply cf) nxs

  uc = seqAdd cc ix ncc

  dr = Insert ix nys

  in (dr, MapC uc)
dmapSingle _ _ _ (Delete ix len) (MapC cc) = let

  uc = seqDel cc ix len

  dr = Delete ix len

  in (dr, MapC uc)
dmapSingle _ _ _ (Shift src len tgt) (MapC cc) = let

  uc = seqShift cc src len tgt

  dr = Shift src len tgt

  in (dr, MapC uc)
dmapSingle cf df cxs (ChangeAt ix dx) (MapC cm) = let

  cx = index cxs ix
  cc = index cm ix
  !(dy, !uc) = dapply cf df cx dx cc

  um = seqReplaceAt cm ix uc

  dr = ChangeAt ix dy

  in (dr, MapC um)


-- Changes

data AtomicChange a
  = Insert Int (Sequence a)
  | Delete Int Int
  | Shift Int Int Int
  | ChangeAt Int (Dt a)
  deriving Generic

instance (NFData a, NFData (Dt a)) => NFData (AtomicChange a)
deriving instance (Show a, Show (Dt a)) => Show (AtomicChange a)

-- Smart constructors, inspired by incremental-computing.
insert :: Int -> Sequence a -> DList (AtomicChange a)
insert ix xs = D.singleton (Insert ix xs)

delete :: Int -> Int -> DList (AtomicChange a)
delete ix len = D.singleton (Delete ix len)

shift :: Int -> Int -> Int -> DList (AtomicChange a)
shift src len tgt = D.singleton (Shift src len tgt)

changeAt :: Int -> Dt a -> DList (AtomicChange a)
changeAt ix change = D.singleton (ChangeAt ix change)


-- Change struct

oplusSequence :: ChangeStruct a => Sequence a -> DList (AtomicChange a) -> Sequence a
oplusSequence = foldl' oplusSingle

oplusSingle :: ChangeStruct a => Sequence a -> AtomicChange a -> Sequence a
oplusSingle xs (Insert ix nxs) = seqAdd xs ix nxs
oplusSingle xs (Delete ix len) = seqDel xs ix len
oplusSingle xs (Shift src len tgt) = seqShift xs src len tgt
oplusSingle xs (ChangeAt ix dx) = seqChangeAt xs ix dx

-- Branches of change applications for the various cases of AtomicChange.
seqAdd :: Sequence a -> Int -> Sequence a -> Sequence a
seqAdd (S xs) ix (S ys) = let
  xs' = foldr (S.insertAt ix) xs ys
  in foldr seq () (S.take (S.length ys) (S.drop ix xs')) `seq` S xs'

seqDel :: Sequence a -> Int -> Int -> Sequence a
seqDel (S xs) ix len = let
  xs' = S.take ix xs >< S.drop (ix + len) xs
  in foldr seq () (S.take 1 (S.drop ix xs')) `seq` S xs'

seqShift :: Sequence a -> Int -> Int -> Int -> Sequence a
seqShift (S xs) src len tgt = let
  --Split in three parts
  (p1, p23) = S.splitAt src xs
  (p2, p3) = S.splitAt len p23
  in seqAdd (S $ p1 >< p3) tgt (S p2)

seqChangeAt :: ChangeStruct a => Sequence a -> Int -> Dt a -> Sequence a
seqChangeAt (S xs) ix dx = S $ S.adjust' (`oplus` dx) ix xs

seqReplaceAt :: Sequence a -> Int -> a -> Sequence a
seqReplaceAt (S xs) ix x1 = let
  xs' = S.update ix x1 xs
  in S.index xs' ix `seq` S xs'

instance ChangeStruct a => ChangeStruct (Sequence a) where
  type Dt (Sequence a) = DList (AtomicChange a)
  oplus = oplusSequence

instance ChangeStruct a => OnilChangeStruct (Sequence a) where
  onil _ = D.empty

instance ChangeStruct a => NilChangeStruct (Sequence a) where
  nil = nilFromOnil

instance (ChangeStruct a) => DiffChangeStruct (Sequence a) where
  ominus ua ca = D.fromList [Delete 0 (length ca), Insert 0 ua]

-- It would be nice to make this a generic instance for dlist-based change structures... with Dt a ~ DList
instance ChangeStruct a => CompChangeStruct (Sequence a) where
  ocompose = D.append
  -- Because of the operation order of ocompose, changes to the left are to be run first.

instance ChangeStruct a => NilTestable (Sequence a) where
  isNil = null
