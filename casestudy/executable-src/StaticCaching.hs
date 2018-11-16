{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase #-}
module StaticCaching where

import Data.Inc.ChangeStruct (
  Dt)
import Data.Inc.Function (
  Fun, ClosureC)
import Data.Inc.Int (
  DivC, MulC)
import Data.Inc.Bag (
  Bag, FoldMapGroupC)
import qualified Data.Inc.Bag as Bag (
  SingletonC)
import Data.Inc.Map (
  Map, SingletonC, FoldMapGroupWithKeyC, MergeC)
import qualified Data.Inc.Map as Map (
  SingletonC)
import Data.Inc.Sequence (
  Sequence, ConcatC, MapC)
import qualified Data.Inc.Sequence as Sequence (
  SingletonC)

import Data.Vinyl (
  Rec(RNil,(:&)), rfoldMap, rappend)
import Data.Vinyl.TypeLevel (
  type (++))

import qualified Data.Map as Map (
  Map, empty, lookup, insert)

import Data.Functor.Identity (
  Identity)

import Control.Monad.Trans.State.Strict (
  State, get, put, evalState)
import Data.List (
  intercalate)
import Data.Maybe (
  fromMaybe)
import Data.Monoid (
  Sum)

import Unsafe.Coerce (
  unsafeCoerce)


data Stm v cs a where
  Pure :: v a -> Stm v '[] a
  Bind :: Exp v x -> (v x -> Stm v cs a) -> Stm v (x ': cs) a
  Call1 :: Prim1 c a b -> v a -> (v b -> Stm v cs r) -> Stm v (b ': c ': cs) r
  Call2 :: Prim2 c a1 a2 b -> v a1 -> v a2 -> (v b -> Stm v cs r) -> Stm v (b ': c ': cs) r
  Call3 :: Prim3 c a1 a2 a3 b -> v a1 -> v a2 -> v a3 -> (v b -> Stm v cs r) -> Stm v (b ': c ': cs) r

data Exp v a where
  Literal :: Int -> Exp v Int
  Plus :: v Int -> v Int -> Exp v Int
  ConSum :: v Int -> Exp v (Sum Int)
  GetSum :: v (Sum Int) -> Exp v Int
  Pair :: v a -> v b -> Exp v (a, b)
  Fst :: v (a, b) -> Exp v a
  Snd :: v (a, b) -> Exp v b
  SequenceEmpty :: Exp v (Sequence a)
  Lambda :: (forall w . w a -> Stm w c b) -> Exp v (Fun a b (Cache c))
  Lambda2 :: (forall w . w a1 -> w a2 -> Stm w c b) -> Exp v (Fun (a1, a2) b (Cache c))
  Lambda3 :: (forall w . w a1 -> w a2 -> w a3 -> Stm w c b) -> Exp v (Fun (a1, (a2, a3)) b (Cache c))

data Prim1 c a b where
  BagSingleton :: Prim1 Bag.SingletonC a (Bag a)
  SequenceSingleton :: Prim1 Sequence.SingletonC a (Sequence a)
  Concat :: Prim1 ConcatC (Sequence (Sequence a)) (Sequence a)

data Prim2 c a1 a2 b where
  Apply1 :: Prim2 c (Fun a b c) a b
  Closure :: Prim2 ClosureC (Fun (e, a) b c) e (Fun a b c)
  Mul :: Prim2 MulC Int Int Int
  Div :: Prim2 DivC Int Int Int
  FoldMapGroup :: Prim2 (FoldMapGroupC a b c) (Fun a b c) (Bag a) b
  MapSingleton :: Prim2 Map.SingletonC k a (Map k a)
  FoldMapGroupWithKey :: Prim2 (FoldMapGroupWithKeyC k c) (Fun (k, a) b c) (Map k a) b
  Merge :: Prim2 MergeC (Map k a) (Map k b) (Map k (a, b))
  Map :: Prim2 (MapC c) (Fun a b c) (Sequence a) (Sequence b)

data Prim3 c a1 a2 a3 b where
  Apply2 :: Prim3 c (Fun (a1, a2) b c) a1 a2 b

type Cache = Rec Identity
type NoCache = Cache '[]


-- Code generation

data Var a = Var { prettyVar :: String }

type Pretty = State (Map.Map String Int)

runPretty :: Pretty a -> a
runPretty m = evalState m Map.empty

fresh :: Pretty (Var a)
fresh = freshNamed "x"

freshNamed :: String -> Pretty (Var a)
freshNamed x = do
  m <- get
  let n = fromMaybe 0 (Map.lookup x m)
  put (Map.insert x (n + 1) m)
  return (Var (x ++ show n))


-- Pretty print original term

pretty :: Stm Var cs a -> Pretty String
pretty (Pure (Var x)) = return x
pretty (Bind e k) = do
  let name = if isLambda e then "f" else "x"
  z <- freshNamed name
  body <- pretty (k z)
  return (prettyLet z (prettyExp e) body)
pretty (Call1 f a k) = do
  x <- freshNamed "x"
  body <- pretty (k x)
  let rhs = prettyPrim1 f ++ " " ++ prettyVar a
  return (prettyLet x rhs body)
pretty (Call2 f a1 a2 k) = do
  x <- freshNamed "x"
  body <- pretty (k x)
  let rhs = prettyPrim2 f ++ " " ++ prettyVar a1 ++ " " ++ prettyVar a2
  return (prettyLet x rhs body)
pretty (Call3 f a1 a2 a3 k) = do
  x <- freshNamed "x"
  body <- pretty (k x)
  let rhs = prettyPrim3 f ++ " " ++ prettyVar a1 ++ " " ++ prettyVar a2 ++ " " ++ prettyVar a3
  return (prettyLet x rhs body)


prettyLet :: Var a -> String -> String -> String
prettyLet x rhs body = "let " ++ prettyVar x ++ " = " ++ rhs ++ " in " ++ body

prettyPrim1 :: Prim1 c a b -> String
prettyPrim1 BagSingleton = "Bag.singleton"
prettyPrim1 SequenceSingleton = "Sequence.singleton"
prettyPrim1 Concat = "concat"

prettyPrim2 :: Prim2 c a1 a2 b -> String
prettyPrim2 Apply1 = "($)"
prettyPrim2 Closure = "closure"
prettyPrim2 Mul = "mul"
prettyPrim2 Div = "div"
prettyPrim2 FoldMapGroup = "foldMapGroup"
prettyPrim2 MapSingleton = "Map.singleton"
prettyPrim2 FoldMapGroupWithKey = "foldMapGroupWithKey"
prettyPrim2 Merge = "merge"
prettyPrim2 Map = "map"


prettyPrim3 :: Prim3 c a1 a2 a3 b -> String
prettyPrim3 Apply2 = "($)"

prettyExp :: Exp Var a -> String
prettyExp (Literal n) = show n
prettyExp (Plus x y) = prettyVar x ++ " + " ++ prettyVar y
prettyExp (ConSum x) = "Sum " ++ prettyVar x
prettyExp (GetSum x) = "getSum " ++ prettyVar x
prettyExp (Pair x y) = "(,) " ++ prettyVar x ++ " " ++ prettyVar y
prettyExp (Fst x)    = "fst " ++ prettyVar x
prettyExp (Snd x)    = "snd " ++ prettyVar x
prettyExp SequenceEmpty = "Sequence.empty"
prettyExp (Lambda f) = runPretty (do
  a <- freshNamed "a"
  body <- pretty (f a)
  return (prettyLam a body))
prettyExp (Lambda2 f) = runPretty (do
  a1 <- freshNamed "a1"
  a2 <- freshNamed "a2"
  body <- pretty (f a1 a2)
  return (prettyLam2Curried a1 a2 body))
prettyExp (Lambda3 f) = runPretty (do
  a1 <- freshNamed "a1"
  a2 <- freshNamed "a2"
  a3 <- freshNamed "a3"
  body <- pretty (f a1 a2 a3)
  return (prettyLam3Curried a1 a2 a3 body))

prettyLam :: Var a -> String -> String
prettyLam a body = "(\\" ++ prettyVar a ++ " -> " ++ body ++ ")"

prettyLam2 :: Var a1 -> Var a2 -> String -> String
prettyLam2 a1 a2 body = "(\\" ++ prettyPair a1 a2 ++ " -> " ++ body ++ ")"

prettyLam2Curried :: Var a1 -> Var a2 -> String -> String
prettyLam2Curried a1 a2 body = "(\\" ++ prettyVar a1 ++ " " ++ prettyVar a2 ++ " -> " ++ body ++ ")"

prettyLam3 :: Var a1 -> Var a2 -> Var a3 -> String -> String
prettyLam3 a1 a2 a3 body = "(\\" ++ prettyTriple a1 a2 a3 ++ " -> " ++ body ++ ")"

prettyLam3Curried :: Var a1 -> Var a2 -> Var a3 -> String -> String
prettyLam3Curried a1 a2 a3 body = "(\\" ++ prettyVar a1 ++ " " ++ prettyVar a2 ++ " " ++ prettyVar a3 ++ " -> " ++ body ++ ")"

isLambda :: Exp v a -> Bool
isLambda (Lambda _) = True
isLambda (Lambda2 _) = True
isLambda (Lambda3 _) = True
isLambda _ = False

-- Pretty print and caching transformation

prettyCaching :: Rec Var cs -> Stm Var us a -> Pretty (String, Rec Var (cs ++ us))
prettyCaching ccs (Pure (Var cx)) = do
  return ("(" ++ cx ++ " ," ++ prettyCache ccs ++ ")", unsafeCoerce ccs)
prettyCaching ccs (Bind e k) = do
  let name = if isLambda e then "cf" else "cx"
  cx <- freshNamed name
  (body, ucs) <- unsafeCoerce prettyCaching (rsnoc ccs cx) (k cx)
  return (prettyLet cx (prettyCachingExp e) body, ucs)
prettyCaching ccs (Call1 f a k) = do
  cx <- freshNamed "cx"
  cc <- freshNamed "cc"
  (body, ucs) <- unsafeCoerce prettyCaching (rsnoc (rsnoc ccs cx) cc) (k cx)
  let rhs = prettyCachingPrim1 f ++ " " ++ prettyVar a
  return (prettyMatchBang cx cc rhs body, ucs)
prettyCaching ccs (Call2 f a1 a2 k) = do
  cx <- freshNamed "cx"
  cc <- freshNamed "cc"
  (body, ucs) <- unsafeCoerce prettyCaching (rsnoc (rsnoc ccs cx) cc) (k cx)
  let rhs = prettyCachingPrim2 f ++ " " ++ prettyVar a1 ++ " " ++ prettyVar a2
  return (prettyMatchBang cx cc rhs body, ucs)
prettyCaching ccs (Call3 f a1 a2 a3 k) = do
  cx <- freshNamed "cx"
  cc <- freshNamed "cc"
  (body, ucs) <- unsafeCoerce prettyCaching (rsnoc (rsnoc ccs cx) cc) (k cx)
  let rhs = prettyCachingPrim3 f ++ " " ++ prettyVar a1 ++ " " ++ prettyVar a2 ++ " " ++ prettyVar a3
  return (prettyMatchBang cx cc rhs body, ucs)


rsnoc :: Rec f as -> f b -> Rec f (as ++ '[b])
rsnoc as b = rappend as (b :& RNil)

prettyCache :: Rec Var cs -> String
prettyCache cs = "(" ++ intercalate ", " (rfoldMap (\v -> [prettyVar v]) cs) ++ ")"

prettyMatch :: Var a -> Var b -> String -> String -> String
prettyMatch x c rhs body = let
  in "let " ++ prettyPair x c ++ " = " ++ rhs ++ " in " ++ body

prettyMatchBang :: Var a -> Var b -> String -> String -> String
prettyMatchBang x c rhs body = let
  in "let !(!" ++ prettyVar x ++ ", !" ++ prettyVar c ++ ") = " ++ rhs ++ " in " ++ body

prettyPair :: Var a -> Var b -> String
prettyPair a b = "(" ++ prettyVar a ++ ", " ++ prettyVar b ++ ")"

prettyTriple :: Var a -> Var b -> Var c -> String
prettyTriple a b c = "(" ++ prettyVar a ++ ",(" ++ prettyVar b ++ ", " ++ prettyVar c ++ "))"

prettyCachingPrim1 :: Prim1 c a b -> String
prettyCachingPrim1 BagSingleton = "Bag.csingleton"
prettyCachingPrim1 SequenceSingleton = "Sequence.csingleton"
prettyCachingPrim1 Concat = "cconcat"

prettyCachingPrim2 :: Prim2 c a1 a2 b -> String
prettyCachingPrim2 Apply1 = "apply"
prettyCachingPrim2 Closure = "cclosure"
prettyCachingPrim2 Mul = "cmul"
prettyCachingPrim2 Div = "cdiv"
prettyCachingPrim2 FoldMapGroup = "cfoldMapGroup"
prettyCachingPrim2 MapSingleton = "Map.csingleton"
prettyCachingPrim2 FoldMapGroupWithKey = "cfoldMapGroupWithKey"
prettyCachingPrim2 Merge = "cmerge"
prettyCachingPrim2 Map = "cmap"

prettyCachingPrim3 :: Prim3 c a1 a2 a3 b -> String
prettyCachingPrim3 Apply2 = "apply2"

prettyCachingExp :: Exp Var a -> String
prettyCachingExp (Literal n) = show n
prettyCachingExp (Plus x y) = prettyVar x ++ " + " ++ prettyVar y
prettyCachingExp (ConSum x) = "Sum " ++ prettyVar x
prettyCachingExp (GetSum x) = "getSum " ++ prettyVar x
prettyCachingExp (Pair x y) = "(,) " ++ prettyVar x ++ " " ++ prettyVar y
prettyCachingExp (Fst x)    = "fst " ++ prettyVar x
prettyCachingExp (Snd x)    = "snd " ++ prettyVar x
prettyCachingExp SequenceEmpty = "Sequence.empty"
prettyCachingExp (Lambda f) = let
  (cf, ccs) = prettyCachingFun1 f
  df = prettyIncrementalCachingFun1 f ccs
  in "Primitive (" ++ cf  ++ ") (" ++ df ++ ")"
prettyCachingExp (Lambda2 f) = let
  (cf, ccs) = prettyCachingFun2 f
  df = prettyIncrementalCachingFun2 f ccs
  in "Primitive (" ++ cf ++ ") (" ++ df ++ ")"
prettyCachingExp (Lambda3 f) = let
  (cf, ccs) = prettyCachingFun3 f
  df = prettyIncrementalCachingFun3 f ccs
  in "Primitive (" ++ cf ++ ") (" ++ df ++ ")"

prettyCachingFun1 :: (Var a -> Stm Var cs b) -> (String, Rec Var cs)
prettyCachingFun1 f = runPretty (do
  a <- freshNamed "a"
  (body, ccs) <- prettyCaching RNil (f a)
  return (prettyLam a body, ccs))

prettyCachingFun2 :: (Var a1 -> Var a2 -> Stm Var cs b) -> (String, Rec Var cs)
prettyCachingFun2 f = runPretty (do
  a1 <- freshNamed "a1"
  a2 <- freshNamed "a2"
  (body, ccs) <- prettyCaching RNil (f a1 a2)
  return (prettyLam2 a1 a2 body, ccs))

prettyCachingFun3 :: (Var a1 -> Var a2 -> Var a3 -> Stm Var cs b) -> (String, Rec Var cs)
prettyCachingFun3 f = runPretty (do
  a1 <- freshNamed "a1"
  a2 <- freshNamed "a2"
  a3 <- freshNamed "a3"
  (body, ccs) <- prettyCaching RNil (f a1 a2 a3)
  return (prettyLam3 a1 a2 a3 body, ccs))


-- Pretty print and incremental caching transformation

data TVar a = TVar (Var a) (Var (Dt a))

prettyIncrementalCaching :: Rec Var cs -> Rec Var us -> Stm TVar cs a -> Pretty String
prettyIncrementalCaching RNil ucs (Pure (TVar _ da)) = do
  return ("(" ++ prettyVar da ++ "," ++ prettyCache ucs ++ ")")
prettyIncrementalCaching (cx :& ccs) ucs (Bind e k) = do
  let name = if (isLambda e) then "f" else "x"
  dx <- freshNamed ('d' : name)
  ux <- freshNamed ('u' : name)
  body <- prettyIncrementalCaching ccs (rsnoc ucs ux) (k (TVar cx dx))
  return (prettyLet dx (prettyIncrementalCachingExp e) (prettyOplus ux cx dx body))
prettyIncrementalCaching (cx :& cc :& ccs) ucs (Call1 f (TVar ca da) k) = do
  dx <- freshNamed "dx"
  ux <- freshNamed "ux"
  uc <- freshNamed "uc"
  let rhs = concat [
        prettyIncrementalCachingPrim1 f, " ",
        prettyVar ca, " ",
        prettyVar da, " ",
        prettyVar cc]
  body <- prettyIncrementalCaching ccs (rsnoc (rsnoc ucs ux) uc) (k (TVar cx dx))
  return (prettyMatchBang dx uc rhs (prettyOplus ux cx dx body))
prettyIncrementalCaching (cx :& cc :& ccs) ucs (Call2 f (TVar ca1 da1) (TVar ca2 da2) k) = do
  dx <- freshNamed "dx"
  ux <- freshNamed "ux"
  uc <- freshNamed "uc"
  let rhs = concat [
        prettyIncrementalCachingPrim2 f, " ",
        prettyVar ca1, " ",
        prettyVar da1, " ",
        prettyVar ca2, " ",
        prettyVar da2, " ",
        prettyVar cc]
  body <- prettyIncrementalCaching ccs (rsnoc (rsnoc ucs ux) uc) (k (TVar cx dx))
  return (prettyMatchBang dx uc rhs (prettyOplus ux cx dx body))
prettyIncrementalCaching (cx :& cc :& ccs) ucs (Call3 f (TVar ca1 da1) (TVar ca2 da2) (TVar ca3 da3) k) = do
  dx <- freshNamed "dx"
  ux <- freshNamed "ux"
  uc <- freshNamed "uc"
  let rhs = concat [
        prettyIncrementalCachingPrim3 f, " ",
        prettyVar ca1, " ",
        prettyVar da1, " ",
        prettyVar ca2, " ",
        prettyVar da2, " ",
        prettyVar ca3, " ",
        prettyVar da3, " ",
        prettyVar cc]
  body <- prettyIncrementalCaching ccs (rsnoc (rsnoc ucs ux) uc) (k (TVar cx dx))
  return (prettyMatchBang dx uc rhs (prettyOplus ux cx dx body))


prettyIncrementalCachingPrim1 :: Prim1 c a b -> String
prettyIncrementalCachingPrim1 BagSingleton = "Bag.dsingleton"
prettyIncrementalCachingPrim1 SequenceSingleton = "Sequence.dsingleton"
prettyIncrementalCachingPrim1 Concat = "dconcat"

prettyIncrementalCachingPrim2 :: Prim2 c a1 a2 b -> String
prettyIncrementalCachingPrim2 Apply1 = "dapply"
prettyIncrementalCachingPrim2 Closure = "dclosure"
prettyIncrementalCachingPrim2 Mul = "dmul"
prettyIncrementalCachingPrim2 Div = "ddiv"
prettyIncrementalCachingPrim2 FoldMapGroup = "dfoldMapGroup"
prettyIncrementalCachingPrim2 MapSingleton = "Map.dsingleton"
prettyIncrementalCachingPrim2 FoldMapGroupWithKey = "dfoldMapGroupWithKey"
prettyIncrementalCachingPrim2 Merge = "dmerge"
prettyIncrementalCachingPrim2 Map = "dmap"

prettyIncrementalCachingPrim3 :: Prim3 c a1 a2 a3 b -> String
prettyIncrementalCachingPrim3 Apply2 = "dapply2"

prettyIncrementalCachingExp :: Exp TVar a -> String
prettyIncrementalCachingExp (Literal _) =
  show (0 :: Int)
prettyIncrementalCachingExp (Plus (TVar _ dx) (TVar _ dy)) =
  prettyVar dx ++ " + " ++ prettyVar dy
prettyIncrementalCachingExp (ConSum (TVar _ dx)) =
  "Sum " ++ prettyVar dx
prettyIncrementalCachingExp (GetSum (TVar _ dx)) =
  "getSum " ++ prettyVar dx
prettyIncrementalCachingExp (Pair (TVar _ dx) (TVar _ dy)) =
  "(,) " ++ prettyVar dx ++ " " ++ prettyVar dy
prettyIncrementalCachingExp (Fst (TVar _ dx)) =
  "fst " ++ prettyVar dx
prettyIncrementalCachingExp (Snd (TVar _ dx)) =
  "snd " ++ prettyVar dx
prettyIncrementalCachingExp SequenceEmpty =
  "nil Sequence.empty"
prettyIncrementalCachingExp (Lambda f) = let
  (_, ccs) = prettyCachingFun1 f
  df = prettyIncrementalCachingFun1 f ccs
  in "DPrimitive (" ++ df ++ ")"
prettyIncrementalCachingExp (Lambda2 f) = let
  (_, ccs) = prettyCachingFun2 f
  df = prettyIncrementalCachingFun2 f ccs
  in "DPrimitive (" ++ df ++ ")"
prettyIncrementalCachingExp (Lambda3 f) = let
  (_, ccs) = prettyCachingFun3 f
  df = prettyIncrementalCachingFun3 f ccs
  in "DPrimitive (" ++ df ++ ")"

prettyIncrementalCachingFun1 :: (TVar a -> Stm TVar cs b) -> Rec Var cs -> String
prettyIncrementalCachingFun1 f ccs = runPretty (do
  ca <- freshNamed "ca"
  da <- freshNamed "da"
  body <- prettyIncrementalCaching ccs RNil (f (TVar ca da))
  return ("\\" ++ prettyVar ca ++ " " ++ prettyVar da ++ " " ++  prettyCache ccs ++ " -> " ++ body))

prettyIncrementalCachingFun2 :: (TVar a1 -> TVar a2 -> Stm TVar cs b) -> Rec Var cs -> String
prettyIncrementalCachingFun2 f ccs = runPretty (do
  ca1 <- freshNamed "ca1"
  da1 <- freshNamed "da1"
  ca2 <- freshNamed "ca2"
  da2 <- freshNamed "da2"
  body <- prettyIncrementalCaching ccs RNil (f (TVar ca1 da1) (TVar ca2 da2))
  return ("\\" ++ prettyPair ca1 ca2 ++ " " ++ prettyPair da1 da2 ++ " " ++  prettyCache ccs ++ " -> " ++ body))

prettyIncrementalCachingFun3 :: (TVar a1 -> TVar a2 -> TVar a3 -> Stm TVar cs b) -> Rec Var cs -> String
prettyIncrementalCachingFun3 f ccs = runPretty (do
  ca1 <- freshNamed "ca1"
  da1 <- freshNamed "da1"
  ca2 <- freshNamed "ca2"
  da2 <- freshNamed "da2"
  ca3 <- freshNamed "ca3"
  da3 <- freshNamed "da3"
  body <- prettyIncrementalCaching ccs RNil (f (TVar ca1 da1) (TVar ca2 da2) (TVar ca3 da3))
  return ("\\" ++ prettyTriple ca1 ca2 ca3 ++ " " ++ prettyTriple da1 da2 da3 ++ " " ++  prettyCache ccs ++ " -> " ++ body))

prettyOplus :: Var a -> Var a -> Var (Dt a) -> String -> String
prettyOplus ux cx dx body = prettyLetBang ux ("oplus " ++ prettyVar cx ++ " " ++ prettyVar dx) body

prettyLetBang :: Var a -> String -> String -> String
prettyLetBang x rhs body = "let !" ++ prettyVar x ++ " = " ++ rhs ++ " in " ++ body

