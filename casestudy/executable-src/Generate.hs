{-# LANGUAGE RankNTypes #-}
module Main where

import StaticCaching

import Examples.Bag (sum, length, average)
import Examples.Map (indexedJoin)
import Examples.Sequence (cartesianProduct)


main :: IO ()
main = do
  prettyAll1 "sum" Examples.Bag.sum
  putStrLn ""
  prettyAll1 "length" Examples.Bag.length
  putStrLn ""
  prettyAll1 "average" Examples.Bag.average
  putStrLn ""
  prettyAll2 "indexedJoin" Examples.Map.indexedJoin
  putStrLn ""
  prettyAll2 "cartesianProduct" Examples.Sequence.cartesianProduct
  putStrLn ""

prettyAll1 :: String -> (forall v . v a -> Stm v c b) -> IO ()
prettyAll1 name f = do
  let prettyF = prettyExp (
        Lambda f)
      prettyCF = prettyCachingExp (
        Lambda f)
  putStrLn (name ++ " = " ++ prettyF)
  putStrLn ""
  putStrLn ("Primitive " ++ ('c' : name) ++ " " ++ ('d' : name) ++ " = " ++ prettyCF)

prettyAll2 :: String -> (forall v . v a1 -> v a2 -> Stm v c b) -> IO ()
prettyAll2 name f = do
  let prettyF = prettyExp (
        Lambda2 f)
      prettyCF = prettyCachingExp (
        Lambda2 f)
  putStrLn (name ++ " = " ++ prettyF)
  putStrLn ""
  putStrLn ("Primitive " ++ ('c' : name) ++ " " ++ ('d' : name) ++ " = " ++ prettyCF)

