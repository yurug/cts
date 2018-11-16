{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -w #-}
module Data.Inc.Map.Generated where

import Data.Inc.ChangeStruct (
  Dt, oplus)
import Data.Inc.Function (
  Fun(Primitive), DFun(DPrimitive),
  apply, dapply,
  apply2, dapply2,
  closure, cclosure, dclosure)
import Data.Inc.Int (
  mul, cmul, dmul)
import Data.Inc.Bag (
  Bag,
  foldMapGroup, cfoldMapGroup, dfoldMapGroup)
import qualified Data.Inc.Bag as Bag (
  singleton, csingleton, dsingleton)
import Data.Inc.Map (
  foldMapGroupWithKey, cfoldMapGroupWithKey, dfoldMapGroupWithKey,
  merge, cmerge, dmerge)
import qualified Data.Inc.Map as Map (
  singleton, csingleton, dsingleton)

import Data.Monoid (Sum(Sum, getSum))

default (Int)

indexedJoin :: Bag (Int, Int) -> Bag (Int, Int) -> Sum Int
cindexedJoin :: (Bag (Int, Int), Bag (Int, Int)) -> (Sum Int, _)
dindexedJoin :: (Bag (Int, Int), Bag (Int, Int)) -> (Dt (Bag (Int, Int), Bag (Int, Int))) -> _ -> (Dt (Sum Int), _)

indexedJoin =
  (\a10 a20 ->
     let f0 =
           (\a0 ->
              let x0 = fst a0
              in x0)
     in let f1 =
              (\a10 a20 ->
                 let f0 =
                       (\a10 a20 ->
                          let x0 = ($) a10 a20
                          in let x1 = Bag.singleton a20
                             in let x2 = Map.singleton x0 x1
                                in x2)
                 in let x0 = closure f0 a10
                    in let x1 = foldMapGroup x0 a20
                       in x1)
        in let f2 =
                 (\a10 a20 ->
                    let f0 =
                          (\a10 a20 a30 ->
                             let x0 = ($) a10 a30
                             in let x1 = Map.singleton a20 x0
                                in x1)
                    in let x0 = closure f0 a10
                       in let x1 = foldMapGroupWithKey x0 a20
                          in x1)
           in let f3 =
                    (\a0 ->
                       let f0 =
                             (\a0 ->
                                let x0 = snd a0
                                in let x1 = Sum x0
                                   in x1)
                       in let x0 = foldMapGroup f0 a0
                          in x0)
              in let f4 =
                       (\a10 a20 ->
                          let f0 =
                                (\a10 a20 a30 ->
                                   let x0 = ($) a10 a30
                                   in x0)
                          in let x0 = closure f0 a10
                             in let x1 = foldMapGroupWithKey x0 a20
                                in x1)
                 in let f5 =
                          (\a0 ->
                             let x0 = fst a0
                             in let x1 = snd a0
                                in let x2 = getSum x0
                                   in let x3 = getSum x1
                                      in let x4 = mul x2 x3
                                         in let x5 = Sum x4
                                            in x5)
                    in let x0 = ($) f1 f0 a10
                       in let x1 = ($) f2 f3 x0
                          in let x2 = ($) f1 f0 a20
                             in let x3 = ($) f2 f3 x2
                                in let x4 = merge x1 x3
                                   in let x5 = ($) f4 f5 x4
                                      in x5)

Primitive cindexedJoin dindexedJoin =
  Primitive
    ((\(a10, a20) ->
        let cf0 =
              Primitive
                ((\a0 ->
                    let cx0 = fst a0
                    in (cx0, (cx0))))
                (\ca0 da0 (cx0) ->
                   let dx0 = fst da0
                   in let !ux0 = oplus cx0 dx0
                      in (dx0, (ux0)))
        in let cf1 =
                 Primitive
                   ((\(a10, a20) ->
                       let cf0 =
                             Primitive
                               ((\(a10, a20) ->
                                   let !(!cx0, !cc0) = apply a10 a20
                                   in let !(!cx1, !cc1) = Bag.csingleton a20
                                      in let !(!cx2, !cc2) =
                                               Map.csingleton cx0 cx1
                                         in ( cx2
                                            , (cx0, cc0, cx1, cc1, cx2, cc2))))
                               (\(ca10, ca20) (da10, da20) (cx0, cc0, cx1, cc1, cx2, cc2) ->
                                  let !(!dx0, !uc0) =
                                        dapply ca10 da10 ca20 da20 cc0
                                  in let !ux0 = oplus cx0 dx0
                                     in let !(!dx1, !uc1) =
                                              Bag.dsingleton ca20 da20 cc1
                                        in let !ux1 = oplus cx1 dx1
                                           in let !(!dx2, !uc2) =
                                                    Map.dsingleton
                                                      cx0
                                                      dx0
                                                      cx1
                                                      dx1
                                                      cc2
                                              in let !ux2 = oplus cx2 dx2
                                                 in ( dx2
                                                    , ( ux0
                                                      , uc0
                                                      , ux1
                                                      , uc1
                                                      , ux2
                                                      , uc2)))
                       in let !(!cx0, !cc0) = cclosure cf0 a10
                          in let !(!cx1, !cc1) = cfoldMapGroup cx0 a20
                             in (cx1, (cf0, cx0, cc0, cx1, cc1))))
                   (\(ca10, ca20) (da10, da20) (cf0, cx0, cc0, cx1, cc1) ->
                      let df0 =
                            DPrimitive
                              (\(ca10, ca20) (da10, da20) (cx0, cc0, cx1, cc1, cx2, cc2) ->
                                 let !(!dx0, !uc0) =
                                       dapply ca10 da10 ca20 da20 cc0
                                 in let !ux0 = oplus cx0 dx0
                                    in let !(!dx1, !uc1) =
                                             Bag.dsingleton ca20 da20 cc1
                                       in let !ux1 = oplus cx1 dx1
                                          in let !(!dx2, !uc2) =
                                                   Map.dsingleton
                                                     cx0
                                                     dx0
                                                     cx1
                                                     dx1
                                                     cc2
                                             in let !ux2 = oplus cx2 dx2
                                                in ( dx2
                                                   , ( ux0
                                                     , uc0
                                                     , ux1
                                                     , uc1
                                                     , ux2
                                                     , uc2)))
                      in let !uf0 = oplus cf0 df0
                         in let !(!dx0, !uc0) = dclosure cf0 df0 ca10 da10 cc0
                            in let !ux0 = oplus cx0 dx0
                               in let !(!dx1, !uc1) =
                                        dfoldMapGroup cx0 dx0 ca20 da20 cc1
                                  in let !ux1 = oplus cx1 dx1
                                     in (dx1, (uf0, ux0, uc0, ux1, uc1)))
           in let cf2 =
                    Primitive
                      ((\(a10, a20) ->
                          let cf0 =
                                Primitive
                                  ((\(a10, (a20, a30)) ->
                                      let !(!cx0, !cc0) = apply a10 a30
                                      in let !(!cx1, !cc1) =
                                               Map.csingleton a20 cx0
                                         in (cx1, (cx0, cc0, cx1, cc1))))
                                  (\(ca10, (ca20, ca30)) (da10, (da20, da30)) (cx0, cc0, cx1, cc1) ->
                                     let !(!dx0, !uc0) =
                                           dapply ca10 da10 ca30 da30 cc0
                                     in let !ux0 = oplus cx0 dx0
                                        in let !(!dx1, !uc1) =
                                                 Map.dsingleton
                                                   ca20
                                                   da20
                                                   cx0
                                                   dx0
                                                   cc1
                                           in let !ux1 = oplus cx1 dx1
                                              in (dx1, (ux0, uc0, ux1, uc1)))
                          in let !(!cx0, !cc0) = cclosure cf0 a10
                             in let !(!cx1, !cc1) = cfoldMapGroupWithKey cx0 a20
                                in (cx1, (cf0, cx0, cc0, cx1, cc1))))
                      (\(ca10, ca20) (da10, da20) (cf0, cx0, cc0, cx1, cc1) ->
                         let df0 =
                               DPrimitive
                                 (\(ca10, (ca20, ca30)) (da10, (da20, da30)) (cx0, cc0, cx1, cc1) ->
                                    let !(!dx0, !uc0) =
                                          dapply ca10 da10 ca30 da30 cc0
                                    in let !ux0 = oplus cx0 dx0
                                       in let !(!dx1, !uc1) =
                                                Map.dsingleton
                                                  ca20
                                                  da20
                                                  cx0
                                                  dx0
                                                  cc1
                                          in let !ux1 = oplus cx1 dx1
                                             in (dx1, (ux0, uc0, ux1, uc1)))
                         in let !uf0 = oplus cf0 df0
                            in let !(!dx0, !uc0) =
                                     dclosure cf0 df0 ca10 da10 cc0
                               in let !ux0 = oplus cx0 dx0
                                  in let !(!dx1, !uc1) =
                                           dfoldMapGroupWithKey
                                             cx0
                                             dx0
                                             ca20
                                             da20
                                             cc1
                                     in let !ux1 = oplus cx1 dx1
                                        in (dx1, (uf0, ux0, uc0, ux1, uc1)))
              in let cf3 =
                       Primitive
                         ((\a0 ->
                             let cf0 =
                                   Primitive
                                     ((\a0 ->
                                         let cx0 = snd a0
                                         in let cx1 = Sum cx0
                                            in (cx1, (cx0, cx1))))
                                     (\ca0 da0 (cx0, cx1) ->
                                        let dx0 = snd da0
                                        in let !ux0 = oplus cx0 dx0
                                           in let dx1 = Sum dx0
                                              in let !ux1 = oplus cx1 dx1
                                                 in (dx1, (ux0, ux1)))
                             in let !(!cx0, !cc0) = cfoldMapGroup cf0 a0
                                in (cx0, (cf0, cx0, cc0))))
                         (\ca0 da0 (cf0, cx0, cc0) ->
                            let df0 =
                                  DPrimitive
                                    (\ca0 da0 (cx0, cx1) ->
                                       let dx0 = snd da0
                                       in let !ux0 = oplus cx0 dx0
                                          in let dx1 = Sum dx0
                                             in let !ux1 = oplus cx1 dx1
                                                in (dx1, (ux0, ux1)))
                            in let !uf0 = oplus cf0 df0
                               in let !(!dx0, !uc0) =
                                        dfoldMapGroup cf0 df0 ca0 da0 cc0
                                  in let !ux0 = oplus cx0 dx0
                                     in (dx0, (uf0, ux0, uc0)))
                 in let cf4 =
                          Primitive
                            ((\(a10, a20) ->
                                let cf0 =
                                      Primitive
                                        ((\(a10, (a20, a30)) ->
                                            let !(!cx0, !cc0) = apply a10 a30
                                            in (cx0, (cx0, cc0))))
                                        (\(ca10, (ca20, ca30)) (da10, (da20, da30)) (cx0, cc0) ->
                                           let !(!dx0, !uc0) =
                                                 dapply ca10 da10 ca30 da30 cc0
                                           in let !ux0 = oplus cx0 dx0
                                              in (dx0, (ux0, uc0)))
                                in let !(!cx0, !cc0) = cclosure cf0 a10
                                   in let !(!cx1, !cc1) =
                                            cfoldMapGroupWithKey cx0 a20
                                      in (cx1, cc0 `seq` (cf0, cx0, cc0, cx1, cc1))))
                            (\(ca10, ca20) (da10, da20) (cf0, cx0, cc0, cx1, cc1) ->
                               let df0 =
                                     DPrimitive
                                       (\(ca10, (ca20, ca30)) (da10, (da20, da30)) (cx0, cc0) ->
                                          let !(!dx0, !uc0) =
                                                dapply ca10 da10 ca30 da30 cc0
                                          in let !ux0 = oplus cx0 dx0
                                             in (dx0, (ux0, uc0)))
                               in let !uf0 = oplus cf0 df0
                                  in let !(!dx0, !uc0) =
                                           dclosure cf0 df0 ca10 da10 cc0
                                     in let !ux0 = oplus cx0 dx0
                                        in let !(!dx1, !uc1) =
                                                 dfoldMapGroupWithKey
                                                   cx0
                                                   dx0
                                                   ca20
                                                   da20
                                                   cc1
                                           in let !ux1 = oplus cx1 dx1
                                              in ( dx1
                                                 , (uf0, ux0, uc0, ux1, uc1)))
                    in let cf5 =
                             Primitive
                               ((\a0 ->
                                   let cx0 = fst a0
                                   in let cx1 = snd a0
                                      in let cx2 = getSum cx0
                                         in let cx3 = getSum cx1
                                            in let !(!cx4, !cc0) = cmul cx2 cx3
                                               in let cx5 = Sum cx4
                                                  in ( cx5
                                                     , ( cx0
                                                       , cx1
                                                       , cx2
                                                       , cx3
                                                       , cx4
                                                       , cc0
                                                       , cx5))))
                               (\ca0 da0 (cx0, cx1, cx2, cx3, cx4, cc0, cx5) ->
                                  let dx0 = fst da0
                                  in let !ux0 = oplus cx0 dx0
                                     in let dx1 = snd da0
                                        in let !ux1 = oplus cx1 dx1
                                           in let dx2 = getSum dx0
                                              in let !ux2 = oplus cx2 dx2
                                                 in let dx3 = getSum dx1
                                                    in let !ux3 = oplus cx3 dx3
                                                       in let !(!dx4, !uc0) =
                                                                dmul
                                                                  cx2
                                                                  dx2
                                                                  cx3
                                                                  dx3
                                                                  cc0
                                                          in let !ux4 =
                                                                   oplus cx4 dx4
                                                             in let dx5 =
                                                                      Sum dx4
                                                                in let !ux5 =
                                                                         oplus
                                                                           cx5
                                                                           dx5
                                                                   in ( dx5
                                                                      , ( ux0
                                                                        , ux1
                                                                        , ux2
                                                                        , ux3
                                                                        , ux4
                                                                        , uc0
                                                                        , ux5)))
                       in let !(!cx0, !cc0) = apply2 cf1 cf0 a10
                          in let !(!cx1, !cc1) = apply2 cf2 cf3 cx0
                             in let !(!cx2, !cc2) = apply2 cf1 cf0 a20
                                in let !(!cx3, !cc3) = apply2 cf2 cf3 cx2
                                   in let !(!cx4, !cc4) = cmerge cx1 cx3
                                      in let !(!cx5, !cc5) = apply2 cf4 cf5 cx4
                                         in ( cx5
                                            , ( cf0
                                              , cf1
                                              , cf2
                                              , cf3
                                              , cf4
                                              , cf5
                                              , cx0
                                              , cc0
                                              , cx1
                                              , cc1
                                              , cx2
                                              , cc2
                                              , cx3
                                              , cc3
                                              , cx4
                                              , cc4
                                              , cx5
                                              , cc5))))
    (\(ca10, ca20) (da10, da20) (cf0, cf1, cf2, cf3, cf4, cf5, cx0, cc0, cx1, cc1, cx2, cc2, cx3, cc3, cx4, cc4, cx5, cc5) ->
       let df0 =
             DPrimitive
               (\ca0 da0 (cx0) ->
                  let dx0 = fst da0
                  in let !ux0 = oplus cx0 dx0
                     in (dx0, (ux0)))
       in let !uf0 = oplus cf0 df0
          in let df1 =
                   DPrimitive
                     (\(ca10, ca20) (da10, da20) (cf0, cx0, cc0, cx1, cc1) ->
                        let df0 =
                              DPrimitive
                                (\(ca10, ca20) (da10, da20) (cx0, cc0, cx1, cc1, cx2, cc2) ->
                                   let !(!dx0, !uc0) =
                                         dapply ca10 da10 ca20 da20 cc0
                                   in let !ux0 = oplus cx0 dx0
                                      in let !(!dx1, !uc1) =
                                               Bag.dsingleton ca20 da20 cc1
                                         in let !ux1 = oplus cx1 dx1
                                            in let !(!dx2, !uc2) =
                                                     Map.dsingleton
                                                       cx0
                                                       dx0
                                                       cx1
                                                       dx1
                                                       cc2
                                               in let !ux2 = oplus cx2 dx2
                                                  in ( dx2
                                                     , ( ux0
                                                       , uc0
                                                       , ux1
                                                       , uc1
                                                       , ux2
                                                       , uc2)))
                        in let !uf0 = oplus cf0 df0
                           in let !(!dx0, !uc0) = dclosure cf0 df0 ca10 da10 cc0
                              in let !ux0 = oplus cx0 dx0
                                 in let !(!dx1, !uc1) =
                                          dfoldMapGroup cx0 dx0 ca20 da20 cc1
                                    in let !ux1 = oplus cx1 dx1
                                       in (dx1, (uf0, ux0, uc0, ux1, uc1)))
             in let !uf1 = oplus cf1 df1
                in let df2 =
                         DPrimitive
                           (\(ca10, ca20) (da10, da20) (cf0, cx0, cc0, cx1, cc1) ->
                              let df0 =
                                    DPrimitive
                                      (\(ca10, (ca20, ca30)) (da10, (da20, da30)) (cx0, cc0, cx1, cc1) ->
                                         let !(!dx0, !uc0) =
                                               dapply ca10 da10 ca30 da30 cc0
                                         in let !ux0 = oplus cx0 dx0
                                            in let !(!dx1, !uc1) =
                                                     Map.dsingleton
                                                       ca20
                                                       da20
                                                       cx0
                                                       dx0
                                                       cc1
                                               in let !ux1 = oplus cx1 dx1
                                                  in (dx1, (ux0, uc0, ux1, uc1)))
                              in let !uf0 = oplus cf0 df0
                                 in let !(!dx0, !uc0) =
                                          dclosure cf0 df0 ca10 da10 cc0
                                    in let !ux0 = oplus cx0 dx0
                                       in let !(!dx1, !uc1) =
                                                dfoldMapGroupWithKey
                                                  cx0
                                                  dx0
                                                  ca20
                                                  da20
                                                  cc1
                                          in let !ux1 = oplus cx1 dx1
                                             in (dx1, (uf0, ux0, uc0, ux1, uc1)))
                   in let !uf2 = oplus cf2 df2
                      in let df3 =
                               DPrimitive
                                 (\ca0 da0 (cf0, cx0, cc0) ->
                                    let df0 =
                                          DPrimitive
                                            (\ca0 da0 (cx0, cx1) ->
                                               let dx0 = snd da0
                                               in let !ux0 = oplus cx0 dx0
                                                  in let dx1 = Sum dx0
                                                     in let !ux1 = oplus cx1 dx1
                                                        in (dx1, (ux0, ux1)))
                                    in let !uf0 = oplus cf0 df0
                                       in let !(!dx0, !uc0) =
                                                dfoldMapGroup
                                                  cf0
                                                  df0
                                                  ca0
                                                  da0
                                                  cc0
                                          in let !ux0 = oplus cx0 dx0
                                             in (dx0, (uf0, ux0, uc0)))
                         in let !uf3 = oplus cf3 df3
                            in let df4 =
                                     DPrimitive
                                       (\(ca10, ca20) (da10, da20) (cf0, cx0, cc0, cx1, cc1) ->
                                          let df0 =
                                                DPrimitive
                                                  (\(ca10, (ca20, ca30)) (da10, (da20, da30)) (cx0, cc0) ->
                                                     let !(!dx0, !uc0) =
                                                           dapply
                                                             ca10
                                                             da10
                                                             ca30
                                                             da30
                                                             cc0
                                                     in let !ux0 = oplus cx0 dx0
                                                        in (dx0, (ux0, uc0)))
                                          in let !uf0 = oplus cf0 df0
                                             in let !(!dx0, !uc0) =
                                                      dclosure
                                                        cf0
                                                        df0
                                                        ca10
                                                        da10
                                                        cc0
                                                in let !ux0 = oplus cx0 dx0
                                                   in let !(!dx1, !uc1) =
                                                            dfoldMapGroupWithKey
                                                              cx0
                                                              dx0
                                                              ca20
                                                              da20
                                                              cc1
                                                      in let !ux1 =
                                                               oplus cx1 dx1
                                                         in ( dx1
                                                            , ( uf0
                                                              , ux0
                                                              , uc0
                                                              , ux1
                                                              , uc1)))
                               in let !uf4 = oplus cf4 df4
                                  in let df5 =
                                           DPrimitive
                                             (\ca0 da0 (cx0, cx1, cx2, cx3, cx4, cc0, cx5) ->
                                                let dx0 = fst da0
                                                in let !ux0 = oplus cx0 dx0
                                                   in let dx1 = snd da0
                                                      in let !ux1 =
                                                               oplus cx1 dx1
                                                         in let dx2 = getSum dx0
                                                            in let !ux2 =
                                                                     oplus
                                                                       cx2
                                                                       dx2
                                                               in let dx3 =
                                                                        getSum
                                                                          dx1
                                                                  in let !ux3 =
                                                                           oplus
                                                                             cx3
                                                                             dx3
                                                                     in let !(!dx4, !uc0) =
                                                                              dmul
                                                                                cx2
                                                                                dx2
                                                                                cx3
                                                                                dx3
                                                                                cc0
                                                                        in let !ux4 =
                                                                                 oplus
                                                                                   cx4
                                                                                   dx4
                                                                           in let dx5 =
                                                                                    Sum
                                                                                      dx4
                                                                              in let !ux5 =
                                                                                       oplus
                                                                                         cx5
                                                                                         dx5
                                                                                 in ( dx5
                                                                                    , ( ux0
                                                                                      , ux1
                                                                                      , ux2
                                                                                      , ux3
                                                                                      , ux4
                                                                                      , uc0
                                                                                      , ux5)))
                                     in let !uf5 = oplus cf5 df5
                                        in let !(!dx0, !uc0) =
                                                 dapply2
                                                   cf1
                                                   df1
                                                   cf0
                                                   df0
                                                   ca10
                                                   da10
                                                   cc0
                                           in let !ux0 = oplus cx0 dx0
                                              in let !(!dx1, !uc1) =
                                                       dapply2
                                                         cf2
                                                         df2
                                                         cf3
                                                         df3
                                                         cx0
                                                         dx0
                                                         cc1
                                                 in let !ux1 = oplus cx1 dx1
                                                    in let !(!dx2, !uc2) =
                                                             dapply2
                                                               cf1
                                                               df1
                                                               cf0
                                                               df0
                                                               ca20
                                                               da20
                                                               cc2
                                                       in let !ux2 =
                                                                oplus cx2 dx2
                                                          in let !(!dx3, !uc3) =
                                                                   dapply2
                                                                     cf2
                                                                     df2
                                                                     cf3
                                                                     df3
                                                                     cx2
                                                                     dx2
                                                                     cc3
                                                             in let !ux3 =
                                                                      oplus
                                                                        cx3
                                                                        dx3
                                                                in let !(!dx4, !uc4) =
                                                                         dmerge
                                                                           cx1
                                                                           dx1
                                                                           cx3
                                                                           dx3
                                                                           cc4
                                                                   in let !ux4 =
                                                                            oplus
                                                                              cx4
                                                                              dx4
                                                                      in let !(!dx5, !uc5) =
                                                                               dapply2
                                                                                 cf4
                                                                                 df4
                                                                                 cf5
                                                                                 df5
                                                                                 cx4
                                                                                 dx4
                                                                                 cc5
                                                                         in let !ux5 =
                                                                                  oplus
                                                                                    cx5
                                                                                    dx5
                                                                            in ( dx5
                                                                               , ( uf0
                                                                                 , uf1
                                                                                 , uf2
                                                                                 , uf3
                                                                                 , uf4
                                                                                 , uf5
                                                                                 , ux0
                                                                                 , uc0
                                                                                 , ux1
                                                                                 , uc1
                                                                                 , ux2
                                                                                 , uc2
                                                                                 , ux3
                                                                                 , uc3
                                                                                 , ux4
                                                                                 , uc4
                                                                                 , ux5
                                                                                 , uc5)))
