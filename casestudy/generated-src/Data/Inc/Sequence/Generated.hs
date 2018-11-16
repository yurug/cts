{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -w #-}
module Data.Inc.Sequence.Generated where

import Prelude hiding (concat, map)

import Data.Inc.ChangeStruct (
  Dt, oplus, nil)
import Data.Inc.Function (
  Fun(Primitive), DFun(DPrimitive),
  apply, dapply,
  apply2, dapply2,
  closure, cclosure, dclosure)
import Data.Inc.Sequence (
  Sequence,
  concat, cconcat, dconcat,
  map, cmap, dmap)
import qualified Data.Inc.Sequence as Sequence (
  empty,
  singleton, csingleton, dsingleton)

default (Int)


cartesianProduct :: Sequence Int -> Sequence Int -> Sequence (Int, Int)
ccartesianProduct :: (Sequence Int, Sequence Int) -> (Sequence (Int, Int), _)
dcartesianProduct :: (Sequence Int, Sequence Int) -> (Dt (Sequence Int, Sequence Int)) -> _ -> (Dt (Sequence (Int, Int)), _)

cartesianProduct =
  (\a10 a20 ->
     let f0 =
           (\a10 a20 ->
              let x0 = map a10 a20
              in let x1 = concat x0
                 in x1)
     in let f1 =
              (\a10 a20 ->
                 let f0 =
                       (\a10 a20 ->
                          let x0 = (,) a10 a20
                          in x0)
                 in let x0 = closure f0 a20
                    in let x1 = map x0 a10
                       in x1)
        in let x0 = closure f1 a20
           in let x1 = ($) f0 x0 a10
              in x1)

Primitive ccartesianProduct dcartesianProduct =
  Primitive
    ((\(a10, a20) ->
        let cf0 =
              Primitive
                ((\(a10, a20) ->
                    let !(!cx0, !cc0) = cmap a10 a20
                    in let !(!cx1, !cc1) = cconcat cx0
                       in (cx1, (cx0, cc0, cx1, cc1))))
                (\(ca10, ca20) (da10, da20) (cx0, cc0, cx1, cc1) ->
                   let !(!dx0, !uc0) = dmap ca10 da10 ca20 da20 cc0
                   in let !ux0 = oplus cx0 dx0
                      in let !(!dx1, !uc1) = dconcat cx0 dx0 cc1
                         in let !ux1 = oplus cx1 dx1
                            in (dx1, (ux0, uc0, ux1, uc1)))
        in let cf1 =
                 Primitive
                   ((\(a10, a20) ->
                       let cf0 =
                             Primitive
                               ((\(a10, a20) ->
                                   let cx0 = (,) a10 a20
                                   in (cx0, (cx0))))
                               (\(ca10, ca20) (da10, da20) (cx0) ->
                                  let dx0 = (,) da10 da20
                                  in let !ux0 = oplus cx0 dx0
                                     in (dx0, (ux0)))
                       in let !(!cx0, !cc0) = cclosure cf0 a20
                          in let !(!cx1, !cc1) = cmap cx0 a10
                             in (cx1, (cf0, cx0, cc0, cx1, cc1))))
                   (\(ca10, ca20) (da10, da20) (cf0, cx0, cc0, cx1, cc1) ->
                      let df0 =
                            DPrimitive
                              (\(ca10, ca20) (da10, da20) (cx0) ->
                                 let dx0 = (,) da10 da20
                                 in let !ux0 = oplus cx0 dx0
                                    in (dx0, (ux0)))
                      in let !uf0 = oplus cf0 df0
                         in let !(!dx0, !uc0) = dclosure cf0 df0 ca20 da20 cc0
                            in let !ux0 = oplus cx0 dx0
                               in let !(!dx1, !uc1) = dmap cx0 dx0 ca10 da10 cc1
                                  in let !ux1 = oplus cx1 dx1
                                     in (dx1, (uf0, ux0, uc0, ux1, uc1)))
           in let !(!cx0, !cc0) = cclosure cf1 a20
              in let !(!cx1, !cc1) = apply2 cf0 cx0 a10
                 in (cx1, (cf0, cf1, cx0, cc0, cx1, cc1))))
    (\(ca10, ca20) (da10, da20) (cf0, cf1, cx0, cc0, cx1, cc1) ->
       let df0 =
             DPrimitive
               (\(ca10, ca20) (da10, da20) (cx0, cc0, cx1, cc1) ->
                  let !(!dx0, !uc0) = dmap ca10 da10 ca20 da20 cc0
                  in let !ux0 = oplus cx0 dx0
                     in let !(!dx1, !uc1) = dconcat cx0 dx0 cc1
                        in let !ux1 = oplus cx1 dx1
                           in (dx1, (ux0, uc0, ux1, uc1)))
       in let !uf0 = oplus cf0 df0
          in let df1 =
                   DPrimitive
                     (\(ca10, ca20) (da10, da20) (cf0, cx0, cc0, cx1, cc1) ->
                        let df0 =
                              DPrimitive
                                (\(ca10, ca20) (da10, da20) (cx0) ->
                                   let dx0 = (,) da10 da20
                                   in let !ux0 = oplus cx0 dx0
                                      in (dx0, (ux0)))
                        in let !uf0 = oplus cf0 df0
                           in let !(!dx0, !uc0) = dclosure cf0 df0 ca20 da20 cc0
                              in let !ux0 = oplus cx0 dx0
                                 in let !(!dx1, !uc1) =
                                          dmap cx0 dx0 ca10 da10 cc1
                                    in let !ux1 = oplus cx1 dx1
                                       in (dx1, (uf0, ux0, uc0, ux1, uc1)))
             in let !uf1 = oplus cf1 df1
                in let !(!dx0, !uc0) = dclosure cf1 df1 ca20 da20 cc0
                   in let !ux0 = oplus cx0 dx0
                      in let !(!dx1, !uc1) =
                               dapply2 cf0 df0 cx0 dx0 ca10 da10 cc1
                         in let !ux1 = oplus cx1 dx1
                            in (dx1, (uf0, uf1, ux0, uc0, ux1, uc1)))

