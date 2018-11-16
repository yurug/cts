{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# OPTIONS_GHC -w #-}
module Data.Inc.Bag.Generated where

import Prelude hiding (sum, length)

import Data.Inc.ChangeStruct
import Data.Inc.Function
import Data.Inc.Bag
import Data.Inc.Int

import Data.Monoid

default (Int)


clength :: Bag Int -> (Int, _)

sum =
  (\a0 ->
     let f0 =
           (\a0 ->
              let x0 = Sum a0
              in x0)
     in let x0 = foldMapGroup f0 a0
        in let x1 = getSum x0
           in x1)

Primitive csum dsum =
  Primitive
    ((\a0 ->
        let cf0 =
              Primitive
                ((\a0 ->
                    let cx0 = Sum a0
                    in (cx0, (cx0))))
                (\ca0 da0 (cx0) ->
                   let dx0 = Sum da0
                   in let !ux0 = oplus cx0 dx0
                      in (dx0, (ux0)))
        in let !(!cx0, !cc0) = cfoldMapGroup cf0 a0
           in let cx1 = getSum cx0
              in (cx1, (cf0, cx0, cc0, cx1))))
    (\ca0 da0 (cf0, cx0, cc0, cx1) ->
       let df0 =
             DPrimitive
               (\ca0 da0 (cx0) ->
                  let dx0 = Sum da0
                  in let !ux0 = oplus cx0 dx0
                     in (dx0, (ux0)))
       in let !uf0 = oplus cf0 df0
          in let !(!dx0, !uc0) = dfoldMapGroup cf0 df0 ca0 da0 cc0
             in let !ux0 = oplus cx0 dx0
                in let dx1 = getSum dx0
                   in let !ux1 = oplus cx1 dx1
                      in (dx1, (uf0, ux0, uc0, ux1)))

length =
  (\a0 ->
     let f0 =
           (\a0 ->
              let x0 = 1
              in let x1 = Sum x0
                 in x1)
     in let x0 = foldMapGroup f0 a0
        in let x1 = getSum x0
           in x1)

Primitive clength dlength =
  Primitive
    ((\a0 ->
        let cf0 =
              Primitive
                ((\a0 ->
                    let cx0 = 1
                    in let cx1 = Sum cx0
                       in (cx1, (cx0, cx1))))
                (\ca0 da0 (cx0, cx1) ->
                   let dx0 = 0
                   in let !ux0 = oplus cx0 dx0
                      in let dx1 = Sum dx0
                         in let !ux1 = oplus cx1 dx1
                            in (dx1, (ux0, ux1)))
        in let !(!cx0, !cc0) = cfoldMapGroup cf0 a0
           in let cx1 = getSum cx0
              in (cx1, (cf0, cx0, cc0, cx1))))
    (\ca0 da0 (cf0, cx0, cc0, cx1) ->
       let df0 =
             DPrimitive
               (\ca0 da0 (cx0, cx1) ->
                  let dx0 = 0
                  in let !ux0 = oplus cx0 dx0
                     in let dx1 = Sum dx0
                        in let !ux1 = oplus cx1 dx1
                           in (dx1, (ux0, ux1)))
       in let !uf0 = oplus cf0 df0
          in let !(!dx0, !uc0) = dfoldMapGroup cf0 df0 ca0 da0 cc0
             in let !ux0 = oplus cx0 dx0
                in let dx1 = getSum dx0
                   in let !ux1 = oplus cx1 dx1
                      in (dx1, (uf0, ux0, uc0, ux1)))

average =
  (\a0 ->
     let f0 =
           (\a0 ->
              let f0 =
                    (\a0 ->
                       let x0 = Sum a0
                       in x0)
              in let x0 = foldMapGroup f0 a0
                 in let x1 = getSum x0
                    in x1)
     in let f1 =
              (\a0 ->
                 let f0 =
                       (\a0 ->
                          let x0 = 1
                          in let x1 = Sum x0
                             in x1)
                 in let x0 = foldMapGroup f0 a0
                    in let x1 = getSum x0
                       in x1)
        in let x0 = ($) f0 a0
           in let x1 = ($) f1 a0
              in let x2 = div x0 x1
                 in x2)

Primitive caverage daverage =
  Primitive
    ((\a0 ->
        let cf0 =
              Primitive
                ((\a0 ->
                    let cf0 =
                          Primitive
                            ((\a0 ->
                                let cx0 = Sum a0
                                in (cx0, (cx0))))
                            (\ca0 da0 (cx0) ->
                               let dx0 = Sum da0
                               in let !ux0 = oplus cx0 dx0
                                  in (dx0, (ux0)))
                    in let !(!cx0, !cc0) = cfoldMapGroup cf0 a0
                       in let cx1 = getSum cx0
                          in (cx1, (cf0, cx0, cc0, cx1))))
                (\ca0 da0 (cf0, cx0, cc0, cx1) ->
                   let df0 =
                         DPrimitive
                           (\ca0 da0 (cx0) ->
                              let dx0 = Sum da0
                              in let !ux0 = oplus cx0 dx0
                                 in (dx0, (ux0)))
                   in let !uf0 = oplus cf0 df0
                      in let !(!dx0, !uc0) = dfoldMapGroup cf0 df0 ca0 da0 cc0
                         in let !ux0 = oplus cx0 dx0
                            in let dx1 = getSum dx0
                               in let !ux1 = oplus cx1 dx1
                                  in (dx1, (uf0, ux0, uc0, ux1)))
        in let cf1 =
                 Primitive
                   ((\a0 ->
                       let cf0 =
                             Primitive
                               ((\a0 ->
                                   let cx0 = 1
                                   in let cx1 = Sum cx0
                                      in (cx1, (cx0, cx1))))
                               (\ca0 da0 (cx0, cx1) ->
                                  let dx0 = 0
                                  in let !ux0 = oplus cx0 dx0
                                     in let dx1 = Sum dx0
                                        in let !ux1 = oplus cx1 dx1
                                           in (dx1, (ux0, ux1)))
                       in let !(!cx0, !cc0) = cfoldMapGroup cf0 a0
                          in let cx1 = getSum cx0
                             in (cx1, (cf0, cx0, cc0, cx1))))
                   (\ca0 da0 (cf0, cx0, cc0, cx1) ->
                      let df0 =
                            DPrimitive
                              (\ca0 da0 (cx0, cx1) ->
                                 let dx0 = 0
                                 in let !ux0 = oplus cx0 dx0
                                    in let dx1 = Sum dx0
                                       in let !ux1 = oplus cx1 dx1
                                          in (dx1, (ux0, ux1)))
                      in let !uf0 = oplus cf0 df0
                         in let !(!dx0, !uc0) =
                                  dfoldMapGroup cf0 df0 ca0 da0 cc0
                            in let !ux0 = oplus cx0 dx0
                               in let dx1 = getSum dx0
                                  in let !ux1 = oplus cx1 dx1
                                     in (dx1, (uf0, ux0, uc0, ux1)))
           in let !(!cx0, !cc0) = apply cf0 a0
              in let !(!cx1, !cc1) = apply cf1 a0
                 in let !(!cx2, !cc2) = cdiv cx0 cx1
                    in (cx2, (cf0, cf1, cx0, cc0, cx1, cc1, cx2, cc2))))
    (\ca0 da0 (cf0, cf1, cx0, cc0, cx1, cc1, cx2, cc2) ->
       let df0 =
             DPrimitive
               (\ca0 da0 (cf0, cx0, cc0, cx1) ->
                  let df0 =
                        DPrimitive
                          (\ca0 da0 (cx0) ->
                             let dx0 = Sum da0
                             in let !ux0 = oplus cx0 dx0
                                in (dx0, (ux0)))
                  in let !uf0 = oplus cf0 df0
                     in let !(!dx0, !uc0) = dfoldMapGroup cf0 df0 ca0 da0 cc0
                        in let !ux0 = oplus cx0 dx0
                           in let dx1 = getSum dx0
                              in let !ux1 = oplus cx1 dx1
                                 in (dx1, (uf0, ux0, uc0, ux1)))
       in let !uf0 = oplus cf0 df0
          in let df1 =
                   DPrimitive
                     (\ca0 da0 (cf0, cx0, cc0, cx1) ->
                        let df0 =
                              DPrimitive
                                (\ca0 da0 (cx0, cx1) ->
                                   let dx0 = 0
                                   in let !ux0 = oplus cx0 dx0
                                      in let dx1 = Sum dx0
                                         in let !ux1 = oplus cx1 dx1
                                            in (dx1, (ux0, ux1)))
                        in let !uf0 = oplus cf0 df0
                           in let !(!dx0, !uc0) =
                                    dfoldMapGroup cf0 df0 ca0 da0 cc0
                              in let !ux0 = oplus cx0 dx0
                                 in let dx1 = getSum dx0
                                    in let !ux1 = oplus cx1 dx1
                                       in (dx1, (uf0, ux0, uc0, ux1)))
             in let !uf1 = oplus cf1 df1
                in let !(!dx0, !uc0) = dapply cf0 df0 ca0 da0 cc0
                   in let !ux0 = oplus cx0 dx0
                      in let !(!dx1, !uc1) = dapply cf1 df1 ca0 da0 cc1
                         in let !ux1 = oplus cx1 dx1
                            in let !(!dx2, !uc2) = ddiv cx0 dx0 cx1 dx1 cc2
                               in let !ux2 = oplus cx2 dx2
                                  in ( dx2
                                     , (uf0, uf1, ux0, uc0, ux1, uc1, ux2, uc2)))
