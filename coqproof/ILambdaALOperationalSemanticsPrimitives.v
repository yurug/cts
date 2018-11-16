From Equations Require Import Equations.
Require Import List.
Require Import Omega.
Require Import Index.
Require Import LambdaAL.
Require Import Constants.
Require Import ErrorMonad.
Require Import Environment.
Require Import ILambdaAL.
Require Import ILambdaALValues.

Equations eval_add (a : value) : ErrorMonad.t (value * cache_value) :=
  eval_add (ITuple [# ILiteral (Nat x); ILiteral (Nat y) ]) :=
    ret (ILiteral (Nat (x + y)), CacheValue nil);
  eval_add _ := error.

Equations eval_curry (a : value) : ErrorMonad.t (value * cache_value) :=
  eval_curry (IClosure env t) :=
    let c := IClosure env t in
    let cache :=
        [((Idx 1), None); ((Idx 0), Some (Cache (Idx 0) (Idx 3) (Idx 0)))]
    in
    let cf :=
        IClosure
          (values_of_list [ c ]) (
            IDefTuple [ Idx 1; Idx 0 ] (
                       IDef (Idx 3) (Idx 0) (
                             IResult (Idx 0) cache
                           )
                     )
          )
    in
    ret (IClosure (values_of_list [ cf; IPrimitive Push]) (
              IDefTuple [ Idx 1; Idx 0 ]
                  (IDef (Idx 3) (Idx 0) 
                       (IResult (Idx 0) cache))
            ), CacheValue []);

   eval_curry _ := error.

Equations eval_push (a : value) : ErrorMonad.t (value * cache_value) :=
  eval_push (ITuple [# IClosure env t; v ]) := 
    ret (IClosure (IVCons v env) t, CacheValue nil);
  eval_push _ := error.

Equations eval_fixrec (a : value) : ErrorMonad.t (value * cache_value) :=
  eval_fixrec (IClosure env t) :=
    let F := (** F : (A -> B) -> (A -> B). *)
        IClosure env t
    in
    let FixF :=
        IClosure
          (values_of_list [ F; IPrimitive FixRec ])
          (IDef (Idx 2) (Idx 1) ( (* FIX F *)
                 IDef (Idx 0) (Idx 1) ( (* (FIX F) X *)
                       (IResult (Idx 0) 
                                [(Idx 1, Some (Cache (Idx 1) (Idx 3) (Idx 2)));
                                   (Idx 0, Some (Cache (Idx 0) (Idx 0) (Idx 1)))])
                     )))
    in
    ret (IClosure
           (values_of_list [ F; FixF ])
           (IDef (Idx 1) (Idx 2) ( (* F (FIX F) *)
                  IDef (Idx 0) (Idx 1) ( (* F (FIX F) X *)
                        (IResult (Idx 0) 
                                 [(Idx 1, Some (Cache (Idx 1) (Idx 2) (Idx 3)));
                                    (Idx 0, Some (Cache (Idx 0) (Idx 0) (Idx 1)))]
           )))), CacheValue nil) ;

  eval_fixrec _ := error.

Definition eval_primitive c :=
  match c with
    | Add => eval_add
    | Push => eval_push
    | Curry => eval_curry
    | FixRec => eval_fixrec
  end.
