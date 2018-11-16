(** * Semantics of primitives *)

Require Import Equations.Equations.
Require Import List.
Require Import Omega.
Require Import Index.
Require Import LambdaAL.
Require Import Constants.
Require Import LambdaALValues.
Require Import ErrorMonad.
Require Import Environment.
Require Import LambdaALDerive.

(** **** Evaluation of primitives *)

Equations eval_add (a : value) : ErrorMonad.t value :=
  eval_add (Tuple [@ Literal (Nat x); Literal (Nat y) ]) := ret (Literal (Nat (x + y)));
  eval_add _ := error.

Equations eval_push (a : value) : ErrorMonad.t value :=
  eval_push (Tuple [@ Closure env t; v ]) := ret (Closure (VCons v env) t);
  eval_push _ := error.

Equations eval_curry (a : value) : ErrorMonad.t value :=
  eval_curry (Closure env t) :=
    let c := Closure env t in
    let cf :=
        Closure
          (values_of_list [ c ]) (
            DefTuple [ Idx 1; Idx 0 ] (
                       Def (Idx 3) (Idx 0) (
                             Var (Idx 0)
                           )
                     )
          )
          (*
            The closure cf has environment (f = c), but the call to push below
            turns that into (x - vx; f = c). Its body is then:
            lam y.
                let z = (x; y)
                let w = (f; z)
                in w
           *)
    in
    ret (Closure (values_of_list [ cf; Primitive Push]) (
              DefTuple [ Idx 1; Idx 0 ]
                  (Def (Idx 3) (Idx 0) (Var (Idx 0)))
            ));
      (* This returns:
         (g = cf; p = Push)[lam x.
            let y = (g; x)
            let z = p y
            in z]
       *)

   eval_curry _ := error.

Equations eval_fixrec (a : value) : ErrorMonad.t value :=
  eval_fixrec (Closure env t) :=
    let F := (** F : (A -> B) -> (A -> B). *)
        Closure env t
    in
    let FixF :=
        Closure
          (values_of_list [ F; Primitive FixRec ])
          (Def (Idx 2) (Idx 1) ( (* FIX F *)
                 Def (Idx 0) (Idx 1) ( (* (FIX F) X *)
                       (Var (Idx 0))
                     )))
    in
    ret (Closure
           (values_of_list [ F; FixF ])
           (Def (Idx 1) (Idx 2) ( (* F (FIX F) *)
                  Def (Idx 0) (Idx 1) ( (* F (FIX F) X *)
                        (Var (Idx 0)))))) ;

  eval_fixrec _ := error.

Definition eval_primitive c :=
  match c with
  | Add => eval_add
  | Push => eval_push
  | Curry => eval_curry
  | FixRec => eval_fixrec
  end.

