(** * Target language \(iλ_{AL}\) *)

Require Import List.
Require Import LambdaAL.
Require Import Constants.
Require Import Index.

(** ** Base terms *)

(** *** Grammar *)

(**

    A cache identifier is a special kind of identifier that refers to
    three other value identifiers, namely [y], [f] and [x]. It denotes
    the intermediate results of the evaluation of [y = f x].
    [Cache y f x] is written \(c^{y}_{f x}\) in the paper.

 *)
Inductive cache_var :=
| Cache : var -> var -> var -> cache_var.

(**

    In the paper, the cache terms are written using the following
    syntax:
#$$\begin{array}{rcl}
C & ::= & \bullet \\
  & \mid & C \; x \\
  & \mid & C \; c^{y}_{f x}
\end{array}$$#

*)
(**

    Yet, we actually never push a cache variable alone in the cache:
    it is always preceded by a variable. Therefore, to enforce this
    invariant, we chose to use the following Coq type to represent C.

*)
Definition cache := list (var * option cache_var).

Definition cache_update := list (var * option cache_var).

(** The type for base terms.

    - "[IResult (x, C)]" represents "\((x, C)\)".
    - "[IDef f x t]" represents "\({\bf let }\; y, c^{y}_{f x} = f\, x \;{\bf in }\; t\)".
    - "[IDefTuple [x₁; ...; xₙ]]" represents "\({\bf let }\; y = (x₁, ..., xₙ) \;{\bf in }\; t\)".

*)
Inductive term :=
| IResult : var -> cache -> term
| IDef : var -> var -> term -> term
| IDefTuple : list var -> term -> term.

(** *** Syntactic sugar *)

Definition call f xs := IDef f xs (IResult (Idx O) (cons (Idx 0, Some (Cache (Idx 0) f xs)) nil)).

Notation "@#( f , x )" := (call f x).

Definition tuple xs := IDefTuple xs (IResult (Idx O) (cons (Idx 0, None) nil)).

(** ** Change terms *)

(**

    The change identifier are imported from the syntax of
    \(\lambda_{AL}\).

*)
Definition dvar := LambdaAL.dvar.

(** The type of change terms. (Figure 1 in paper.)

    - "[dIResult x dC]" represents "[\(dx, dC\)]".
    - "[dIDef f x dM]" represents "\({\bf let}\; dy, c^{y}_{f x} = df\, x\, dx {\bf in}\; dM\)".
    - "[dIDefTuple [dx₁; ...; dxₙ] dM]"
       represents "\({\bf let}\; dy = (dx₁, ..., dxₙ) {\bf in}\; dM\)".

*)
Inductive dterm :=
| dIResult : dvar -> cache -> dterm
| dIDef : var -> var -> dterm -> dterm
| dIDefTuple : list dvar -> dterm -> dterm.

(** *** Syntactic sugar *)

Definition dcall f x := dIDef f x (dIResult (d (Idx O)) (cons (Idx 0, Some (Cache (Idx 0) f x)) nil)).

Definition dtuple xs := dIDefTuple xs (dIResult (d (Idx O)) (cons (Idx 0, None) nil)).
