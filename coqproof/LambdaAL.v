(** * Source language \(λ_{AL}\) *)

Require Import Index.
Require Import List.

(** ** Base terms *)

(** *** Grammar for base terms *)

(** The type of base terms. (Figure 1 in paper.)

    - "[Var x]" represents "\(x\)".
    - "[Def f x t]" represents "\({\bf let }\; y = f\, x \;{\bf in }\; t\)".
    - "[DefTuple [x₁; ...; xₙ]]" represents "\({\bf let }\; y = (x₁, ..., xₙ) \;{\bf in }\; t\)".

*)
Inductive term :=
| Var : var -> term
| Def : var -> var -> term -> term
| DefTuple : list var -> term -> term.

(** *** Syntactic sugar *)

(** In the paper, we write [@(f, x)] for [let y = f x in y] where [y]
    is chosen sufficiently fresh.

    Notice that [Var (Idx O)] is an adequate implementation for [y]. *)
Definition call f x := Def f x (Var (Idx O)).
Notation "@( f , x )" := (call f x).

Definition ttuple xs := DefTuple xs (Var (Idx 0)).

(** ** Change terms *)

(** *** Grammar for change terms *)

(** Change variables are represented by DeBruijn indices. *)
Inductive dvar := d : var -> dvar.

(** The type of change terms. (Figure 1 in paper.)

    - "[dVar x]" represents "\(dx\)".
    - "[dDef f x dt]" represents "\({\bf let}\; y = f\, x, dy = df\, x\, dx\, {\bf in}\, dt\)".
    - "[dDefTuple [dx₁; ...; dxₙ] dt]" represents "\({\bf let}\; y = (x₁, ..., xₙ), dy = (dx₁, ..., dxₙ) \, {\bf in}\, dt\)".

*)

(**

    Notice that we could have used the same syntax as [term] to
    represent change terms since they are totally isomorphic. Yet, we
    prefer a form of "strong" typing in the formalization to avoid any
    confusion in the definitions, in particular in the operational
    semantics, in the program transformation and the validity
    relation.

*)
Inductive dterm :=
| dVar : dvar -> dterm
| dDef : var -> var -> dterm -> dterm
| dDefTuple : list dvar -> dterm -> dterm.

Definition dcall f x := dDef f x (dVar (d (Idx O))).

Definition dttuple xs := dDefTuple xs (dVar (d (Idx 0))).

(** *** Basic syntax mechanisms *)

(** Read as "un-d", undo d, not German und. *)
Definition und (dx : dvar) : var :=
  match dx with d x => x end.

Lemma d_und:
  forall dx, d (und dx) = dx.
Proof. destruct dx. auto. Qed.

Lemma und_d:
  forall x, und (d x) = x.
Proof. destruct x. auto. Qed.

Lemma map_und_d_id :
  forall xs, List.map und (List.map d xs) = xs.
Proof.
  induction xs; simpl; eauto.
  rewrite IHxs. auto.
Qed.

Definition context := term.

Fixpoint graft (ctx : context) (u : term) : term :=
  match ctx with
  | Var _ => u
  | DefTuple xs ctx => DefTuple xs (graft ctx u)
  | Def f x ctx => Def f x (graft ctx u)
  end.

Definition dcontext := dterm.

Fixpoint dgraft (dctx : dcontext) (du : dterm) : dterm :=
  match dctx with
  | dVar _ => du
  | dDefTuple xs dctx => dDefTuple xs (dgraft dctx du)
  | dDef f x dctx => dDef f x (dgraft dctx du)
  end.
