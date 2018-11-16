Require Import Misc.
Require Import Constants.
Require Import LambdaAL.
Require Import LambdaALValues.


(** * Static derivatives form  base terms *)

(**

   In this module, we implement a program transformation [derive] that
   turns a base term into its derivative change term, mimicking the
   transformation introduced by Cai et al. This transformation is
   reversible as witnessed by the function [underive] and its lemmas.

*)

(** [derive t] turns a base term [t] into its derivative change term. *)
Fixpoint derive (t : term) : dterm :=
  match t with
    | Var x => dVar (d x)
    | Def f x t => dDef f x (derive t)
    | DefTuple xs t => dDefTuple (List.map d xs) (derive t)
  end.

(** [underive t] *)
Fixpoint underive (dt : dterm) : term :=
  match dt with
    | dVar (d x) => Var x
    | dDef f x t => Def f x (underive t)
    | dDefTuple xs t => DefTuple (List.map und xs) (underive t)
  end.

Lemma derive_underive:
  forall dt, derive (underive dt) = dt.
Proof.
  induction dt; simpl; eauto.
  destruct d. auto.
  rewrite IHdt. auto.
  rewrite IHdt. auto.
  rewrite map_map.
  erewrite map_equiv with (g := fun x => x).
  rewrite map_id. auto.
  apply d_und.
Qed.

Lemma underive_derive:
  forall t, underive (derive t) = t.
Proof.
  induction t; simpl; eauto.
  rewrite IHt. auto.
  rewrite map_map.
  erewrite map_equiv with (g := fun x => x).
  rewrite map_id. rewrite IHt.
  auto.
  apply und_d.
Qed.

(** **** An other implementation for nil changes *)

(**

    Instead of using a dedicated constructor [dNil], we could actually
    have implemented a nil change by means of other constructors.

    The case for [Closure] in [dNil'] is using [derive] since
    derivatives are nil function changes.

*)

Definition nil_literal l :=
  match l with
  | Nat n => dPos O
  end.

Fixpoint dNil' v :=
  match v with
  | Closure vs t => dClosure (dNilpdenv vs) (derive t)
  | Tuple vs => dTuple (dNilpldvalues vs)
  | Literal l => dLiteral (nil_literal l)
  | Primitive p => dPrimitiveNil
  end
with dNilpdenv vs :=
  match vs with
  | VNil =>  CDNil
  | VCons v vs => CDCons v (dNil' v) (dNilpdenv vs)
  end
with dNilpldvalues vs :=
  match vs with
  | VNil => DVNil
  | VCons v vs => DVCons (dNil' v) (dNilpldvalues vs)
  end.
