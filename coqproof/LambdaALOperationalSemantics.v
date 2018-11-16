(** * Operational semantics of λ_{AL} *)

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
Require Import LambdaALOperationalSemanticsPrimitives.

(** ** Evaluation of base terms *)

(** *** Evaluation environments *)

Definition environment := Environment.t value.

(** *** Big step evaluation *)

(** *** An indexed big step evaluation relation. *)

(**

  We define two similar big step interpretations of terms which only
  differ with respect to the presence or absence of indices. For this
  reason, we use a single inductive type to represent both and we
  parameterize it with respect to the presence or absence of step
  indices.

*)

(** An [indexType] characterizes the presence or absence of step
    indices. *)
Inductive indexType :=
| Steps
| NoSteps.

(** [index i] returns the type of inductive type parameter. *)
Definition index (i : indexType) :=
  match i with Steps => nat | NoSteps => unit end.

(** [toI i n] erases the step index [n] if [i] is [NoSteps]. *)
Definition toI {i : indexType} n : index i :=
  match i with Steps => n | NoSteps => tt end.

(** [geval n E t v] is the big-step evaluation judgement reads
    as ``Under "E", the base term "t" evaluates to "v" in "n" steps.''

    This judgement is defined in Figure 2 of the paper.
*)
Inductive geval (i : indexType)
: (index i) -> environment -> term -> value -> Prop :=
| SVar :
    forall E x v,
      lookup E x = Some v ->
      geval i (toI 1) E (Var x) v

| STuple :
    forall env xs vs n t v,
    lookups env xs = Some vs ->
    geval i (toI n) (bind env (tuple vs)) t v ->
    geval i (toI (S n)) env (DefTuple xs t) v

| SPrimitiveCall :
    forall n E f x t v vx p v',
      lookup E f = Some (Primitive p) ->
      lookup E x = Some vx ->
      eval_primitive p vx = Some v' ->
      geval i (toI n) (bind E v') t v ->
      geval i (toI (S n)) E (Def f x t) v

| SClosureCall :
    forall n m E f x t v vx Ef tf vy,
      lookup E f = Some (closure Ef tf) ->
      lookup E x = Some vx ->
      geval i (toI n) (bind Ef vx) tf vy ->
      geval i (toI m) (bind E vy) t v ->
      geval i (toI (S (n + m))) E (Def f x t) v.

Definition eval     := geval Steps.
Definition neval    := geval NoSteps tt.

Notation "[ E ⊢ t ⇓ v ]"     := (neval E t v).
Notation "[ E ⊢ t ⇓ v @ n ]" := (eval n E t v).

(** ** Evaluation of change terms *)

(** *** Semantics for change application *)

(** [move_literal ℓ dℓ]. *)
Definition move_literal (c : literal) (dc : dliteral) :=
  match c, dc with
    | Nat x, dPos dx =>
      ret (Nat (x + dx))
  end.

(** [move v dv] applies a change [dv] to a value [v].

    The following definition of [move] implements the specification of
    [∙ ⊕ ∙] as defined in page 9 of the paper. Notice however that the
    function [move_closure_environment] does not require [E] and [dE]
    to be "synchronized" in terms of the value it contains.

*)
Fixpoint move v dv :=
  match v, dv with
    | v, dReplace v' =>
      ret v'
    | Literal c, dLiteral dc =>
      nv <- move_literal c dc;
      ret (Literal nv)
    | Tuple vs, dTuple dvs =>
      nvs <- move_values vs dvs;
      ret (Tuple nvs)
    | Primitive _, dPrimitiveNil =>
      ret v
    | Closure env t, dClosure denv dt =>
      env' <- move_closure_environment env denv;
      ret (Closure env' t)
    | _, _ =>
      error
  end
with move_closure_environment E dE { struct E } :=
  match E, dE with
    | VNil, CDNil =>
      ret VNil
    | VCons v E, CDCons v' dv dE =>
      (** Notice that, contrary to the paper definition, we do not require v = v'. *)
      v' <- move v dv;
      E' <- move_closure_environment E dE;
      ret (VCons v' E')
    | _, _ =>
      error
  end
with move_values vs dvs { struct vs } :=
  match vs, dvs with
    | VNil, DVNil =>
      ret VNil
    | VCons v vs, DVCons dv dvs =>
      v' <- move v dv;
      vs' <- move_values vs dvs;
      ret (VCons v' vs')
    | _, _ =>
      error
  end.

Notation "v ⊕ dv" := (move v dv) (at level 60).

(**

    An evaluation environment for change terms is made of pairs
    composed of a value and a change to this value.

*)
Definition denvironment := Environment.t (value * dvalue).

(** [move_environment E dE] applies environment change [dE] to base enviroment [E]. *)
Fixpoint move_environment E (dE : denvironment) { struct E } :=
  match E, dE with
    | VNil, nil =>
      ret VNil
    | VCons v E, (v', dv) :: dE =>
      (** Notice that, contrary to the paper definition, we do not require v = v'. *)
      v' <- move v dv;
      E' <- move_environment E dE;
      ret (VCons v' E')
    | _, _ =>
      error
  end.

(**

    An evaluation environment for change terms is related to
    two evaluation environments for base terms, the original
    and the modified environment.

*)
Definition original_environment (dE : denvironment) : environment :=
  List.map fst dE.

Notation "⌊ dE ⌋" := (original_environment dE).

Definition modified_environment (dE : denvironment) : ErrorMonad.t environment :=
  ErrorMonad.list_map (fun x => fst x ⊕ snd x) dE.

Notation "⌈ dE ⌉" := (modified_environment dE).

(**

    A closure enviroment is isomorphic to a [denvironment].

    In the sequel, we try to move from [closure_environment] to
    [denvironment] as soon as possible in all definitions so that
    most of the proofs focus on [denvironment].

*)
Definition denvironment_of_closure_denvironment := list_of_closure_denvironment.

(** * Big step evaluation for change terms *)

(**

     Change terms enjoy a standard big step evaluation.

*)

(** Evaluation of functional constants derivatives. *)
Definition recompute_primitive c a da :=
  a' <- a ⊕ da;
  v' <- eval_primitive c a';
  ret (dReplace v').

Equations eval_dadd (a : value) (da : dvalue) : ErrorMonad.t dvalue :=
  eval_dadd
    (Tuple [@ Literal (Nat x); Literal (Nat y) ])
    (dTuple (DVCons (dLiteral (dPos dx)) (DVCons (dLiteral (dPos dy)) DVNil)))
    := ret (dLiteral (dPos (dx + dy)));

  eval_dadd (Tuple  [@ Literal (Nat x); Literal (Nat y) ]) da
    := recompute_primitive Add (Tuple  [@ Literal (Nat x); Literal (Nat y) ]) da;

  eval_dadd _ _ := error.

Definition eval_dpush (a : value) (da : dvalue) : ErrorMonad.t dvalue :=
  recompute_primitive Push a da.

Definition eval_dcurry (a : value) (da : dvalue) : ErrorMonad.t dvalue :=
  recompute_primitive Curry a da.

Definition eval_dfixrec (a : value) (da : dvalue) : ErrorMonad.t dvalue :=
  recompute_primitive FixRec a da.

Definition eval_dprimitive c :=
  match c with
    | Add => eval_dadd
    | Push => eval_dpush
    | Curry => eval_dcurry
    | FixRec => eval_dfixrec
  end.

(** Big step evaluation relation for change terms, as implemented in
    Figure 3 of the paper. *)
Inductive gdeval (i : indexType)
: (index i) -> denvironment -> dterm -> dvalue -> Prop :=
| SDVar :
    forall dE x v dv,
      lookup dE x = Some (v, dv) ->
      gdeval i (toI 1) dE (dVar (d x)) dv

| SDTuple :
    forall n dE xs dt dv bs,
      lookups dE xs = Some bs ->
      let vs := List.map fst bs in
      let dvs := List.map snd bs in
      gdeval i (toI n) (bind dE (tuple vs, dtuple dvs)) dt dv ->
      gdeval i (toI (S n)) dE (dDefTuple (List.map d xs) dt) dv

| SDReplaceCall:
    forall k m n dE f vf vf' dv x vy vy' dt E',
      lookup dE f = Some (vf, dReplace vf') ->
      geval i (toI k) ⌊ dE ⌋ (call f x) vy ->
      ⌈ dE ⌉ = Some E' ->
      geval i (toI m) E' (call f x) vy' ->
      gdeval i (toI n) (bind dE (vy, dReplace vy')) dt dv ->
      gdeval i (toI (S (k + m + n))) dE (dDef f x dt) dv

| SPrimitiveNil :
    forall n dE f p x dt vx dvx dv vy dvy,
      lookup dE f = Some (Primitive p, dPrimitiveNil) ->
      lookup dE x = Some (vx, dvx) ->
      eval_primitive p vx = Some vy ->
      eval_dprimitive p vx dvx = Some dvy ->
      gdeval i (toI n) (bind dE (vy, dvy)) dt dv ->
      gdeval i (toI (S n)) dE (dDef f x dt) dv

| SDefClosure :
    forall k n m dE f x dt Ef dEf tf dtf vx dvx dv vy dvy,
      lookup dE f = Some (closure Ef tf, dclosure dEf dtf) ->
      lookup dE x = Some (vx, dvx) ->
      ⌊ dEf ⌋ = Ef ->
      tf = underive dtf ->
      geval i (toI k) (bind Ef vx) tf vy ->
      gdeval i (toI n) (bind dEf (vx, dvx)) dtf dvy ->
      gdeval i (toI m) (bind dE (vy, dvy)) dt dv ->
      gdeval i (toI (S (k + n + m))) dE (dDef f x dt) dv.

Definition deval := gdeval NoSteps tt.

Notation "[[ dE ⊢ dt ⇓ dv ]]" := (deval dE dt dv).

Notation "[[ dE ⊢ dt ⇓ dv @ n ]]" := (gdeval Steps n dE dt dv).
