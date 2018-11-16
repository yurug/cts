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
Require Import ILambdaALOperationalSemanticsPrimitives.

Definition environment := Environment.t (value * option cache_value).

Definition lookup_value (F : environment) x :=
  p <- lookup F x;
  ret (fst p).

Definition lookup_values (F : environment) xs :=
  p <- lookups F xs;
  ret (values_of_list (List.map fst p)).

Definition lookup_cache (F : environment) x :=
  p <- lookup F x;
  ret (snd p).

Fixpoint list_of_closure_environment vs : environment :=
  match vs with
  | IVNil => nil
  | IVCons v vs => (v, None) :: list_of_closure_environment vs
  end.

Fixpoint closure_environment_of_list (vs : environment) : values :=
  match vs with
  | nil => IVNil
  | (v, _) :: vs => IVCons v (closure_environment_of_list vs)
  end.

(** ** A big step evaluation relation. *)
Inductive eval_cache : environment -> cache -> cache_value -> Prop :=
| TEmptyCache:
    forall F,
    eval_cache F nil (CacheValue nil)

| TCachedVar:
    forall F C x V VC Cx VCx,
      lookup F x = Some (V,  VCx) ->
      eval_cache F C (CacheValue VC) ->
      eval_cache F ((x, Cx) :: C) (CacheValue ((V, VCx) :: VC)).

Inductive eval : environment -> term -> (value * cache_value) -> Prop :=
| TResult :
    forall F C x V VC VCx,
      lookup F x = Some (V, VCx) ->
      eval_cache F C VC ->
      eval F (IResult x C) (V, VC)

| TPrimitiveCall :
    forall F f p x Vx M V V' VC',
      lookup_value F f = Some (IPrimitive p) ->
      lookup_value F x = Some Vx ->
      eval_primitive p Vx = Some (V', VC') ->
      eval (bind F (V', Some VC')) M V ->
      eval F (IDef f x M) V

| TClosureCall :
    forall F f x M V F' M' Vx V' VC',
      lookup_value F f = Some (IClosure F' M') ->
      lookup_value F x = Some Vx ->
      eval (bind (list_of_closure_environment F') (Vx, None)) M' (V', VC') ->
      eval (bind F (V', Some VC')) M V ->
      eval F (IDef f x M) V

| TTuple :
    forall F xs Vs M V,
    lookup_values F xs = Some Vs ->
    eval (bind F (ITuple Vs, None)) M V ->
    eval F (IDefTuple xs M) V.

Notation "[# F ⊢ M ⇓ V ]"     := (eval F M V).

Reserved Notation "[# E ⊢ ctx ⇑ E' ]".

Definition context := term.

Inductive eval_context: environment -> context -> environment -> Prop :=
| TNilContext: forall F x C,
    [# F ⊢ IResult x C ⇑ nil ]

| TTupleContext: forall F xs ctx F' Vs,
    lookup_values F xs = Some Vs ->
    [# (ITuple Vs, None) :: F ⊢ ctx ⇑ F' ] ->
    [# F ⊢ IDefTuple xs ctx ⇑ F' ++ (cons (ITuple Vs, None) nil) ]

| TCallContext: forall F f x ctx F' V VC,
    [# F ⊢ call f x ⇓ (V, CacheValue ((V, Some VC) :: nil)) ] ->
    [# (V, Some VC) :: F ⊢ ctx ⇑ F' ] ->
    [# F ⊢ IDef f x ctx ⇑ F' ++ (cons (V, Some VC) nil) ]

where "[# F ⊢ ctx ⇑ F' ]" := (eval_context F ctx F').

Definition denvironment :=
  list ((value * option cache_value) * dvalue).

Definition list_of_closure_denvironment (vs : list (value * dvalue)) : denvironment :=
  List.map (fun b => ((fst b, None), snd b)) vs.

Definition move_literal (ℓ : literal) (dℓ : dliteral) :=
  match ℓ, dℓ with
    | Nat x, dPos dx =>
      ret (Nat (x + dx))
  end.

(** [move] applies a change to a value. *)
Fixpoint move v dv :=
  match v, dv with
    | v, dIReplace v' =>
      ret v'
    | IPrimitive _, dIPrimitiveNil =>
      ret v
    | ILiteral c, dILiteral dc =>
      nv <- move_literal c dc;
      ret (ILiteral nv)
    | ITuple vs, dITuple dvs =>
      nvs <- move_values vs dvs;
      ret (ITuple nvs)
    | IClosure env t, dIClosure dcenv dt =>
      env' <- move_closure_environment env dcenv;
      ret (IClosure env' t)
    | _, _ =>
      error
  end
with move_closure_environment env denv { struct env } :=
  match env, denv with
    | IVNil, nil =>
      ret IVNil
    | IVCons v env, ((_, dv) :: denv) =>
      v' <- move v dv;
      env' <- move_closure_environment env denv;
      ret (IVCons v' env')
    | _, _ =>
      error
  end
with move_values vs dvs { struct vs } :=
  match vs, dvs with
    | IVNil, nil =>
      ret IVNil
    | IVCons v vs, dv :: dvs =>
      v' <- move v dv;
      vs' <- move_values vs dvs;
      ret (IVCons v' vs')
    | _, _ =>
      error
  end.

Bind Scope ivalue_scope with value.
Open Scope ivalue_scope.

Notation "x ⊕ dx" := (move x dx) (at level 60) : ivalue_scope.

(** Evaluation of functional constants derivatives. *)

Definition recompute_primitive c x dx :=
  x' <- x ⊕ dx;
  y' <- eval_primitive c x';
  ret (dIReplace (fst y'), snd y').

Equations eval_dadd (a : value) (da : dvalue) (cache : cache_value)
: ErrorMonad.t (dvalue * cache_value)
:=
  eval_dadd
    (ITuple  [# ILiteral (Nat x); ILiteral (Nat y) ])
    (dITuple (cons (dILiteral (dPos dx)) (cons (dILiteral (dPos dy)) nil)))
    _
  =>
  ret (dILiteral (dPos (dx + dy)), CacheValue nil);

  eval_dadd (ITuple [# ILiteral (Nat x); ILiteral (Nat y) ]) da _ :=
    recompute_primitive Add (ITuple [# ILiteral (Nat x); ILiteral (Nat y) ]) da;

  eval_dadd _ _ _ := error.

Definition eval_dpush (a : value) (da : dvalue) (cache : cache_value)
: ErrorMonad.t (dvalue * cache_value)
:= recompute_primitive Push a da.

Definition eval_dcurry (a : value) (da : dvalue) (cache : cache_value)
: ErrorMonad.t (dvalue * cache_value)
:= recompute_primitive Curry a da.

Definition eval_dfixrec (a : value) (da : dvalue) (cache : cache_value)
: ErrorMonad.t (dvalue * cache_value)
:= recompute_primitive FixRec a da.

Definition eval_dprimitive c :=
  match c with
    | Add => eval_dadd
    | Push => eval_dpush
    | Curry => eval_dcurry
    | FixRec => eval_dfixrec
  end.

Definition denvironment_of_dclosure_denvironment dFc : denvironment :=
  List.map (fun p => ((fst p, None), snd p)) dFc.

Definition original_environment (dF : denvironment) : environment :=
  List.map fst dF.

Notation "⌊# dF ⌋" := (original_environment dF).

(** From [dF] we can compute updated values. A subtility: we preserve the caches
    stored in [dF]. Therefore, we must make sure that the caches in [dF] are the
    new caches, i.e. caches corresponding to the evaluation under the modified
    environment. *)
Definition modified_binding (b : (value * option cache_value * dvalue)) :=
  let V := fst (fst b) in
  let dV := snd b in
  V' <- V ⊕ dV;
  ret (V', snd (fst b)).

Definition modified_environment (dF : denvironment) : ErrorMonad.t environment :=
  ErrorMonad.list_map modified_binding dF.

Notation "⌈# dF ⌉" := (modified_environment dF).

Inductive eval_cache_update: denvironment -> cache_update -> cache_value -> Prop :=
| TEmptyCacheUpdate:
    forall dF,
    eval_cache_update dF nil (CacheValue nil)

| TCachedVarUpdate:
    forall dF dC x V dV VC Cx VCx V',
      (**

          If (x : ((V, VCx), dV)) ∈ dF, during evaluation of a change term,
          [V] is the original value of "x", [dV] is the change computed by the
          derivative of f if "x = f y" and VCx is the updated cache for "f y".

       *)
      lookup dF x = Some ((V, VCx), dV) ->
      eval_cache_update dF dC (CacheValue VC) ->
      V ⊕ dV = Some V' ->
      (* XXX Sounds like Cx is redundant but kept for consistency between cache and cache_update. *)
      eval_cache_update dF ((x, Cx) :: dC) (CacheValue ((V', VCx) :: VC)).

(**

    Our Coq definition of the evaluation of change terms slighly
    differs from the judgment defined in the paper, Figure 8.

    Indeed, the judgment on paper has following form:

#$$
    dF \vdash dM \Downarrow (dV, V_c)
$$#

    but \(dF\) enjoys an implicit invariant: it starts with the original
    cached values of the computation.

    In Coq, we make this invariant explicit by considering a judgment
    of the form:

#$$
    F, dF \vdash dM \Downarrow (dV, V_c)
$$#

    where \(F\) is an environment containing the original cached values. This
    environment is "consumed" along the computation: each time a value definition is
    updated by the change term, it is moved from \(F\) to \(dF\).

*)

Inductive deval
: denvironment -> environment -> dterm -> (dvalue * cache_value) -> Prop :=
| TDResult :
    forall dF Fo x dC dVx Vx VCx VC,
      lookup dF x = Some ((Vx, VCx), dVx) ->
      eval_cache_update dF dC VC ->
      deval dF Fo (dIResult (d x) dC) (dVx, VC)

| TDTuple :
    forall dF xs Vs Fo dM dV VCdVs,
      lookups dF xs = Some VCdVs ->
      let VCs := List.map fst VCdVs in
      let dVs := List.map snd VCdVs in
      Vs = values_of_list (List.map fst VCs) ->
      let dF' := bind dF (ITuple Vs, None, dITuple dVs) in
      deval dF' Fo dM dV ->
      deval dF ((ITuple Vs, None) :: Fo) (dIDefTuple (List.map d xs) dM) dV

| TDReplaceCall:
    forall dF f Vf VCf Vf' F' x V' VC' Fo dM dV V VC,
      lookup dF f = Some ((Vf, VCf), dIReplace Vf') ->
      ⌈# dF ⌉ = Some F' ->
      eval F' (call f x) (V', CacheValue ((V', Some VC') :: nil)) ->
      deval (bind dF ((V, Some VC'), dIReplace V')) Fo dM dV ->
      deval dF ((V, Some VC) :: Fo) (dIDef f x dM) dV

| TDPrimitiveNil :
    forall dF f p VCp x Vx VCx dVx Fo dM V dV VC VC' dV',
      lookup dF f = Some ((IPrimitive p, VCp), dIPrimitiveNil) ->
      lookup dF x = Some ((Vx, VCx), dVx) ->
      eval_dprimitive p Vx dVx VC = Some (dV', VC') ->
      deval (bind dF ((V, Some VC'), dV')) Fo dM dV ->
      deval dF ((V, Some VC) :: Fo) (dIDef f x dM) dV

| TDClosureChange:
    forall dF f Ff Mf VCf x Vx VCx dVx dFf Fo' dMf dV' VC' V dM dV Fo,
      lookup dF f = Some ((IClosure Ff Mf, VCf), dIClosure dFf dMf) ->
      lookup dF x = Some ((Vx, VCx), dVx) ->
      deval (bind (list_of_closure_denvironment dFf) ((Vx, None), dVx)) Fo' dMf (dV', VC') ->
      deval (bind dF ((V, Some VC'), dV')) Fo dM dV ->
      deval dF ((V, Some (CacheValue Fo')) :: Fo) (dIDef f x dM) dV.

Notation "[[# Fo , dF ⊢ dM ⇓ dV ]]" := (deval dF Fo dM dV).
