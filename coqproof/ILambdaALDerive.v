Require Import List.
Require Import Index.
Require Import LambdaAL.
Require Import LambdaALDerive.
Require Import LambdaALValues.
Require Import LambdaALOperationalSemantics.
Require Import ILambdaAL.
Require Import ILambdaALValues.
Require Import ILambdaALOperationalSemantics.

Fixpoint depth_of_term t :=
  match t with
    | Var x => 0
    | DefTuple xs t => S (depth_of_term t)
    | Def f x t => S (depth_of_term t)
  end.

Definition shift n v :=
  match v with Idx k => Idx (n + k) end.

(** [cache_of_term t] returns the associated cache of [t]. *)
Fixpoint cache_of_term (t : LambdaAL.term) : ILambdaAL.cache :=
  match t with
  | Var x =>
    nil
  | DefTuple xs t =>
    (Idx (depth_of_term t), None) :: cache_of_term t
  | Def f x t =>
    let n := depth_of_term t in
    let f := shift n f in
    let x := shift n x in
    (Idx n, Some (Cache (Idx n) f x)) :: cache_of_term t
  end.

Definition cache_update_of_term t : ILambdaAL.cache_update :=
  cache_of_term t.

Fixpoint cts_term_aux global_t t : term :=
  match t with
  | Var x =>
    (IResult x (cache_of_term global_t))
  | Def f x t =>
    IDef f x (cts_term_aux global_t t)
  | DefTuple xs t =>
    IDefTuple xs (cts_term_aux global_t t)
  end.

Definition cts_term t :=
  cts_term_aux t t.

Fixpoint uncts_term t :=
  match t with
  | IResult x _ => Var x
  | IDef f x t => Def f x (uncts_term t)
  | IDefTuple xs t => DefTuple xs (uncts_term t)
  end.

Fixpoint cts_derive_term global_t t : dterm :=
  match t with
  | Var x =>
    dIResult (d x) (cache_update_of_term global_t)
  | Def f x t =>
    dIDef f x (cts_derive_term global_t t)
  | DefTuple xs t =>
    dIDefTuple (List.map d xs) (cts_derive_term global_t t)
  end.

Definition cts_derive (t : LambdaAL.term) :=
  cts_derive_term t t.

Fixpoint cts_value (v : LambdaALValues.value) : ILambdaALValues.value :=
  match v with
  | Closure env t =>
    IClosure (cts_values env) (cts_term t)
  | Tuple vs =>
    ITuple (cts_values vs)
  | Literal l =>
    ILiteral l
  | Primitive p =>
    IPrimitive p
  end
with cts_values (vs : LambdaALValues.values) : ILambdaALValues.values :=
  match vs with
  | VNil => IVNil
  | VCons v vs => IVCons (cts_value v) (cts_values vs)
  end.

Fixpoint uncts_value v :=
  match v with
    | IClosure env t =>
      Closure (uncts_values env) (uncts_term t)
    | ITuple vs =>
      Tuple (uncts_values vs)
    | ILiteral l =>
      Literal l
    | IPrimitive p =>
      Primitive p
  end
with uncts_values vs :=
    match vs with
    | IVNil => VNil
    | IVCons v vs => VCons (uncts_value v) (uncts_values vs)
    end.

Definition cts_dterm (dt : LambdaAL.dterm) :=
  cts_derive (LambdaALDerive.underive dt).

Fixpoint cts_dvalue (dv : LambdaALValues.dvalue) :=
  match dv with
  | dClosure denv dt =>
    dIClosure (cts_closure_denvironment denv) (cts_dterm dt)
  | dTuple dvs =>
    dITuple (cts_dvalues dvs)
  | dLiteral dl =>
    dILiteral dl
  | dPrimitiveNil =>
    dIPrimitiveNil
  | dReplace v =>
    dIReplace (cts_value v)
  end
with cts_closure_denvironment denv :=
  match denv with
  | CDNil => nil
  | CDCons v dv denv =>
    (cts_value v, cts_dvalue dv) :: cts_closure_denvironment denv
  end
with cts_dvalues dvs :=
  match dvs with
    | DVNil => nil
    | DVCons dv dvs => (cts_dvalue dv) :: cts_dvalues dvs
end.

Definition cts_binding v :=
  (cts_value v, None (A := cache_value)).

Definition cts_environment (E : LambdaALOperationalSemantics.environment) : environment :=
  List.map cts_binding E.

Definition cts_dbinding vdv :=
  (cts_value (fst vdv), None (A := cache_value), cts_dvalue (snd vdv)).

Definition cts_denvironment (dE : LambdaALOperationalSemantics.denvironment) : denvironment :=
  List.map cts_dbinding dE.

