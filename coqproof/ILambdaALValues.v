(** * The values of \(i\lambda_{AL}\) *)

Require Import List.
Require Import ILambdaAL.
Require Import Constants.
Require Import Index.

Definition literal := Constants.literal.

Definition primitive := Constants.primitive.

Definition dliteral := Constants.dliteral.

Inductive value :=
| IClosure   : values -> term -> value
| ITuple     : values -> value
| ILiteral   : literal -> value
| IPrimitive : primitive -> value
with values :=
| IVNil  : values
| IVCons : value -> values -> values.

Inductive cache_value :=
| CacheValue : list (value * option cache_value) -> cache_value.

Bind Scope ivalues_scope with values.
Open Scope ivalues_scope.
Notation " [# ] " := IVNil (format "[# ]") : ivalues_scope.
Notation " [# x ; y ; .. ; z ] " := (IVCons x (IVCons y .. (IVCons z IVNil) ..))
                                   : ivalues_scope.
Fixpoint values_of_list vs :=
  match vs with
    | nil => IVNil
    | x :: xs => IVCons x (values_of_list xs)
  end.

Fixpoint list_of_values vs :=
  match vs with
    | IVNil => nil
    | IVCons x xs => x :: list_of_values xs
  end.

Inductive dvalue :=
| dIClosure : list (value * dvalue) -> dterm -> dvalue
| dITuple : list dvalue -> dvalue
| dILiteral : dliteral -> dvalue
| dIPrimitiveNil : dvalue
| dIReplace : value -> dvalue.
