(** **  Values *)

Require Import List.
Require Import Omega.
Require Import LambdaAL.
Require Import Constants.
Require Import ErrorMonad.

(** *** Base values *)

(** **** Grammar for base values *)

(** The type for base closed values. (Figure 1 of paper.)

    - (Closure) "[Closure E t]" is "[E[λx. t]]".
    - (Tuple)   "[Tuple [v₁; ...; vₙ]]" is "(v₁; ...; vₙ)".
    - (Literal) "[Literal l]" is "[ℓ]".
    - (Primitive) "[Primitive p]" is "[p]".
*)

(** As usual in Coq, we cannot use [list value] to represent list of
    values because the definition of [value] requires a list of values
    and Coq is not able to automatically generate the proper induction
    scheme for such definitions.
*)
Inductive value :=
| Closure  : values -> term -> value
| Tuple    : values -> value
| Literal : literal -> value
| Primitive: primitive -> value

with values :=
| VNil : values
| VCons : value -> values -> values.

(** **** Induction schemes *)

(** As said above, in Coq, induction schemes are better suited when
    manually generated. *)

Scheme value_mut := Induction for value Sort Prop
with values_mut := Induction for values Sort Prop.

Combined Scheme value_mutind from value_mut, values_mut.

(** *** Notations *)

Bind Scope values_scope with values.
Open Scope values_scope.
Notation " [@ ] " := VNil (format "[@ ]") : values_scope.
Notation " [@ x ] " := (cons x nil) : values_scope.
Notation " [@ x ; y ; .. ; z ] " := (VCons x (VCons y .. (VCons z VNil) ..))
                                    : values_scope.
Fixpoint values_of_list vs :=
  match vs with
    | nil => VNil
    | x :: xs => VCons x (values_of_list xs)
  end.

Fixpoint list_of_values vs :=
  match vs with
    | VNil => nil
    | VCons x xs => x :: list_of_values xs
  end.

Definition tuple vs :=
  Tuple (values_of_list vs).

Definition closure E t :=
  Closure (values_of_list E) t.

(** **** Functions over base values *)

(** Universal quantification over a list of values *)
Fixpoint values_forall2_from (p  : nat -> value -> value -> Prop) n vs vs' : Prop :=
  match vs with
  | VNil =>
    match vs' with
      | VNil => True
      | _ => False
    end
  | VCons x xs =>
    match vs' with
      | VCons x' xs' =>
        p n x x' /\ values_forall2_from p (S n) xs xs'
      | _ =>
        False
    end
  end.

Definition values_forall2 p := values_forall2_from p O.

(** *** Change values *)

(** **** Grammar for change values. *)

(** The type for closed change values. (Figure 1 of the paper.)

     - (Closure) "[dClosure dE dt]" is "[λx dx. dt]".
     - (Tuple) "[dTuple [dv₁; ...; dvₙ]]" is "[(dv₁; ...; dvₙ)]".
     - (Literal) "[dLiteral dl]" is "[dℓ]".
     - (Replace) "[dReplace v]" is "[!v]".

*)

(**

    For the same reason as for base values, we define
    [closure_denvironment] and [ldvalues] to represent, respectively,
    [dE] and list of change values.

*)
Inductive dvalue :=
| dClosure : closure_denvironment -> dterm -> dvalue
| dTuple : ldvalues -> dvalue
| dLiteral : dliteral -> dvalue
| dPrimitiveNil : dvalue
| dReplace : value -> dvalue
with closure_denvironment :=
| CDNil : closure_denvironment
| CDCons : value -> dvalue -> closure_denvironment -> closure_denvironment
with ldvalues :=
| DVNil : ldvalues
| DVCons : dvalue -> ldvalues -> ldvalues.

Notation " [@# ] " := DVNil (format "[@# ]") : values_scope.
Notation " [@# x ] " := (DVCons x DVNil) : values_scope.
Notation " [@# x ; y ; .. ; z ] " := (DVCons x (DVCons y .. (DVCons z DVNil) ..))
                                    : values_scope.

(** **** Basic functions over change values *)

Fixpoint ldvalues_of_list dvs :=
  match dvs with
  | nil => DVNil
  | dv :: dvs => DVCons dv (ldvalues_of_list dvs)
  end.

Fixpoint list_of_ldvalues dvs :=
  match dvs with
  | DVNil => nil
  | DVCons dv dvs => dv :: (list_of_ldvalues dvs)
  end.

Fixpoint closure_denvironment_of_list l :=
  match l with
  | nil => CDNil
  | (v, dv) :: l => CDCons v dv (closure_denvironment_of_list l)
  end.

Fixpoint list_of_closure_denvironment dE :=
  match dE with
  | CDNil => nil
  | CDCons v dv dE => (v, dv) :: list_of_closure_denvironment dE
  end.

Definition dtuple vs :=
  dTuple (ldvalues_of_list vs).

Definition dclosure dE dt :=
  dClosure (closure_denvironment_of_list dE) dt.
