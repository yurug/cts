(** * Constants *)

(** The entire development should be parameterized with respect to the
    builtin constants of the language but to avoid too much boilerplate,
    we instead give concrete definitions for these constants and we make
    sure that we reason about them generically. *)

(** ** Base constants *)

(** We distinguish two kinds of constants: *)

(** - [literal]s are first-order values. They are passive. They cannot
    be applied. They are values. *)
Inductive literal :=
| Nat : nat -> literal.

(** - [primitive]s are higher-order values. They have a dynamic behavior
    when they are applied. They are not values. *)
Inductive primitive :=
| Add : primitive
| Push : primitive
| Curry : primitive
| FixRec : primitive.

(** ** Change constants *)

(** A change on a literal can be described by a change literal. *)
Inductive dliteral :=
| dPos : nat -> dliteral.

(** Primitives can only be replaced by other functions or other
    primitives using a generic replace change (see
    [LambdaALOperationalSemantics.dvalue]). Therefore, there is no
    specific change construction for primitives here. *)

