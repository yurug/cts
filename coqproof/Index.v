Inductive var := Idx : nat -> var.

Definition lift x := match x with Idx n => Idx (S n) end.
