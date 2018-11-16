(****************)
(* Error monad. *)
(****************)

Require Import List.

Definition t A := option A.

Definition ret {A : Type} (x : A) := Some x.

Definition mbind {A B : Type} (a : option A) (f : A -> option B) : option B :=
  match a with
    | Some x => f x
    | None => None
  end.

Notation "A >>= F" :=
  (mbind A F)
    (at level 42, left associativity).

Notation "X '<-' A ';' B" :=
  (mbind A (fun X => B))
    (at level 81, A at level 100, B at level 200, right associativity).

Definition error {A} := None (A:=A).

Fixpoint list_map {A B: Type} (f : A -> t B) (l : list A) : t (list B) :=
  match l with
    | nil =>
      ret nil
    | cons x xs =>
      y <- f x;
      ys <- list_map f xs;
      ret (cons y ys)
  end.

Fixpoint list_map2 {A B C: Type} (f : A -> B -> t C) (l : list A) (l' : list B)
: t (list C) :=
  match l, l' with
    | nil, nil =>
      ret nil
    | cons x xs, cons y ys =>
      z <- f x y;
      zs <- list_map2 f xs ys;
      ret (cons z zs)
    | _, _ =>
      error
  end.

Lemma inv_success_mbind:
  forall {A B} {f : A -> t B} {c : t A} {x},
    mbind c f = Some x ->
    exists y, c = Some y.
Proof.
  intros.
  destruct c; simpl in * |-; try congruence.
  exists a. auto.
Qed.

Lemma inv_success_mbind2:
  forall {A B} {f : A -> option B} {c} {x},
    mbind c f = Some x ->
    exists y, c = Some y /\ f y = Some x.
Proof.
  intros * H.
  destruct c; simpl in * |-; try congruence.
  exists a. auto.
Qed.

Lemma inv_error_mbind:
  forall {A B} (c : t A),
    (_ <- c; @error B) = error.
Proof.
  intros.
  destruct c; simpl; auto.
Qed.

Lemma inv_error_mbind2:
  forall {A B} {c : t A} (f : A -> B),
    mbind c (fun x => ret (f x)) = error ->
    c = error.
Proof.
  destruct c; simpl; intros; unfold ret, error in * |- *; try congruence; eauto.
Qed.

Lemma list_map_length:
  forall {A B} (f : A -> t B) l l',
    list_map f l = Some l' ->
    List.length l = List.length l'.
Proof.
  induction l; intros * Hm; destruct l'; simpl in * |- *; inversion Hm; eauto.
  destruct (inv_success_mbind Hm). rewrite H in Hm. simpl in Hm.
  destruct (inv_success_mbind Hm). rewrite H1 in Hm. simpl in Hm.
  inversion Hm.
  destruct (inv_success_mbind Hm). rewrite H in Hm. simpl in Hm.
  destruct (inv_success_mbind Hm). rewrite H1 in Hm. simpl in Hm.
  inversion Hm; subst.
  erewrite IHl; eauto.
Qed. 

Lemma commute_bind:
  forall {A B C} (c1 : t A) (c2 : t B) (f : A -> B -> C),
    (x <- c1; y <- c2; ret (f x y)) =
    (y <- c2; x <- c1; ret (f x y)).
Proof.
  intros.
  destruct c1; destruct c2; simpl; auto.
Qed.

Lemma bind_ret:
  forall {A} (c : t A),
      (x <- c; ret x) = c.
Proof.
  destruct c; simpl; eauto.
Qed.

Lemma assoc_bind:
  forall {A} {c1 : t A} {B} {c2 : t B} {C} {c3 : t C},
    (x <- (y <- c1; c2); c3) = (y <- c1; x <- c2; c3).
Proof.
  intros.
  destruct c1; destruct c2; simpl; auto.
Qed.

Lemma list_map_app:
  forall {A B} (f : A -> t B) (l l': list A),
    list_map f (l ++ l') =
    (x <- list_map f l; y <- list_map f l'; ret (x ++ y)).
Proof.
  induction l; intros; simpl in * |- *; eauto.
  rewrite bind_ret; eauto.
  destruct (f a); simpl. rewrite IHl.
  destruct (list_map f l); destruct (list_map f l'); eauto.
  eauto.
Qed.

Lemma list_map_cons:
  forall {A B} (f : A -> t B) (x : A) (l : list A) bs b,
    list_map f l = Some bs ->
    f x = Some b ->
    list_map f (cons x l) = Some (b :: bs).
Proof.
  simpl. intros.
  rewrite H. rewrite H0. simpl. eauto.
Qed.

Lemma list_map_post_cons:
  forall {A B} (f : A -> t B) (x : A) (l : list A) bs b,
    list_map f l = Some bs ->
    f x = Some b ->
    list_map f (l ++ cons x nil) = Some (bs ++ cons b nil).
Proof.
  simpl. intros.
  rewrite list_map_app. rewrite H. simpl.
  rewrite H0. simpl.
  auto.
Qed.

Ltac simpl_unfold_err :=
  repeat (unfold ret, error in *; simpl in *).

Ltac simpl_unfold_err_mbind :=
  repeat (unfold ret, error, mbind in *; simpl in *).

(* Use inv_success_mbind2 to help inversion. *)
Ltac inv_mbind :=
  match goal with
    H : mbind _ _ = Some _ |- _ =>
    let x := fresh "x" in
    let Ha := fresh "Ha" in
    let Hb := fresh "Hb" in
    apply inv_success_mbind2 in H;
    (* invert, in one go, H into its pieces *)
    inversion H as [x [Ha Hb] ]
  end.

Require Import Misc.

Ltac inv_mbind_some :=
  repeat inv_mbind; repeat injections_some.

Ltac simpl_inv_mbind_some := simpl_unfold_err; inv_mbind_some.
