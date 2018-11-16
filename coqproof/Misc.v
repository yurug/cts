(** General purpose definitions, lemmas and tactics. *)

Require Import Omega.

Lemma lt_comp :
  forall {n j1 j2 k}, j1 + j1 + j2 <= k -> k < n -> k - j1 - j1 - j2 < n.
Proof.
  intros. omega.
Qed.

Lemma lt_lt:
  forall {n j k}, j <= k -> k < n -> j  < n.
Proof.
  intros. omega.
Qed.

Lemma minus_commute:
  forall a b c,
    c <= a - b ->
    b <= a - c ->
    a - b - c = a - c - b.
Proof.
  intros. omega.
Qed.

Lemma minus_factorize:
  forall a b c,
    b + c <= a ->
    a - b - c = a - (b + c).
Proof.
  intros. omega.
Qed.

Lemma uniq_commute:
  forall A,
  forall (P : A -> nat -> Prop),
    (forall x y z z', P x z -> P y z' -> x = y) ->
    (forall z, exists y, P y z) ->
    (exists y, forall z, P y z).
Proof.
  intros.
  destruct (H0 O).
  exists x.
  intro z.
  destruct (H0 z).
  rewrite (H x x0 0 z H1 H2); auto.
Qed.

Require Import List.

Lemma reverse_map:
  forall A B (f : A -> B) (Hfinj : forall x y, f x = f y -> x = y),
  forall l1 l2, map f l1 = map f l2 -> l1 = l2.
Proof.
  induction l1; destruct l2; simpl in * |- *; try congruence; intros.
  assert (a = a0). apply Hfinj. congruence.
  assert (l1 = l2). apply IHl1; congruence.
  subst. auto.
Qed.

Theorem map_map:
  forall A B C (f : A -> B) (g : C -> A) xs, map f (map g xs) = map (fun x => f (g x)) xs.
Proof.
  induction xs; simpl; intros; auto. rewrite IHxs. auto.
Qed.

Lemma map_equiv:
  forall A B l (f : A -> B) (g : A -> B), (forall x, f x = g x) -> List.map f l = List.map g l.
Proof.
  induction l; simpl; eauto. intros.
  rewrite H. erewrite IHl. eauto. auto.
Qed.

Lemma map_id:
  forall A (l : list A), map (fun x => x) l = l.
Proof.
  induction l; simpl; eauto.
  rewrite IHl. auto.
Qed.

Lemma map_equiv_length:
  forall {A B C l l'} {f : A -> B} {g : C -> B}, 
    List.map f l = List.map g l' -> 
    List.length l = List.length l'.
Proof.
  induction l; intros * Heq; destruct l'; simpl in * |- *; inversion Heq; try congruence; eauto.
Qed.

Lemma eq_dec_nat_refl:
  forall x, PeanoNat.Nat.eq_dec x x = left (refl_equal x).
Proof.
  induction x; simpl; auto. rewrite IHx. auto.
Qed.

Fixpoint drop {A} n (l : list A) :=
  match n with
  | O => l
  | S k => match l with
          | nil => nil
          | x :: xs => drop k xs
          end
  end.

Fixpoint take {A} n (l : list A) :=
  match n with
    | O => nil
    | S k => match l with
              | nil => nil
              | x :: xs => x :: take k xs
            end
  end.

Lemma drop_app: forall {A} {l : list A} {l'},
    drop (length l) (l ++ l') = l'.
Proof.
  induction l; simpl; eauto.
Qed.

Lemma drop_nil: forall {A} n,
    drop n (@nil A) = nil.
Proof.
  induction n; simpl; eauto.
Qed.

Lemma drop_inversion: forall {A x} {l l' : list A} {n},
    drop n l = x :: l' ->
    n < length l.
Proof.
  induction l; simpl; intros; eauto.
  rewrite drop_nil in H. congruence.
  destruct n. omega.
  simpl in H. generalize (IHl _ _ H). omega.
Qed.

Lemma take_drop: forall {A n} {l : list A},
    take n l ++ drop n l = l.
Proof.
  induction n; simpl; eauto.
  intros. destruct l.
  simpl. eauto.
  rewrite <- app_comm_cons.
  rewrite IHn. eauto.
Qed.

Lemma drop_decompose:
  forall {A} {x : A} {l l' n},
  drop n l = x :: l' ->
  exists p, l = p ++ x :: l' /\ length p = n.
Proof.
  induction l; simpl; intros; eauto.
  rewrite drop_nil in H. congruence.
  destruct n. simpl in H.
  inversion H. subst.
  exists nil. intuition.
  simpl in H. destruct (IHl _ _ H). intuition. subst.
  exists (a :: x0).
  intuition.
Qed.

Lemma drop_cons: forall {A} x {l l' : list A} n,
    drop n l = x :: l' ->
    drop (S n) l = l'.
Proof.
  intros. destruct (drop_decompose H).
  intuition. subst.
  replace (x :: l') with (cons x nil ++ l').
  replace (S (length x0)) with (length (x0 ++ (x :: nil))).
  rewrite app_assoc.
  rewrite drop_app; eauto.
  rewrite app_length. simpl. omega.
  eauto.
Qed.

Lemma app_comm_cons_2:
  forall {A} (l : list A) l' x,
    l ++ x :: l' = (l ++ x :: nil) ++ l'.
Proof.
  induction l; simpl; intros; eauto.
  rewrite IHl. eauto.
Qed.

Lemma rev_injective:
  forall {A} (l l' : list A), rev l = rev l' -> l = l'.
Proof.
  intros.
  assert (length (rev l) = length (rev l')). rewrite H. auto.
  generalize H H0. generalize l'. clear H H0 l'. 
  induction l; intros; destruct l'; simpl in * |- *; intros; try rewrite app_length in H0; 
    try (easy; simpl in * |- *; omega).
  simpl in H0. omega.
  simpl in H0. omega.
  destruct (app_inj_tail _ _ _ _ H). subst. rewrite (IHl _ H1); eauto.
  rewrite H1. auto.
Qed.

Lemma rev_nil:
  forall {A} (l : list A), rev l = nil -> l = nil.
Proof.
  intros * Hrev.
  replace (@nil A) with (@rev A (@nil A)) in Hrev; eauto.
  apply rev_injective; eauto.
Qed.

Lemma tl_app:
  forall {A} (l : list A) x l',
    tl ((l ++ x :: nil) ++ l') = tl (l ++ x :: nil) ++ l'.
Proof.
  destruct l; simpl; eauto; intros.
Qed.

Lemma length_tl:
  forall {A} (l : list A) x,
  length (tl (l ++ x :: nil)) = length l.
Proof.
  destruct l; simpl; eauto; intros.
  rewrite app_length. simpl. omega.
Qed.

Ltac easy := (intuition; simpl in * |- *; try congruence; eauto).

Ltac easy_assert H := (assert H by easy).

Ltac easy_eqs H := (match H with 
                      | ?X = ?Y /\ ?H' => easy_assert (X = Y); subst; easy_eqs H'
                      | ?H' => easy_assert H'; subst
                    end).

Ltac inverse H := (inversion H; subst).

Ltac use H := (eapply H; easy).

Ltac break H := (destruct H; intuition).

Ltac remark_by H := (generalize H; intro). (* FIXME: Give a name. *)

(* PG: Try case-splitting to simplify and invert hypotheses. *)

(* https://stackoverflow.com/a/28458457/53974 gives: *)
(* Ltac match_case_analysis := *)
(*   repeat *)
(*     match goal with *)
(*     | H : match ?x with _ => _ end = _ |- _ => *)
(*       destruct x; try solve [inversion H] *)
(*     end. *)

Ltac match_case_analysis :=
  repeat
    match goal with
    | H : context f [match ?x with _ => _ end] |- _ =>
      destruct x; try solve [inverse H]
    end.

Ltac match_case_analysis_eauto :=
  repeat
    match goal with
    | H : context f [match ?x with _ => _ end] |- _ =>
      destruct x; try solve [inverse H; eauto]
    end.

(* Try automatic inversion on hypotheses matching Some to Some, in a few variants.
 * I use these variants depending on the scenario; they are needed because no
 * inversion tactic is too robust.
 *)
Ltac inverse_some :=
  (* Below, using inversion instead of inversion_clear reduces the
  danger of destroying information and producing false goals, but
  means that repeat inverse_some will loop! *)
  match goal with
  | H : Some ?x = Some ?y |- _ => inversion_clear H; subst
  end.
Ltac inverts_some :=
  match goal with
  | H : Some ?x = Some ?y |- _ => inversion H; subst; clear H
  end.
Ltac inversions_some :=
  match goal with
  | H : Some ?x = Some ?y |- _ => inversion H; subst
  end.

(* From Chlipala's tactics. *)
Ltac inject H := injection H; clear H; intros; try subst.

(* More reliable (?) variant of inversions_some. *)
Ltac injections_some :=
  match goal with
    [H : Some ?a = Some ?b |- _ ] => inject H
  end.

(* Much cheaper than intuition, often as good, but produces different hypotheses names! *)
Ltac splitHyps :=
  repeat match goal with
         | H: exists _, _ |- _ => destruct H
         | H: _ /\  _ |- _ => destruct H
         end.

(* Split in the goal. *)
Ltac split_conj :=
  repeat
    match goal with
    | |- _ /\ _ => split
    end.