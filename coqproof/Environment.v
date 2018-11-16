(** * Generic environments *)

Require Import Omega.
Require Import List.
Require Import Misc.
Require Import ErrorMonad.
Require Import Index.
Require Import FunInd.

Definition t A := list A.

Fixpoint lookup {A} (env : t A) x :=
  match env with
    | nil => error
    | v :: env =>
      match x with
        | Idx O => ret v
        | Idx (S x) => lookup env (Idx x)
      end
  end.

Functional Scheme lookup_ind := Induction for lookup Sort Prop.

Lemma map_lookup:
  forall {A B} {env : t A} {f : A -> B},
    forall {x y}, lookup env x = Some y ->
           lookup (List.map f env) x = Some (f y).
Proof.
  induction env; intros * Hlookup; inverse Hlookup; simpl in * |- *; eauto.
  destruct x; destruct n. inverse H0. eauto.
  rewrite (IHenv _ _ _ H0). eauto.
Qed.

Lemma map_lookup_2:
  forall {A B} {env : t A} {f : A -> B},
    forall {x y}, lookup (List.map f env) x = Some y ->
             exists z, lookup env x = Some z /\ y = f z.
Proof.
  induction env; intros * Hlookup; inverse Hlookup; simpl in * |- *; eauto.
  destruct x; destruct n; inverse H0. eauto.
  apply IHenv; eauto.
Qed.

Lemma list_map_lookup:
  forall {A B} {env : t A} {E} {f : A -> ErrorMonad.t B},
    forall {x y},
      list_map f env = Some E ->
      lookup env x = Some y ->
      exists z, lookup E x = Some z /\ f y = Some z.
Proof.
  induction env; intros * Heq Hlookup; inverse Hlookup; simpl in * |- *; eauto.
  destruct (inv_success_mbind Heq). rewrite H in Heq. simpl in Heq.
  destruct (inv_success_mbind Heq). rewrite H1 in Heq. simpl in Heq.
  inverse Heq. simpl.
  destruct x; destruct n. inverse H0.
  eexists. eauto.
  eapply (IHenv _ _ _ _ H1 H0).
Qed.

Lemma list_map_lookup_2:
  forall {A B} {env : t A} {E} {f : A -> ErrorMonad.t B},
    forall {x y},
      list_map f env = Some E ->
      lookup E x = Some y ->
      exists z, lookup env x = Some z /\ f z = Some y.
Proof.
  induction env; intros * Hm Hlookup; inverse Hlookup; simpl in * |- *; eauto.
  inverse Hm. simpl in H0. inverse H0.
  destruct x; destruct n; inverse H0. 
  destruct (inv_success_mbind Hm). rewrite H in Hm. simpl in Hm.
  destruct (inv_success_mbind Hm). rewrite H2 in Hm. simpl in Hm.
  inverse Hm.
  eauto.
  destruct (inv_success_mbind Hm). rewrite H in Hm. simpl in Hm.
  destruct (inv_success_mbind Hm). rewrite H2 in Hm. simpl in Hm.
  inverse Hm.
  simpl in H1 |- *. 
  rewrite H1.
  eapply IHenv; eauto.
Qed.

Fixpoint lookups {A} (env : t A) xs :=
  match xs with
  | nil =>
    ret nil
  | x :: xs =>
    vs <- lookups env xs;
    v <- lookup env x;
    ret (v :: vs)
  end.

Lemma split_lookup:
  forall {A} {E E' : t A} {n v},
    lookup (E ++ E') (Idx n) = Some v ->
    (n < length E /\ lookup E (Idx n) = Some v) 
    \/ ((n >= length E) /\ lookup E' (Idx (n - length E)) = Some v).
Proof.
  induction E; simpl; intros * H; eauto.
  right. intuition. replace (n - 0) with n. eauto. omega.
  destruct n. left. intuition.
  destruct (IHE _ _ _ H). left; intuition.
  right. intuition.
Qed.

Lemma restrict_lookup:
  forall {A} (E E' : t A) n,
    n < length E ->
    lookup (E ++ E') (Idx n) = lookup E (Idx n).
Proof.
  induction E; simpl; intros * H; eauto. omega.
  destruct n; eauto. eapply IHE. omega.
Qed.

Lemma restrict_lookup_2:
  forall {A} (E E' : t A) n,
    n >= length E ->
    lookup (E ++ E') (Idx n) = lookup E' (Idx (n - length E)).
Proof.
  induction E; simpl; intros * H; eauto. replace (n - 0) with n. eauto. omega.
  destruct n; eauto. omega. eapply IHE. omega.
Qed.

Lemma focus_lookup:
  forall {A} (E E' : t A) x y n,
    (n = List.length E 
     /\ lookup (E ++ x :: E') (Idx n) = Some x 
     /\ lookup (E ++ y :: E') (Idx n) = Some y)
    \/ (n <> List.length E 
       /\ lookup (E ++ x :: E') (Idx n) = lookup (E ++ y :: E') (Idx n)).
Proof.
  intros.
  destruct (eq_nat_dec n (List.length E)).
  left. intuition.
  rewrite restrict_lookup_2. subst. simpl. 
  rewrite Nat.sub_diag. eauto. omega.
  rewrite restrict_lookup_2. subst. simpl. 
  rewrite Nat.sub_diag. eauto. omega.
  right. intuition.
  destruct (lt_dec n (List.length E)); eauto.
  rewrite restrict_lookup; eauto.
  rewrite restrict_lookup; eauto.
  assert (n >= length E) by omega.  
  rewrite restrict_lookup_2; eauto.
  rewrite restrict_lookup_2; eauto.
  case_eq (n - length E); intros * Hnl.
  omega.
  simpl. eauto.
Qed.

Lemma invalid_lookup:
  forall {A} (E : t A) n v,
    n >= length E -> lookup E (Idx n) = Some v -> False.
Proof.
  induction E; simpl; unfold error; try congruence; eauto.
  destruct n. intros. omega.
  intros. 
  eapply (IHE n); eauto. omega.
Qed.

Lemma map_lookups:
  forall {A B} {env : t A} (f : A -> B),
    forall {xs ys}, lookups env xs = Some ys ->
           lookups (List.map f env) xs = Some (List.map f ys).
Proof.
  induction xs; intros * Hlookup; simpl in * |- *.
  inverse Hlookup. eauto.
  destruct (inv_success_mbind Hlookup). rewrite H in Hlookup. simpl in Hlookup. 
  destruct (inv_success_mbind Hlookup). rewrite H0 in Hlookup. simpl in Hlookup. 
  inverse Hlookup.
  rewrite (IHxs _ H). rewrite (map_lookup H0). eauto.
Qed.

Definition bind {A} (env : t A) v := v :: env.

Definition postbind {A} (env : t A) v := env ++ cons v nil.

Lemma lookups_length :
  forall {A} (E : t A) xs vs,
    lookups E xs = Some (vs) -> List.length xs = List.length vs.
Proof.
  induction xs; destruct vs; simpl; intros; eauto; try discriminate.
  destruct (inv_success_mbind H). rewrite H0 in H. simpl in H.
  destruct (inv_success_mbind H). rewrite H1 in H. simpl in H. inversion H.

  destruct (inv_success_mbind H). rewrite (IHxs _ H0). f_equal.
  rewrite H0 in H. simpl in H.
  destruct (inv_success_mbind H). rewrite H1 in H. simpl in H. inversion H.
  auto.
Qed.

Lemma lift_lookup:
  forall {A} x (E : t A) y, lookup E x = Some y -> forall v, lookup (bind E v) (lift x) = Some y.
Proof.
  intros. destruct x. simpl. auto.
Qed.

Lemma weaken:
  forall {A} (E : t A) (v : A) P,
    (forall x y, lookup (bind E v) x = Some y -> P y) ->
    (forall x y, lookup E x = Some y -> P y).
Proof.
  induction E; intros.
  - simpl in * |- *. inversion H.
  - assert (lookup (bind (a :: E) v) (lift x) = Some y) by (eapply lift_lookup; easy).
    eapply X; easy.
Qed.

Lemma split_bind:
  forall A n v (env : t A),
    (lookup env (Idx n) = lookup (bind env v) (Idx (S n)))
  \/ (lookup (bind env v) (Idx n) = Some v).
Proof.
  induction env.
  simpl.
  left. auto.
  simpl. destruct n. right. unfold ret. f_equal. auto.
Qed.

(* Implicit precondition: i < length env. *)
Fixpoint split_at {A} i (env : t A) :=
  match i with
  | O =>
    (nil, env)
  | S k =>
    match env with
    | x :: xs =>
      let '(before, after) := split_at k xs in
      (x :: before, after)
    | nil =>
      (nil, nil) (* Absurd if precondition holds. *)
    end
  end.

Lemma lookup_app:
  forall {A} (E : t A) x E', lookup (E ++ x :: E') (Index.Idx (List.length E)) = Some x.
Proof.
  induction E; simpl; unfold ret; unfold error; intros *; eauto.
Qed.

Lemma lookup_app_2:
  forall {A} (E : t A) x E' v, lookup E x = Some v -> lookup (E ++ E') x = Some v.
Proof.
  induction E; simpl; unfold error; unfold ret; intros; easy.
  destruct x; destruct n; eauto.
Qed.

Lemma bind_postbind_nil:
  forall {A} x, @bind A nil x = postbind nil x.
Proof.
  eauto.
Qed.

Lemma bind_postbind:
  forall {A} x y (E : t A), bind (postbind E x) y = postbind (bind E y) x.
Proof.
  induction E; simpl; eauto.
Qed.

Lemma postbind_of_single:
  forall {A} (v : A), cons v nil = postbind nil v.
Proof.
  unfold postbind. eauto.
Qed.
