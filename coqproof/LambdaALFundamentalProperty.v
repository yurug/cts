Require Import ErrorMonad.
Require Import Misc.
Require Import Environment.
Require Import Omega.
Require Import LibTactics.
Require Import List.
Import ListNotations.

Require Import LambdaAL.
Require Import LambdaALValues.
Require Import LambdaALOperationalSemantics.
Require Import LambdaALOperationalSemanticsPrimitives.
Require Import LambdaALOperationalSemanticsProofs.
Require Import LambdaALDerive.
Require Import LambdaALValidity.


Lemma related_primitive_calls:
  forall {env denv env' k f x vx vx' vf vf' v v'},
    k >= 1 ->
    drel_env k env denv env' ->
    lookup env x = Some vx ->
    lookup env' x = Some vx' ->
    lookup env f = Some (Primitive vf) ->
    lookup env' f = Some (Primitive vf') ->
    eval_primitive vf vx = Some v ->
    eval_primitive vf' vx' = Some v' ->
    exists dv dvx dvf,
    drel_value k v dv v' /\
    lookup denv f = Some (Primitive vf, dvf)
    /\ lookup denv x = Some (vx, dvx) /\ (
      (dvf = dPrimitiveNil /\ eval_dprimitive vf vx dvx = Some dv)
      \/
      (dvf = dReplace (Primitive vf') /\ dv = dReplace v')
    ).
Proof.
  intros * Hk. intros.
  destruct (drel_env_lookup H H2 H3) as [dv Hdv].
  destruct (drel_env_lookup H H0 H1) as [dvx Hdvx].
  intuition.
  rewrite unfold_drel_value in H7. unfold drel_value_F in H7.
  case_eq dv; intros * Heqdv; rewrite Heqdv in H7; try intuition.
  - assert (vf = vf'). congruence. subst.
    destruct (sound_dprimitive vf' _ _ _ _ _ _ Hk H9 H4 H5).
    eexists x0, dvx, dPrimitiveNil. intuition.
  - eexists (dReplace v'), dvx, (dReplace (Primitive vf')); intuition.
    + unfold_drel_value. destruct v; auto.
    + subst. assumption.
Qed.

Lemma drel_env_bind_rel_value:
  forall {k env denv env' v v' dv},
    drel_env k env denv env' ->
    drel_value k v dv v' ->
    drel_env k (bind env v) (bind denv (v, dv)) (bind env' v').
Proof.
  intros.
  constructor; auto.
Qed.

Definition congruence_hypothesis t :=
  forall (env : environment) (denv : denvironment) (env' : environment) (k : nat),
    drel_env k env denv env' -> drel_term k env denv env' t (derive t) t.

Lemma related_calls:
  forall {env denv env' k f x t} (Hrec: congruence_hypothesis t),
    drel_env k env denv env' ->
    drel_term k env denv env' (Def f x t) (dDef f x (derive t)) (Def f x t).
Proof.
  intros *.
  rewrite unfold_drel_term. unfold drel_term_F; simpl.
  intros Hrec Henv * Hk * Heval1 * Heval2.
  lets Horig : @original_env_of_drel_env Henv. subst.
  assert (Hk2: 0 < k) by omega.
  lets Hmod : @modified_env_of_drel_env Hk2 Henv.
  inversion Heval1; inversion Heval2; subst; clear Heval1; clear Heval2; simpl in * |- *; easy.

  - assert (HkO: 0 < k) by omega.
    destruct (related_primitive_calls HkO Henv H5 H13 H2 H12 H7 H15).
    destruct H. destruct H.
    destruct H. destruct H0. destruct H1.
    assert (drel_env (k - S O) (bind ⌊ denv ⌋ v'0) (bind denv (v'0, x0)) (bind env' v'1)).
    apply drel_env_bind_rel_value. eapply (drel_env_antimonotonic _ _ Henv).
    apply (drel_value_antimonotonic k). omega. auto.
    lets Hrel : Hrec H4.
    rewrite unfold_drel_term in * |- *. unfold drel_term_F in * |- *.
    assert (toI (i := Steps) n < k - 1) as Hkk. simpl. simpl in Hk. omega.
    edestruct (Hrel _ Hkk _ H8 _ H17).
    exists x3.
    replace (k - S n) with (k - 1 - n).
    simpl in * |- *. split. intuition.
    destruct H3; destruct H3.
    * subst. eapply (SPrimitiveNil NoSteps); easy.
    * subst. eapply (SDReplaceCall NoSteps); easy.
      use (SPrimitiveCall NoSteps). use (SVar NoSteps).
      use (SPrimitiveCall NoSteps). use (SVar NoSteps).
    * intuition.

  - destruct (drel_env_lookup Henv H2 H12).
    destruct (drel_env_lookup Henv H5 H13).
    intuition.
    destruct x0; rewrite unfold_drel_value in H3; simpl in H3; try intuition; try congruence.
    inversion H3. subst.
    intuition; easy.
    assert (drel_env (k - S O) (bind ⌊ denv ⌋ v'0) (bind denv (v'0, dReplace vy)) (bind env' vy)).
    apply drel_env_bind_rel_value. eapply (drel_env_antimonotonic _ _ Henv).
    use drel_value_replace.
    generalize (Hrec _ _ _ _ H0). intro Hrel.
    rewrite unfold_drel_term in * |- *. unfold drel_term_F in * |- *.
    assert (toI (i := Steps) n < k - 1) as Hkk. simpl. simpl in Hk. omega.
    edestruct (Hrel _ Hkk _ H8 _ H17).
    exists x0; easy.
    replace (k - S n) with (k - 1 - n).
    easy. omega.
    use (SDReplaceCall NoSteps).
    use (SPrimitiveCall NoSteps). use SVar.
    use (SClosureCall NoSteps). use SVar.

  - destruct (drel_env_lookup Henv H2 H12).
    destruct (drel_env_lookup Henv H5 H13).
    intuition.
    destruct x0; rewrite unfold_drel_value in H3; simpl in H3;
      unfold closure in * |-; try intuition; try congruence.
    assert (drel_env (k - S O) (bind ⌊ denv ⌋ vy) (bind denv (vy, dReplace v'0)) (bind env' v'0)).
    apply drel_env_bind_rel_value. eapply (drel_env_antimonotonic _ _ Henv).
    apply (drel_value_antimonotonic k). simpl in Hk. omega. auto.
    use drel_value_replace.
    generalize (Hrec _ _ _ _ H0). intro Hrel.
    rewrite unfold_drel_term in * |- *. unfold drel_term_F in * |- *.
    assert (toI (i := Steps) m < k - 1) as Hkk. simpl. simpl in Hk. omega.
    edestruct (Hrel _ Hkk _ H8 _ H17).
    intuition.
    exists x0.
    split.
    apply drel_value_antimonotonic with (n := (k - 1 - m)).
    replace (k - 1 - m) with (k - (S m)). simpl in Hkk.
    assert (S (n + m) > S m).
    replace (S (n + m)) with (n + S m).
    assert (0 < n). eapply at_least_one_step; eauto.
    all: try omega.
    easy. subst.
    use (SDReplaceCall NoSteps).
    use (SClosureCall NoSteps).
    use complete_eval. use SVar.
    use (SPrimitiveCall NoSteps). use SVar.

  - destruct (drel_env_lookup Henv H2 H12).
    destruct (drel_env_lookup Henv H5 H13).
    intuition.
    destruct x0; rewrite unfold_drel_value in H3; simpl in H3; try intuition; try congruence.

    (* 2 subcases because there are three possible changes to move
      from a closure to another. *)

    * (* dClosure. *)
      assert (0 < m). eapply at_least_one_step; eauto.
      assert (k - 1 < k) as Hn. omega.
      assert (drel_value (k - 1) vx x1 vx0) as Hvx. eapply drel_value_antimonotonic with k; eauto.
      destruct (H3 _ Hn).
      destruct H9. destruct H10. destruct H11. destruct H14. subst.
      generalize (H16 _ _ _ Hvx). intro Hbody.
      rewrite unfold_drel_term in Hbody.
      unfold drel_term_F in Hbody.
      repeat (erewrite list_of_values_of_values_of_list in * |-).
      assert (n < k - 1) as Hsn. omega.
      destruct (Hbody _ Hsn _ H7 _ H15).
      destruct H9. destruct H10.
      assert (drel_env (k - 1 - n) (bind ⌊ denv ⌋ vy) (bind denv (vy, x0)) (bind env' vy0)).
      apply drel_env_bind_rel_value. eapply (drel_env_antimonotonic _ _ Henv).
      destruct H11. auto.
      generalize (Hrec _ _ _ _ H9).
      intro Ht.
      rewrite unfold_drel_term in Ht. unfold drel_term_F in Ht.
      assert (m < k - 1 - n) as Hm. omega.
      destruct (Ht _ Hm _ H8 _ H17).
      intuition.
      exists x2.
      intuition.
      replace (k - 1 - n - m) with (k - (S (n + m))) in H11. auto.
      clear Hn Hsn. 
      omega.
      use (SDefClosure NoSteps).
      rewrite underive_derive. rewrite H1. unfold closure, dclosure.
      rewrite closure_denvironment_of_list_list_of_closure_denvironment.
      repeat f_equal.
      rewrite underive_derive.
      eapply complete_eval; eauto.

    * (* dReplace. *)
      assert (drel_env (k - S O) (bind ⌊ denv ⌋ vy) (bind denv (vy, dReplace vy0)) (bind env' vy0)).
      apply drel_env_bind_rel_value. eapply (drel_env_antimonotonic _ _ Henv); eauto.
      use drel_value_replace.
      generalize (Hrec _ _ _ _ H0). intro Hrel.
      rewrite unfold_drel_term in Hrel. unfold drel_term_F in Hrel.
      assert (m < k - 1) as Hkk. simpl. omega.
      destruct (Hrel _ Hkk  _ H8 _ H17). destruct H6. exists x0.
      intuition.
      eapply (drel_value_antimonotonic _ _ _ H6); eauto.
      subst.
      use (SDReplaceCall NoSteps).
      use (SClosureCall NoSteps). use complete_eval. use SVar.
      use (SClosureCall NoSteps). use complete_eval. use SVar.

      Unshelve. all:(try omega || exact 0).
      assert (0 < m /\ 0 < n); intuition; eapply at_least_one_step; eauto.
Qed.

Lemma related_tuples:
  forall {env denv env' k xs t} (Hrec: congruence_hypothesis t) ,
    drel_env k env denv env' ->
    drel_term k env denv env' (DefTuple xs t) (dDefTuple (List.map d xs) (derive t)) (DefTuple xs t).
Proof.
  intros *.
  rewrite unfold_drel_term. unfold drel_term_F; simpl.
  intros Hrec Henv * Hk * Heval1 * Heval2.
  inversion Heval1; subst. clear Heval1.
  inversion Heval2; subst. clear Heval2.
  simpl in * |- *.
  assert (Hk0: 0 < k). omega.
  destruct (drel_env_dlookups _ _ _ _ Hk0 Henv H3 H1).  destruct H.
  assert (drel_env (k - S O)
                   (bind env (Tuple (values_of_list vs)))
                   (bind denv (Tuple (values_of_list vs), dTuple (ldvalues_of_list (List.map snd x))))
                   (bind env' (Tuple (values_of_list vs0)))).
  apply drel_env_bind_rel_value. eapply (drel_env_antimonotonic _ _ Henv). intuition.
  apply (drel_value_antimonotonic k). simpl in Hk. omega. auto.
  generalize (Hrec _ _ _ _ H2). intro Hrel.
  rewrite unfold_drel_term in * |- *. unfold drel_term_F in * |- *.
  assert (toI (i := Steps) n < k - 1) as Hkk. simpl. simpl in Hk. omega.
  edestruct (Hrel _ Hkk _ H5 _ H4).
  exists x0.
  intuition.
  simpl in * |- *.
  replace (k - S n) with (k - 1 - n).
  exact H0. omega.
  use (SDTuple NoSteps).
  subst.
  unfold tuple, dtuple.
  auto.
  Unshelve.
  omega.
  Unshelve. exact 0.
Qed.

Lemma fundamental_lemma:
  forall t env denv env' k,
    drel_env k env denv env' ->
    drel_term k env denv env' t (derive t) t.
Proof.
  induction t; intros; simpl in * |- *.
  - apply related_lookups; eauto.
  - apply (related_calls IHt H (f := v) (x := v0)).
  - apply (related_tuples IHt H (xs := l)).
Qed.