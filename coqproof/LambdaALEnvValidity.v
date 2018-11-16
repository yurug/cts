Require Import ErrorMonad.
Require Import Misc.
Require Import Environment.
Require Import Omega.
Require Import LibTactics.
Require Import List.
Require Import FunInd.
Import ListNotations.

Require Import LambdaAL.
Require Import LambdaALValues.
Require Import LambdaALOperationalSemantics.
Require Import LambdaALOperationalSemanticsProofs.
Require Import LambdaALDerive.
Require Import LambdaALValidity.

(** The following relation represents values and change values that
    are related at every level of precision. *)
Definition rel_value v dv v' := forall k, drel_value k v dv v'.
Definition rel_env env denv env' := forall n, drel_env n env denv env'.

Inductive valid_denvironment : denvironment -> Prop :=
| ValidNil:
    valid_denvironment nil

| ValidCons:
    forall denv v dv v',
      valid_denvironment denv ->
      move v dv = Some v' ->
      (forall denv' dt',
          dv = dClosure denv' dt' ->
          let env' := values_of_list ⌊ list_of_closure_denvironment denv' ⌋ in
          v = Closure env' (underive dt')
          /\ valid_denvironment (denvironment_of_closure_denvironment denv')
      ) ->
      valid_denvironment (bind denv (v, dv)).

Definition valid_closure_changes v dv :=
  (forall denv' dt',
      dv = dClosure denv' dt' ->
      let env' := values_of_list ⌊ list_of_closure_denvironment denv' ⌋ in
      v = Closure env' (underive dt')
      /\ valid_denvironment (denvironment_of_closure_denvironment denv')
  ).

Lemma valid_denvironment_lookup_moves_well:
  forall denv,
    valid_denvironment denv ->
    forall x v dv, lookup denv x = Some (v, dv) ->
    exists v', move v dv = Some v'.
Proof.
  intros * Henv. induction Henv; intros.
  simpl in H. unfold error in H. congruence.
  destruct x. destruct n.
  simpl in H1. inversion H1. subst. eexists. eauto.
  simpl in H1. eapply IHHenv; eauto.
Qed.

Lemma valid_denvironment_lookups_moves_well:
  forall denv,
    valid_denvironment denv ->
    forall x vdv, lookups denv x = Some vdv ->
             let v := List.map fst vdv in
             let dv := List.map snd vdv in
    exists v', move_values (values_of_list v) (ldvalues_of_list dv) = Some v'.
Proof.
  intros * Henv. induction x; simpl in * |- *; intros.
  inversion H. subst. simpl. eexists. eauto.
  case_eq (lookups denv x); intros * Heq.
  case_eq (lookup denv a); intros * Heq'.
  rewrite Heq in * |- *. rewrite Heq' in * |- *. simpl  in H.
  destruct p. simpl in * |- *. inverse H.
  simpl.
  edestruct IHx. eauto.
  destruct (valid_denvironment_lookup_moves_well _ Henv _ _ _ Heq').
  rewrite H1. simpl.
  eexists; intuition.
  rewrite H0. simpl. eauto.
  rewrite Heq' in H. simpl in H. rewrite Heq in H. simpl in H. congruence.
  rewrite Heq in H. simpl in H. congruence.
Qed.

Lemma valid_denvironment_moves_well:
  forall denv,
    valid_denvironment denv ->
    exists env', move_environment (values_of_list ⌊ denv ⌋) denv = Some env'.
Proof.
  intros denv Henv.
  induction Henv.
  - exists VNil. simpl. auto.
  - destruct IHHenv. exists (VCons v' x).
    simpl. rewrite H. rewrite H1.
    simpl. auto.
Qed.

Lemma valid_denvironment_contains_ok_closure:
  forall { denv },
    valid_denvironment denv ->
    forall { f v denv' dt' },
    lookup denv f = Some (v, dClosure denv' dt') ->
    valid_closure_changes v (dClosure denv' dt').
Proof.
  intros * Henv. induction Henv; intros.
  simpl in H. unfold error in H. congruence.
  destruct f. destruct n.
  simpl in H1. inversion H1. subst.
  unfold ret in H1. destruct v0; inversion H1; try congruence; intuition; eauto.
  simpl in H1.
  eapply IHHenv; eauto.
Qed.

Theorem lookup_env_of_denv:
  forall { denv v dv x },
    lookup denv x = Some (v, dv) ->
    lookup ⌊ denv ⌋ x = Some v.
Proof.
  induction denv; simpl; unfold ret, error; intros; try congruence; eauto.
  destruct x. destruct n; eauto. destruct a. simpl. congruence.
Qed.

Theorem lookup_move_environment:
  forall { x denv v dv env' },
    lookup denv x = Some (v, dv) ->
    move_environment (values_of_list ⌊ denv ⌋) denv = Some env' ->
    exists v', lookup (list_of_values env') x = Some v' /\ move v dv = Some v'.
Proof.
  introv Hlookup_x_denv Hmove.
  gen env'.
  functional induction (lookup denv x); inversion Hlookup_x_denv; subst; introv Hmove; destruct env';
    try destruct v0 as [v2 dv2];
    apply inv_success_mbind2 in Hmove; unfold ret in Hmove;
      inversion_clear Hmove as [ x [ Heq Hmove' ] ]; apply inv_success_mbind2 in Hmove';
           inversion_clear Hmove' as [ x' [ Heq' Hmove'' ] ]; inverts Hmove''.
  - exists v0. auto.
  - apply IHo; auto.
Qed.

(*
  Switch around quantifiers to help inversion on the result.
  In the input, we get for each step-index k, an inductive proof that the environments match at depth n.
  In the result, we get an inductive proof that for each step-index k, the environments match at depth k. *)

Lemma invert_rel_env:
  forall E dE E', rel_env E dE E' -> pre_drel_env (rel_value) E dE E'.
Proof.
  intro.
  induction E; destruct dE; destruct E'; introv Hrel; lets Hrel1 : Hrel 1; inverts Hrel1; subst; constructor.
  - intro k.
    lets Hrel__k : Hrel k.
    inversion Hrel__k; auto.
  - apply IHE.
    intro n.
    lets Hrel__n : Hrel n.
    inverts Hrel__n; auto.
Qed.

Lemma original_environment_under_rel_env:
  forall E dE E', rel_env E dE E' -> ⌊ dE ⌋ = E.
Proof.
  introv Hrel.
  lets Hrel__alt: invert_rel_env Hrel.
  clear Hrel.
  induction Hrel__alt; auto.
  - simpl. fequals.
Qed.

Lemma modified_environment_under_rel_env:
  forall E dE E', rel_env E dE E' -> ⌈ dE ⌉ = Some E'.
Proof.
  introv Hrel.
  apply invert_rel_env in Hrel.
  induction Hrel. auto.
  - unfold modified_environment in IHHrel |- *; simpl. rewrite IHHrel.
    lets Hvmove : @drel_value_move_value 1 (H 1); auto. rewrite Hvmove.
    reflexivity.
Qed.

(* Lemma rel_env_original_and_modified_env: *)
(*   forall dE E', *)
(*     ⌈ dE ⌉ = Some E' -> *)
(*     rel_env ⌊ dE ⌋ dE E'. *)
(* Proof. *)
(*   intros * HE'. intro n. *)
(*   unfold drel_env.  *)
  

Lemma rel_env_lookup_value':
  forall {E dE E' v x v0 dv},
    rel_env E dE E' ->
    Environment.lookup E x = Some v ->
    Environment.lookup dE x = Some (v0, dv) ->
    v0 = v.
Proof.
  introv Hrel.
  apply invert_rel_env in Hrel.
  destruct x as [n].
  gen n.
  induction Hrel; introv HlookE HlookdE.
  - inverts HlookE.
  - induction n; inverts HlookE; inverts HlookdE; eauto.
Qed.

Lemma rel_env_lookup_value:
  forall {E dE E' v x dEu Eu Eu' v0 dv},
    rel_env (Eu ++ E) (dEu ++ dE) (Eu' ++ E') ->
    Environment.lookup (Eu ++ E) x = Some v ->
    Environment.lookup (dEu ++ dE) x = Some (v0, dv) ->
    v0 = v.
  eauto using rel_env_lookup_value'.
Qed.

Require Import LambdaALFundamentalProperty.

Lemma rel_env_through_context_evaluation:
  forall ctx E dE E' Eu Eu' dEu,
    rel_env E dE E' ->
    [ E ⊢ ctx ⇑ Eu ] ->
    [ E' ⊢ ctx ⇑ Eu' ] ->
    [[ dE ⊢ derive ctx ⇑ dEu ]] ->
    rel_env (Eu ++ E) (dEu ++ dE) (Eu' ++ E').
Proof.
  induction ctx; intros * Hrelenv Hoeval Hmeval Hdeval;
    inverse Hoeval; inverse Hmeval; inverse Hdeval; simpl; eauto;
      intro k; do 3 rewrite <- app_assoc; simpl; eapply IHctx;
        try intro k'; eauto.
  - assert (v3 = v1).
    erewrite (original_environment_under_rel_env E dE E' Hrelenv) in H9.
    eapply deterministic_eval; eauto. subst.
    eapply DrelCons.
    destruct (sound_eval _ _ _ H5) as [ k'' Heval ].
    generalize (fundamental_lemma (@(v, v0)) _ _ _ _ (Hrelenv (k' + k'' + 1))).
    rewrite unfold_drel_term. unfold drel_term_F. intro Hrel.
    assert (Hk'' : k'' < k' + k'' + 1) by omega.
    destruct (Hrel k'' Hk'' _ Heval _ H7). intuition.
    assert (x = dv). eapply deterministic_deval; eauto. subst.
    eapply (drel_value_antimonotonic _ _ _ H0); eauto.
    eapply Hrelenv; eauto.

  - erewrite (original_environment_under_rel_env E dE E' Hrelenv) in H7.
    assert (l = xs). eapply reverse_map; eauto. intros. congruence. subst.
    assert (v = v1). eapply deterministic_eval; eauto. subst.
    eapply DrelCons.
    destruct (sound_eval _ _ _ H4) as [ k'' Heval ].
    generalize (fundamental_lemma (ttuple xs) _ _ _ _ (Hrelenv (k' + k'' + 1))).
    rewrite unfold_drel_term. unfold drel_term_F. intro Hrel.
    assert (Hk'' : k'' < k' + k'' + 1) by omega.
    destruct (Hrel k'' Hk'' _ Heval _ H6). intuition.
    assert (x = dv). eapply deterministic_deval; eauto. subst.
    eapply (drel_value_antimonotonic _ _ _ H5); eauto.
    eapply Hrelenv; eauto.

   Unshelve. all: omega.
Qed.

Lemma rel_env_length:
  forall E dE E', rel_env E dE E' -> length E = length dE /\ length E' = length dE.
Proof.
  intros.
  assert (E = ⌊ dE ⌋). erewrite original_environment_under_rel_env; eauto.
  unfold original_environment in H0. subst. rewrite map_length.
  assert (⌈ dE ⌉ = Some E'). erewrite modified_environment_under_rel_env; eauto.
  unfold modified_environment in H0. rewrite (list_map_length _ _ _ H0).
  eauto.
Qed.

Lemma rel_env_lookup_change:
  forall E dE E' x v,
    rel_env E dE E' ->
    lookup E x = Some v ->
    exists dv, lookup dE x = Some (v, dv).
Proof.
  intros. rewrite <- (original_environment_under_rel_env _ _ _ H) in H0.
  unfold original_environment in H0.
  destruct (map_lookup_2 H0). exists (snd x0). destruct x0. simpl in * |- *. intuition. subst.
  eauto.
Qed.
