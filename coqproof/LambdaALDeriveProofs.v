(** * New proof of correctness for "classic" non caching differentiation. *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import Wf_nat.
Require Import Misc.
Require Import ErrorMonad.
Require Import Environment.
Require Import LambdaAL.
Require Import Constants.
Require Import LambdaALValues.
Require Import LambdaALOperationalSemantics.
Require Import LambdaALOperationalSemanticsProofs.
Require Import LambdaALDerive.
Require Import LambdaALValidity.
Require Import LambdaALEnvValidity.
Require Import LambdaALFundamentalProperty.

(**

    Proof of Theorem 3.3 (Soundness of differentiation in λAL).

    If [dE] is a valid change environment from base environment [E] to
    updated environment [E'], and if [t] converges both in the base
    and updated environment, then the derivative of [t] evaluates
    under the change environment [dE] to a valid change [dv] between
    base result [v] and updated result [v'].

*)
Theorem derive_soundness:
  forall {dE E E' t v v'},
    rel_env E dE E' ->
    [ E ⊢ t ⇓ v ] ->
    [ E' ⊢ t ⇓ v' ] ->
    exists dv, [[ dE ⊢ derive t ⇓ dv ]] /\ v ⊕ dv = Some v'.
Proof.
  intros * Hrel Heval Heval'.
  destruct (sound_eval _ _ _ Heval) as [n Hneval].
  assert (Hreln: drel_env (S n) E dE E'). easy.
  generalize (fundamental_lemma t _ _ _ _ Hreln). intro Hrelt.
  rewrite unfold_drel_term in Hrelt. unfold drel_term_F in Hrelt.
  assert (Hn : n < S n). omega.
  edestruct (Hrelt n Hn _ Hneval _ Heval'). intuition.
  exists x. intuition; auto.
  replace (S n - n) with 1 in H0.
  eapply drel_value_move_value; eauto.
  omega.
Qed.

Corollary derive_soundness2:
  forall {dE E E' t v v' dv},
    rel_env E dE E' ->
    [ E ⊢ t ⇓ v ] ->
    [ E' ⊢ t ⇓ v' ] ->
    [[ dE ⊢ derive t ⇓ dv ]] ->
    v ⊕ dv = Some v'.
Proof.
  intros * Hrel H H' Hd.
  destruct (derive_soundness Hrel H H') as [ dv' [ Hd' Hm ] ].
  assert (dv = dv').
  eapply deterministic_deval; eauto. subst. eauto.
Qed.

Lemma modified_environment_of_closure_denvironment:
  forall {c x},
    move_environment (values_of_list ⌊ list_of_closure_denvironment c ⌋)
                     (denvironment_of_closure_denvironment c) = Some x ->
    ⌈ list_of_closure_denvironment c ⌉ = Some (list_of_values x).
Proof.
  unfold modified_environment.
  induction c; intros * HmoveE; simpl in * |- *; inverse HmoveE; eauto.
  destruct (v ⊕ d); simpl in * |- *.
  destruct (inv_success_mbind H0). rewrite H in H0. simpl in H0. inverse H0. clear H0.
  destruct (inv_success_mbind HmoveE). rewrite H0 in HmoveE. simpl in HmoveE. inverse HmoveE. clear HmoveE.
  rewrite (IHc _ H0). simpl. 
  eauto.
  congruence.
Qed.


Lemma derive_graft_tuple:
  forall ctx xs,
  derive (graft ctx (ttuple xs)) = dgraft (derive ctx) (derive (ttuple xs)).
Proof.
  induction ctx; simpl; intros; eauto; rewrite IHctx; eauto.
Qed.

Lemma derive_context_ended_with_tuple:
  forall { ctx dE xs dEu bs },
    [[dE ⊢ derive ctx ⇑ dEu]] ->
    Environment.lookups (dEu ++ dE) xs = Some bs ->
    let vs := map fst bs in
    let dvs := map snd bs in
    [[dE ⊢ derive (graft ctx (ttuple xs))
         ⇑ (LambdaALValues.tuple vs, LambdaALValues.dtuple dvs) :: dEu]].
Proof.
  induction ctx; simpl; intros; eauto.
  inverse H.
  generalize (original_environment_lookups dE xs). simpl in H0. rewrite H0. intro Hlookups.
  apply SDTupleContext with (dE' := nil); try constructor; eauto.
  eapply (STuple NoSteps); eauto.
  simpl.
  constructor.
  simpl. auto.
  eapply (SDTuple NoSteps); try constructor; eauto.
  eapply SDVar; simpl; eauto.
  inverse H.
  rewrite <- app_assoc in H0. simpl in H0. eauto.
  rewrite app_comm_cons. use SDCallContext.
  inverse H.
  rewrite <- app_assoc in H0. simpl in H0. eauto.
  rewrite app_comm_cons. use SDTupleContext.
  Unshelve. all: exact 0.
Qed.

Lemma derive_context_ended_with_call:
  forall { ctx dE dEu f x v dv},
    [[dE ⊢ derive ctx ⇑ dEu]] ->
    [⌊ dEu ++ dE ⌋ ⊢ @( f, x) ⇓ v] ->
    [[dEu ++ dE ⊢ LambdaAL.dcall f x ⇓ dv]] ->
    [[dE ⊢ derive (graft ctx @(f, x)) ⇑ ((v, dv) :: dEu) ]].
Proof.
  induction ctx; simpl; intros * Hderive Hcall Hdcall; inverse Hderive; eauto.
  - eapply SDCallContext with (dE' := nil); simpl; eauto.
    eapply SDNilContext.
  - rewrite app_comm_cons. eapply SDCallContext; eauto. eapply IHctx; eauto.
    rewrite <- app_assoc in Hcall. simpl in Hcall. eauto.
    rewrite <- app_assoc in Hdcall. simpl in Hdcall. eauto.
  - rewrite app_comm_cons. eapply SDTupleContext; eauto. eapply IHctx; eauto.
    rewrite <- app_assoc in Hcall. simpl in Hcall. eauto.
    rewrite <- app_assoc in Hdcall. simpl in Hdcall. eauto.
Qed.
