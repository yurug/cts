From Equations Require Import Equations.
Require Import List.
Require Import Omega.
Require Import Misc.
Require Import LambdaAL.
Require Import Constants.
Require Import ErrorMonad.
Require Import ILambdaAL.
Require Import ILambdaALValues.
Require Import ILambdaALOperationalSemanticsPrimitives.
Require Import ILambdaALOperationalSemantics.

Inductive has_no_cache: environment -> Prop :=
  | NilHasNoCache: 
      has_no_cache nil
  | ConsHasNoCache:
      forall V F,
        has_no_cache F ->
        has_no_cache ((V, None) :: F).

Lemma list_of_closure_environment_of_closure_environment_of_list:
  forall {F}, 
    has_no_cache F ->
    F = list_of_closure_environment (closure_environment_of_list F).
Proof.
  induction F; intro Hnoc; inverse Hnoc; simpl; eauto.
  f_equal. eapply IHF; eauto.
Qed.

Lemma values_of_list_list_of_values:
  forall vs, values_of_list (list_of_values vs) = vs.
Proof.
  induction vs; simpl; intros; auto.
  f_equal. auto.
Qed.

Lemma eval_primitive_add_cache:
  forall a V VC, eval_primitive Add a = Some (V, VC) ->
            VC = CacheValue nil.
Proof.
  intros; simpl in * |-.
  funelim (eval_add a); try simpl_unfold_err; easy.
Qed.

Lemma call_evaluation:
  forall {F f x Vy VCy V VC M},
    [# F ⊢ @#(f, x) ⇓ (Vy, CacheValue ((Vy, Some VCy) :: nil)) ] ->
    [# (Vy, Some VCy) :: F ⊢ M ⇓ (V, VC) ] ->
    [# F ⊢ IDef f x M ⇓ (V ,VC) ].
Proof.
  intros.
  inverse H; inverse H9.
  - simpl in H7. inverse H7.
    inverse H11. simpl in H5. inverse H5.
    eapply TPrimitiveCall; eauto.
  - inverse H11. simpl in H5. inverse H5.
    eapply TClosureCall; eauto.
Qed.

Lemma inverse_call_evaluation:
  forall {F f x V VC M},
    [# F ⊢ IDef f x M ⇓ (V, VC) ] ->
    exists Vy VCy, 
      [# F ⊢ @#(f, x) ⇓ (Vy, CacheValue ((Vy, Some VCy) :: nil)) ] /\
      [# (Vy, Some VCy) :: F ⊢ M ⇓ (V, VC) ].
Proof.
  intros.
  inverse H; do 2 eexists; intuition; simpl in * |- *; eauto.
  - eapply TPrimitiveCall; repeat (try econstructor; eauto).
  - eapply TClosureCall; repeat (try econstructor; eauto).
Qed.


Lemma inverse_closure_call_evaluation:
  forall {F f x Vy VCy Vx Ef M},
    [# F ⊢ @#(f, x) ⇓ (Vy, CacheValue ((Vy, Some VCy) :: nil)) ] ->
    lookup_value F f = Some (IClosure Ef M) ->
    lookup_value F x = Some Vx ->
    [# (Vx, None) :: (list_of_closure_environment Ef) ⊢ M ⇓ (Vy, VCy) ].
Proof.
  intros * Hevalcall Hlf Hlx.
  inverse Hevalcall; try congruence.
  assert (F' = Ef). congruence.
  assert (M = M'). congruence. subst.
  inverse H7. simpl in H5. inverse H5.
  inverse H9. simpl in H3. inverse H3.
  assert (Vx = Vx0). congruence.
  subst. eauto.
Qed.

Lemma inverse_primitive_call_evaluation:
  forall {F f x Vy VCy Vx p},
    [# F ⊢ @#(f, x) ⇓ (Vy, CacheValue ((Vy, Some VCy) :: nil)) ] ->
    lookup_value F f = Some (IPrimitive p) ->
    lookup_value F x = Some Vx ->
    eval_primitive p Vx = Some (Vy, VCy).
Proof.
  intros * Hevalcall Hlf Hlx.
  inverse Hevalcall; try congruence.
  assert (p = p0) by congruence.
  assert (Vx = Vx0) by congruence.
  subst.
  inverse H7.
  simpl in H5. inverse H5.
  inverse H9. simpl in H3. inverse H3.
  eauto.
Qed.

Lemma dcall_evaluation:
  forall dF f x V' VC'' VC' dV' mV mVC dV (VC : cache_value) dM,
    [[# (V', VC') :: nil, dF ⊢ dcall f x ⇓ (dV', CacheValue ((mV, mVC) :: nil)) ]] ->
    [[# VC'', (V', mVC, dV') :: dF ⊢ dM ⇓ (dV, VC)]] ->
    [[# (V', VC') :: VC'', dF ⊢ dIDef f x dM ⇓ (dV, VC) ]].
Proof.
  intros * Hevalcall Heval.
  inverse Hevalcall; simpl in * |- *.
  - inverse H10; simpl in * |- *. inverse H4. inverse H6. simpl in H5. inverse H5.
    eapply TDReplaceCall; eauto.
  - inverse H10; simpl in * |- *. inverse H4. inverse H6. simpl in H5. inverse H5.
    eapply TDPrimitiveNil; eauto.
  - inverse H10; simpl in * |- *. inverse H4. inverse H6. simpl in H5. inverse H5.
    eapply TDClosureChange; eauto.
Qed.

Lemma lookup_value_lookup:
  forall {F x V}, lookup_value F x = Some V -> exists VC, Environment.lookup F x = Some (V, VC).
Proof.
  unfold lookup_value. intros. destruct (inv_success_mbind H).
  rewrite H0 in H. simpl in H. inverse H.
  destruct x0. exists o; eauto.
Qed.

Lemma lookup_value_lookup_2:
  forall {F x}, lookup_value F x = None -> Environment.lookup F x = None.
Proof.
  unfold lookup_value. intros. destruct (Environment.lookup F x). simpl in H.
  unfold ret in H. congruence.
  eauto.
Qed.

Lemma lookup_values_unfold:
  forall {F x xs},
    lookup_values F (x :: xs) = (v <- lookup_value F x; vs <- lookup_values F xs; ret (IVCons v vs)).
Proof.
  intros.
  unfold lookup_values.
  simpl.
  case_eq (lookup_value F x); intros.
  destruct (lookup_value_lookup H).
  rewrite H0.
  simpl.
  destruct (Environment.lookups F xs); simpl; eauto.
  rewrite lookup_value_lookup_2; eauto; simpl.
  destruct (Environment.lookups F xs); simpl; eauto.
Qed.

Lemma lookup_original_environment:
  forall {dF x V},
    Environment.lookup dF x = Some V ->
    Environment.lookup ⌊# dF ⌋ x = Some (fst V).
Proof.
  intros. eapply Environment.map_lookup; eauto.
Qed.

Lemma lookups_original_environment:
  forall {xs dF Vs},
    Environment.lookups dF xs = Some Vs ->
    Environment.lookups ⌊# dF ⌋ xs = Some (map fst Vs).
Proof.
  intros. eapply Environment.map_lookups; eauto.
Qed.

Lemma lookup_values_original_environment:
  forall {xs dF Vs},
    Environment.lookups dF xs = Some Vs ->
    lookup_values ⌊# dF ⌋ xs = Some (values_of_list (map fst (map fst Vs))).
Proof.
  intros. unfold lookup_values. rewrite (lookups_original_environment H). simpl.
  auto.
Qed.

Lemma lookup_modified_environment:
  forall { dF' x F' V },
    ⌈# dF' ⌉ = Some F' ->
    Environment.lookup dF' x = Some V ->
    exists V', Environment.lookup F' x = Some V' /\ modified_binding V = Some V'.
Proof.
  induction dF'; intros * HF' Hlookup; inverse Hlookup; simpl in * |- *; eauto.
  unfold modified_environment in HF'. simpl in HF'.
  destruct (inv_success_mbind HF'). rewrite H in HF'. simpl in HF'.
  destruct (inv_success_mbind HF'). rewrite H1 in HF'. simpl in HF'.
  inverse HF'. simpl. eauto.

  destruct x; destruct n. inverse Hlookup.
  eauto.
  apply (IHdF' _ _ _ H1 Hlookup).
Qed.

Lemma lookups_modified_environment:
  forall { xs dF' F' Vs },
    ⌈# dF' ⌉ = Some F' ->
    Environment.lookups dF' xs = Some Vs ->
    Environment.lookups F' xs = list_map modified_binding Vs.
Proof.
  induction xs; intros * HF' Hlookups; inverse Hlookups; simpl in * |- *; eauto.
  destruct (inv_success_mbind H0). rewrite H in H0. simpl in H0.
  destruct (inv_success_mbind H0). rewrite H1 in H0. simpl in H0.
  inverse H0.
  rewrite (IHxs _ _ _ HF' H).
  destruct (lookup_modified_environment HF' H1). intuition. rewrite H3. 
  simpl. rewrite ErrorMonad.commute_bind. rewrite H4. eauto.
Qed.

Lemma map_modified_binding_is_move_values:
  forall Vs : list (value * option cache_value * dvalue),
    (p <- list_map modified_binding Vs; ret (values_of_list (map fst p))) =
    move_values (values_of_list (map fst (map fst Vs))) (map snd Vs).
Proof.
  induction Vs; simpl; eauto.
  destruct a; simpl. rewrite <- IHVs.
  unfold modified_binding. simpl.
  do 10  (rewrite ErrorMonad.commute_bind).
  destruct p; simpl.
  destruct (v ⊕ d); simpl; eauto.
  set (F := (fun b : value * option cache_value * dvalue => V' <- fst (fst b) ⊕ snd b; ret (V', snd (fst b)))).
  destruct (list_map F Vs); simpl; eauto.
Qed.

Lemma lookup_values_modified_environment:
  forall { xs dF' F' Vs },
    ⌈# dF' ⌉ = Some F' ->
    Environment.lookups dF' xs = Some Vs ->
    lookup_values F' xs = move_values (values_of_list (map fst (map fst Vs))) (map snd Vs).
Proof.
  intros. unfold lookup_values. rewrite (lookups_modified_environment H H0).
  apply map_modified_binding_is_move_values.
Qed.

Lemma modified_environment_implied_valid_moves:
  forall xs dF' F' Bs,
    ⌈# dF' ⌉ = Some F' ->
    Environment.lookups dF' xs = Some Bs ->
    exists Vs' : values, move_values (values_of_list (map fst (map fst Bs))) (map snd Bs) = Some Vs'.
Proof.
  induction xs; intros * HF' Hlookups; inverse Hlookups; simpl in * |- *; eauto.
  destruct (inv_success_mbind H0). rewrite H in H0. simpl in H0.
  destruct (inv_success_mbind H0). rewrite H1 in H0. simpl in H0.
  inverse H0.
  simpl.
  destruct (lookup_modified_environment HF' H1). intuition.
  unfold modified_binding in H4. destruct (inv_success_mbind H4). rewrite H2. simpl.
  edestruct (IHxs _ _ _ HF' H). rewrite H5.
  simpl. eexists. eauto.
Qed.

Lemma eval_cache_preserves_length:
  forall {C VC F},
    eval_cache F C (CacheValue VC) ->
    List.length C = List.length VC.
Proof.
  induction C; simpl; intros * Hevalcache; inverse Hevalcache; eauto.
  erewrite IHC; simpl; eauto.
Qed.

Lemma eval_cache_weakening:
  forall {F' F C VC},
    eval_cache F C VC ->
    eval_cache (F ++ F') C VC.
Proof.
  intros * Hcache.
  induction Hcache; constructor; try eapply Environment.lookup_app_2; eauto.
Qed.

(* Lemma eval_cache_decomposition: *)
(*   eval_cache F (graft (graft ctx t) u) VC -> *)
(*   exists *)

Lemma eval_cache_deterministic:
  forall {C F VC VC'},
    eval_cache F C VC ->
    eval_cache F C VC' ->
    VC = VC'.
Proof.
  induction C; simpl; intros * He He'; inverse He; inverse He'; eauto.
  generalize (IHC _ _ _ H4 H7). intros.
  congruence.
Qed.

Lemma lookup_in_modified_environment:
  forall {dF F x V' VCx },
    ⌈# dF ⌉ = Some F ->
    Environment.lookup F x = Some (V', VCx) ->
    exists V dV,
      V ⊕ dV = Some V' /\
      Environment.lookup dF x = Some (V, VCx, dV).
Proof.
  induction dF; simpl in * |- *; intros; inverse H.
  - inverse H0.
  - unfold modified_environment in H. simpl in H. 
    destruct (inv_success_mbind H). 
    rewrite H1 in H. simpl in H.
    destruct (inv_success_mbind H). rewrite H3 in H. simpl in H. inverse H. simpl in * |-.

    destruct x. destruct n.
    * destruct a as [ a dV ]. destruct a as [ V VC ].
      exists V, dV.
      inverse H0.
      unfold modified_binding in H1.
      destruct (inv_success_mbind H1).  rewrite H4 in H1. simpl in H1.
      simpl in H4. inverse H1. easy.
    * use IHdF.
Qed.

Lemma eval_cache_update_of_eval_cache_under_modified_environment:
  forall { C dF F' VC' },
    ⌈# dF ⌉ = Some F' ->
    eval_cache F' C (CacheValue VC') ->
    eval_cache_update dF C (CacheValue VC').
Proof.
  intros.
  induction H0.
  - constructor.
  - destruct (lookup_in_modified_environment H H0). destruct H2. intuition.
    eapply TCachedVarUpdate; eauto.
Qed.

Lemma eval_cache_under_modified_environment_of_eval_cache_update:
  forall { C dF F' VC' },
    ⌈# dF ⌉ = Some F' ->
    eval_cache_update dF C (CacheValue VC') ->
    eval_cache F' C (CacheValue VC').
Proof.
  intros.
  induction H0.
  - constructor.
  - econstructor; eauto.
    destruct (Environment.list_map_lookup H H0). intuition. unfold modified_binding in H5.
    simpl in H5. rewrite H2 in H5. simpl in H5. inverse H5. eauto.
Qed.

Lemma graft_def:
  forall ctx f x u,
    graft ctx (Def f x u) = graft (graft ctx @( f, x)) u.
Proof.
  induction ctx; simpl; intros; eauto.
  - f_equal. eapply IHctx.
  - f_equal. eapply IHctx.
Qed.

Lemma graft_tuple:
  forall ctx xs u,
    graft ctx (DefTuple xs u) = graft (graft ctx (ttuple xs)) u.
Proof.
  induction ctx; simpl; intros; eauto.
  - f_equal. eapply IHctx.
  - f_equal. eapply IHctx.
Qed.

Lemma modified_environment_bind:
  forall {dF F V VC dV V'},
    ⌈# dF ⌉ = Some F ->
    V ⊕ dV = Some V' ->
    ⌈# (V, VC, dV) :: dF ⌉ = Some (Environment.bind F (V', VC)).
Proof.
  intros.
  unfold modified_environment.
  simpl.
  fold (⌈# dF ⌉).
  rewrite H.
  unfold modified_binding.
  simpl. rewrite H0.
  simpl.
  eauto.
Qed.

Lemma move_nil:
  forall p, IPrimitive p ⊕ dIPrimitiveNil = Some (IPrimitive p).
Proof.
  destruct p; simpl; eauto.
Qed.

Lemma move_replace:
  forall V V', V ⊕ dIReplace V' = Some V'.
Proof.
  intros. destruct V; eauto.
Qed.

Lemma eval_deterministic:
  forall {t F R},
    [# F ⊢ t ⇓ R ] -> forall {R'},
    [# F ⊢ t ⇓ R' ] ->
    R = R'.
Proof.
  intros * Heval; induction Heval; intros * Heval'; inverse Heval';
  simpl in * |- *; try congruence; eauto.
  - f_equal; try congruence; eapply eval_cache_deterministic; eauto.
  - easy_eqs (p = p0 /\ Vx = Vx0).
    rewrite H9 in H1. inverse H1.
    eapply (IHHeval _ H10); eauto.
  - easy_eqs (F' = F'0 /\ M' = M'0 /\ Vx = Vx0).
    generalize (IHHeval1 _ H8). intro He. inverse He.
    eapply (IHHeval2 _ H9).
  - rewrite H3 in H. inverse H. eapply (IHHeval _ H5).
Qed.