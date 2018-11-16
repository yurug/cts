(** * Soundness of CTS differentiation. *)

From Equations Require Import Equations.
Require Import Omega.
Require Import List.
Require Import ErrorMonad.
Require Import Misc.
Require Import Index.
Require Import Environment.
Require Import Constants.
Require Import LambdaAL.
Require Import LambdaALOperationalSemanticsPrimitives.
Require Import LambdaALOperationalSemantics.
Require Import LambdaALOperationalSemanticsProofs.
Require Import LambdaALDerive.
Require Import LambdaALValidity.
Require Import LambdaALEnvValidity.
Require Import LambdaALFundamentalProperty.
Require Import LambdaALDeriveProofs.
Require Import ILambdaAL.
Require Import ILambdaALValues.
Require Import ILambdaALOperationalSemanticsPrimitives.
Require Import ILambdaALOperationalSemantics.
Require Import ILambdaALDerive.
Require Import ILambdaALOperationalSemanticsProofs.

Lemma cts_environment_lookup:
  forall {E x v},
    lookup E x = Some v ->
    lookup (cts_environment E) x = Some (cts_binding v).
Proof.
  induction E; simpl; intros x v Hlookup; inverse Hlookup; intros.
  destruct x. destruct n; inverse Hlookup; eauto.
Qed.

Lemma cts_environment_lookups:
  forall {xs E vs},
    lookups E xs = Some vs ->
    lookups (cts_environment E) xs = Some (List.map cts_binding vs).
Proof.
  induction xs; simpl; intros E vs Hlookups; inverse Hlookups; simpl; eauto.
  destruct (ErrorMonad.inv_success_mbind Hlookups). rewrite H in Hlookups. simpl in Hlookups.
  destruct (ErrorMonad.inv_success_mbind Hlookups). rewrite H1 in Hlookups. simpl in Hlookups.
  inverse Hlookups.
  erewrite IHxs; simpl; eauto.
  erewrite cts_environment_lookup; simpl; eauto.
Qed.

Lemma cts_environment_app:
  forall E F, cts_environment (E ++ F) = cts_environment E ++ cts_environment F.
Proof.
  eapply map_app.
Qed.

Lemma cts_denvironment_app:
  forall dE dF, cts_denvironment (dE ++ dF) = cts_denvironment dE ++ cts_denvironment dF.
Proof.
  eapply map_app.
Qed.

Lemma cts_denvironment_lookup:
  forall {dE x v},
    lookup dE x = Some v ->
    lookup (cts_denvironment dE) x = Some (cts_dbinding v).
Proof.
  induction dE; simpl; intros x v Hlookup; inverse Hlookup; intros.
  destruct x. destruct n; inverse Hlookup; eauto.
Qed.

Lemma cts_denvironment_lookups:
  forall {xs dE vs},
    lookups dE xs = Some vs ->
    lookups (cts_denvironment dE) xs = Some (List.map cts_dbinding vs).
Proof.
  induction xs; simpl; intros dE vs Hlookups; inverse Hlookups; simpl; eauto.
  destruct (ErrorMonad.inv_success_mbind Hlookups). rewrite H in Hlookups. simpl in Hlookups.
  destruct (ErrorMonad.inv_success_mbind Hlookups). rewrite H1 in Hlookups. simpl in Hlookups.
  inverse Hlookups.
  erewrite IHxs; simpl; eauto.
  erewrite cts_denvironment_lookup; simpl; eauto.
Qed.

Lemma cts_values_cts_dbinding:
  forall bs,
    cts_values (LambdaALValues.values_of_list (map fst bs)) =
    values_of_list (map fst (map fst (map cts_dbinding bs))).
Proof.
  induction bs; simpl; intros; eauto. rewrite IHbs. auto.
Qed.

Lemma cts_values_cts_binding:
  forall vs,
  values_of_list (map fst (map cts_binding vs)) =
  cts_values (LambdaALValues.values_of_list vs).
Proof.
  induction vs; simpl; intros; eauto. rewrite IHvs. eauto.
Qed.

Lemma cts_dvalues_cts_dbinding_2:
  forall bs,
    map snd (map cts_dbinding bs) = cts_dvalues (LambdaALValues.ldvalues_of_list (map snd bs)).
Proof.
  induction bs; simpl; intros; eauto. rewrite IHbs. auto.
Qed.

Lemma shape_of_cts_generated_cache:
  forall {u dF t V rVC},
    [# dF ⊢ cts_term_aux t u ⇓ (V, CacheValue rVC)] ->
    List.length (cache_of_term t) = List.length rVC.
Proof.
  induction u; intros * Heval; inverse Heval; simpl in * |- *; try (eapply IHu; eauto).
  eapply eval_cache_preserves_length; eauto.
Qed.

Lemma cts_nonvar_has_nonempty_cache:
  forall {t u dF V rVC },
    (forall x, t <> Var x) ->
    [# dF ⊢ cts_term_aux t u ⇓ (V, CacheValue rVC)] ->
    rVC <> nil.
Proof.
  intros * Hnotvar Heval.
  generalize (shape_of_cts_generated_cache Heval). intros Hlen.
  intro HVC. subst. simpl in * |- *.
  destruct t; simpl in * |- *; try congruence.
Qed.

Require Import LibTactics.

Lemma cache_of_term_reverse_environment:
  forall {t F Fr},
    depth_of_term t = List.length F ->
    eval_cache (F ++ Fr) (cache_of_term t) (CacheValue (List.rev F)).
Proof.
  induction t; intros * He; easy; try constructor.

  - destruct F; simpl in He; inverse He; simpl; try constructor.

  - assert (Hrlen: length (rev F) = length F) by (eapply rev_length).
    assert (Hcons: exists x F', rev F = x :: F').
    destruct (rev F); simpl in * |- *; try omega; eexists; eauto.
    destruct Hcons as [ x Hcons ].
    destruct Hcons as [ F' Hcons ].
    rewrite Hcons.
    destruct x.
    assert (Hlast: F = rev F' ++ (v1, o) :: nil).
    replace ((v1, o) :: F') with (rev (rev ((v1, o) :: F'))) in Hcons.
    apply rev_injective; eauto.
    apply rev_involutive.
    rewrite Hlast in He |- *.
    rewrite app_length in He.
    rewrite Nat.add_comm in He.
    simpl in He.
    inverse He.
    replace ((rev F' ++ (v1, o) :: nil) ++ Fr)
       with (rev F' ++ (v1, o) :: Fr).
    constructor.
    rewrite H0.
    apply lookup_app.
    generalize (IHt _ ((v1, o) :: Fr) H0). intro Hrec.
    rewrite rev_involutive in Hrec.
    eauto.
    rewrite <- app_assoc. f_equal.

  - assert (Hrlen: length (rev F) = length F) by (eapply rev_length).
    assert (Hcons: exists x F', rev F = x :: F').
    destruct (rev F); simpl in * |- *; try omega; eexists; eauto.
    destruct Hcons as [ x Hcons ].
    destruct Hcons as [ F' Hcons ].
    rewrite Hcons.
    destruct x.
    assert (Hlast: F = rev F' ++ (v, o) :: nil).
    replace ((v, o) :: F') with (rev (rev ((v, o) :: F'))) in Hcons.
    apply rev_injective; eauto.
    apply rev_involutive.
    rewrite Hlast in He |- *.
    rewrite app_length in He.
    rewrite Nat.add_comm in He.
    simpl in He.
    inverse He.
    replace ((rev F' ++ (v, o) :: nil) ++ Fr)
       with (rev F' ++ (v, o) :: Fr).
    constructor.
    rewrite H0.
    apply lookup_app.
    generalize (IHt _ ((v, o) :: Fr) H0). intro Hrec.
    rewrite rev_involutive in Hrec.
    eauto.
    rewrite <- app_assoc. f_equal.
Qed.

Lemma depth_of_term_graft:
  forall ctx t, depth_of_term (graft ctx t) = depth_of_term ctx + depth_of_term t.
Proof.
  induction ctx; simpl; eauto.
Qed.

Lemma length_of_eval_context:
  forall t dE dE',
  [[ dE ⊢ derive t ⇑ dE' ]] ->
  depth_of_term t = List.length dE'.
Proof.
  induction t; intros * Hd; inverse Hd; simpl in * |- *; eauto.
  rewrite (IHt _ _ H3). rewrite app_length. simpl. omega.
  rewrite (IHt _ _ H1). rewrite app_length. simpl. omega.
Qed.

Lemma cts_denvironment_preserves_length:
  forall dE, List.length dE = List.length (cts_denvironment dE).
Proof.
  unfold cts_denvironment. intros. rewrite map_length. eauto.
Qed.

Lemma cts_environment_preserves_length:
  forall E, List.length E = List.length (cts_environment E).
Proof.
  unfold cts_environment. intros. rewrite map_length. eauto.
Qed.

Lemma cts_denvironment_original_environment:
  forall { dE },
    cts_environment ⌊ dE ⌋ = ⌊# cts_denvironment dE ⌋.
Proof.
  intros.
  unfold
    cts_environment, cts_denvironment,
    LambdaALOperationalSemantics.original_environment, original_environment.
  unfold cts_dbinding, cts_binding.
  do 2 rewrite map_map.
  eapply map_equiv. eauto.
Qed.

Definition binding u :=
  (exists f x, u = @(f, x)) \/ (exists xs, u = ttuple xs).

(* precondition: u is a binding. *)
Definition derive_binding u :=
  match u with
    | Def f x t => LambdaAL.dcall f x
    | DefTuple xs t => LambdaAL.dttuple (List.map d xs)
    | _ => dVar (d (Index.Idx 0)) (* Unused case. *)
  end.

Definition compile_binding u :=
  match u with
    | Def f x t => ILambdaAL.call f x
    | DefTuple xs t => ILambdaAL.tuple xs
    | _ => ILambdaAL.IResult (Index.Idx 0) nil (* Unused case. *)
  end.

Lemma depth_of_binding:
  forall b, binding b -> depth_of_term b = 1.
Proof.
  intros b Hb; destruct Hb.
  -  do 2 destruct H; subst; easy.
  - destruct H; subst; easy.
Qed.

Lemma uncts_term_cts_term:
  forall u t, uncts_term (cts_term_aux u t) = t.
Proof.
  induction t; easy.
Qed.

Lemma uncts_value_cts_value:
  forall { v },
    uncts_value (cts_value v) = v
with uncts_values_cts_values:
  forall { vs },
    uncts_values (cts_values vs) = vs.
Proof.
  * intro v. destruct v; simpl in * |- *.
  - rewrite uncts_values_cts_values.
    rewrite uncts_term_cts_term. reflexivity.
  - rewrite uncts_values_cts_values. reflexivity.
  - reflexivity.
  - reflexivity.
  * intro vs. destruct vs. reflexivity.
    simpl. rewrite uncts_values_cts_values. rewrite uncts_value_cts_value.
    reflexivity.
Qed.

Lemma cts_value_injective:
  forall v v', cts_value v = cts_value v' -> v = v'.
Proof.
  intros.
  rewrite <- uncts_value_cts_value.
  rewrite <- (uncts_value_cts_value (v := v')).
  rewrite H.
  eauto.
Qed.

Lemma move_cts_value:
  forall { v dv v' },
    LambdaALOperationalSemantics.move v dv = Some v' ->
    move (cts_value v) (cts_dvalue dv) = Some (cts_value v')
with move_cts_values:
  forall { vs dvs vs' },
    LambdaALOperationalSemantics.move_values vs dvs = Some vs' ->
    move_values (cts_values vs) (cts_dvalues dvs) = Some (cts_values vs')
with move_closure_environments:
  forall { E dE E' },
     LambdaALOperationalSemantics.move_closure_environment E dE = Some E' ->
     move_closure_environment (cts_values E) (cts_closure_denvironment dE)
                              = Some (cts_values E').
Proof.
  - introv Hplus.
    destruct v;
      destruct dv; inverts Hplus; simpl_inv_mbind_some; try reflexivity; simpl_unfold_err_mbind.
    + erewrite move_closure_environments.
      all: (reflexivity || eassumption).
    + erewrite move_cts_values.
      all: (reflexivity || eassumption).
    + unfold LambdaALOperationalSemantics.move_literal in *.
      match_case_analysis.
      simpl_inv_mbind_some.
      reflexivity.
  - induction vs; destruct dvs; simpl in *; introv Hplus; inverse Hplus; try reflexivity.
    simpl_inv_mbind_some.
    erewrite move_cts_value.
    erewrite IHvs.
    all: (reflexivity || eassumption).
  - induction E; destruct dE; simpl in *; introv Hplus; inverse Hplus; try reflexivity.
    simpl_inv_mbind_some.
    erewrite move_cts_value.
    erewrite IHE.
    all: (reflexivity || eassumption).
Qed.

Lemma cts_denvironment_modified_environment:
  forall { dE E F },
    ⌈ dE ⌉ = Some E ->
    ⌈# cts_denvironment dE ⌉ = Some F ->
    cts_environment E = F.
Proof.
  unfold
    cts_environment, cts_denvironment,
    LambdaALOperationalSemantics.modified_environment, modified_environment.
  unfold cts_dbinding, cts_binding, modified_binding.
  induction dE; intros; simpl in * |- *.
  - inverse H. inverse H0. eauto.
  - destruct a. simpl in * |-.
    case_eq (LambdaALOperationalSemantics.move v d). intros.
    rewrite H1 in H.
    rewrite (move_cts_value H1) in H0. simpl in * |-.
    destruct (inv_success_mbind H). rewrite H2 in H. simpl in H. inverse H.
    destruct (inv_success_mbind H0). rewrite H3 in H0. simpl in H0. inverse H0.
    simpl.
    erewrite IHdE; eauto.
    intro. rewrite H1 in H. simpl in H. congruence.
Qed.

Lemma cts_denvironment_modified_environment2:
  forall { dE E },
    ⌈ dE ⌉ = Some E ->
    ⌈# cts_denvironment dE ⌉ = Some (cts_environment E).
Proof.
  induction dE; simpl; intros; eauto.
  unfold LambdaALOperationalSemantics.modified_environment in H.
  simpl in H. inverse H. simpl. eauto.
  unfold modified_environment.
  destruct a.
  unfold LambdaALOperationalSemantics.modified_environment in H.
  simpl in H.
  destruct (inv_success_mbind H).
  rewrite H0 in H. simpl in H.
  destruct (inv_success_mbind H).
  generalize (IHdE _ H1).
  intro Hm. unfold modified_environment in Hm.
  rewrite H1 in H. inverse H. unfold cts_environment.
  rewrite map_cons.
  erewrite (list_map_cons _ _ _ (map cts_binding x0) (cts_binding x)); eauto.
  unfold modified_binding. simpl.
  rewrite (move_cts_value H0). simpl.
  eauto.
Qed.

Lemma eval_context_length:
  forall {ctx E E'},
    [E ⊢ ctx ⇑ E'] -> depth_of_term ctx = length E'.
Proof.
  induction ctx; intros * Hctx; inverse Hctx; simpl; eauto.
  rewrite (IHctx _ _ H4). rewrite app_length. simpl. omega.
  rewrite (IHctx _ _ H2). rewrite app_length. simpl. omega.
Qed.

Lemma eval_context_ended_with_tuple:
  forall {ctx E E'},
    [E ⊢ ctx ⇑ E'] ->
    forall {vs xs},
    lookups (E' ++ E) xs = Some vs ->
    [E ⊢ graft ctx (ttuple xs) ⇑ LambdaALValues.tuple vs :: E'].
Proof.
  intros * Hctx; induction Hctx; intros * Hl; simpl in * |- *; eauto.
  - replace (LambdaALValues.tuple vs :: nil) with (nil ++ (LambdaALValues.tuple vs) :: nil).
    constructor.
    eapply SNilContext.
    unfold ttuple.
    eapply (STuple NoSteps); eauto.
    eapply (SVar NoSteps); eauto.
    simpl. eauto.
  - rewrite app_comm_cons.
    econstructor.
    eapply IHHctx; eauto.
    replace ((E' ++ v :: nil) ++ E) with (E' ++ v :: E) in Hl.
    eauto.
    rewrite <- app_assoc. simpl. eauto.
    eauto.
  - rewrite app_comm_cons.
    econstructor.
    eapply IHHctx; eauto.
    replace ((E' ++ v :: nil) ++ E) with (E' ++ v :: E) in Hl.
    eauto.
    rewrite <- app_assoc. simpl. eauto.
    eauto.
Qed.

Lemma eval_context_ended_with_call:
  forall {ctx E E'},
    [E ⊢ ctx ⇑ E'] ->
    forall {v f x},
      [E' ++ E ⊢ @(f, x) ⇓ v ] ->
      [E ⊢ graft ctx @(f, x) ⇑ v :: E'].
Proof.
  intros * Hctx; induction Hctx; intros * Hl; simpl in * |- *; eauto.
  - replace (v :: nil) with (nil ++ v :: nil).
    constructor; eauto.
    eapply SNilContext; eauto.
    simpl. eauto.
  - rewrite app_comm_cons.
    econstructor.
    eapply IHHctx; eauto.
    replace ((E' ++ v :: nil) ++ E) with (E' ++ v :: E) in Hl.
    eauto.
    rewrite <- app_assoc. simpl. eauto.
    eauto.
  - rewrite app_comm_cons.
    econstructor.
    eapply IHHctx; eauto.
    replace ((E' ++ v :: nil) ++ E) with (E' ++ v :: E) in Hl.
    eauto.
    rewrite <- app_assoc. simpl. eauto.
    eauto.
Qed.

Lemma list_of_closure_environment_cts_environment:
  forall Ef,
    list_of_closure_environment (cts_values (LambdaALValues.values_of_list Ef)) =
    cts_environment Ef.
Proof.
  induction Ef; simpl; eauto.
  unfold cts_binding. rewrite IHEf. eauto.
Qed.

Lemma eval_cache_strenghening:
  forall {C F F' v VC'},
    eval_cache (F' ++ bind F (v, None)) C VC' ->
    forall VC, exists VC'', eval_cache (F' ++ bind F (v, Some VC)) C VC''.
Proof.
  induction C; intros * He; intro VC; inverse He; simpl in * |- *; eauto.
  eexists. econstructor.
  destruct (IHC _ _ _ _ H4  VC).
  destruct x0.
  destruct x.
  destruct (Environment.focus_lookup F' F (v, None) (v, Some VC) n); splitHyps; unfold bind in *.
  - exists (CacheValue ((V, Some VC) :: l)).
    constructor; eauto;
    congruence.
  - exists (CacheValue ((V, VCx) :: l)).
    constructor; eauto;
    congruence.
Qed.

Lemma lookup_value_is_cache_independent:
  forall {F F' v VC VC' x},
    lookup_value (F ++ (v, VC) :: F') x = lookup_value (F ++ (v, VC') :: F') x.
Proof.
  intros. destruct x.
  destruct (Environment.focus_lookup F F' (v, VC) (v, VC') n); unfold lookup_value; splitHyps.
  - rewrite H0. rewrite H1. eauto.
  - rewrite H0. eauto.
Qed.

Lemma lookup_values_is_cache_independent:
  forall {xs F F' v VC VC'},
    lookup_values (F ++ (v, VC) :: F') xs = lookup_values (F ++ (v, VC') :: F') xs.
Proof.
  induction xs; simpl; intros; eauto.
  destruct a.
  destruct (Environment.focus_lookup F F' (v, VC) (v, VC') n); splitHyps.
  do 2 rewrite lookup_values_unfold.
  rewrite (lookup_value_is_cache_independent (VC:=VC) (VC':=VC')).
  destruct (lookup_value (F ++ (v, VC') :: F') (Idx n)); simpl; eauto.
  rewrite (IHxs F F' v VC VC').
  eauto.
  do 2 rewrite lookup_values_unfold.
  rewrite (lookup_value_is_cache_independent (VC:=VC) (VC':=VC')).
  destruct (lookup_value (F ++ (v, VC') :: F') (Idx n)); simpl; eauto.
  rewrite (IHxs F F' v VC VC').
  eauto.
Qed.

Lemma cache_strenghening:
  forall {t F F' v VC VC' v'},
    [# F' ++ bind F (v, None) ⊢ t ⇓ (v', VC') ] ->
    exists VC'', [# F' ++ bind F (v, Some VC) ⊢ t ⇓ (v', VC'') ].
Proof.
  unfold bind.
  induction t; intros * He; inverse He; simpl in * |- *; eauto.
  - destruct (eval_cache_strenghening H5 VC).
    exists x.
    destruct v.
    destruct (Environment.focus_lookup F' F (v0, None) (v0, Some VC) n); splitHyps.
    + econstructor; eauto.
      rewrite H2. rewrite H1 in H3. injections_some. eauto.
    + econstructor; eauto.
      rewrite <- H1. eauto.
  - unfold bind in H7.
    rewrite app_comm_cons in H7.
    destruct (IHt _ _ _ VC _ _ H7) as [ VC'' Hr ].
    eexists. eapply TPrimitiveCall; eauto.
    erewrite lookup_value_is_cache_independent. eauto.
    erewrite lookup_value_is_cache_independent. eauto.
  - unfold bind in H7.
    rewrite app_comm_cons in H7.
    destruct (IHt _ _ _ VC _ _ H7) as [ VC'' Hr ].
    eexists. eapply TClosureCall; eauto.
    erewrite lookup_value_is_cache_independent. eauto.
    erewrite lookup_value_is_cache_independent. eauto.
  - unfold bind in H4.
    rewrite app_comm_cons in H4.
    destruct (IHt _ _ _ VC _ _ H4) as [ VC'' Hr ].
    eexists. eapply TTuple; eauto.
    rewrite (lookup_values_is_cache_independent (VC:=Some VC) (VC':=None)).
    eauto.
Qed.

Lemma eval_add_cts_value:
  forall {vx v'},
    LambdaALOperationalSemanticsPrimitives.eval_add vx = Some v' ->
    exists VC, eval_add (cts_value vx) = Some (cts_value v', VC).
Proof.
  intros. funelim (LambdaALOperationalSemanticsPrimitives.eval_add vx); try simpl_unfold_err; easy.
  inv_mbind_some. eexists; eauto.
Qed.

Lemma eval_push_cts_value:
  forall {vx v'},
    LambdaALOperationalSemanticsPrimitives.eval_push vx = Some v' ->
    exists VC, eval_push (cts_value vx) = Some (cts_value v', VC).
Proof.
  intros. funelim (LambdaALOperationalSemanticsPrimitives.eval_push vx); try simpl_unfold_err; easy.
  inv_mbind_some. eexists; eauto.
Qed.

Lemma eval_curry_cts_value:
  forall {vx v'},
    LambdaALOperationalSemanticsPrimitives.eval_curry vx = Some v' ->
    exists VC, eval_curry (cts_value vx) = Some (cts_value v', VC).
Proof.
  intros. funelim (LambdaALOperationalSemanticsPrimitives.eval_curry vx); try simpl_unfold_err; easy.
  inv_mbind_some. eexists; eauto.
Qed.

Lemma eval_fixrec_cts_value:
  forall {vx v'},
    LambdaALOperationalSemanticsPrimitives.eval_fixrec vx = Some v' ->
    exists VC, eval_fixrec (cts_value vx) = Some (cts_value v', VC).
Proof.
  intros. funelim (LambdaALOperationalSemanticsPrimitives.eval_fixrec vx); try simpl_unfold_err; easy.
  inv_mbind_some. eexists; eauto.
Qed.

Lemma eval_primitive_cts_value:
  forall {vx p v'},
    LambdaALOperationalSemanticsPrimitives.eval_primitive p vx = Some v' ->
    exists VC, eval_primitive p (cts_value vx) = Some (cts_value v', VC).
Proof.
  intros.
  destruct p; [ eapply eval_add_cts_value 
              | eapply eval_push_cts_value 
              | eapply eval_curry_cts_value 
              | eapply eval_fixrec_cts_value 
              ]; eauto.
Qed.

Lemma recompute_primitive_eq:
  forall {p v dv v' vy VC},
    v ⊕ dv = Some v' ->
    eval_primitive p v' = Some (vy, VC) ->
    recompute_primitive p v dv = Some (dIReplace vy, VC).
Proof.
  intros.
  unfold recompute_primitive. rewrite H. simpl. rewrite H0. eauto.
Qed.

Lemma correct_recompute:
  forall p vx vy dvx dvy vx' VCy VCy' vy' VX DVX DVY,
  LambdaALOperationalSemanticsPrimitives.eval_primitive p vx = Some vy ->
  LambdaALOperationalSemantics.recompute_primitive p vx dvx = Some dvy ->
  eval_primitive p (cts_value vx) = Some (cts_value vy, VCy) ->
  eval_primitive p (cts_value vx') = Some (cts_value vy', VCy') ->
  cts_value vx ⊕ cts_dvalue dvx = Some (cts_value vx') ->
  cts_value vy ⊕ cts_dvalue dvy = Some (cts_value vy') ->
  VX = cts_value vx ->
  DVX = cts_dvalue dvx ->
  DVY = cts_dvalue dvy ->
  recompute_primitive p VX DVX = Some (DVY, VCy').
Proof.
  intros.
  unfold LambdaALOperationalSemantics.recompute_primitive, recompute_primitive in * |- *.
  subst. rewrite H3. simpl. rewrite H2. simpl.
  case_eq (LambdaALOperationalSemantics.move vx dvx). intros * Hmoveorg.
  rewrite Hmoveorg in H0. simpl in H0.
  assert (v = vx'). {
    rewrite (move_cts_value Hmoveorg) in H3.
    eapply cts_value_injective.
    easy.
  }
  subst.
  case_eq (LambdaALOperationalSemanticsPrimitives.eval_primitive p vx').
  intros * Hevalprim'.
  destruct (eval_primitive_cts_value Hevalprim') as [ VX' HVX' ].
  rewrite HVX' in H2. inverse H2.
  rewrite Hevalprim' in H0. simpl in H0. inverse H0.
  simpl in H4. rewrite move_replace in H4. 
  eauto.
  intro Hr. rewrite Hr in H0. easy.
  intro Hr. rewrite Hr in H0. easy.
Qed.

Definition correct_dprimitive p :=
  forall vx vy dvx dvy vx' VCy VCy' vy',
  LambdaALOperationalSemanticsPrimitives.eval_primitive p vx = Some vy ->
  LambdaALOperationalSemantics.eval_dprimitive p vx dvx = Some dvy ->
  eval_primitive p (cts_value vx) = Some (cts_value vy, VCy) ->
  eval_primitive p (cts_value vx') = Some (cts_value vy', VCy') ->
  cts_value vx ⊕ cts_dvalue dvx = Some (cts_value vx') ->
  cts_value vy ⊕ cts_dvalue dvy = Some (cts_value vy') ->
  eval_dprimitive p (cts_value vx) (cts_dvalue dvx) VCy = Some (cts_dvalue dvy, VCy').

Lemma correct_dprimitive_add : correct_dprimitive Constants.Add.
Proof.
  unfold correct_dprimitive. intros * Hevalo Hdevalo Heval Heval' Hmovex Hmovey.
  simpl in Hevalo, Hdevalo.
  generalize (recompute_primitive_eq Hmovex Heval'); intro Hrecompute.

  funelim (LambdaALOperationalSemantics.eval_dadd vx dvx);
    try solve [ simpl_unfold_err; congruence ].

  - inverse Hmovex. inverse Hdevalo. simpl. rewrite <- H0 in Heval'. simpl in * |- *.
    inverse Heval'. eauto.

  - simpl in * |- *. eapply correct_recompute; eauto.
    simpl. destruct l; easy.

  - simpl in * |- *. eapply correct_recompute; eauto.
    simpl. destruct l; easy.

  - simpl in * |- *. eapply correct_recompute; eauto.
    simpl. inverse Heval. easy.
Qed.

Lemma correct_dprimitive_curry : correct_dprimitive Constants.Curry.
Proof.
  unfold correct_dprimitive. intros. eapply correct_recompute; eauto.
Qed.

Lemma correct_dprimitive_push : correct_dprimitive Constants.Push.
Proof.
  unfold correct_dprimitive. intros. eapply correct_recompute; eauto.
Qed.

Lemma correct_dprimitive_fixrec : correct_dprimitive Constants.FixRec.
Proof.
  unfold correct_dprimitive. intros. eapply correct_recompute; eauto.
Qed.

Lemma eval_dprimitive_cts_value:
  forall {p vx vy dvx dvy vx' VCy VCy' vy'},
  LambdaALOperationalSemanticsPrimitives.eval_primitive p vx = Some vy ->
  LambdaALOperationalSemantics.eval_dprimitive p vx dvx = Some dvy ->
  eval_primitive p (cts_value vx) = Some (cts_value vy, VCy) ->
  eval_primitive p (cts_value vx') = Some (cts_value vy', VCy') ->
  cts_value vx ⊕ cts_dvalue dvx = Some (cts_value vx') ->
  cts_value vy ⊕ cts_dvalue dvy = Some (cts_value vy') ->
  eval_dprimitive p (cts_value vx) (cts_dvalue dvx) VCy = Some (cts_dvalue dvy, VCy').
Proof.
  unfold correct_dprimitive; destruct p; [
     eapply correct_dprimitive_add
   | eapply correct_dprimitive_push
   | eapply correct_dprimitive_curry
   | eapply correct_dprimitive_fixrec
  ].
Qed.

Lemma eval_cts_compat_gen:
  forall {n E E' t u v ctx},
    [ E' ++ E ⊢ u ⇓ v @ n ] ->
    t = graft ctx u ->
    [ E ⊢ ctx ⇑ E' ] ->
    exists VC,
    [# cts_environment E' ++ cts_environment E ⊢ cts_term_aux t u ⇓ (cts_value v, VC) ].
Proof.
  intro n.
  eapply (lt_wf_ind n). clear n. intros n Hrec; intros * He Hg Hc; inverse He; simpl in * |- *.

  - eexists. econstructor; eauto.
    rewrite <- cts_environment_app.
    eapply cts_environment_lookup; eauto.
    eapply cache_of_term_reverse_environment.
    rewrite <- cts_environment_preserves_length.
    rewrite depth_of_term_graft. simpl.
    rewrite Nat.add_0_r.
    eapply eval_context_length.
    eauto.
  - unfold bind in H0. rewrite app_comm_cons in H0.
    rewrite graft_tuple.
    assert (Hn: n0 < S n0) by auto.
    destruct (Hrec _ Hn _ _ _ _ _ (graft ctx (ttuple xs)) H0 (@refl_equal _ _)).
    eapply eval_context_ended_with_tuple; eauto.
    exists x.
    eapply TTuple; eauto.
    generalize (cts_environment_lookups H).
    intro Hls. unfold lookup_values.
    rewrite <- cts_environment_app.
    rewrite Hls.
    simpl. eauto.
    simpl in H0.
    replace (cts_environment (LambdaALValues.tuple vs :: E') ++ cts_environment E)
      with (bind (cts_environment E' ++ cts_environment E)
                 (ITuple (values_of_list (map fst (map cts_binding vs))), None)) in H1.
    eauto.
    unfold bind, cts_environment, cts_binding.
    repeat (f_equal; simpl).
    eapply cts_values_cts_binding.

  - assert (Hn0 : n0 < S n0) by auto.
    destruct (eval_primitive_cts_value H1). eauto.
    destruct (Hrec _ Hn0 E (bind E' v') (graft ctx (Def f x t0)) t0 v (graft ctx @(f, x))).
    unfold bind. rewrite <- app_comm_cons. eauto.
    eapply graft_def.
    eapply eval_context_ended_with_call; eauto.
    eapply (SPrimitiveCall NoSteps); eauto.
    eapply complete_eval; eauto.
    econstructor. simpl. eauto.
    destruct (cache_strenghening H4 (F' := nil) (VC := x0)) as [ VC ].
    exists VC.
    eapply TPrimitiveCall.
    rewrite <- cts_environment_app.
    generalize (cts_environment_lookup H).
    unfold cts_binding. simpl. intro Hlf. unfold lookup_value. rewrite Hlf.
    simpl. eauto.
    rewrite <- cts_environment_app.
    generalize (cts_environment_lookup H0).
    unfold cts_binding. simpl. intro Hlf. unfold lookup_value. rewrite Hlf.
    simpl. eauto.
    eauto.
    eauto.

  - assert (Hn0 : n0 < S (n0 + m)) by omega.
    assert (Hm : m < S (n0 + m)) by omega.
    assert (Hnil: [bind Ef vx ⊢ Var (Idx 0) ⇑ nil]). constructor.
    destruct (Hrec _ Hn0 _ nil _ _ _ (Var (Idx 0)) H1 (@refl_equal _ _) Hnil) as [VCF Hf].
    destruct (Hrec _ Hm E (bind E' vy) (graft ctx (Def f x t0)) t0 v (graft ctx (@(f, x)))).
    unfold bind. rewrite <- app_comm_cons.
    eauto.
    eapply graft_def.
    eapply eval_context_ended_with_call; eauto.
    eapply (SClosureCall NoSteps); eauto.
    eapply complete_eval; eauto.
    eapply complete_eval; eauto.
    econstructor. simpl. eauto.
    destruct (cache_strenghening H3 (F' := nil) (VC := VCF)) as [ VC ].
    exists VC.
    eapply TClosureCall.
    rewrite <- cts_environment_app.
    generalize (cts_environment_lookup H).
    unfold cts_binding. simpl. intro Hlf. unfold lookup_value. rewrite Hlf.
    simpl. eauto.
    rewrite <- cts_environment_app.
    generalize (cts_environment_lookup H0).
    unfold cts_binding. simpl. intro Hlf. unfold lookup_value. rewrite Hlf.
    simpl. eauto.
    simpl in Hf.
    replace (cts_binding vx :: cts_environment Ef)
      with ((cts_value vx, None)
    :: list_of_closure_environment (cts_values (LambdaALValues.values_of_list Ef))) in Hf.
    eauto.
    f_equal.
    eapply list_of_closure_environment_cts_environment.
    replace (cts_environment (bind E' vy) ++ cts_environment E)
      with (bind (cts_environment E' ++ cts_environment E) (cts_value vy, None))
      in H3.
    eauto.
    unfold bind, cts_environment, cts_binding.
    simpl.
    eauto.
    Unshelve. all: exact 0.
Qed.

Lemma eval_cts_compat_gen_nosteps:
  forall {E E' t u v ctx},
    [ E' ++ E ⊢ u ⇓ v ] ->
    t = graft ctx u ->
    [ E ⊢ ctx ⇑ E' ] ->
    exists VC,
    [# cts_environment E' ++ cts_environment E ⊢ cts_term_aux t u ⇓ (cts_value v, VC) ].
Proof.
  intros * Heval. destruct (sound_eval _ _ _ Heval) as [ n Hevals ].
  eapply (eval_cts_compat_gen Hevals).
Qed.

Lemma eval_cts_compat:
  forall {E u v},
    [ E ⊢ u ⇓ v ] ->
    exists VC,
    [# cts_environment E ⊢ cts_term_aux u u ⇓ (cts_value v, VC) ].
Proof.
  intros * He.
  assert (Hu : u = graft (Var (Idx 0)) u). simpl. eauto.
  assert (Hnil : [ E ⊢ Var (Idx 0) ⇑ nil ]). constructor.
  destruct (sound_eval _ _ _ He) as [ n Hee ].
  destruct (eval_cts_compat_gen (ctx := Var (Idx O)) (E' := nil) Hee Hu Hnil).
  simpl in H.
  eexists. eauto.
Qed.

Lemma cts_values_cts_denvironment:
  forall {dEf},
    cts_values (LambdaALValues.values_of_list ⌊ dEf ⌋) =
    closure_environment_of_list ⌊# cts_denvironment dEf ⌋.
Proof.
  intro dEf.
  rewrite cts_values_cts_dbinding.
  rewrite map_map. rewrite map_map.
  unfold cts_dbinding. simpl.
  induction dEf; simpl; eauto.
  f_equal. rewrite IHdEf. eauto.
Qed.

Lemma original_cts_denvironment_has_no_cache:
  forall {dE},
    has_no_cache ⌊# cts_denvironment dE ⌋.
Proof.
  induction dE; simpl; econstructor; eauto.
Qed.

Lemma cts_environment_has_no_cache:
  forall {E},
    has_no_cache (cts_environment E).
Proof.
  induction E; simpl; econstructor; eauto.
Qed.

Lemma cts_closure_denvironment_cts_denvironment:
  forall {dE},
    list_of_closure_denvironment
    (cts_closure_denvironment (LambdaALValues.closure_denvironment_of_list dE))
    = cts_denvironment dE.
Proof.
  induction dE; simpl; eauto.
  destruct a. simpl. rewrite <- IHdE.
  eauto.
Qed.

Lemma move_closure_environment_cts_denvironment:
  forall {dEf E''},
    ⌈ dEf ⌉ = Some E'' ->
    move_closure_environment 
      (closure_environment_of_list ⌊# cts_denvironment dEf ⌋)
      (cts_closure_denvironment (LambdaALValues.closure_denvironment_of_list dEf)) 
    = Some (closure_environment_of_list (cts_environment E'')).
Proof.
  induction dEf; simpl; intros; eauto.
  inverse H. simpl. eauto.
  destruct a. simpl.
  unfold LambdaALOperationalSemantics.modified_environment in H. simpl in H.
  destruct (inv_success_mbind H). rewrite H0 in H. simpl in H.
  destruct (inv_success_mbind H). rewrite H1 in H. simpl in H.
  inverse H. 
  rewrite (move_cts_value H0). simpl.
  rewrite (IHdEf _ H1). simpl.
  eauto.
Qed.

Lemma eval_cache_of_cts_term:
  forall {u F t V VC},
    [# F ⊢ cts_term_aux t u ⇓ (V, VC) ] ->
    exists F', eval_cache F' (cache_of_term t) VC.
Proof.
  induction u; simpl in * |- *; intros.
  - inverse H. eexists. eauto.
  - inverse H. 
    ** eapply (IHu _ _ _ _ H8). 
    ** eapply (IHu _ _ _ _ H8).
  - inverse H. eapply (IHu _ _ _ _ H5).
Qed.