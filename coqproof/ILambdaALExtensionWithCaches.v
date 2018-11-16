(** * Soundness of CTS differentiation. *)
Require Import Program.
Require Import List.
Require Import Omega.
Require Import LibTactics.
Require Import Environment.
Require Import ErrorMonad.
Require Import Misc.
Require Import LambdaAL.
Require Import LambdaALOperationalSemantics.
Require Import LambdaALOperationalSemanticsProofs.
Require Import LambdaALDerive.
Require Import LambdaALValidity.
Require Import LambdaALEnvValidity.
Require Import LambdaALFundamentalProperty.
Require Import LambdaALDeriveProofs.
Require Import ILambdaAL.
Require Import ILambdaALValues.
Require Import ILambdaALOperationalSemantics.
Require Import ILambdaALDerive.
Require Import ILambdaALOperationalSemanticsProofs.
Require Import ILambdaALCTSProofs.

(**

   The compilation of environments of the source language produces
   environments of the target language that miss caches.

   The following judgment extends the compiled environments
   into compiled environments that contain caches.

*)

Reserved Notation "[ F0 ⊢ F ↑ ctx ⇾ F' ]".

Inductive base_extended_with_cache
: environment -> environment -> LambdaAL.context -> environment -> Prop :=
| BExtendNil: forall F0 x,
    [ F0 ⊢ nil ↑ (Var x) ⇾ nil ]
(** An empty environment is not extended. *)

| BExtendWithTuple: forall F0 V F ctx xF xs,
    [ (V, None) :: F0 ⊢ F ↑ ctx ⇾ xF ] ->
    [ F0 ⊢ (V, None) :: F ↑ DefTuple xs ctx ⇾ (V, None) :: xF ]
(** Tuples have no associated cache. *)

| BExtendWithOldDef: forall F0 V F f x ctx VC xF,
    [# F0 ⊢ @#(f, x) ⇓ (V, CacheValue (cons (V, Some VC) nil))] ->
    [ (V, Some VC) :: F0 ⊢ F ↑ ctx ⇾ xF ] ->
    [ F0 ⊢ (V, None) :: F ↑ Def f x ctx ⇾ (V, Some VC) :: xF ]
(** In the original environment, for function calls, we compute the
    function call under the original environment ⌊# dF0 ⌋ = F' and
    inject the computed cache in the extended change environment. *)

where "[ F0 ⊢ F ↑ ctx ⇾ F' ]" := (base_extended_with_cache F0 F ctx F').

(**

   Assume that [dF] is the change environment obtained by the
   compilation of the values bound during the evaluation of the
   [LambdaAL.context] [ctx], i.e.:

                      [dF0 ⊢ ctx ⇑ dF ]

   then the following relation:

                      [dF0 ⊢ dF ↑ ctx ⇾ dF']

   extends [dF] with the caches for the function calls of the context
   [ctx]. These caches are computed under the modified environment,
   extracted from the change environment [dF0].

*)
Reserved Notation "[[ k # dF0 ⊢ dF ↑ ctx ⇾ dF' ]]".

Inductive extension := New | Old.

Inductive extended_with_cache
: extension -> denvironment -> denvironment -> LambdaAL.context -> denvironment -> Prop :=
| ExtendNil: forall dF0 x k,
    [[ k # dF0 ⊢ nil ↑ (Var x) ⇾ nil ]]
(** An empty environment is not extended. *)

| ExtendWithTuple: forall k dF0 V dV dF ctx xdF xs,
    [[ k # ((V, None), dV) :: dF0 ⊢ dF ↑ ctx ⇾ xdF ]] ->
    [[ k # dF0 ⊢ postbind dF ((V, None), dV) ↑ DefTuple xs ctx
         ⇾ postbind xdF ((V, None), dV) ]]
(** Tuples have no associated cache. *)

| ExtendWithNewDef: forall dF0 V dV dF f x ctx VC0 VC xdF F' V',
    ⌈# dF0 ⌉ = Some F' ->
    [# F' ⊢ @#(f, x) ⇓ (V', CacheValue [(V', Some VC)]) ] ->
    move V dV = Some V' ->
    [[ New # (V, Some VC, dV) :: dF0 ⊢ dF ↑ ctx ⇾ xdF ]] ->
    [[ New # dF0 ⊢ postbind dF ((V, VC0), dV) ↑ Def f x ctx
           ⇾ postbind xdF ((V, Some VC), dV) ]]
(** In the updated environment, for function calls, we compute the
    function call under the modified environment ⌈# dF0 ⌉ = F' and
    inject the computed cache in the extended change environment. *)

| ExtendWithOldDef: forall dF0 V dV dF f x ctx VC0 VC xdF F',
    ⌊# dF0 ⌋ = F' ->
    [# F' ⊢ @#(f, x) ⇓ (V, CacheValue [(V, Some VC)])] ->
    [[ Old # (V, Some VC, dV) :: dF0 ⊢ dF ↑ ctx ⇾ xdF ]] ->
    [[ Old # dF0 ⊢ postbind dF ((V, VC0), dV) ↑ Def f x ctx
           ⇾ postbind xdF ((V, Some VC), dV) ]]
(** In the original environment, for function calls, we compute the
    function call under the original environment ⌊# dF0 ⌋ = F' and
    inject the computed cache in the extended change environment. *)

where "[[ kind # dF0 ⊢ dF ↑ ctx ⇾ dF' ]]" := (extended_with_cache kind dF0 dF ctx dF').

Definition extended_environment k dF F :=
  match k with
    | New => ⌈# dF ⌉ = Some F
    | Old => ⌊# dF ⌋ = F
  end.

Definition denvironment_equivalent_modulo_caches (dF dF' : denvironment) :=
    List.map (fun x => fst (fst x)) dF = List.map (fun x => fst (fst x)) dF' /\
    List.map snd dF = List.map snd dF'.

Definition denvironment_equivalent_modulo_caches_extend:
  forall {dF dF' dF0},
    denvironment_equivalent_modulo_caches dF dF' ->
    denvironment_equivalent_modulo_caches (dF ++ dF0) (dF' ++ dF0).
Proof.
  unfold denvironment_equivalent_modulo_caches.
  intros. intuition.
  do 2 rewrite map_app. rewrite H0. auto.
  do 2 rewrite map_app. rewrite H1. auto.
Qed.

Lemma lookup_value_tail:
  forall x0 x1 n,
    lookup_value (x0 :: x1) (Index.Idx (S n)) = lookup_value x1 (Index.Idx n).
Proof.
  intros. unfold lookup_value. simpl.
  eauto.
Qed.

Lemma denvironment_equivalent_modulo_caches_lookup_value_original:
  forall {dF k dF' F F'},
    denvironment_equivalent_modulo_caches dF dF' ->
    extended_environment k dF F ->
    extended_environment k dF' F' ->
    forall x, lookup_value F x = lookup_value F' x.
Proof.
  induction dF; intros * Hequiv HF HF'; destruct k; destruct dF';
    unfold denvironment_equivalent_modulo_caches in Hequiv;
    simpl in * |- *; try congruence; intuition; try (inverse H || inverse H0).
  - unfold modified_environment in HF. simpl in HF.
    destruct (inv_success_mbind HF). rewrite H1 in HF. simpl in HF.
    destruct (inv_success_mbind HF). rewrite H4 in HF. simpl in HF.
    inverse HF.
    unfold modified_environment in HF'. simpl in HF'.
    destruct (inv_success_mbind HF'). rewrite H5 in HF'. simpl in HF'.
    destruct (inv_success_mbind HF'). rewrite H6 in HF'. simpl in HF'.
    inverse HF'.

    destruct x; destruct n; simpl in * |- *.
    inverse H0. destruct a. destruct p.
    simpl in * |- *. subst.
    unfold lookup_value. simpl. destruct p. destruct p0. simpl in * |- *. subst.
    destruct x0. destruct x2. simpl in * |- *. unfold modified_binding in * |- *.
    simpl in * |- *.
    destruct (v ⊕ d0); simpl in * |- *. inverse H1. inverse H5. eauto.
    congruence.

    do 2 rewrite lookup_value_tail.
    rewrite (IHdF New dF' _ x3); eauto.
    inverse H. unfold denvironment_equivalent_modulo_caches.
    inverse H0. intuition.
  - inverse H. inverse H0. destruct p. destruct a.
    simpl in * |- *. subst.
    destruct x. destruct n.
    unfold lookup_value in * |- *. simpl. congruence.

    do 2 rewrite lookup_value_tail.
    erewrite (IHdF Old) with (dF' := dF'); simpl; eauto.
    unfold denvironment_equivalent_modulo_caches.
    intuition.
Qed.

Lemma denvironment_equivalent_modulo_caches_lookup_original:
  forall {k dF dF' F F'},
    denvironment_equivalent_modulo_caches dF dF' ->
    extended_environment k dF F ->
    extended_environment k dF' F' ->
    forall {x V VC},
      lookup F x = Some (V, VC) ->
      exists VC', lookup F' x = Some (V, VC').
Proof.
  intros * Hequiv HF HF' x V VC Hl.
  generalize (denvironment_equivalent_modulo_caches_lookup_value_original Hequiv HF HF' x).
  unfold lookup_value. rewrite Hl. simpl.
  intro. symmetry in H. destruct (inv_success_mbind H). rewrite H0 in H. simpl in H.
  destruct x0. simpl in H. inverse H. eexists. eauto.
Qed.

Lemma denvironment_equivalent_modulo_caches_lookup_original_2:
  forall {k dF dF' F F'},
    denvironment_equivalent_modulo_caches dF dF' ->
    extended_environment k dF F ->
    extended_environment k dF' F' ->
    forall x, lookup F x = None ->
         lookup F' x = None.
Proof.
  intros * Hequiv HF HF' x.
  generalize (denvironment_equivalent_modulo_caches_lookup_value_original Hequiv HF HF' x).
  unfold lookup_value.
  intros.
  rewrite H0 in H. simpl in H.
  case_eq (lookup F' x); intros; simpl in * |- *.
  rewrite H1 in H. simpl in H. unfold ret in H. congruence.
  auto.
Qed.

Lemma denvironment_equivalent_modulo_caches_lookup_values_original:
  forall {k dF dF' F F'},
    denvironment_equivalent_modulo_caches dF dF' ->
    extended_environment k dF F ->
    extended_environment k dF' F' ->
    forall xs, lookup_values F xs = lookup_values F' xs.
Proof.
  intros * Heq HF HF'. induction xs; unfold lookup_values; simpl; eauto.
  case_eq (lookup_values F xs); intros.
  unfold lookup_values in IHxs, H.
  destruct (inv_success_mbind H). rewrite H0 in H. simpl in H. inverse H.
  rewrite H0 in IHxs. simpl in IHxs.
  symmetry in IHxs.
  destruct (inv_success_mbind IHxs). rewrite H1 in IHxs. simpl in IHxs.
  rewrite H0.
  rewrite H1.
  simpl.
  case_eq (lookup F a). intros.
  destruct p.
  destruct (denvironment_equivalent_modulo_caches_lookup_original Heq HF HF' H2).
  rewrite H3.
  simpl. unfold ret in IHxs. inverse IHxs. eauto. intro Hl.
  rewrite (denvironment_equivalent_modulo_caches_lookup_original_2 Heq HF HF' a Hl).
  simpl. eauto.
  rewrite H in IHxs.
  unfold lookup_values in * |-.
  destruct (lookups F xs);
  destruct (lookups F' xs); simpl in * |- *; unfold ret in * |-; try congruence; eauto.
Qed.

Lemma denvironment_equivalent_modulo_caches_eval_cache:
  forall {k c dF dF' VC F F'},
    denvironment_equivalent_modulo_caches dF dF' ->
    extended_environment k dF F ->
    extended_environment k dF' F' ->
    eval_cache F c VC ->
    exists VC', eval_cache F' c VC'.
Proof.
  induction c; intros * Hequiv HF HF' He.
  - eexists; econstructor; eauto.
  - inverse He.
    destruct (IHc _ _ _ _ _ Hequiv HF HF' H4).
    destruct (denvironment_equivalent_modulo_caches_lookup_original Hequiv HF HF' H2).
    destruct x0.
    eexists. econstructor; eauto.
Qed.

Lemma denvironment_equivalent_modulo_caches_original_evaluation:
  forall {k t V VC dF dF' F F'},
    denvironment_equivalent_modulo_caches dF dF' ->
    extended_environment k dF F ->
    extended_environment k dF' F' ->
    [# F ⊢ t ⇓ (V, VC) ] ->
    exists VC', [# F' ⊢ t ⇓ (V, VC') ].
Proof.
  induction t; intros * Hequiv HF HF' He; inverse He.

  - destruct (denvironment_equivalent_modulo_caches_lookup_original Hequiv HF HF' H3).
    destruct (denvironment_equivalent_modulo_caches_eval_cache Hequiv HF HF' H5); eauto.
    exists x0. econstructor; eauto.
  - destruct k; simpl in * |-; subst.
    * assert (Hb:
                ⌈# (V', Some VC', dIReplace V') :: dF ⌉ = Some (bind F (V', Some VC'))
             ).
      eapply modified_environment_bind; eauto; eapply move_replace.
      assert (Hb':
                ⌈# (V', Some VC', dIReplace V') :: dF' ⌉ = Some (bind F' (V', Some VC'))
             ).
      eapply modified_environment_bind; eauto; eapply move_replace.
      assert (Hequiv':
                denvironment_equivalent_modulo_caches
                  ((V', Some VC', dIReplace V') :: dF)
                  ((V', Some VC', dIReplace V') :: dF')).
      unfold denvironment_equivalent_modulo_caches in * |- *; simpl;
        intuition; try congruence.

      destruct (IHt _ _ _ _ _ _ Hequiv' Hb Hb' H7).
      eexists.

      eapply TPrimitiveCall; eauto.
      rewrite <- (denvironment_equivalent_modulo_caches_lookup_value_original (k := New) Hequiv HF HF' v); eauto.
      rewrite <- (denvironment_equivalent_modulo_caches_lookup_value_original (k := New) Hequiv HF HF' v0); eauto.

    * assert (Hb:
              bind ⌊# dF ⌋ (V', Some VC') = ⌊# (V', Some VC', dIReplace V') :: dF ⌋
           ) by eauto.
      rewrite Hb in H7.
      assert (Hb':
                bind ⌊# dF' ⌋ (V', Some VC') = ⌊# (V', Some VC', dIReplace V') :: dF' ⌋
             ) by eauto.
      assert (Hequiv' :
                denvironment_equivalent_modulo_caches
                  ((V', Some VC', dIReplace V') :: dF)
                  ((V', Some VC', dIReplace V') :: dF'))
        by (
            unfold denvironment_equivalent_modulo_caches in * |- *; simpl;
            intuition; congruence
          ).

      edestruct (IHt _ _ _ _ _ _ Hequiv' (@refl_equal _ _) (@refl_equal _ _) H7).
      eexists.
      eapply TPrimitiveCall; eauto.
      rewrite <- (denvironment_equivalent_modulo_caches_lookup_value_original (k := Old) Hequiv (@refl_equal _ _) (@refl_equal _ _) v).
      eauto.
      rewrite <- (denvironment_equivalent_modulo_caches_lookup_value_original (k := Old) Hequiv (@refl_equal _ _) (@refl_equal _ _) v0).
      eauto.

  - destruct k; simpl in * |- *; subst.
    * assert (Hb:
                ⌈# (V', Some VC', dIReplace V') :: dF ⌉ = Some (bind F (V', Some VC'))
             ).
      eapply modified_environment_bind; eauto; eapply move_replace.
      assert (Hb':
                ⌈# (V', Some VC', dIReplace V') :: dF' ⌉ = Some (bind F' (V', Some VC'))
             ).
      eapply modified_environment_bind; eauto; eapply move_replace.
      assert (Hequiv':
                denvironment_equivalent_modulo_caches
                  ((V', Some VC', dIReplace V') :: dF)
                  ((V', Some VC', dIReplace V') :: dF')).
      unfold denvironment_equivalent_modulo_caches in * |- *; simpl;
        intuition; try congruence.

      destruct (IHt _ _ _ _ _ _ Hequiv' Hb Hb' H7).
      eexists.

      eapply TClosureCall; eauto.
      rewrite <- (denvironment_equivalent_modulo_caches_lookup_value_original (k := New) Hequiv HF HF' v); eauto.
      rewrite <- (denvironment_equivalent_modulo_caches_lookup_value_original (k := New) Hequiv HF HF' v0); eauto.

    * assert (Hb:
              exists dV, bind ⌊# dF ⌋ (V', Some VC') = ⌊# (V', Some VC', dV) :: dF ⌋
           ) by (exists (dIReplace V'); eauto).
      destruct Hb as [ dV Hb ]. rewrite Hb in H7.
      assert (Hb':
                bind ⌊# dF' ⌋ (V', Some VC') = ⌊# (V', Some VC', dV) :: dF' ⌋
             ) by eauto.

      assert (Hequiv' :
                denvironment_equivalent_modulo_caches
                  ((V', Some VC', dV) :: dF)
                  ((V', Some VC', dV) :: dF'))
        by (
            unfold denvironment_equivalent_modulo_caches in * |- *; simpl;
            intuition; congruence
          ).

      edestruct (IHt _ _ _ _ _ _ Hequiv' (@refl_equal _ _) (@refl_equal _ _) H7).
      eexists.
      eapply TClosureCall; eauto.
      rewrite <- (denvironment_equivalent_modulo_caches_lookup_value_original (k := Old) Hequiv (@refl_equal _ _) (@refl_equal _ _) v).
      eauto.
      rewrite <- (denvironment_equivalent_modulo_caches_lookup_value_original (k := Old) Hequiv (@refl_equal _ _) (@refl_equal _ _) v0).
      eauto.

  - destruct k; simpl in * |- *; subst.
    * assert (Hb:
                ⌈# (ITuple Vs, None, dIReplace (ITuple Vs)) :: dF ⌉ = Some (bind F (ITuple Vs, None))
             ).
      eapply modified_environment_bind; eauto; eapply move_replace.
      assert (Hb':
                ⌈# (ITuple Vs, None, dIReplace (ITuple Vs)) :: dF' ⌉ = Some (bind F' (ITuple Vs, None))
             ).
      eapply modified_environment_bind; eauto; eapply move_replace.
      assert (Hequiv':
                denvironment_equivalent_modulo_caches
                  ((ITuple Vs, None, dIReplace (ITuple Vs)) :: dF)
                  ((ITuple Vs, None, dIReplace (ITuple Vs)) :: dF')).
      unfold denvironment_equivalent_modulo_caches in * |- *; simpl;
        intuition; try congruence.

      destruct (IHt _ _ _ _ _ _ Hequiv' Hb Hb' H4).
      eexists.
      eapply TTuple; eauto.
      rewrite <- (denvironment_equivalent_modulo_caches_lookup_values_original (k := New) Hequiv HF HF' l).
      eauto.

    * assert (Hb:
                exists dV, bind ⌊# dF ⌋ (ITuple Vs, None) = ⌊# (ITuple Vs, None, dV) :: dF ⌋
             ) by (exists (dIReplace (ITuple Vs)); eauto).
      destruct Hb as [ dV Hb ]. rewrite Hb in H4.
      assert (Hb':
                bind ⌊# dF' ⌋ (ITuple Vs, None) = ⌊# (ITuple Vs, None, dV) :: dF' ⌋
             ) by eauto.

      assert (Hequiv' :
                denvironment_equivalent_modulo_caches
                  ((ITuple Vs, None, dV) :: dF)
                  ((ITuple Vs, None, dV) :: dF'))
        by (
            unfold denvironment_equivalent_modulo_caches in * |- *; simpl;
            intuition; congruence
          ).

      edestruct (IHt _ _ _ _ _ _ Hequiv' (@refl_equal _ _) (@refl_equal _ _) H4).
      eexists.
      eapply TTuple.
      rewrite <- (denvironment_equivalent_modulo_caches_lookup_values_original (k := Old) Hequiv (@refl_equal _ _) (@refl_equal _ _) l).
      eauto.
      eauto.
Qed.

Lemma extension_components:
  forall {ctx k dE dE' dF},
    [[k # dE ⊢ dE' ↑ ctx ⇾ dF ]] ->
    denvironment_equivalent_modulo_caches dE' dF.
Proof.
  unfold denvironment_equivalent_modulo_caches.
  induction ctx; intros * Hx; inverse Hx; simpl in * |- *; unfold postbind;
    eauto.
  - generalize (IHctx _ _ _ _ H9); intro; intuition;
    do 2 rewrite map_app; simpl; congruence.
  - generalize (IHctx _ _ _ _ H8); intro; intuition;
    do 2 rewrite map_app; simpl; congruence.
  - generalize (IHctx _ _ _ _ H5); intro; intuition;
    do 2 rewrite map_app; simpl; congruence.
Qed.

(* Maybe unused? *)
Lemma invert_rel_env_len:
  forall {E dE E'},
    rel_env E dE E' ->
    exists n, length E = n /\ length dE = n /\ length E' = n.
  intros * Henv.
  apply invert_rel_env in Henv.
  dependent induction Henv; simpl.
  - exists 0. auto.
  - destruct IHHenv as [x]. exists (S x). iauto.
Qed.

(* Maybe unused? *)
Lemma invert_rel_env_append:
  forall {E dE E' Eu dEu Eu'},
    rel_env E dE E' ->
    rel_env (Eu ++ E) (dEu ++ dE) (Eu' ++ E') ->
    Eu = [] /\ dEu = [] /\ Eu' = []
    \/
    exists v dv v' Eu1 dEu1 Eu'1,
      Eu = (v :: Eu1) /\ dEu = ((v, dv) :: dEu1) /\ (Eu' = v' :: Eu'1) /\
      rel_value v dv v' /\ rel_env Eu1 dEu1 Eu'1.
Proof.
  intros * Henv Henv'.
  lets (n1 & HlE & HldE & HlE') : @invert_rel_env_len Henv.
  lets (n2 & HlEu & HldEudE & HlE'uE') : @invert_rel_env_len Henv'.

  rewrite app_length in *.
  subst.
  replace (length E') with (length E) in HlE'uE'.
  replace (length dE) with (length E) in HldEudE.

  apply (f_equal (fun x => x - length E)) in HlE'uE'.
  apply (f_equal (fun x => x - length E)) in HldEudE.

  assert (HldEu: length dEu = length Eu) by omega.
  assert (HlEu': length Eu' = length Eu) by omega.
  clear HlE'uE' HldEudE.

  apply invert_rel_env in Henv'.
  dependent induction Henv'.
  - left.
    repeat
      match goal with
        H: [] = (?x ++ ?y) |- _ =>
        destruct x; destruct y; inverts H end.
    auto.
  -
    destruct Eu; destruct dEu; destruct Eu'; simpl in *; try discriminate.
    + left. auto.
    +
      destruct p.
      inversion x.
      inversion x0.
      inversion x1.
      subst.

      lets H01 : (IHHenv' Eu' dEu Eu) E' dE E __; auto.
      assert
        (HeInd: Eu = [] /\ dEu = [] /\ Eu' = [] \/
        (exists v dv v' Eu1 dEu1 Eu'1,
         Eu = v :: Eu1 /\
         dEu = (v, dv) :: dEu1 /\
         Eu' = v' :: Eu'1 /\ rel_value v dv v' /\ rel_env Eu1 dEu1 Eu'1))
        by (apply H01; auto).
      right.
      exists.
      repeat split; repeat fequals; auto.
      destruct HeInd as [H0|].
      * destruct H0 as [HEu [HdEu HEu'] ].
        subst. constructor.
      * destruct H0 as [v [dv [ v' [Eu1 [dEu1 [Eu1' [ H1 [H2 [ H3 [H4 H5] ] ] ] ] ] ] ] ] ].
        subst. intro. constructor; auto. apply H5.
Qed.

Lemma extension_preserves_length:
  forall {ctx k dE dE' dF},
    [[k # dE ⊢ dE' ↑ ctx ⇾ dF ]] ->
    List.length dF = List.length dE'.
Proof.
  intros.
  generalize (extension_components H). unfold denvironment_equivalent_modulo_caches.
  intuition. eapply map_equiv_length; eauto.
Qed.

Lemma extension_length_is_depth_of_context:
  forall {ctx k dE dE' dF},
    [[k # dE ⊢ dE' ↑ ctx ⇾ dF ]] ->
    List.length dF = depth_of_term ctx.
Proof.
  induction ctx; intros * Hx; inverse Hx; simpl in * |- *; eauto;
  unfold postbind; rewrite app_length; erewrite IHctx; simpl; eauto; omega.
Qed.

Lemma extended_with_caches_lookup:
  forall { k ctx dF0 dF dF' x V dV VC},
    [[k # dF0 ⊢ dF ↑ ctx ⇾ dF']] ->
    lookup (dF ++ dF0) x = Some (V, VC, dV) ->
    exists VC', lookup (dF' ++ dF0) x = Some (V, VC', dV).
Proof.
  intros * Hx Hl. destruct x.
  generalize (split_lookup Hl); intro Hsplit.
  generalize (extension_preserves_length Hx). intuition.
  generalize (extension_components Hx).
  unfold denvironment_equivalent_modulo_caches.
  intuition.

  rewrite restrict_lookup.
  generalize (map_lookup H2 (f := fun x => fst (fst x))); simpl.
  rewrite H3.
  intro Hlmap.
  destruct (map_lookup_2 Hlmap). destruct x. destruct p. simpl in H. clear Hlmap.
  generalize (map_lookup H2 (f := snd)); simpl.
  rewrite H4.
  intro Hlmap.
  destruct (map_lookup_2 Hlmap).
  intuition.
  subst.
  exists o. destruct x. simpl. congruence.
  rewrite H; eauto.
  rewrite restrict_lookup_2. rewrite H. eexists; eauto.
  rewrite H; eauto.
Qed.

Lemma extended_with_new_caches_lookup_modified_env:
  forall {E dE E' v' x ctx Eu Eu' dEu' dF' F'},
    rel_env (Eu ++ E) (dEu' ++ dE) (Eu' ++ E') ->
    [[New # cts_denvironment dE ⊢ cts_denvironment dEu' ↑ ctx ⇾ dF']] ->
    ⌈# dF' ++ cts_denvironment dE ⌉ = Some F' ->
    Environment.lookup (Eu' ++ E') x = Some v' ->
    exists VC, Environment.lookup F' x = Some (cts_value v', VC).
Proof.
  intros * Hrel Hx Hn Hl.
  assert (Hk : 0 < 1) by auto.
  generalize (modified_env_of_drel_env Hk (Hrel 1)).
  case_eq (lookup (dEu' ++ dE) x); intros.
  generalize (modified_environment_lookup H0 x). rewrite H. destruct p. intros.
  destruct H1. intuition. assert (x0 = v') by congruence. subst.

  assert (exists VC, lookup (cts_denvironment dEu' ++ cts_denvironment dE) x =
                   Some (cts_value v, VC, cts_dvalue d)).
  unfold cts_denvironment. rewrite <- map_app. rewrite (map_lookup H).
  unfold cts_dbinding. simpl. do 2 eexists; eauto.
  destruct H1.
  destruct (extended_with_caches_lookup Hx H1).
  case_eq (lookup F' x). intros. destruct p.
  generalize (lookup_in_modified_environment Hn H5).
  intros.
  do 2 destruct H6. intuition.
  assert (x2 = cts_value v). congruence. subst.
  assert (x3 = cts_dvalue d). congruence. subst.
  assert (o = x1). congruence. subst.
  rewrite (move_cts_value H3) in H7. inverse H7.
  eexists; eauto.

  intro.
  generalize (modified_environment_lookup H0 x). rewrite H. intros.
  do 2 destruct H6.
  destruct (extended_with_caches_lookup Hx H1).
  destruct (lookup_modified_environment Hn H8). intuition. congruence.

  generalize (modified_environment_lookup H0 x). rewrite H. intros.
  congruence.
Qed.

Lemma post_extend_old_with_tuple:
  forall {ctx dF dE xs dF' Vs dVs},
    [[Old # dF ⊢ dE ↑ ctx ⇾ dF' ]] ->
    [[Old # dF ⊢
          Environment.bind dE (ITuple Vs, None, dITuple dVs) ↑ graft ctx (ttuple xs)
          ⇾ Environment.bind dF' (ITuple Vs, None, dITuple dVs)]].
Proof.
  induction ctx; intros * Hx; inverse Hx; simpl in * |- *; eauto.
  - rewrite bind_postbind_nil. constructor. constructor.
  - do 2 rewrite bind_postbind. eapply ExtendWithOldDef; eauto.
  - do 2 rewrite bind_postbind. eapply ExtendWithTuple; eauto.
Qed.

Lemma post_extend_new_with_tuple:
  forall {ctx dE xs dF dF' Vs dVs},
    [[New # dF ⊢ dE ↑ ctx ⇾ dF' ]] ->
    [[New # dF ⊢
          Environment.bind dE (ITuple Vs, None, dITuple dVs) ↑ graft ctx (ttuple xs)
          ⇾ Environment.bind dF' (ITuple Vs, None, dITuple dVs)]].
Proof.
  induction ctx; intros * Hx; inverse Hx; simpl in * |- *; eauto.
  - rewrite bind_postbind_nil. constructor. constructor.
  - do 2 rewrite bind_postbind. eapply ExtendWithNewDef; eauto.
  - do 2 rewrite bind_postbind. eapply ExtendWithTuple; eauto.
Qed.

Lemma extended_with_caches_lookups:
  forall {k xs dE ctx dEu dF Bs},
    [[k # dE ⊢ dEu ↑ ctx ⇾ dF]] ->
    Environment.lookups (dEu ++ dE) xs = Some Bs ->
    exists Bs',
      Environment.lookups (dF ++ dE) xs = Some Bs'
      /\ List.map fst (List.map fst Bs) = List.map fst (List.map fst Bs')
      /\ List.map snd Bs = List.map snd Bs'.
Proof.
  induction xs; simpl; eauto; intros * Hx Hl.
  destruct (inv_success_mbind Hl). rewrite H in Hl. simpl in Hl.
  destruct (inv_success_mbind Hl). rewrite H0 in Hl. simpl in Hl.
  inverse Hl.
  destruct (IHxs _ _ _ _ _ Hx H). intuition.
  rewrite H2. simpl.
  rewrite H1. rewrite H4. destruct x0. destruct p.
  destruct (extended_with_caches_lookup Hx H0).
  rewrite H3.
  eexists; intuition.
Qed.

Lemma eval_cache_under_old_extended:
  forall {ctx dF0 x dF dF'},
    [[Old # dF0 ⊢ dF ↑ ctx ⇾ dF']] ->
    exists VC,
      eval_cache
        ⌊# dF' ++ dF0 ⌋
        (cache_of_term (graft ctx (Var x))) (CacheValue VC).
Proof.
  intros * Hx.
  exists (List.rev (original_environment dF')).
  unfold original_environment. rewrite map_app.
  eapply cache_of_term_reverse_environment.
  rewrite map_length.
  rewrite (extension_length_is_depth_of_context Hx).
  rewrite (depth_of_term_graft ctx (Var x)).
  simpl. eauto.
Qed.

Lemma eval_cache_under_new_extended:
  forall {ctx dF0 x dF dF' F'},
    ⌈# dF' ++ dF0 ⌉ = Some F' ->
    [[New # dF0 ⊢ dF ↑ ctx ⇾ dF']] ->
    exists VC,
      eval_cache F' (cache_of_term (graft ctx (Var x))) (CacheValue VC).
Proof.
  intros * Hx Hm.
  unfold modified_environment in Hx.
  rewrite list_map_app in Hx.
  destruct (inv_success_mbind Hx). rewrite H in Hx. simpl in Hx.
  destruct (inv_success_mbind Hx). rewrite H0 in Hx. simpl in Hx.
  inverse Hx.

  exists (List.rev x0).
  eapply cache_of_term_reverse_environment.
  rewrite <- (list_map_length _ _ _ H).
  rewrite (extension_length_is_depth_of_context Hm).
  rewrite (depth_of_term_graft ctx (Var x)).
  simpl. eauto.
Qed.

Lemma extension_lookup:
  forall {k dF dF0 dF' x VC v dv ctx},
    [[k # dF0 ⊢ dF ↑ ctx ⇾ dF']] ->
    lookup dF x = Some (v, VC, dv) ->
    exists VC', lookup dF' x = Some (v, VC', dv).
Proof.
  introv Hext.
  destruct x as [n]. gen n.
  induction Hext; introv Heq; inversion Heq;
  generalize (extension_preserves_length Hext); intro Hlen;
  unfold postbind in * |- *;
  destruct (split_lookup Heq); intuition;

    (try rewrite restrict_lookup; eauto; rewrite Hlen; eauto)
  || (try rewrite restrict_lookup_2; rewrite Hlen; try eexists; eauto).

  destruct (n - length dF); simpl in * |- *. inverse H5. eauto.
  inverse H5.

  destruct (n - length dF); simpl in * |- *. inverse H4. eauto.
  inverse H4.
Qed.

Lemma extension_lookup2:
  forall {k dF dF0 dF' x VC v dv ctx},
    [[k # dF0 ⊢ dF ↑ ctx ⇾ dF']] ->
    lookup (dF ++ dF0) x = Some (v, VC, dv) ->
    exists VC', lookup (dF' ++ dF0) x = Some (v, VC', dv).
Proof.
  intros.
  destruct x.
  destruct (split_lookup H0); intuition.
  rewrite restrict_lookup. eapply extension_lookup; eauto.
  rewrite (extension_preserves_length H); eauto.
  rewrite restrict_lookup_2. eexists.
  rewrite (extension_preserves_length H); eauto. eauto.
  rewrite (extension_preserves_length H); eauto.
Qed.

Lemma extension_lookup_cts_denvironment:
  forall {k dEu dE dF' x v dv ctx},
    [[k # cts_denvironment dE ⊢ cts_denvironment dEu ↑ ctx ⇾ dF']] ->
    lookup (dEu ++ dE) x = Some (v, dv) ->
    exists VC', lookup (dF' ++ cts_denvironment dE) x = Some (cts_value v, VC', cts_dvalue dv).
Proof.
  intros.
  generalize (cts_denvironment_lookup H0).
  unfold cts_dbinding. simpl. intro Hlookup.
  rewrite cts_denvironment_app in Hlookup.
  destruct (extension_lookup2 H Hlookup).
  eexists; eauto.
Qed.

Lemma extended_with_old_caches_lookup:
  forall {ctx E dE E' v x Eu Eu' dEu dF},
    rel_env E dE E' ->
    rel_env (Eu ++ E) (dEu ++ dE) (Eu' ++ E') ->
    [[Old # cts_denvironment dE ⊢ cts_denvironment dEu ↑ ctx ⇾ dF]] ->
    Environment.lookup (Eu ++ E) x = Some v ->
    exists VCx,
    Environment.lookup ⌊# dF ++ cts_denvironment dE ⌋ x = Some (cts_value v, VCx).
Proof.
  intros. destruct x.

  destruct (rel_env_lookup_change _ _ _ _ _ H0 H2) as [ dv Hl ].
  generalize (cts_denvironment_lookup Hl). intro Hdl.
  rewrite cts_denvironment_app in Hdl. unfold cts_dbinding in Hdl. simpl in Hdl.
  generalize (lookup_original_environment Hdl). intro.
  unfold original_environment. rewrite map_app.
  unfold original_environment in H3. rewrite map_app in H3.
  simpl in H3.

  assert (length (map fst (cts_denvironment dEu)) = length dF).
  erewrite extension_preserves_length; eauto.
  unfold cts_denvironment. rewrite map_length. eauto.
  generalize (rel_env_length _ _ _ H).
  generalize (rel_env_length _ _ _ H0).
  do 3 rewrite app_length.
  intuition.
  assert (length dF = length (map fst dF)) by (rewrite map_length; eauto).

  destruct (split_lookup H3).
  intuition.
  destruct (map_lookup_2 H12). intuition.

  rewrite H4 in H11.
  rewrite H6 in H11.
  rewrite (restrict_lookup _ _ _ H11).
  destruct x. destruct p.
  destruct (extension_lookup H1 H13).
  inverse H14.
  exists x. generalize (map_lookup H10 (f := fst)). simpl. eauto.

  intuition.
  rewrite H4 in H11.
  rewrite H6 in H11.
  rewrite (restrict_lookup_2 _ _ _ H11).
  rewrite H4 in H12. rewrite H6 in H12.
  eexists None.
  eauto.
Qed.

Lemma lookup_original_of_extended_environment:
  forall {k v dF0 dF dF' v0 VCx ctx F F'},
    [[k # dF0 ⊢ dF ↑ ctx ⇾ dF']] ->
    extended_environment k (dF ++ dF0) F ->
    extended_environment k (dF' ++ dF0) F' ->
    lookup F v = Some (v0, VCx) ->
    exists VCx', lookup F' v = Some (v0, VCx').
Proof.
  intro k; destruct k; simpl.
  (* k = New. *)
  - intros * Hx HF HF' Hl.
    destruct (Environment.list_map_lookup_2 HF Hl).
    intuition. destruct x. destruct p.
    destruct (extended_with_caches_lookup Hx H0).
    destruct (lookup_modified_environment HF' H). intuition.
    simpl.
    unfold modified_binding in * |- *. simpl in * |- *.
    destruct x0.
    destruct (v1 ⊕ d); simpl in * |- *; try congruence.
    unfold ret in * |- *.
    assert (v0 = v2). congruence. subst.
    eexists. eauto.

  - (* k = Old *)
  intros * Hx HF HF' Hl. subst.
  destruct (Environment.map_lookup_2 Hl).
  intuition. destruct x. destruct p.
  destruct (extended_with_caches_lookup Hx H0).
  exists x.
  generalize (lookup_original_environment H). inverse H1. eauto.
Qed.

Lemma eval_cache_under_extended_environment:
  forall {k c dF0 dF dF' VC ctx F F'},
    [[k # dF0 ⊢ dF ↑ ctx ⇾ dF']] ->
    extended_environment k (dF ++ dF0) F ->
    extended_environment k (dF' ++ dF0) F' ->
    eval_cache F c VC ->
    exists VC',  eval_cache F' c VC'.
Proof.
  - induction c; intros * Hx HF HF' He; inverse He.
    * eexists; econstructor.
    * destruct (lookup_original_of_extended_environment Hx HF HF' H2).
      edestruct (IHc _ _ _ _ _ _ F' Hx HF HF' H4).
      destruct x1.
      eexists; econstructor; eauto.
Qed.

Lemma eval_under_extended_environment:
  forall {k t dF dF0 dF' v VC ctx F F'},
    [[k # dF0 ⊢ dF ↑ ctx ⇾ dF']] ->
    extended_environment k (dF ++ dF0) F ->
    extended_environment k (dF' ++ dF0) F' ->
    [# F ⊢ t ⇓ (v, VC) ] ->
    exists VC', [# F' ⊢ t ⇓ (v, VC') ].
Proof.
  intros.
  generalize (extension_components H). intros.
  generalize (denvironment_equivalent_modulo_caches_extend H3 (dF0 := dF0)). intro He.
  eapply (denvironment_equivalent_modulo_caches_original_evaluation He); eauto.
Qed.

Lemma cache_of_call:
  forall { F f x V VC},
    [# F ⊢ @#(f, x) ⇓ (V, VC) ] ->
    exists VC', VC = CacheValue ((V, Some VC') :: nil).
Proof.
  intros.
  inverse H.
  - inverse H8. inverse H10. simpl in * |- *.
    inverse H11. inverse H6. inverse H12. eexists; eauto.
  - inverse H8. inverse H10. simpl in * |- *.
    inverse H11. inverse H6. inverse H12. eexists; eauto.
Qed.

Lemma shift0: forall x, shift 0 x = x.
Proof.
  intro. unfold shift. destruct x. auto.
Qed.

Lemma eval_call_under_old_extended_environment:
  forall {dE f x ctx dEu dF v''},
    [[Old # cts_denvironment dE ⊢ cts_denvironment dEu ↑ ctx ⇾ dF]] ->
    [⌊ dEu ++ dE ⌋ ⊢ @( f, x) ⇓ v''] ->
    exists VC,
      [# ⌊# dF ++ cts_denvironment dE ⌋ ⊢ @#( f, x)
      ⇓ (cts_value v'', CacheValue ((cts_value v'', Some VC) :: nil))].
Proof.
  intros.
  destruct (eval_cts_compat H0 (u := @(f, x))) as [ VC He ]. simpl in * |-.
  replace (cts_environment ⌊ dEu ++ dE ⌋)
    with (⌊# cts_denvironment dEu ++ cts_denvironment dE ⌋) in He.
  destruct (eval_under_extended_environment (k := Old) H (@refl_equal _ _) (@refl_equal _ _) He).
  unfold ILambdaAL.call.
  repeat (rewrite shift0 in H1).
  destruct (cache_of_call H1). subst.
  exists x1. eauto.
  rewrite <- cts_denvironment_app.
  rewrite cts_denvironment_original_environment; eauto.
Qed.

Lemma cts_denvironment_inherits_valid_modified_environment:
  forall {dE E},
    ⌈ dE ⌉ = Some E ->
    exists F, ⌈# cts_denvironment dE ⌉ = Some F.
Proof.
  induction dE; unfold modified_environment; simpl in * |- *; intros.
  - eexists; eauto.
  - unfold LambdaALOperationalSemantics.modified_environment in * |- *.
    simpl in H.
    destruct (inv_success_mbind H).
    rewrite H0 in H. simpl in H.
    destruct (inv_success_mbind H).
    destruct (IHdE _ H1).
    unfold modified_environment in H2.
    rewrite H2.
    unfold modified_binding.
    unfold cts_dbinding.
    simpl.
    destruct a.
    simpl in * |- *.
    rewrite (move_cts_value H0).
    simpl. eexists. eauto.
Qed.

Lemma eval_call_under_modified_extended_environment:
  forall {dE f x ctx dEu dF v'' F' E'},
    ⌈# dF ++ cts_denvironment dE ⌉ = Some F' ->
    [[New # cts_denvironment dE ⊢ cts_denvironment dEu ↑ ctx ⇾ dF]] ->
    ⌈ dEu ++ dE ⌉ = Some E' ->
    [ E' ⊢ @( f, x) ⇓ v''] ->
    exists (VC : cache_value),
      [# F' ⊢ @#( f, x) ⇓ (cts_value v'', CacheValue ((cts_value v'', Some VC) :: nil))].
Proof.
  intros.
  destruct (eval_cts_compat H2 (u := @(f, x))) as [ VC He ]. simpl in * |-.
  assert (HF: exists F, ⌈# cts_denvironment dEu ++ cts_denvironment dE ⌉ = Some F).
  rewrite <- cts_denvironment_app.
  eapply cts_denvironment_inherits_valid_modified_environment; eauto.
  destruct HF as [ F HF ].
  replace (cts_environment E') with F in He.
  destruct (eval_under_extended_environment (k := New) H0 HF H He).
  unfold ILambdaAL.call.
  repeat (rewrite shift0 in H3).
  destruct (cache_of_call H3). subst.
  exists x1. eauto.
  rewrite (cts_denvironment_modified_environment H1 (F := F)); eauto.
  rewrite cts_denvironment_app. eauto.
Qed.

Lemma extend_old_environment_with_call:
  forall { ctx dF dF' xdF f x V VC dV },
    [[Old # dF ⊢ dF' ↑ ctx ⇾ xdF]] ->
    [# ⌊# xdF ++ dF ⌋ ⊢ @#( f, x) ⇓ (V, CacheValue ((V, Some VC) :: nil))] ->
    [[Old # dF ⊢ bind dF' (V, None, dV) ↑ graft ctx @( f, x)
          ⇾ bind xdF (V, Some VC, dV) ]].
Proof.
  induction ctx; intros * Hx He; inverse Hx; simpl in * |- *.
  - do 2 rewrite bind_postbind_nil.
    eapply ExtendWithOldDef; eauto; try constructor.
  - do 2 rewrite bind_postbind.
    eapply ExtendWithOldDef; unfold postbind in * |- *; eauto.
    eapply IHctx; eauto.
    rewrite <- app_assoc in He. eauto.
  - do 2 rewrite bind_postbind.
    eapply ExtendWithTuple; unfold postbind in * |- *; eauto.
    eapply IHctx; eauto.
    rewrite <- app_assoc in He. eauto.
Qed.

Lemma extend_new_environment_with_call:
  forall { ctx dF dF' xdF f x V VC dV F' V' },
    [[New # dF ⊢ dF' ↑ ctx ⇾ xdF]] ->
    ⌈# xdF ++ dF ⌉ = Some F' ->
    V ⊕ dV = Some V' ->
    [# F' ⊢ @#( f, x) ⇓ (V', CacheValue ((V', Some VC) :: nil))] ->
    [[New # dF ⊢ bind dF' (V, None, dV) ↑ graft ctx @( f, x)
          ⇾ bind xdF (V, Some VC, dV)]].
Proof.
  induction ctx; intros * Hx HF' Hm He; inverse Hx; simpl in * |- *.
  - do 2 rewrite bind_postbind_nil.
    eapply ExtendWithNewDef; eauto.
    constructor.
  - do 2 rewrite bind_postbind.
    eapply ExtendWithNewDef; unfold postbind in * |- *; eauto.
    eapply IHctx; eauto.
    rewrite <- app_assoc in HF'. eauto.
  - do 2 rewrite bind_postbind.
    eapply ExtendWithTuple; unfold postbind in * |- *; eauto.
    eapply IHctx; eauto.
    rewrite <- app_assoc in HF'. eauto.
Qed.

Lemma graft_assoc:
  forall {ctx ctx' t u},
    graft (graft (graft ctx t) ctx') u
    = graft (graft ctx t) (graft ctx' u).
Proof.
  induction ctx; simpl; eauto; intros.
  induction t; simpl; eauto. rewrite IHt. eauto.
  rewrite IHt. eauto.
  rewrite IHctx. eauto.
  rewrite IHctx. eauto.
Qed.

Lemma graft_hole:
  forall {ctx u v},
    graft (graft ctx (Var v)) u = graft ctx u.
Proof.
  induction ctx; simpl; eauto; intros.
  rewrite IHctx. eauto.
  rewrite IHctx. eauto.
Qed.

Lemma graft_var_depth:
  forall {ctx v},
    depth_of_term (graft ctx (Var v)) = depth_of_term ctx.
Proof.
  induction ctx; simpl; eauto.
Qed.

Lemma graft_binding_depth:
  forall {ctx b},
    binding b ->
    depth_of_term (graft ctx b) = S (depth_of_term ctx).
Proof.
  induction ctx; simpl; eauto.
  intros. destruct H. destruct H as [ f [ x Hfx ] ]. subst. simpl. eauto.
  destruct H. subst. simpl. auto.
Qed.

Lemma eval_cache_app_context:
  forall {ctx dF0 ctx' b VC xdF Vy VCy F},
    length F = depth_of_term ctx' ->
    binding b ->
    [#⌊# xdF ++ dF0 ⌋ ⊢ compile_binding b ⇓ (Vy, CacheValue [(Vy, VCy)])] ->
    eval_cache (F ++ (Vy, VCy) :: ⌊# xdF ++ dF0 ⌋)
               (cache_of_term (graft (graft ctx b) ctx')) (CacheValue VC) ->
    exists preVC postVC,
      VC = preVC ++ (Vy, VCy) :: postVC /\ length preVC = depth_of_term ctx.
Proof.
  induction ctx; intros; simpl in * |- *; eauto.
  - destruct H0. destruct H0 as [ f [ x Hfx ] ]. subst.
    simpl in H2. inverse H2.
    rewrite <- H in H5.
    rewrite (Environment.restrict_lookup_2 _ _ (length F)) in H5.
    replace (length F - length F) with 0 in H5. simpl in H5. inverse H5.
    eexists nil. exists VC0.
    simpl. intuition.
    omega. omega.
    destruct H0. subst.
    simpl in H2. inverse H2.
    rewrite <- H in H5.
    rewrite (Environment.restrict_lookup_2 _ _ (length F)) in H5.
    replace (length F - length F) with 0 in H5. simpl in H5. inverse H5.
    eexists nil. exists VC0.
    simpl. intuition.
    omega. omega.

  - inverse H2.
    destruct (IHctx _ _ _ _ _ _ _ _ H H0 H1 H9) as [ preVC [ postVC HVC ] ].
    exists ((V, VCx) :: preVC). exists postVC.
    intuition. subst. eauto.
    simpl. eauto.

  - inverse H2.
    destruct (IHctx _ _ _ _ _ _ _ _ H H0 H1 H9) as [ preVC [ postVC HVC ] ].
    exists ((V, VCx) :: preVC). exists postVC.
    intuition. subst. eauto.
    simpl. eauto.
Qed.

Lemma result_in_cache_gen:
  forall {u ctx ctx' dF0 dF xdF V VC Vy VCy F b},

    length F = depth_of_term ctx' ->

    binding b ->

    [[Old # dF0 ⊢ dF ↑ ctx ⇾ xdF]] ->

    [#⌊# xdF ++ dF0 ⌋ ⊢ compile_binding b ⇓ (Vy, CacheValue ((Vy, VCy) :: nil))] ->

    [# F ++ (Vy, VCy) :: ⌊# xdF ++ dF0 ⌋
      ⊢ cts_term_aux (graft (graft (graft ctx b) ctx') u) u ⇓ (V, CacheValue VC)] ->

    exists preVC postVC,
      VC = preVC ++ (Vy, VCy) :: postVC
      /\ length preVC = depth_of_term ctx.
Proof.
  induction u; intros * Hlen Hbind Hextend Hevalb Heval; simpl in * |- *; eauto.

  - inverse Heval.
    assert (graft (graft (graft ctx b) ctx') (Var v)
    = graft (graft ctx b) (graft ctx' (Var v))).
    eapply graft_assoc.
    rewrite H in H5.
    eapply (eval_cache_app_context (ctx' := graft ctx' (Var v))); eauto.
    rewrite graft_var_depth. eauto.

  - inverse Heval.
    * rewrite graft_def in H7.
      unfold bind in H7. rewrite app_comm_cons in H7.
      assert (
          graft (graft (graft ctx b) ctx') @( v, v0)
          = graft (graft ctx b) (graft ctx' @(v, v0))
        ) by (eapply graft_assoc).
      rewrite H in H7.
      eapply (IHu _ _ _ _ _ _ _ _ _ _ _ _ _ Hextend _ H7).
    *  rewrite graft_def in H7.
      unfold bind in H7. rewrite app_comm_cons in H7.
      assert (
          graft (graft (graft ctx b) ctx') @( v, v0)
          = graft (graft ctx b) (graft ctx' @(v, v0))
        ) by (eapply graft_assoc).
      rewrite H in H7.
      eapply (IHu _ _ _ _ _ _ _ _ _ _ _ _ _ Hextend _ H7).
  - inverse Heval.
    rewrite graft_tuple in H4.
    assert (
        graft (graft (graft ctx b) ctx') (ttuple l)
        = graft (graft ctx b) (graft ctx' (ttuple l))
      ) by (eapply graft_assoc).
    rewrite H in H4.
    unfold bind in H4. rewrite app_comm_cons in H4.
    eapply (IHu _ _ _ _ _ _ _ _ _ _ _ _ _ Hextend _ H4).
    Unshelve.
    all: eauto.
    simpl.
    rewrite Hlen.
    rewrite graft_binding_depth. eauto.
    left. do 2 eexists. eauto.
    rewrite graft_binding_depth. simpl. rewrite Hlen. eauto.
    left. do 2 eexists. eauto.
    simpl. rewrite Hlen. rewrite graft_binding_depth. eauto.
    right. eexists. eauto.
Qed.

Lemma call_result_in_cache:
  forall {ctx u dE dEu f x v VC xdF vy VCy},
    [[Old # cts_denvironment dE ⊢ cts_denvironment dEu ↑ ctx ⇾ xdF]] ->
    [#⌊# xdF ++ cts_denvironment dE ⌋ ⊢ @#( f, x)
         ⇓ (cts_value vy, CacheValue ((cts_value vy, Some VCy) :: nil))] ->
    [# (cts_value vy, Some VCy) :: ⌊# xdF ++ cts_denvironment dE ⌋
      ⊢ cts_term_aux (graft (graft ctx @( f, x)) u) u ⇓ (cts_value v, CacheValue VC)] ->
    exists preVC postVC,
      VC = preVC ++ (cts_value vy, Some VCy) :: postVC
      /\ length preVC = depth_of_term ctx.
Proof.
  intros.
  assert (binding (@(f, x))). unfold binding. left. do 2 eexists. eauto.
  generalize (
      result_in_cache_gen (@refl_equal _ 0 ) H2 H H0
                               (V := cts_value v)
                               (VC := VC)
                               (F := nil) (ctx' := Var (Index.Idx 0)) (u := u)).
  simpl.
  intro Hc.
  eapply Hc.
  rewrite graft_hole. eauto.
Qed.

Lemma tuple_result_in_cache:
  forall {ctx u dE dEu xs v VC xdF vs},
    let vy := LambdaALValues.tuple vs in
    [[Old # cts_denvironment dE ⊢ cts_denvironment dEu ↑ ctx ⇾ xdF]] ->
    [#⌊# xdF ++ cts_denvironment dE ⌋ ⊢ tuple xs
         ⇓ (cts_value vy, CacheValue ((cts_value vy, None) :: nil))] ->
    [# (cts_value vy, None) :: ⌊# xdF ++ cts_denvironment dE ⌋
      ⊢ cts_term_aux (graft (graft ctx (LambdaAL.ttuple xs)) u) u ⇓ (cts_value v, CacheValue VC)] ->
    exists preVC postVC,
      VC = preVC ++ (cts_value vy, None) :: postVC
      /\ length preVC = depth_of_term ctx.
Proof.
  intros.
  assert (binding (LambdaAL.ttuple xs)). unfold binding. right. eexists. eauto.
  generalize (
      result_in_cache_gen (@refl_equal _ 0) H2 H H0
                               (V := cts_value v)
                               (VC := VC)
                               (F := nil) (ctx' := Var (Index.Idx 0)) (u := u)).
  simpl.
  intro Hc.
  eapply Hc.
  rewrite graft_hole. eauto.
Qed.
