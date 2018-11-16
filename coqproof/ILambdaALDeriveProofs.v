(** * Soundness of CTS differentiation. *)

Require Import Index.
Require Import Omega.
Require Import List.
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
Require Import ILambdaALOperationalSemanticsPrimitives.
Require Import ILambdaALOperationalSemantics.
Require Import ILambdaALDerive.
Require Import ILambdaALOperationalSemanticsProofs.
Require Import ILambdaALExtensionWithCaches.
Require Import ILambdaALCTSProofs.

Lemma cts_derive_cts_dvalue_gen:
  forall {n E dE E' dEu Eu' t ctx u v v' dv VC VC' xdF xdF' F'},

    rel_env E dE E' ->

    let Eu := ⌊ dEu ⌋ in
    ⌈ dEu ⌉ = Some Eu' ->
    graft ctx u = t ->

    [ E  ⊢ ctx ⇑ Eu  ] ->  [ Eu ++ E ⊢ u ⇓ v ] ->

    [ E' ⊢ ctx ⇑ Eu' ] ->  [ Eu' ++ E' ⊢ u ⇓ v' ] ->

    [[ dE ⊢ derive ctx ⇑ dEu ]] -> [[ dEu ++ dE ⊢ derive u ⇓ dv @ n]] ->

    [[ Old # cts_denvironment dE ⊢ cts_denvironment dEu ↑ ctx ⇾ xdF   ]] ->
    [[ New # cts_denvironment dE ⊢ cts_denvironment dEu ↑ ctx ⇾ xdF'  ]] ->

    let VCu := drop (List.length xdF) VC in
    let dF  := xdF  ++ cts_denvironment dE in
    let dF' := xdF' ++ cts_denvironment dE in

    [# ⌊# dF ⌋  ⊢ cts_term_aux t u ⇓ (cts_value v, CacheValue VC)] ->
    ⌈# dF' ⌉ = Some F' ->
    [# F' ⊢ cts_term_aux t u ⇓ (cts_value v', CacheValue VC')] ->

    [[#VCu, dF' ⊢ cts_derive_term t u ⇓ (cts_dvalue dv, CacheValue VC')]].
Proof.
  intro n. eapply (lt_wf_ind n). clear n. intros n Hrec.
    intros * Hrelenv Eu HEu' Hgraft Hevalctxu Hevalu Hevalctxu' Hevalu'
         Hdevalctx Hdeval Holdextend Hnewextend
                               VCu dF dF' Holdeval HF' Hneweval.

    assert (HrelenvEu:
              rel_env (Eu ++ E) (dEu ++ dE) (Eu' ++ E')
           ).
    eapply rel_env_through_context_evaluation; eauto.
    unfold Eu in * |- *.

    generalize (original_environment_under_rel_env _ _ _ Hrelenv). intro HE.
    rewrite <- HE in * |-. clear HE. clear E.

    generalize (modified_environment_under_rel_env _ _ _ Hrelenv). intro HE'.
    rewrite original_environment_app in HrelenvEu.

    assert (HEuE': ⌈ dEu ++ dE ⌉ = Some (Eu' ++ E')) by
        (eapply modified_environment_app; eauto).


  - destruct u as [ x | f x | xs ]; simpl in * |- *.

    * (** Case "x" *)

      inverse Hdeval.
      assert (Environment.lookup (cts_denvironment dEu ++ cts_denvironment dE) x =
              Some (cts_value v0, None, cts_dvalue dv)). {
        rewrite <- cts_denvironment_app.
        unfold cts_denvironment.
        generalize (Environment.map_lookup H2 (f := cts_dbinding)).
        unfold cts_dbinding. simpl. eauto.
      }
      destruct (extended_with_caches_lookup Hnewextend (x := x) H).
      econstructor; eauto.
      inverse Hneweval.
      eapply eval_cache_update_of_eval_cache_under_modified_environment; eauto.

    * (** Case "let y = f x in u" *)

      (** Update the context we are working under. *)

      assert (Hgraft':
                graft (graft ctx (LambdaAL.call f x)) u = t
             ) by (rewrite <- graft_def; eauto).
      clear Hgraft.

      (** Make explicit the values and the caches produced by the
          evaluation of [f x] in the original and the modified
          evaluations, as well as their compiled counterparts. *)
      destruct (call_inversion Hevalu) as [ vy [ Hfx Hnfx ] ].
      rewrite original_environment_app in Hfx.
      destruct (eval_call_under_old_extended_environment Holdextend Hfx) as [ VCy Hctsfx ].
      destruct (call_inversion Hevalu') as [ vy' [ Hfx' Hnfx' ] ].
      destruct (eval_call_under_modified_extended_environment HF' Hnewextend HEuE' Hfx')
               as [ VCy' Hctsfx' ].

      (** [VCu] is starting with [Vy and VCy]. *)
      assert (HVCu:
                exists VCu', VCu = (cts_value vy, Some VCy) :: VCu'
             ).
      {
        unfold VCu.
        destruct (inverse_call_evaluation Holdeval) as [ altVy [ altVCy HaltVy ] ].
        splitHyps.
        generalize (eval_deterministic H Hctsfx). intro Heq. inverse Heq.
        unfold dF in H, H0.
        assert (exists preVC postVC,
                   VC = preVC ++ (cts_value vy, Some VCy) :: postVC
                   /\ List.length preVC = depth_of_term ctx)
               by (eapply call_result_in_cache; eauto).
        destruct H1 as [ preVC [ postVC HVC ] ].
        splitHyps. rewrite H1. exists postVC.
        assert (length xdF = depth_of_term ctx)
          by (eapply extension_length_is_depth_of_context; eauto).
        rewrite H4. rewrite <- H2. rewrite drop_app. eauto.
      }

      destruct HVCu as [ VCu' ]. rewrite H in * |- *.
      destruct VCy as [ VCy ].

      (** We reason by cases on the last rule that produced [Hdeval]. *)
      inverse Hdeval.

      ** (** df = dReplace. *)
        unfold Eu in * |- *.
        generalize (original_environment_lookup (dEu ++ dE) f). rewrite H3. simpl. intro HlookupVf.
        destruct (extension_lookup_cts_denvironment Holdextend H3) as [ oldVCf Holdlookupf ].
        destruct (extension_lookup_cts_denvironment Hnewextend H3) as [ VCf Hlookupf ].

        assert (vy'0 = vy').
        {
          assert (E'0 = (Eu' ++ E')). congruence. subst.
          destruct (sound_eval _ _ _ Hfx').
          eapply deterministic_eval; eauto.
        }

        assert (vy0 = vy).
        {
          destruct (sound_eval _ _ _ Hfx).
          eapply deterministic_eval; eauto.
        }

        subst.
        assert (
            [[#VCu', Environment.bind dF' (cts_value vy, Some VCy', dIReplace (cts_value vy'))
            ⊢ cts_derive_term (graft (graft ctx @( f, x)) u) u ⇓ (cts_dvalue dv, CacheValue VC')]]
        ).
        {
          pose (nxdF  := (cts_value vy, Some (CacheValue VCy), dIReplace (cts_value vy')) :: xdF).
          pose (nxdF' := (cts_value vy, Some VCy', dIReplace (cts_value vy')) :: xdF').

          assert (HVCu': VCu' = drop (length nxdF) VC).
          {
            unfold nxdF. unfold length. symmetry.
            eapply drop_cons; eauto.
          }

          rewrite HVCu'.
          eapply (Hrec n0) with
              (dEu := (vy, LambdaALValues.dReplace vy') :: dEu)
              (Eu' := vy' :: Eu')
              (xdF' := (cts_value vy, Some VCy', dIReplace (cts_value vy')) :: xdF');
            simpl in * |- *; eauto; try omega.
          eapply LambdaALOperationalSemanticsProofs.modified_environment_bind; eauto.
          eapply LambdaALOperationalSemanticsProofs.move_replace; eauto.
          eapply eval_context_ended_with_call; eauto.
          rewrite original_environment_app. eauto.
          eapply eval_context_ended_with_call; eauto.
          eapply derive_context_ended_with_call; eauto.
          unfold LambdaAL.dcall.
          eapply (SDReplaceCall NoSteps); eauto.
          eapply complete_eval; eauto.
          simpl. eauto.
          subst.
          eapply (SDVar NoSteps); eauto.
          simpl. eauto.
          unfold nxdF.
          eapply extend_old_environment_with_call; eauto.
          eapply extend_new_environment_with_call; eauto.
          eapply move_cts_value; eauto.
          simpl. eapply LambdaALOperationalSemanticsProofs.move_replace; eauto.
          destruct (inverse_call_evaluation Holdeval). destruct H0. splitHyps.
          generalize (eval_deterministic H0 Hctsfx). intro He. inject He. eauto.
          eapply modified_environment_bind; eauto.
          eapply (move_cts_value (dv := LambdaALValues.dReplace vy')); eauto.
          eapply LambdaALOperationalSemanticsProofs.move_replace.

          destruct (inverse_call_evaluation Hneweval). destruct H0. splitHyps.
          generalize (eval_deterministic H0 Hctsfx'). intro He. inject He. eauto.

        }

        eapply TDReplaceCall; eauto.

      ** (** F is a primitive, df is a nil change. *)
        unfold Eu in * |- *.
        generalize (original_environment_lookup (dEu ++ dE) f). rewrite H3. simpl. intro HlookupVf.
        destruct (extension_lookup_cts_denvironment Holdextend H3) as [ oldVCf Holdlookupf ].
        destruct (extension_lookup_cts_denvironment Holdextend H4) as [ oldVCx Holdlookupx ].
        destruct (extension_lookup_cts_denvironment Hnewextend H3) as [ VCf Hlookupf ].
        destruct (extension_lookup_cts_denvironment Hnewextend H4) as [ VCx Hlookupx ].
        generalize (modified_environment_lookup HEuE' x). rewrite H4.
        intro Hok. destruct Hok as [ vx' [ Hlookupvx' Hmovex ] ].
        generalize (modified_environment_lookup HEuE' f). rewrite H3.
        intro Hok. destruct Hok as [ Vf' [ HlookupVf' HmoveVf' ] ].
        unfold modified_binding in HmoveVf'. simpl in HmoveVf'.

        assert (vy0 = vy).
        {
          assert (Hlf: Environment.lookup ⌊ dEu ++ dE ⌋ f = Some (LambdaALValues.Primitive p)).
          generalize (original_environment_lookup (dEu ++ dE) f). rewrite H3. eauto.
          assert (Hlx: Environment.lookup ⌊ dEu ++ dE ⌋ x = Some vx).
          generalize (original_environment_lookup (dEu ++ dE) x). rewrite H4. eauto.
          generalize (primitive_call_inversion Hfx Hlx Hlf). intro Hprim'.
          congruence.
        }
        subst.

        assert ([[ dEu ++ dE ⊢ derive (@(f, x)) ⇓ dvy ]]).
        {
          simpl.
          eapply (SPrimitiveNil NoSteps); eauto.
          eapply SDVar; eauto. simpl. eauto.
        }

        assert (Hmovey: LambdaALOperationalSemantics.move vy dvy = Some vy').
        {
          eapply (derive_soundness2 _ Hfx Hfx' H0); eauto.
        }

        assert (Hprim': eval_primitive p (cts_value vx') = Some (cts_value vy', VCy')).
        {
          assert (lookup_value F' f = Some (IPrimitive p)).
          destruct (lookup_modified_environment HF' Hlookupf). splitHyps.
          unfold modified_binding in H2. simpl in H2. inverse H2.
          unfold lookup_value. rewrite H1. simpl. eauto.
          assert (lookup_value F' x = Some (cts_value vx')).
          destruct (lookup_modified_environment HF' Hlookupx). splitHyps.
          unfold modified_binding in H5. simpl in H5.
          rewrite (move_cts_value Hmovex) in H5. simpl in H5. inverse H5.
          unfold lookup_value. rewrite H2. simpl. eauto.
          eapply (inverse_primitive_call_evaluation Hctsfx'); assumption.
        }

        destruct (eval_primitive_cts_value H7) as [ VCy0 Hprim ].
        generalize (eval_dprimitive_cts_value H7 H9 Hprim Hprim' (move_cts_value Hmovex) (move_cts_value Hmovey)).
        intro Hd.

        assert (
            Hdnext:
              [[#VCu',
                Environment.bind
                  (xdF' ++ cts_denvironment dE) (cts_value vy, Some VCy', cts_dvalue dvy)
                  ⊢ cts_derive_term (graft (graft ctx @( f, x)) u) u
                  ⇓ (cts_dvalue dv, CacheValue VC')]]
          ).
        {
          unfold Environment.bind. rewrite app_comm_cons.

          pose (nxdF  := (cts_value vy, Some (CacheValue VCy), cts_dvalue dvy) :: xdF).
          pose (nxdF' := (cts_value vy, Some VCy', cts_dvalue dvy) :: xdF').

          assert (HVCu': VCu' = drop (length nxdF) VC).
          {
            unfold nxdF. unfold length. symmetry.
            eapply drop_cons; eauto.
          }

          rewrite HVCu'.
          eapply (Hrec n0) with
              (dEu := (vy, dvy) :: dEu)
              (Eu' := vy' :: Eu')
              (xdF' := (cts_value vy, Some VCy', cts_dvalue dvy) :: xdF');
            simpl in * |- *; eauto; try omega.

          - eapply LambdaALOperationalSemanticsProofs.modified_environment_bind; eauto.
          - eapply eval_context_ended_with_call; eauto. rewrite original_environment_app. eauto.
          - eapply eval_context_ended_with_call; eauto.
          - eapply derive_context_ended_with_call; eauto.
          - eapply extend_old_environment_with_call; eauto.
          - eapply extend_new_environment_with_call; eauto.
            eapply move_cts_value; eauto.
          - destruct (inverse_call_evaluation Holdeval). splitHyps.
            generalize (eval_deterministic H1 Hctsfx). intro He. inject He. eauto.
          - eapply modified_environment_bind; eauto. eapply move_cts_value; eauto.
          - destruct (inverse_call_evaluation Hneweval). destruct H1. splitHyps.
            generalize (eval_deterministic H1 Hctsfx'). intro He. inject He. eauto.
        }

        eapply TDPrimitiveNil; eauto.

        assert (CacheValue VCy = VCy0).
        {
          inverse Hctsfx.
          - inverse H14. simpl in H12. inverse H12. inverse H16. simpl in H8.
            inverse H8. clear H12 H8.
            assert (Vx = cts_value vx).
            {
              generalize (lookup_original_environment Holdlookupx). simpl. intro Hr.
              unfold lookup_value in H11. rewrite Hr in H11.
              simpl in H11. inverse H11. auto.
            }
            assert (p0 = p).
            {
              generalize (lookup_original_environment Holdlookupf). simpl. intro Hr.
              unfold lookup_value in H6. rewrite Hr in H6.
              simpl in H6. inverse H6. auto.
            }
            subst.
            rewrite Hprim in H13. inverse H13. eauto.
          - unfold lookup_value in H6.
            generalize (lookup_original_environment Holdlookupf). simpl. intro Hr. rewrite Hr in H6.
            simpl in H6. inverse H6.
        }
        subst.
        eauto.

      ** (** f is a closure, df is a dclosure. *)
        unfold Eu in * |- *.
        generalize (original_environment_lookup (dEu ++ dE) x). rewrite H4. intro Hlookupvx.
        generalize (original_environment_lookup (dEu ++ dE) f). rewrite H3. intro HlookupVf.
        generalize (modified_environment_lookup HEuE' x). rewrite H4.
        intro Hok. destruct Hok as [ vx' [ Hlookupvx' Hmovex ] ].
        generalize (modified_environment_lookup HEuE' f). rewrite H3.
        intro Hok. destruct Hok as [ Vf' [ HlookupVf' HmoveVf' ] ].
        unfold modified_binding in HmoveVf'. simpl in HmoveVf'.


        assert (vy0 = vy).
        {
          destruct (inv_success_mbind HmoveVf').
          rewrite H0 in HmoveVf'. simpl in HmoveVf'. inverse HmoveVf'.
          eauto.
          rewrite <- move_closure_environment_move_environment in H0.
          unfold denvironment_of_closure_denvironment in H0.
          rewrite list_of_closure_denvironment_closure_denvironment_of_list in H0.
          edestruct sound_eval with (v := vy).
          eapply closure_call_inversion; eauto.
          simpl in H1.
          eapply (deterministic_eval _ _ _ _ _ H9); eauto.
        }
        subst.

        unfold dF' in * |- *.
        destruct (extension_lookup_cts_denvironment Holdextend H3) as [ oldVCf Holdlookupf ].
        destruct (extension_lookup_cts_denvironment Holdextend H4) as [ oldVCx Holdlookupx ].

        destruct (extension_lookup_cts_denvironment Hnewextend H3) as [ VCf Hlookupf ].
        destruct (extension_lookup_cts_denvironment Hnewextend H4) as [ VCx Hlookupx ].

        assert ([[ dEu ++ dE ⊢ derive (@(f, x)) ⇓ dvy ]]).
        {
          simpl.
          eapply (SDefClosure NoSteps); eauto.
          eapply complete_eval; eauto.
          eapply erase_steps_evaluation; eauto.
          econstructor. simpl. eauto.
        }

        assert (Hmovevy : LambdaALOperationalSemantics.move vy dvy = Some vy').
        {
          eapply (derive_soundness2 _ Hfx Hfx' H0); eauto.
        }

        assert (HdEF': exists E', ⌈ dEf ⌉ = Some E').
        {
          destruct (inv_success_mbind HmoveVf').
          rewrite (move_original_closure_environment _ _ H1). eexists. eauto.
        }

        destruct HdEF' as [ E'' HE'' ].
        generalize (cts_denvironment_modified_environment2 HE'').
        intro HFf.

        (**

            By induction, we show that the remaining term of the derivative
            indeed produces a valid change and a valid cache.

         *)
        assert (
            Hdnext:
              [[#VCu',
                Environment.bind
                  (xdF' ++ cts_denvironment dE) (cts_value vy, Some VCy', cts_dvalue dvy)
                  ⊢ cts_derive_term (graft (graft ctx @( f, x)) u) u
                  ⇓ (cts_dvalue dv, CacheValue VC')]]
          ).
        {
          unfold Environment.bind. rewrite app_comm_cons.

          pose (nxdF  := (cts_value vy, Some (CacheValue VCy), cts_dvalue dvy) :: xdF).
          pose (nxdF' := (cts_value vy, Some VCy', cts_dvalue dvy) :: xdF').

          assert (HVCu': VCu' = drop (length nxdF) VC).
          {
            unfold nxdF. unfold length. symmetry.
            eapply drop_cons; eauto.
          }

          rewrite HVCu'.
          eapply (Hrec m) with
              (dEu := (vy, dvy) :: dEu)
              (Eu' := vy' :: Eu')
            (xdF' := (cts_value vy, Some VCy', cts_dvalue dvy) :: xdF');
            simpl in * |- *; eauto; try omega.

          - eapply LambdaALOperationalSemanticsProofs.modified_environment_bind; eauto.
          - eapply eval_context_ended_with_call; eauto. rewrite original_environment_app. eauto.
          - eapply eval_context_ended_with_call; eauto.
          - eapply derive_context_ended_with_call; eauto.
          - eapply extend_old_environment_with_call; eauto.
          - eapply extend_new_environment_with_call; eauto.
            eapply move_cts_value; eauto.
          - destruct (inverse_call_evaluation Holdeval). splitHyps.
            generalize (eval_deterministic H1 Hctsfx). intro He. inject He. eauto.
          - eapply modified_environment_bind; eauto. eapply move_cts_value; eauto.

          - destruct (inverse_call_evaluation Hneweval). splitHyps.
            generalize (eval_deterministic H1 Hctsfx'). intro He. inject He. eauto.
        }

        use TDClosureChange.

        {
          unfold cts_dterm.
          rewrite <- (derive_underive dtf) in H11.
          assert (Hn0 : n0 < S (k + n0 + m)) by omega.
          destruct VCy' as [ VCy' ].
          rewrite cts_closure_denvironment_cts_denvironment.

          assert (HequivEnv:
                    Environment.bind
                      (cts_denvironment dEf)
                      (cts_value vx, None, cts_dvalue dvx)
                    = nil ++ cts_denvironment ((vx, dvx) :: dEf)) by trivial.
          rewrite HequivEnv.

          assert (
              HVCy : VCy = drop (length (@nil (value * option cache_value))) VCy
            ) by eauto.
          rewrite HVCy.
          unfold cts_derive.

          assert (
              Hrelenvf:
                rel_env ⌊ dEf ⌋ dEf E''
            ).
          {
            intro k'.
            generalize (drel_env_lookup2 (HrelenvEu (S k')) HlookupVf HlookupVf' H3). simpl.
            intro HrelVf.
            rewrite unfold_drel_value in HrelVf. simpl in HrelVf. destruct Vf'. {
              assert (HSk : k' < S k') by auto.
              destruct (HrelVf _ HSk). splitHyps.
              rewrite list_of_values_of_values_of_list in H5.
              rewrite list_of_closure_denvironment_closure_denvironment_of_list in H5.
              assert (E'' = LambdaALValues.list_of_values v0).
              {
                generalize (move_original_closure_environment _ _ H2). intro. congruence.
              }
              subst.
              rewrite list_of_values_of_values_of_list in H1.
              unfold denvironment_of_closure_denvironment in H1.
              rewrite list_of_closure_denvironment_closure_denvironment_of_list in H1.
              eauto.
            }
            all: intuition.
          }

          assert (
            Hrelxvx:
              rel_value vx dvx vx'
          ).
          {
            intro k';
              eapply (drel_env_lookup2 (HrelenvEu k')); eauto;
                unfold Eu;
                rewrite original_environment_app; eauto.
          }

          assert (
            Hrelenvf':
              rel_env (vx :: ⌊ dEf ⌋) ((vx, dvx) :: dEf) (vx' :: E'')
          ) by (intro; eapply drel_env_bind_rel_value; eauto).

          assert (
              Hevalvy':
                [vx' :: E'' ⊢ underive dtf ⇓ vy']
            ).
          {
            generalize (modified_environment_lookup HEuE' f). rewrite H3.
            intro Hok. destruct Hok. destruct H1.
            simpl_inv_mbind_some.
            generalize (move_original_closure_environment _ _ Ha).
            intro Hok. rewrite HE'' in Hok. inverse Hok. clear Hok.
            eapply closure_call_inversion; eauto.
            rewrite values_of_list_of_list_of_values. eauto.
          }

          eapply (Hrec n0 Hn0)
            with
              (dEu := nil) (Eu' := nil)
              (xdF' := nil) (xdF := nil) (ctx := Var (Idx 0)) (v := vy) (v' := vy')
              (t0 := underive dtf) (u := underive dtf) (E := vx :: ⌊ dEf ⌋) (E' := vx' :: E'');
            try simpl in * |- *; try constructor; eauto.

          - eapply (Hrelenvf n).
          - eapply complete_eval; eauto.
          (* I expect the statement of Hbuggy1 and Hbuggy2 to change once I fix
             an efficiency bug in TDClosureChange. *)
          -
            (* assert ( *)
            (*   Hbuggy1: [#(cts_value vx, None) :: ⌊# cts_denvironment dEf ⌋ *)
            (*     ⊢ cts_term_aux (underive dtf) (underive dtf) ⇓ (cts_value vy, CacheValue VCy)] *)
            (* ). *)
          {
            simpl in HlookupVf.
            rewrite (list_of_closure_environment_of_closure_environment_of_list (F := ⌊# cts_denvironment dEf ⌋)).
            - eapply (inverse_closure_call_evaluation Hctsfx).
              + unfold lookup_value.
                rewrite (lookup_original_environment Holdlookupf). simpl. unfold ret.
                f_equal. f_equal.
                eapply cts_values_cts_denvironment; eauto.
              + unfold lookup_value.
                rewrite (lookup_original_environment Holdlookupx). simpl. unfold ret.
                f_equal.
            - eapply original_cts_denvironment_has_no_cache.
          }

          - eapply modified_environment_bind; eauto. simpl. eapply move_cts_value; eauto.

          - {
            rewrite (list_of_closure_environment_of_closure_environment_of_list (F := cts_environment E'')).
            - eapply (inverse_closure_call_evaluation Hctsfx'); unfold lookup_value.
              + destruct (lookup_modified_environment HF' Hlookupf).
                splitHyps.
                rewrite H1.
                unfold modified_binding in *.
                simpl_inv_mbind_some. f_equal.
                simpl_inv_mbind_some. f_equal.
                rewrite cts_values_cts_denvironment in Ha0.
                rewrite (move_closure_environment_cts_denvironment (E'' := E'')) in Ha0 by eauto.
                congruence.
              + destruct (lookup_modified_environment HF' Hlookupx).
                splitHyps.
                rewrite H1.
                unfold modified_binding in *. simpl in *. rewrite (move_cts_value Hmovex) in *.
                repeat simpl_inv_mbind_some. eauto.
            - eapply cts_environment_has_no_cache.
          }

        }

  * (** Case "let y = xs in u" *)
    inverse Hdeval.

    pose (vy := LambdaALValues.tuple vs).
    pose (dvy := LambdaALValues.dtuple dvs).

    generalize (cts_denvironment_lookups H3). rewrite cts_denvironment_app. intro Hll.
    destruct (extended_with_caches_lookups Holdextend Hll)
      as [ Bs [ Holdlookups [ HoldlookupsEq1 HoldlookupsEq2 ] ] ].
    destruct (extended_with_caches_lookups Hnewextend Hll)
      as [ Bs' [ Hnewlookups [ HnewlookupsEq1 HnewlookupsEq2 ] ] ].
    clear Hll.

    assert (xs0 = xs).
    {
      eapply reverse_map; eauto. intros. congruence.
    }
    subst. clear H.

    inverse Holdeval.
    assert (Vs = cts_values (LambdaALValues.values_of_list vs)).
    {
      unfold dF in H2.
      rewrite (lookup_values_original_environment Holdlookups) in H2.
      inverse H2. unfold vs. rewrite cts_values_cts_dbinding.
      rewrite <- HoldlookupsEq1. eauto.
    }
    subst.

    assert (HVCu:
              exists VCu', VCu = (cts_value (LambdaALValues.tuple vs), None) :: VCu'
            ).
    {
      unfold VCu.
      assert (exists preVC postVC,
                  VC = preVC ++ (cts_value vy, None) :: postVC
                  /\ List.length preVC = depth_of_term ctx).
      {
        unfold dF in H6.
        eapply (tuple_result_in_cache (u := u) (xs := xs)); eauto.

        econstructor; eauto.
        econstructor; eauto.
        simpl. eauto.
        constructor; eauto.
        constructor; eauto.
        rewrite <- graft_tuple. eauto.
      }
      destruct H as [ preVC [ postVC HVC ] ].
      splitHyps. rewrite H. exists postVC.
      assert (Hl: length xdF = depth_of_term ctx)
        by (eapply extension_length_is_depth_of_context; eauto).
      rewrite Hl. rewrite <- H0. rewrite drop_app. eauto.
    }

    destruct HVCu as [ VCu' HVCu ]. rewrite HVCu.

    pose (nxdF  := (cts_value vy, None, cts_dvalue dvy) :: xdF).

    assert (HVCu': VCu' = drop (length nxdF) VC).
    {
      unfold nxdF. unfold length. symmetry.
      eapply drop_cons; eauto.
    }

    inverse Hevalu'.

    assert (Hmove:
        LambdaALOperationalSemantics.move
          (LambdaALValues.tuple vs)
          (LambdaALValues.dtuple dvs)
        = Some (LambdaALValues.tuple vs0)
      ).
    {
      generalize (modified_environment_lookups xs HEuE'). rewrite H3.
      intro Hll. destruct Hll as [ vs00 [ Hvs00 Hlm ] ].
      unfold vs. unfold dvs.
      rewrite (move_tuple _ _ Hlm). congruence.
    }
    generalize (move_cts_value Hmove). intro Hmovects.

    assert (
        [[#drop (length nxdF) VC,
          Environment.bind
            dF'
            (ITuple (cts_values (LambdaALValues.values_of_list vs)), None,
              dITuple (map snd Bs')) ⊢ cts_derive_term (graft ctx (DefTuple xs u)) u
            ⇓ (cts_dvalue dv, CacheValue VC')]]
      ).
    {
      eapply (Hrec n0) with
          (dEu := (vy, dvy) :: dEu)
          (Eu' := (LambdaALValues.tuple vs0 :: Eu'))
          (xdF' := Environment.bind
                      xdF'
                      (ITuple (cts_values (LambdaALValues.values_of_list vs)),
                      None,
                      dITuple (map snd Bs')));
        simpl in * |- *; eauto; try omega.
      - eapply LambdaALOperationalSemanticsProofs.modified_environment_bind; eauto.
      - rewrite graft_tuple. eauto.
      - eapply eval_context_ended_with_tuple; eauto.
        rewrite original_environment_app.
        generalize (original_environment_lookups (dEu ++ dE) xs). rewrite H3. eauto.
      - inverse Hevalu. assert (vs1 = vs).
        generalize (original_environment_lookups (dEu ++ dE) xs). rewrite H3. eauto.
        rewrite <- original_environment_app. rewrite H4. unfold vs. congruence. subst.
        eauto.
      - eapply eval_context_ended_with_tuple; eauto.
      - eapply derive_context_ended_with_tuple; eauto.
      - eapply post_extend_old_with_tuple; eauto.
      - assert (cts_dvalues (LambdaALValues.ldvalues_of_list dvs) = map snd Bs').
        {
          unfold dvs. rewrite <- cts_dvalues_cts_dbinding_2.
          eauto.
        }
        rewrite <- H.
        eapply post_extend_new_with_tuple; eauto.

      - eapply modified_environment_bind; eauto.
        rewrite <- HnewlookupsEq2.
        rewrite cts_dvalues_cts_dbinding_2.
        eauto.
      - inverse Hneweval.
        assert (Vs = (cts_values (LambdaALValues.values_of_list vs0))).
        {
          rewrite (lookup_values_modified_environment HF' Hnewlookups) in H8.
          unfold vs in Hmovects.
          rewrite cts_values_cts_dbinding in Hmovects.
          rewrite <- HnewlookupsEq1 in H8.
          rewrite <- HnewlookupsEq2 in H8.
          unfold dvs in Hmovects.
          rewrite <- cts_dvalues_cts_dbinding_2 in Hmovects.
          rewrite H8 in Hmovects.
          simpl in Hmovects. inverse Hmovects. eauto.
        }
        subst.
        eauto.
    }

    eapply TDTuple; eauto.
    unfold vs. fold (cts_values (LambdaALValues.values_of_list (map fst bs))).
    rewrite cts_values_cts_dbinding. rewrite <- HnewlookupsEq1. eauto.

    Unshelve.
    all: try (exact 0).
    + eauto.
    + eauto.
Qed.

Lemma cts_derive_cts_dvalue:
  forall {n E dE E' u v v' dv VC VC' F'},
    rel_env E dE E' ->

    [ E ⊢ u ⇓ v ] ->

    [ E' ⊢ u ⇓ v' ] ->

    [[ dE ⊢ derive u ⇓ dv @ n]] ->

    LambdaALOperationalSemantics.move v dv = Some v' ->

    [# ⌊# cts_denvironment dE ⌋  ⊢ cts_term_aux u u ⇓ (cts_value v, CacheValue VC)] ->
    ⌈# cts_denvironment dE ⌉ = Some F' ->
    [# F' ⊢ cts_term_aux u u ⇓ (cts_value v', CacheValue VC')] ->

    [[#VC, cts_denvironment dE ⊢ cts_derive_term u u ⇓ (cts_dvalue dv, CacheValue VC')]].
Proof.
  intros.
  replace VC with (drop (length (@nil (value * option cache_value))) VC); simpl; eauto.
  eapply (cts_derive_cts_dvalue_gen
            (Eu' := nil) (dEu := nil) (ctx := Var (Idx 0))
            (xdF := nil) (xdF' := nil)
         ); simpl; try econstructor; simpl; eauto.
Qed.

Lemma original_environment_of_rel_env:
  forall {E dE E'},
    rel_env E dE E' ->
    cts_environment E = ⌊# cts_denvironment dE ⌋.
Proof.
  intros * Hrel.
  rewrite <- (original_env_of_drel_env (Hrel 0)).
  eapply cts_denvironment_original_environment.
Qed.

Lemma modified_environment_of_rel_env:
  forall {dE E E'},
    rel_env E dE E' ->
     exists F, ⌈# cts_denvironment dE ⌉ = Some F /\ cts_environment E' = F.
Proof.
  intros * Hrel.
  assert (Ho: 0 < 1) by auto.
  generalize (modified_env_of_drel_env Ho (Hrel 1)). intro Hd.
  exists (cts_environment E').
  split; trivial.
  clear Ho. clear Hrel.
  generalize Hd. generalize E'. clear Hd.
  induction dE; intros; unfold LambdaALOperationalSemantics.modified_environment in Hd; simpl in * |- *.
  unfold ret in Hd. inverse Hd. simpl. eauto.
  destruct (inv_success_mbind Hd). rewrite H in Hd. simpl in Hd.
  destruct (inv_success_mbind Hd). rewrite H0 in Hd. simpl in Hd.
  inverse Hd.
  simpl.
  unfold modified_environment in * |- *.
  simpl.
  rewrite (IHdE x0). simpl.
  unfold modified_binding. simpl.
  destruct a.
  rewrite (move_cts_value H). simpl.
  eauto.
  eauto.
Qed.

Theorem cts_derive_soundness:
  forall E dE E',
    (** Let [dE] be a valid denvironment between [E] and [E']. *)
    rel_env E dE E' ->

    forall t,

    (**

        Let [t] be a closure body. Its free variables are taken in [E]
        or [E'] and they are not attached to any cache. The
        intermediate values met during the evaluation of [t] are
        stored in a cache, given by [cache_of_term t].

     *)

    forall v v',

      (** Let us assume that [t] converges under both [E] and [E']. *)

      [ E  ⊢ t ⇓ v  ] ->
      [ E' ⊢ t ⇓ v' ] ->

      exists dv VC VC', (

            (**

               The cts compilation of [u] converges under the cts
               compilation of the original environment (Eu ++ E)
               and produces a value which is the cts compilation of
               [v], and a cache [VC].

             *)
                [# cts_environment E ⊢ cts_term t ⇓ (cts_value v, CacheValue VC) ] /\

                [# cts_environment E' ⊢ cts_term t ⇓ (cts_value v', CacheValue VC') ] /\

                [[# VC, cts_denvironment dE ⊢ cts_derive t ⇓ (cts_dvalue dv, CacheValue VC') ]] /\

                LambdaALOperationalSemantics.move v dv = Some v'
              ).
Proof.
  intros * HrelE * Hoeval Hmeval.

  (** The existence of [dv] is a direct consequence of the soundness
      of standard differentiation.  *)
  destruct (derive_soundness HrelE Hoeval Hmeval) as [ dv [ Hsound Hmove ] ].
  exists dv.

  (** [cts_term] is compatible with evaluation. *)
  destruct (eval_cts_compat Hoeval) as [ VC Hoctseval ].
  destruct (eval_cts_compat Hmeval) as [ VC' Hmctseval ].
  destruct VC as [ VC ]. exists VC.
  destruct VC' as [ VC' ]. exists VC'.
  split_conj; auto.

  (**
      We have reached the heart of this proof: when provided old
      caches, [cts_derive t] indeed computes [cts_dvalue dv] and the
      cache [VC'] is the same as the one produced by the modified cts
      evaluation.
   *)
  assert (Hderiven : exists n, [[dE ⊢ derive t ⇓ dv @ n]]) by (eapply step_indexed_evaluation; eauto).
  destruct Hderiven as [ n Hderiven ].
  clear Hsound.

  rewrite (original_environment_of_rel_env HrelE) in Hoctseval.
  destruct (modified_environment_of_rel_env HrelE) as [ F [ HF Hr ] ].
  rewrite Hr in Hmctseval.
  eapply cts_derive_cts_dvalue; eauto.

Qed.
