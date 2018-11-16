(** * Overview *)

(** ** Non-CTS Languages \(λ_{AL}\) and \(λ_{IAL}\) *)

(** The source language syntax. *)
Require Import LambdaAL.

(** The values of this language. *)
Require Import LambdaALValues.

(** A big-step step-indexed operational semantics for \(λ_{AL}\). *)
Require Import LambdaALOperationalSemantics.

(** We prove
    - that Step-indexed and non step-indexed semantics coincide ;
    - that λ_{AL} enjoys a deterministic operational semantics ;
    - and many projection lemmas from evaluations of change terms
      to evaluations of base terms.
*)
Require Import LambdaALOperationalSemanticsProofs.

(** ** Classic (non caching) static differentiation in \(λ_{AL}\) *)

(** The definition of the [derive] program transformation *)
Require Import LambdaALDerive.

(** A new correctness proof for this transformation. *)
Require Import LambdaALDeriveProofs.

(** It is based on a step-indexed relation called "validity". *)
Require Import LambdaALValidity.

(** Note: theorems are named following the numbering in the paper, so _3_1 is theorem 3.1. *)
(** ⊕ agrees with validity. *)
Theorem _3_1: forall k v dv v', 0 < k ->
  [ k ⊢ dv ▷ v ⤳ v' ] -> v ⊕ dv = Some v'.
Proof. intros. eapply drel_value_move_value; eauto. Qed.

(** Downward closure. *)
Lemma _3_2:
  forall n v dv v' k,
    k < n -> [ n ⊢ dv ▷ v ⤳ v' ] -> [ k ⊢ dv ▷ v ⤳ v' ].
Proof. intros. eapply drel_value_antimonotonic; eauto. Qed.

(** Fundamental property for this logical relation. *)
Require Import LambdaALFundamentalProperty.

(** Extension to environments. *)
Require Import LambdaALEnvValidity.

(** Soundness of differentiation in \(λ_{AL}\) *)
Theorem _3_3:
    forall {dE E E' t v v'},
    rel_env E dE E' ->
    [ E ⊢ t ⇓ v ] ->
    [ E' ⊢ t ⇓ v' ] ->
    exists dv, [[ dE ⊢ derive t ⇓ dv ]] /\ v ⊕ dv = Some v'.
Proof. intros. eapply derive_soundness; eauto. Qed.

(** Fundamental property. *)
Lemma _3_4:
  forall t env denv env' k,
    drel_env k env denv env' ->
    drel_term k env denv env' t (derive t) t.
Proof. intros. eapply fundamental_lemma; eauto. Qed.

(** ** CTS languages \(λ_{CAL}\) and \(λ_{ICAL}\) *)
Require ILambdaAL.

(** The values of this language. *)
Require Import ILambdaALValues.

(** A big-step step-indexed operational semantics for \(iλ_{AL}\). *)
Require Import ILambdaALOperationalSemantics.

(** ** Cache-Transfer Style differentiation *)

(** The definition of the [cts_derive] program transformation *)
Require Import ILambdaALDerive.

(** Properties of CTS terms. *)
Require Import ILambdaALCTSProofs.

(** Evaluation of base terms commutes with evaluation of CTS terms. *)
Theorem _3_5:
  forall {E u v},
    [ E ⊢ u ⇓ v ] ->
    exists VC,
    [# cts_environment E ⊢ cts_term_aux u u ⇓ (cts_value v, VC) ].
Proof. intros. eapply eval_cts_compat; eauto. Qed.

(* begin hide *)
Require Import Misc.
Require Import List.
(* end hide *)

(** Extension of environments with caches. *)
Require Import ILambdaALExtensionWithCaches.

(** A correctness proof for CTS differentiation. *)
Require Import ILambdaALDeriveProofs.

(** Evaluation of derivatives commutes with evaluation of CTS derivatives. *)
(** This is sketched as lemma 3.6 and stated formally in the appendix as lemma
    B.1. *)
Lemma _3_6_B_1:
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
Proof. intros. eapply cts_derive_cts_dvalue_gen; eauto. Qed.

(** Soundness of CTS differentiation. *)
Theorem _3_7:
  forall E dE E',
    rel_env E dE E' ->
    forall t v v',
      [ E  ⊢ t ⇓ v  ] -> [ E' ⊢ t ⇓ v' ] ->

      exists dv VC VC', (
          [# cts_environment E ⊢ cts_term t ⇓ (cts_value v, CacheValue VC) ] /\
          [# cts_environment E' ⊢ cts_term t ⇓ (cts_value v', CacheValue VC') ] /\
          [[# VC, cts_denvironment dE ⊢ cts_derive t ⇓ (cts_dvalue dv, CacheValue VC') ]] /\
          LambdaALOperationalSemantics.move v dv = Some v'
        ).
Proof. intros. eapply cts_derive_soundness; eauto. Qed.

