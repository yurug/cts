(** * Properties of operational semantics *)

Require Import Equations.Equations.
Require Misc.
Require Import Index.
Require Import ErrorMonad.
Require Import Omega.
Require Import List.
Require Import Misc.
Require Import LambdaAL.
Require Import Constants.
Require Import LambdaALValues.
Require Import LambdaALOperationalSemanticsPrimitives.
Require Import LambdaALOperationalSemantics.
Require Import LambdaALDerive.
Require Import Environment.
Require Import Crush.
Require Import FunInd.

Require Import Coq.Logic.FinFun.
(** ** Properties of functions over values *)

(** [values_of_list] is injective. *)
Lemma injective_values_of_list:
  forall l1 l2, values_of_list l1 = values_of_list l2 -> l1 = l2.
Proof.
  induction l1; intros; destruct l2; simpl in * |- *; try congruence.
  inversion H. subst. rewrite H2 in IHl1.
  f_equal. eapply IHl1; auto.
Qed.

Lemma values_of_list_of_list_of_values:
  forall vs, values_of_list (list_of_values vs) = vs.
Proof.
  induction vs; simpl; intros; auto.
  f_equal. auto.
Qed.

Lemma list_of_values_of_values_of_list:
  forall vs, list_of_values (values_of_list vs) = vs.
Proof.
  induction vs; simpl; intros; auto.
  f_equal. auto.
Qed.

Lemma list_of_ldvalues_of_ldvalues_of_list:
  forall x, list_of_ldvalues (ldvalues_of_list x) = x.
Proof.
  induction x; simpl; auto.
  rewrite IHx. auto.
Qed.

Lemma list_of_closure_denvironment_closure_denvironment_of_list:
  forall dE, list_of_closure_denvironment (closure_denvironment_of_list dE) = dE.
Proof.
  induction dE; easy.
Qed.

Lemma closure_denvironment_of_list_list_of_closure_denvironment:
  forall dE, closure_denvironment_of_list (list_of_closure_denvironment dE) = dE.
Proof.
  induction dE; easy.
Qed.

(*
References on LibTactics:
http://www.chargueraud.org/softs/tlc/
http://www.chargueraud.org/softs/tlc/src/TacticsOverview.html
https://softwarefoundations.cis.upenn.edu/plf-current/UseTactics.html
https://softwarefoundations.cis.upenn.edu/plf-current/LibTactics.html
*)
Require Import LibTactics.

Lemma injective_map_injf: forall {A B} {f : A -> B}, Injective f -> Injective (map f).
Proof.
  introv Hinj__f; intro xs1.
  induction xs1; intros xs2 H; destruct~ xs2; inverts H.
  fequals; auto.
Qed.

Lemma injective_d: Injective d.
Proof.
  introv H; inverts~ H.
Qed.

Lemma injective_map_d: Injective (map d).
Proof.
  apply (injective_map_injf injective_d).
Qed.

Lemma injective_und: Injective und.
Proof.
  intros dx1 dx2.
  destruct dx1. destruct dx2. simpl. congruence.
Qed.

Lemma injective_map_und: Injective (map und).
Proof.
  apply (injective_map_injf injective_und).
Qed.

Lemma injective_underive: forall dt1 dt2, underive dt1 = underive dt2 -> dt1 = dt2.
Proof.
  induction dt1 as [ dx | | ] ;
    intros * H;
    try destruct dx;
    destruct dt2 as [ dx | | ]; inverts H; try destruct dx; fequals; auto using injective_map_und.
Qed.

Lemma injective_closure_denvironment_of_list: forall dEf1 dEf2,
    closure_denvironment_of_list dEf1 = closure_denvironment_of_list dEf2 ->
    dEf1 = dEf2.
Proof.
  intros.
  rewrite <- (list_of_closure_denvironment_closure_denvironment_of_list dEf1).
  rewrite <- (list_of_closure_denvironment_closure_denvironment_of_list dEf2).
  congruence.
Qed.

Lemma values_forall2_change:
  forall (p p' : nat -> value -> value -> Prop) vs,
    (forall x y i, p i x y -> p' (S i) x y) ->
    forall vs' k,
    values_forall2_from p k vs vs' ->
    values_forall2_from p' (S k) vs vs'.
Proof.
  intros * H.

  induction vs; simpl in * |- *.

  destruct vs'; simpl in * |- *; auto.

  intuition.
  destruct vs'. auto.
  generalize (IHvs vs' (S k)).
  simpl.
  intros.
  intuition.
Qed.

(** ** Properties of change application *)

(** [move_closure_environment] and [move_environment] are consistent. *)
Lemma move_closure_environment_move_environment:
  forall E dEc,
  move_environment E (denvironment_of_closure_denvironment dEc) =
  move_closure_environment E dEc.
Proof.
  induction E; destruct dEc; simpl; auto.
  destruct (move v d); simpl; auto.
  rewrite IHE; auto.
Qed.

(** [dClosure dEf dtf] only applies to [Closure]s. *)
Lemma dclosure_only_applies_to_closure:
  forall {dEf dtf v v'},
    v ⊕ dClosure dEf dtf = Some v' ->
    exists Ef tf, v = Closure Ef tf.
Proof.
  intros * Heval.
  destruct v; inverse Heval; easy.
Qed.

Lemma move_tuple:
  forall vdvs vs,
    ErrorMonad.list_map (fun vdv => fst vdv ⊕ snd vdv) vdvs = Some vs ->
    tuple (List.map fst vdvs) ⊕ dtuple (List.map snd vdvs) = Some (tuple vs).
Proof.
  induction vdvs; simpl; intros.

  - inversion H. subst. auto.

  - destruct (inv_success_mbind H). rewrite H0 in * |- *. simpl in * |- *. clear H0.
    destruct (inv_success_mbind H). rewrite H0 in * |- *. simpl in * |- *. clear H0.
    inversion H. subst. clear H.
    generalize (IHvdvs x0 (@eq_refl _ (Some x0))). intro Hr.
    clear IHvdvs.
    destruct (move_values (values_of_list (map fst vdvs)) (ldvalues_of_list (map snd vdvs)));
      simpl in * |- *; unfold ret, tuple in * |- *; simpl; try congruence.
Qed.

Lemma move_replace:
  forall v v', v ⊕ dReplace v' = Some v'.
Proof.
  intros. destruct v; auto.
Qed.

Lemma invert_move_values_nil:
  forall dvs, move_values [@] dvs = Some [@] -> dvs = DVNil.
Proof.
  intros * H.
  destruct dvs; inverts~ H.
Qed.

Lemma invert_move_values_cons:
  forall v vs dvs0 v' vs',
    move_values (VCons v vs) dvs0 = Some (VCons v' vs') ->
    exists dv dvs, dvs0 = DVCons dv dvs /\ move v dv = Some v' /\ move_values vs dvs = Some vs'.
Proof.
  intros * H.
  destruct dvs0; inverts~ H.
  exists d dvs0. split; auto.
  unfold ret, mbind in H1.
  apply inv_success_mbind2 in H1. inverts H1 as [Heq H1].
  destruct (move_values vs dvs0);
  inverts H1; auto.
Qed.

Lemma recompute_primitive_eq:
  forall {p v dv v' vy},
    v ⊕ dv = Some v' ->
    eval_primitive p v' = Some vy ->
    recompute_primitive p v dv = Some (dReplace vy).
Proof.
  intros.
  unfold recompute_primitive.
  rewrite H. simpl. rewrite H0. eauto.
Qed.
 
Definition correct_dprimitive p :=
  forall v__x dv__x v__x' v__y dv__y,
    eval_primitive p v__x = Some v__y ->
    eval_dprimitive p v__x dv__x = Some dv__y ->
    v__x ⊕ dv__x = Some v__x' ->
    exists v__y', v__y ⊕ dv__y = Some v__y' /\ eval_primitive p v__x' = Some v__y'.

Lemma correct_recompute_primitive:
  forall {p v__x dv__x v__x' v__y dv__y},
    eval_primitive p v__x = Some v__y ->
    recompute_primitive p v__x dv__x = Some dv__y ->
    v__x ⊕ dv__x = Some v__x' ->
    exists v__y', v__y ⊕ dv__y = Some v__y' /\ eval_primitive p v__x' = Some v__y'.
Proof.
  intros.
  unfold recompute_primitive in * |- *.
  rewrite H1 in H0.
  simpl in * |- *.
  inv_mbind_some. inverse Hb. destruct H0. intuition.
  exists x. rewrite move_replace. intuition.
Qed.

Ltac dprimitive_correction_easy_part p :=
  funelim p; 
    try solve [ simpl_unfold_err; easy ];
    try solve [ eapply correct_recompute_primitive; eauto ].

Lemma correct_dprimitive_add : correct_dprimitive Add. 
Proof.
  unfold correct_dprimitive. intros.
  dprimitive_correction_easy_part (eval_dadd v__x dv__x).
  - simpl_inv_mbind_some; eexists; easy. do 3 fequals. omega.
Qed.

Lemma correct_dprimitive_push : correct_dprimitive Push. 
Proof.
  unfold correct_dprimitive. intros.
  eapply correct_recompute_primitive; eauto.
Qed.

Lemma correct_dprimitive_fixrec : correct_dprimitive FixRec.
Proof.
  unfold correct_dprimitive. intros.
  eapply correct_recompute_primitive; eauto.
Qed.

Lemma correct_dprimitive_curry : correct_dprimitive Curry. 
Proof.
  unfold correct_dprimitive. intros.
  eapply correct_recompute_primitive; eauto.
Qed.

Lemma move_with_eval_dprimitive:
  forall {p}, correct_dprimitive p.
Proof.
  introv.
  destruct p; [ 
    apply correct_dprimitive_add 
  | apply correct_dprimitive_push 
  | apply correct_dprimitive_curry 
  | apply correct_dprimitive_fixrec
  ].
Qed.

(** ** Properties of the operational semantics of base terms *)

(** To ease the definition of the step-indexed relation, we make sure
    that each evaluation step consumes at least one step. *)
Lemma at_least_one_step:
  forall {k E t v}, eval k E t v -> k > 0.
Proof.
  intros.
  destruct H; simpl in * |- *; omega.
Qed.

Lemma at_least_one_step_deval:
  forall {k dE dt dv}, gdeval Steps k dE dt dv -> k > 0.
Proof.
  intros.
  destruct H; simpl in * |- *; try omega.
Qed.

(** From a non indexed evaluation, it is possible to build a step-indexed one. *)
Theorem sound_eval:
  forall t E v, [ E ⊢ t ⇓ v ] -> exists n, [ E ⊢ t ⇓ v @ n ].
Proof.
  - intros t E v Heval; induction Heval.

    * exists 1. constructor. auto.

    * destruct IHHeval. exists (S x). eapply (STuple Steps); eauto.

    * destruct IHHeval as [ i IHH ].
      exists (S i).
      eapply (SPrimitiveCall Steps); eauto.

    * destruct IHHeval1, IHHeval2.
      exists (S (x0 + x1)). eapply (SClosureCall Steps); eauto.
Qed.

Theorem complete_eval:
  forall n t E v, [ E ⊢ t ⇓ v @ n ] -> [ E ⊢ t ⇓ v ].
Proof.
  intros n t E v Heval. induction Heval.
  * constructor; auto.
  * eapply (STuple NoSteps); eauto.
  * eapply (SPrimitiveCall NoSteps); eauto.
  * eapply (SClosureCall NoSteps); eauto.
    Unshelve. all: auto.
Qed.

(** Evaluation of base term is deterministic. *)
Theorem deterministic_eval:
  forall i n t env v,
  geval i n env t v ->
  forall m w, geval i m env t w -> v = w.
 Proof.
  intros * Heval1.
  induction Heval1; intros * Heval2; inversion Heval2; subst;
    unfold closure in * |-; try congruence.

  *  assert (vs = vs0) by congruence. subst.
     eapply IHHeval1; eauto.

  * assert (p = p0 /\ vx = vx0) by (intuition; congruence). intuition. subst.
    assert (v' = v'0) by (intuition; congruence). subst.
    eapply IHHeval1; eauto.

  * assert (tf = tf0 /\ vx = vx0) by (intuition; congruence).
    assert (Ef = Ef0). apply injective_values_of_list. congruence.
    intuition; subst.
    assert (vy = vy0) by (eapply IHHeval1_1; eauto; subst). subst.
    eapply IHHeval1_2; eauto.

Qed.

Theorem deterministic_deval:
  forall {dt dE dv dv'},
    [[ dE ⊢ dt ⇓ dv ]] ->
    [[ dE ⊢ dt ⇓ dv' ]] ->
    dv = dv'.
Proof.
  intros * Hdeval1.
  generalize dependent dv'.
  induction Hdeval1; intros * Hdeval2; inversion Hdeval2; subst;
    unfold closure, dclosure in * |-; try congruence.
  - apply IHHdeval1; clear IHHdeval1.
    assert (Hxs : xs0 = xs) by (auto using injective_map_d).
    subst xs0. clear H0.
    assert (bs = bs0) by congruence. subst bs0.
    inverts Hdeval2.
    assumption.
  - apply IHHdeval1; clear IHHdeval1.
    assert (Hvy : vy = vy0) by (eapply deterministic_eval; eauto); subst vy0.
    assert (He : E' = E'0) by congruence; subst E'0.
    assert (Hvy' : vy' = vy'0) by (eapply deterministic_eval; eauto); subst vy'0.
    assumption.
  - apply IHHdeval1; clear IHHdeval1.
    assert (p = p0) by congruence; subst p0.
    assert (vx = vx0) by congruence; subst vx0.
    assert (dvx = dvx0) by congruence; subst dvx0.
    assert (vy = vy0) by congruence; subst vy0.
    assert (dvy = dvy0) by congruence; subst dvy0.
    assumption.
  - apply IHHdeval1_2; clear IHHdeval1_2.
    assert (dtf = dtf0) by (apply injective_underive; congruence); subst dtf0.
    assert (dEf = dEf0) by (apply injective_closure_denvironment_of_list; congruence); subst dEf0.
    assert (vx = vx0) by congruence; subst vx0.
    assert (dvx = dvx0) by congruence; subst dvx0.
    assert (vy = vy0) by (eapply deterministic_eval; eauto); subst vy0.
    assert (dvy = dvy0) by auto; subst dvy0.
    assumption.
Qed.

(**
    Even though there are two rules for applications, we can recover
    a standard inversion lemma about the continuation of a let binding
    the result of an application.

*)
Lemma call_inversion:
  forall {E f x v t},
    [ E ⊢ Def f x t ⇓ v ] ->
    exists vy, [ E ⊢ @(f, x) ⇓ vy ] /\ [ bind E vy ⊢ t ⇓ v ].
Proof.
  intros. inverse H.
  - exists v'. intuition.
    use (SPrimitiveCall NoSteps); constructor; easy.

  - exists vy. intuition.
    use (SClosureCall NoSteps); constructor; easy.

    Unshelve. all: exact 0.
Qed.

Lemma closure_call_inversion:
  forall {E f x v tf Ef vx},
    [E ⊢ @( f, x) ⇓ v] ->
    Environment.lookup E x = Some vx ->
    Environment.lookup E f = Some (LambdaALValues.Closure (values_of_list Ef) tf) ->
    [vx :: Ef ⊢ tf ⇓ v].
Proof.
  intros * Heval Hlx Hlf.
  inverse Heval. congruence.
  assert (Ef0 = Ef). eapply injective_values_of_list.
  unfold closure in H2. congruence. subst.
  assert (tf = tf0). unfold closure in H2. congruence. subst.
  inverse H7. simpl in H0. inverse H0.
  assert (vx = vx0). congruence.
  subst.
  auto.
Qed.

Lemma primitive_call_inversion:
  forall {E f x v p vx},
    [E ⊢ @( f, x) ⇓ v] ->
    Environment.lookup E x = Some vx ->
    Environment.lookup E f = Some (LambdaALValues.Primitive p) ->
    eval_primitive p vx = Some v.
Proof.
  intros * Heval Hlx Hlf.
  inverse Heval. 
  assert (p = p0). congruence.
  assert (vx = vx0). congruence.
  subst.
  inverse H7. simpl in H0. inverse H0.
  eauto.
  unfold closure in H2. congruence.
Qed.

(**

    Similarly, the two rules for applications can be abstract by a
    single rule as long as we are not interested in the nature of the
    function being applied (i.e. if it is a closure or a primitive).

*)
Lemma call_evaluation:
  forall {E f x v t vy},
    [ E ⊢ @(f, x) ⇓ vy ] ->
    [ bind E vy ⊢ t ⇓ v ] ->
    [ E ⊢ Def f x t ⇓ v ].
Proof.
  intros.
  inverse H.
  - use (SPrimitiveCall NoSteps 0).
    inverse H9. inversion H2. easy.
  - use (SClosureCall NoSteps 0).
    inverse H9. inversion H2. easy.

    Unshelve. all: exact 0.
Qed.

(**

    Decomposition of evaluations

*)
Reserved Notation "[ E ⊢ ctx ⇑ E' ]".

Inductive eval_context: environment -> context -> environment -> Prop :=
| SNilContext: forall E x,
    [ E ⊢ Var x ⇑ nil ]

| STupleContext: forall E xs ctx E' v,
    [ v :: E ⊢ ctx ⇑ E' ] ->
    [ E ⊢ ttuple xs ⇓ v ] ->
    [ E ⊢ DefTuple xs ctx ⇑ E' ++ (cons v nil) ]

| SCallContext: forall E f x ctx E' v,
    [ v :: E ⊢ ctx ⇑ E' ] ->
    [ E ⊢ call f x ⇓ v ] ->
    [ E ⊢ Def f x ctx ⇑ E' ++ (cons v nil) ]

where "[ E ⊢ ctx ⇑ E' ]" := (eval_context E ctx E').

Lemma decompose_evaluation:
  forall {ctx t u E v},
    graft ctx u = t ->
    [ E ⊢ t ⇓ v ] ->
    exists E', [ E' ++ E ⊢ u ⇓ v ] /\ [ E ⊢ ctx ⇑ E' ].
Proof.
  induction ctx; simpl; intros; subst.
  - eexists nil; easy. constructor.
  - inverse H0;
      evar (v__n: value); remember v__n as v__n'; (* v__n and v__n' are only needed for the next two lines. *)
      destruct IHctx with (t := graft ctx u) (u := u) (E := bind E v__n) (v := v1); subst v__n; easy;
      exists (x ++ cons v__n' nil); subst v__n'; rewrite <- app_assoc; simpl; easy;
      apply SCallContext; easy.
    * use (SPrimitiveCall NoSteps); constructor; easy.
    * use (SClosureCall NoSteps); constructor; easy.
  - inverse H0.
    destruct IHctx with (t := graft ctx u) (u := u) (E := bind E (tuple vs)) (v := v); easy.
    exists (x ++ cons (tuple vs) nil). rewrite <- app_assoc. simpl. easy.
    constructor; easy. use (STuple NoSteps). constructor; easy.

    Unshelve. all: exact 0.
Qed.

Reserved Notation "[[ dE ⊢ dctx ⇑ dE' ]]".

Inductive eval_dcontext: denvironment -> dcontext -> denvironment -> Prop :=
| SDNilContext: forall dE x,
    [[ dE ⊢ dVar x ⇑ nil ]]

| SDTupleContext: forall dE xs dctx dE' v dv,
    [[ (v, dv) :: dE ⊢ dctx ⇑ dE' ]] ->
    [ ⌊ dE ⌋ ⊢ ttuple xs ⇓ v ] ->
    [[ dE ⊢ dttuple (List.map d xs) ⇓ dv ]] ->
    [[ dE ⊢ dDefTuple (List.map d xs) dctx ⇑ dE' ++ (cons (v, dv) nil) ]]

| SDCallContext: forall dE f x dctx dE' v dv,
    [[ (v, dv) :: dE ⊢ dctx ⇑ dE' ]] ->
    [ ⌊ dE ⌋ ⊢ call f x ⇓ v ] ->
    [[ dE ⊢ dcall f x ⇓ dv ]] ->
    [[ dE ⊢ dDef f x dctx ⇑ dE' ++ (cons (v, dv) nil) ]]

where "[[ dE ⊢ dctx ⇑ dE' ]]" := (eval_dcontext dE dctx dE').


(** ** Properties of the operational semantics of change terms

    An evaluation of a change term can be seen as a bi-evaluation of
    the same term under an original and a modified environment.

    In this section, we make explicit the two projections to extract
    these two evaluations from an evaluation of a change term.

*)

Lemma original_environment_bind:
  forall dE v dv, bind ⌊ dE ⌋ v = ⌊ bind dE (v, dv) ⌋.
Proof.
  induction dE; simpl; auto.
Qed.

Lemma original_environment_app:
  forall { dE dE' }, ⌊ dE ⌋ ++ ⌊ dE' ⌋ = ⌊ dE ++ dE' ⌋.
Proof.
  unfold original_environment. intros. rewrite map_app. eauto.
Qed.

Lemma modified_environment_bind:
  forall dE E v dv v',
    ⌈ dE ⌉ = Some E ->
    v ⊕ dv = Some v' ->
    ⌈ bind dE (v, dv) ⌉ = Some (bind E v').
Proof.
  induction dE; unfold bind, modified_environment, ErrorMonad.list_map;
    intros; simpl in * |- *; auto.

  - rewrite H0. simpl. inversion H. subst. auto.
  - rewrite H0; rewrite H; simpl; auto.
Qed.

Lemma modified_environment_app:
  forall { dE dE' E E' }, 
    ⌈ dE ⌉ = Some E ->
    ⌈ dE' ⌉ = Some E' ->
    ⌈ dE ++ dE' ⌉ = Some (E ++ E').
Proof.
  unfold modified_environment.
  intros. rewrite list_map_app.
  rewrite H. rewrite H0.
  simpl.
  eauto.
Qed.

Lemma inverse_modified_environment_bind:
  forall dE E v dv,
    ⌈ bind dE (v, dv) ⌉ = Some E ->
    exists v', v ⊕ dv = Some v'.
Proof.
  intros. unfold modified_environment in H.  unfold bind in H. simpl in H.
  destruct (inv_success_mbind H).
  exists x. auto.
Qed.

Lemma original_environment_lookup:
  forall dE x,
    match (lookup dE x) with
      | None => lookup ⌊ dE ⌋ x = None
      | Some b => lookup ⌊ dE ⌋ x = Some (fst b)
    end.
Proof.
  induction dE; simpl; intros; auto.
  destruct x; destruct n; destruct a; simpl; auto.
  generalize (IHdE (Idx n)). destruct (lookup dE (Idx n)).
  destruct p; simpl; auto.
  auto.
Qed.

Lemma modified_environment_lookup:
  forall {dE E},
    ⌈ dE ⌉ = Some E ->
    forall x, match (lookup dE x) with
      | None => lookup E x = None
      | Some (v, dv) => exists v', lookup E x = Some v' /\ v ⊕ dv = Some v'
    end.
Proof.
  induction dE; unfold bind, modified_environment;
    simpl; intros * H x.

  - inversion H; subst; auto.

  - destruct a. simpl in * |- *.
    destruct (inv_success_mbind H).
    rewrite H0 in H. simpl in H.
    destruct (inv_success_mbind H).
    rewrite H1 in H. simpl in H.
    inversion H. subst. clear H.

    destruct x; destruct n; simpl; auto.
    eexists; intuition.
    generalize (IHdE x1 H1 (Idx n)); auto.
Qed.

Lemma original_environment_lookups:
  forall dE xs,
    match (lookups dE xs) with
      | None => lookups ⌊ dE ⌋ xs = None
      | Some p => lookups ⌊ dE ⌋ xs = Some (List.map fst p)
    end.
Proof.
  induction xs; simpl; eauto.
  generalize (original_environment_lookup dE a).
  destruct (lookup dE a); intro Hr; rewrite Hr; simpl;
  destruct (lookups dE xs); simpl in * |- *; rewrite IHxs; simpl; eauto.
Qed.

Lemma modified_environment_lookups:
  forall {dE E} xs,
    ⌈ dE ⌉ = Some E ->
    match (lookups dE xs) with
      | None => lookups E xs = None
      | Some p => exists vs, lookups E xs = Some vs /\ ErrorMonad.list_map (fun a => fst a ⊕ snd a) p = Some vs
    end.
Proof.
  induction xs; simpl; eauto; intro HmE.
  generalize (modified_environment_lookup HmE a).
  destruct (lookup dE a); intros * Hr. destruct p. destruct Hr as [ v' Hr ]. destruct Hr as [ Hr Hr2 ].
  rewrite Hr; simpl.
  destruct (lookups dE xs); simpl in * |- *.
  destruct (IHxs HmE); simpl. destruct H.
  rewrite H; auto. simpl. eexists.
  intuition. rewrite Hr2. simpl. rewrite H0. simpl. auto.
  rewrite IHxs. simpl. auto. auto.
  simpl. rewrite inv_error_mbind. simpl.
  rewrite Hr. simpl.
  apply inv_error_mbind.
Qed.

Lemma move_original_closure_environment:
  forall (dEf : denvironment) (Ef' : values),
    move_closure_environment
      (values_of_list ⌊ dEf ⌋)
      (closure_denvironment_of_list dEf) = Some Ef' ->
    ⌈ dEf ⌉ = Some (list_of_values Ef').
Proof.
  induction dEf; intros; easy.
  - inverse H. easy.
  - destruct a. simpl in * |- *.
    destruct (inv_success_mbind H). rewrite H0 in H. simpl in H.
    destruct (inv_success_mbind H). rewrite H1 in H. simpl in H.
    inverse H.
    simpl.
    replace ((v, d) :: dEf) with (bind dEf (v, d)).
    erewrite modified_environment_bind; easy.
    easy.
Qed.

Lemma inverse_move_closure:
  forall {v tf dEf dtf},
    closure ⌊ dEf ⌋ tf ⊕ dclosure dEf dtf = Some v ->
    exists Ef', ⌈ dEf ⌉ = Some Ef' /\ v = closure Ef' tf.
Proof.
  intros.
  simpl in H.
  destruct (inv_success_mbind H) as [ Ef' HEf' ]. rewrite HEf' in H. simpl in H.
  inversion H. subst.
  unfold closure.
  exists (list_of_values Ef'). intuition.
  use move_original_closure_environment.
  rewrite values_of_list_of_list_of_values. easy.
Qed.

Lemma extract_original_and_modified_evaluation:
  forall dE dt dv,
    [[ dE ⊢ dt ⇓ dv ]] ->
    forall E', ⌈ dE ⌉ = Some E' ->
          exists v v',
            [ ⌊ dE ⌋ ⊢ underive dt ⇓ v  ]
            /\ [ E' ⊢ underive dt ⇓ v' ]
            /\ v ⊕ dv = Some v'.
Proof.
  intros * Hdeval; induction Hdeval; intros.

  - generalize (modified_environment_lookup H0 x). rewrite H. intro Hf. destruct Hf.
    generalize (original_environment_lookup dE x). rewrite H.
    intuition.
    eexists v, x0. intuition; use (SVar NoSteps).

  - generalize (modified_environment_lookups xs H0). rewrite H. intro Hf. destruct Hf.
    generalize (original_environment_lookups dE xs). rewrite H. intro Hxs.
    intuition.
    destruct IHHdeval with (E' := bind E' (tuple x)).
    erewrite modified_environment_bind; easy.
    use move_tuple.
    destruct H1. intuition.
    eexists x0, x1.
    intuition; use (STuple NoSteps).
    rewrite map_und_d_id. easy.
    rewrite map_und_d_id. easy.

  - generalize (modified_environment_lookup H3 f). rewrite H. intro Hf. destruct Hf.
    generalize (original_environment_lookup dE f). rewrite H.
    simpl. intuition.
    destruct IHHdeval with (E' := bind E' vy').
    erewrite modified_environment_bind; easy.
    use move_replace.
    destruct H4. intuition.
    eexists x1, x2.
    assert (E' = E'0). congruence. subst.
    intuition; eapply call_evaluation; easy.

  - generalize (modified_environment_lookup H3 f). rewrite H. intro Hf. destruct Hf.
    generalize (modified_environment_lookup H3 x). rewrite H0. intro Hf. destruct Hf.
    generalize (original_environment_lookup dE f). rewrite H.
    generalize (original_environment_lookup dE x). rewrite H0.
    simpl. intuition. subst.
    inverse H9.
    destruct (move_with_eval_dprimitive _ _ _ _ _ H1 H2 H10).
    intuition.
    destruct IHHdeval with (E' := bind E' x0).
    erewrite modified_environment_bind; easy.
    destruct H5. intuition.
    eexists x2, x3.
    intuition; use (SPrimitiveCall NoSteps).

  - generalize (modified_environment_lookup H4 f). rewrite H. intro Hf. destruct Hf.
    generalize (modified_environment_lookup H4 x). rewrite H0. intro Hf. destruct Hf.
    generalize (original_environment_lookup dE f). rewrite H.
    generalize (original_environment_lookup dE x). rewrite H0.
    simpl. intuition. subst.
    destruct (inverse_move_closure H10). intuition. subst.
    destruct IHHdeval1 with (E' := bind x2 x1). use modified_environment_bind.
    destruct H1.
    assert (x0 = vy). use deterministic_eval. subst.
    destruct IHHdeval2 with (E' := bind E' x3). use modified_environment_bind.
    easy.
    destruct H6. intuition.
    eexists x0, x4.
    intuition.
    use (SClosureCall NoSteps 0).
    use (SClosureCall NoSteps 0).

    Unshelve. all: exact 0.
Qed.

Lemma decompose_devaluation:
  forall {dctx dt du dE dv},
    dgraft dctx du = dt ->
    [[ dE ⊢ dt ⇓ dv ]] ->
    exists dE', [[ dE' ++ dE ⊢ du ⇓ dv ]] /\ [[ dE ⊢ dctx ⇑ dE' ]].
Proof.
  induction dctx; simpl; intros; subst.
  - eexists nil; easy. constructor.
  - inverse H0.
    * destruct IHdctx with (dt := dgraft dctx du) (du := du) (dE := bind dE (vy, dReplace vy')) (dv := dv); easy.
      exists (x ++ cons (vy, dReplace vy') nil). rewrite <- app_assoc. simpl. easy. apply SDCallContext; easy.
      eapply (SDReplaceCall NoSteps); easy.
      use (SDVar NoSteps).
    *
      destruct IHdctx with (dt := dgraft dctx du) (du := du) (dE := bind dE (vy, dvy)) (dv := dv); easy.
      exists (x ++ cons (vy, dvy) nil). rewrite <- app_assoc. simpl. easy.
      apply SDCallContext; easy.
      -- use (SPrimitiveCall NoSteps).
         ++ lets Hlookup : original_environment_lookup dE v. replace (lookup dE v) with (Some (Primitive p, dPrimitiveNil)) in Hlookup by auto. eassumption.
         ++ lets Hlookup : original_environment_lookup dE v0. replace (lookup dE v0) with (Some (vx, dvx)) in Hlookup by auto. eassumption.
         ++ simpl. constructor. auto.
      -- use (SPrimitiveNil NoSteps). use (SDVar NoSteps).
    *
      destruct IHdctx with (dt := dgraft dctx du) (du := du) (dE := bind dE (vy, dvy)) (dv := dv); easy.
      exists (x ++ cons (vy, dvy) nil). rewrite <- app_assoc. simpl. easy.
      apply SDCallContext; easy.
      -- eapply (SClosureCall NoSteps).
         ++ lets Hlookup : original_environment_lookup dE v. replace (lookup dE v) with (Some (closure ⌊ dEf ⌋ (underive dtf), dclosure dEf dtf)) in Hlookup by auto. eassumption.
         ++ lets Hlookup : original_environment_lookup dE v0. replace (lookup dE v0) with (Some (vx, dvx)) in Hlookup by auto. eassumption.
         ++ eassumption.
         ++ simpl. constructor. auto.
      -- use (SDefClosure NoSteps). use SDVar.
  - inverse H0.
    destruct IHdctx with (dt := dgraft dctx du) (du := du) (dE := bind dE (tuple vs, dtuple dvs)) (dv := dv); easy.
    exists (x ++ cons (tuple vs, dtuple dvs) nil). rewrite <- app_assoc. simpl. easy.
    constructor; easy.
    use (STuple NoSteps).
    + lets Hlookups : original_environment_lookups dE xs. replace (lookups dE xs) with (Some bs) in Hlookups by assumption. eassumption.
    + constructor. auto.
    + use (SDTuple NoSteps).
      use (SDVar NoSteps).
    Unshelve. all: exact 0.
Qed.

Lemma step_indexed_dcall_inversion:
  forall {f x dt dE dv n},
    [[ dE ⊢ dDef f x dt ⇓ dv @ n]] ->
    exists u du k m,
      [[ dE ⊢ dcall f x ⇓ du @ m ]] /\ m <= n
      /\ [ ⌊ dE ⌋ ⊢ @(f, x) ⇓ u ]
      /\ [[ bind dE (u, du) ⊢ dt ⇓ dv @ k ]] /\ k < n.
Proof.
  intros. 
  generalize (at_least_one_step_deval H). intro Hn.
  inverse H.
  - generalize (at_least_one_step_deval H10). intro Hn0.
    generalize (at_least_one_step H4). intro Hk. 
    generalize (at_least_one_step H9). intro Hm. 
    simpl in * |- *.
    exists vy (dReplace vy'). exists n0 (S (k + m + 1)).
    intuition easy.
    + eapply (SDReplaceCall Steps k m 1); eauto.
      eapply (SDVar Steps); eauto.
      simpl. eauto.
    + eapply complete_eval; eauto.
  - generalize (at_least_one_step_deval H10). intro Hn0.
    simpl in * |- *.
    do 2 eexists. exists n0 (S (1)).
    intuition easy.
    + eapply (SPrimitiveNil Steps); eauto. eapply SDVar; simpl; eauto.
    + use (SPrimitiveCall NoSteps).
      * lets Hlookup : original_environment_lookup dE __. replace (lookup dE f) with (Some (Primitive p, dPrimitiveNil)) in Hlookup by auto. eassumption.
      * lets Hlookup : original_environment_lookup dE __. replace (lookup dE x) with (Some (vx, dvx)) in Hlookup by auto. eassumption.
      * simpl. constructor. auto.
  - generalize (at_least_one_step_deval H11). intro Hn0.
    generalize (at_least_one_step_deval H12). intro Hm.
    simpl in * |- *.
    do 2 eexists. exists m (S (k + n0 + 1)).
    intuition easy.
    + use (SDefClosure Steps k n0 1). use SDVar.
    + use (SClosureCall NoSteps).
      * lets Hlookup : original_environment_lookup dE f.
        replace (lookup dE f) with (Some (closure ⌊ dEf ⌋ (underive dtf), dclosure dEf dtf)) in Hlookup by auto. eassumption.
      * lets Hlookup : original_environment_lookup dE x. replace (lookup dE x) with (Some (vx, dvx)) in Hlookup by auto. eassumption.
      * simpl. eapply complete_eval; eauto.
      * eapply complete_eval; eauto.
        eapply (SVar Steps); eauto.

    Unshelve. all: exact 0.
Qed.

Lemma erase_steps_evaluation:
  forall {dE dt dv n},
    [[ dE ⊢ dt ⇓ dv @ n]] ->
    [[ dE ⊢ dt ⇓ dv ]].
Proof.
  intros * Heval. induction Heval; simpl in * |- *; try (econstructor; eauto).
  - eapply (SDTuple NoSteps); eauto.
  - eapply (SDReplaceCall NoSteps); eauto.
    eapply complete_eval; eauto.
    eapply complete_eval; eauto.
  - eapply (SPrimitiveNil NoSteps); eauto.
  - eapply (SDefClosure NoSteps); eauto.
    eapply complete_eval; eauto.
    Unshelve. all: exact 0.
Qed.

Lemma step_indexed_evaluation:
  forall {dE dt dv},
    [[ dE ⊢ dt ⇓ dv ]] ->
    exists n, [[ dE ⊢ dt ⇓ dv @ n ]].
Proof.
  intros * Heval. induction Heval; simpl in * |- *.
  - eexists; econstructor; eauto.
  - destruct IHHeval; try (eexists; econstructor; eauto).
  - destruct IHHeval; 
    destruct (sound_eval _ _ _ H0);
    destruct (sound_eval _ _ _ H2);
    try (eexists; econstructor; eauto).
  - destruct IHHeval. 
    eexists. eapply SPrimitiveNil; eauto.
  - destruct IHHeval1; destruct IHHeval2.
    destruct (sound_eval _ _ _ H3);
    eexists. eapply SDefClosure; eauto.
Qed.

Lemma dcall_inversion:
  forall f x dt dE dv,
    [[ dE ⊢ dDef f x dt ⇓ dv ]] ->
    exists u du, [[ dE ⊢ dcall f x ⇓ du ]]
          /\ [ ⌊ dE ⌋ ⊢ @(f, x) ⇓ u ]
          /\ [[ bind dE (u, du) ⊢ dt ⇓ dv ]].
Proof.
  intros. destruct (step_indexed_evaluation H) as [ n Heval ].
  inverse Heval.
  destruct (step_indexed_dcall_inversion Heval) as [ u [ du [ k' [ m' Hu ] ] ] ].
  do 2 eexists. intuition; try eapply erase_steps_evaluation; eauto.
  destruct (step_indexed_dcall_inversion Heval) as [ u [ du [ k' [ m'  Hu ] ] ] ].
  do 2 eexists. intuition; try eapply erase_steps_evaluation; eauto.
  destruct (step_indexed_dcall_inversion Heval) as [ u [ du [ k' [ m'  Hu ] ] ] ].
  do 2 eexists. intuition; try eapply erase_steps_evaluation; eauto.
Qed.

(** Check that "(curry f) x y = f (x, y)". *)
Lemma curry_adequacy:
  forall vx vy v Ef tf,
    let vf := Closure Ef tf in

    (* x = vx, y = vy, f = vf, p = Curry*)
    let E' := vx :: vy :: vf :: (Primitive Curry) :: nil in

    (* let z = (x, y) in
       f z *)
    let direct_call :=
        DefTuple [Idx 0; Idx 1] (
          call (Idx 3) (Idx 0)
        )
    in
    (* let z = p f in
       let w1 = z x in
       let w2 = w1 y in
       w2
     *)
    let first_curry_then_apply_twice :=
        Def (Idx 3) (Idx 2) (
              Def (Idx 0) (Idx 1) (
                    Def (Idx 0) (Idx 3) (
                          Var (Idx 0)
                        )
                  )
            )
    in
    [ E' ⊢ direct_call ⇓ v ] -> [ E' ⊢ first_curry_then_apply_twice ⇓ v ].
Proof.
  intros.
  unfold vf, direct_call, first_curry_then_apply_twice in * |- *.
  inverse H. inverse H2.
  inverse H4; inverse H5. 
  eapply (SPrimitiveCall NoSteps). simpl. eauto.
  simpl. eauto.
  simpl. eauto.
  eapply (SClosureCall NoSteps). simpl. unfold ret. f_equal.
  unfold closure. f_equal. rewrite values_of_list_of_list_of_values. eauto.
  simpl. eauto.
  eapply (STuple NoSteps). simpl. unfold ret. f_equal.
  eapply (SPrimitiveCall NoSteps). simpl. eauto.
  simpl. unfold ret. f_equal. simpl.
  unfold ret. f_equal.
  eapply (SVar NoSteps). simpl. eauto.
  eapply (SClosureCall NoSteps). simpl. unfold ret. f_equal.
  unfold closure. f_equal. rewrite values_of_list_of_list_of_values. eauto.
  simpl. eauto.
  eapply (STuple NoSteps). simpl. unfold ret. f_equal.
  eapply (SClosureCall NoSteps). simpl. unfold ret. f_equal.
  unfold closure. f_equal. 
  simpl. eauto.
  eauto.
  eapply (SVar NoSteps). simpl. eauto.
  eapply (SVar NoSteps). simpl.
  inverse H10. simpl in H1. inverse H1.
  eauto.
Qed.