(** * Validity relation. *)

Require Import Equations.Equations.
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
Require Import LambdaALOperationalSemanticsPrimitives.
Require Import LambdaALOperationalSemantics.
Require Import LambdaALOperationalSemanticsProofs.
Require Import LambdaALDerive.

(** ** Axioms

   The following two axioms are needed. They are standard and as far
   as we know, they do not jeopardize the consistency of the logic.

*)

Axiom fun_extensionality:
  forall (A B: Type) (f g: A -> B),
  (forall x, f x = g x) -> f = g.

Axiom prop_extensionality:
  forall (P Q: Prop), (P <-> Q) -> P = Q.

(** ** Validity *)

(**

     The transformation relies on a strong invariant between the
     original environment, the modified environment and the
     environment of the derivative. It basically says that the
     environment of the derivative correctly relates base values with
     modified values.

*)

(** *** From ternary relations over values to ternary relations over environments. *)

(**

     An original environment [E] is related to a modified environment
     [E'] and a change environment [dE] if [E'] contains at least all
     the bindings of [E] and [dE] contains changes that relate the
     original values of [E] with the modified values of [E'].

*)

Inductive pre_drel_env (drel_value : value -> dvalue -> value -> Prop)
: environment -> denvironment -> environment -> Prop :=
| DrelNil:
    pre_drel_env drel_value nil nil nil
| DrelCons:
    forall v dv v' env denv env',
      drel_value v dv v' ->
      pre_drel_env drel_value env denv env' ->
      pre_drel_env drel_value (v :: env) ((v, dv) :: denv) (v' :: env').

Lemma pre_drel_env_alt:
  forall drel_value env denv env',
    pre_drel_env drel_value env denv env' ->
    (forall {x v}, lookup env x = Some v -> exists v', lookup env' x = Some v')
    /\
    (forall {x v}, lookup env x = Some v -> exists dv, lookup denv x = Some (v, dv))
    /\
    forall {x v' v},
      lookup env x = Some v ->
      lookup env' x = Some v' ->
      exists dv,
        lookup denv x = Some (v, dv) /\ drel_value v dv v'.
Proof.
  intros.
  induction H; simpl.
  - intuition; intros; unfold error in * |- *; try congruence.

  - intuition; intros. destruct x. destruct n. exists v'. auto.
    eapply H1; eauto.
    destruct x. destruct n. exists dv. unfold ret in * |- *. congruence.
    apply H3; eauto.
    destruct x. destruct n. exists dv. unfold ret in * |- *. intuition. congruence.
    inversion H2. inversion H5. subst. auto.
    apply H4; auto.
Qed.

Lemma pre_drel_env__lookup :
  forall {drel_value env denv env' x v v'},
    pre_drel_env drel_value env denv env' ->
    lookup env x = Some v ->
    lookup env' x = Some v' ->
    exists dv, lookup denv x = Some (v, dv) /\ drel_value v dv v'.
Proof.
  intros. generalize (pre_drel_env_alt drel_value env denv env' H).
  firstorder.
Qed.

(** *** Step-indexed relations between values *)

(**

   The construction of the step-indexed relation between values is
   highly inspired by the work of Xavier Leroy:

   http://pauillac.inria.fr/~xleroy/uncurry/doc/Uncurry.html

   We define the step-indexed relation [drel_value] as the partial
   composition of a functional [drel_value_F] which type is:

   forall j: nat, j < n -> value -> dvalue -> value -> Prop

*)

Section FUNCTOR.

Variable n: nat.

Variable rec_value:
  forall j: nat, j < n -> value -> dvalue -> value -> Prop.

Variable rec_term:
  forall j: nat, j < n -> environment -> denvironment -> environment -> term -> dterm -> term -> Prop.

Definition drel_value_F v dv v' :=
  match v, dv, v' with
    | _,  dReplace v'', _ =>
      v'' = v'

    | Literal l, dLiteral dl, Literal l' =>
      move_literal l dl = Some l'

    | Primitive _, dPrimitiveNil, _ =>
      v = v'

    | Closure Ef tf, dClosure dEf dtf, Closure Ef' tf' =>
      forall k (Hk: k < n),
        pre_drel_env (rec_value k Hk)
                     (list_of_values Ef)
                     (denvironment_of_closure_denvironment dEf)
                     (list_of_values Ef') /\
        move_closure_environment Ef dEf = Some Ef' /\
        ⌊ list_of_closure_denvironment dEf ⌋ = list_of_values Ef /\
        tf = tf' /\
        dtf = derive tf /\
        forall vx dvx vx',
          rec_value k Hk vx dvx vx' ->
          rec_term k Hk
                   (bind (list_of_values Ef) vx)
                   (bind (list_of_closure_denvironment dEf) (vx, dvx))
                   (bind (list_of_values Ef') vx') tf dtf tf'

    | Tuple xs, dTuple dxs, Tuple xs' =>
      move_values xs dxs = Some xs' /\
      forall k (Hk: k < n),
      values_forall2
        (fun i v v' =>
           rec_value k Hk v (List.nth i (list_of_ldvalues dxs) dPrimitiveNil) v'
        ) xs xs'

    | _, _, _ =>
      False

  end.

Lemma recurse_valid:
  forall {k env t v}, eval k env t v -> k < n -> n - k < n.
Proof.
  intros. generalize (at_least_one_step H). omega.
Qed.

Definition drel_term_F env denv env' t dt t' :=
  forall k (Hk: k < n) {v},
    forall (Heval : eval k env t v),
    forall {v'}, neval env' t' v' ->
      exists dv,
      rec_value (n - k) (recurse_valid Heval Hk) v dv v'
      /\ deval denv dt dv.

End FUNCTOR.

Definition drels_type (n : nat) := (
  (value -> dvalue -> value -> Prop)
* (environment -> denvironment -> environment -> term -> dterm -> term -> Prop)
)%type.

Definition drels_F n rec_funs :=
  let rec_value := fun k Hk => let '(f, _) := rec_funs k Hk in f in
  let rec_term := fun k Hk => let '(_, f) := rec_funs k Hk in f in
  (drel_value_F n rec_value rec_term,
   drel_term_F n rec_value).

(** Finally, the relation is obtained by a fixpoint of the functional
    using the induction principle of natural numbers. *)
Definition drels (k: nat) : drels_type k :=
  @Fix nat lt lt_wf drels_type drels_F k.

Definition drel_value k := let '(f, _) := drels k in f.
Definition drel_term k  := let '(_, f) := drels k in f.
Definition drel_env k   := pre_drel_env (drel_value k).

Notation "[ k ⊢ dv ▷ v ⤳ v' ]" := (drel_value k v dv v').

Inductive drel_value_inductive (n : nat) : value -> dvalue -> value -> Prop :=
| dReplaceValid:
    forall v v',
    drel_value_inductive n v (dReplace v') v'
| dLitValid :
    forall l dl l',
      move_literal l dl = Some l' ->
      drel_value_inductive n (Literal l) (dLiteral dl) (Literal l')
| dPrimitiveNilValid :
    forall p, drel_value_inductive n (Primitive p) dPrimitiveNil (Primitive p)
| dTupleValid : forall vs dvs vs',
    move_values vs dvs = Some vs' ->
    (forall k (Hk: k < n),
      values_forall2
        (fun i v v' =>
           drel_value k v (List.nth i (list_of_ldvalues dvs) dPrimitiveNil) v'
        ) vs vs') ->
      drel_value_inductive n (Tuple vs) (dTuple dvs) (Tuple vs')
| dClosureValid: forall Ef tf dEf dtf Ef' tf',
    (forall k (Hk: k < n),
        drel_env k
                 (list_of_values Ef)
                 (denvironment_of_closure_denvironment dEf)
                 (list_of_values Ef') /\
        move_closure_environment Ef dEf = Some Ef' /\
        ⌊ list_of_closure_denvironment dEf ⌋ = list_of_values Ef /\
        tf = tf' /\
        dtf = derive tf /\
        forall vx dvx vx',
          drel_value k vx dvx vx' ->
          drel_term k
                   (bind (list_of_values Ef) vx)
                   (bind (list_of_closure_denvironment dEf) (vx, dvx))
                   (bind (list_of_values Ef') vx') tf dtf tf') ->
    drel_value_inductive n (Closure Ef tf) (dClosure dEf dtf) (Closure Ef' tf').

Lemma unfold_drels:
  forall k, drels k = drels_F k (fun x H => drels x).
Proof.
  intros.
  unfold drels.
  rewrite (@Init.Wf.Fix_eq nat lt lt_wf drels_type drels_F).
  f_equal.
  intros.
  unfold drels_F. f_equal.
  unfold drel_value_F.
  apply fun_extensionality; intro v.
  apply fun_extensionality; intro dv.
  apply fun_extensionality; intro v'.
  destruct v; destruct dv; destruct v'; simpl; auto.

  - apply prop_extensionality. split.
    + intro Hr. intros j Hj. destruct (Hr j Hj).
      rewrite <- H. intuition.

    + intro Hr. intros j Hj. destruct (Hr j Hj).
      rewrite H. intuition.

  - apply prop_extensionality. split. intro Hr. destruct Hr as [ Hc Hr ]. split.
    + intuition.
    + intuition. rewrite <- H. auto.
    + intuition. rewrite H. auto.

  - unfold drel_term_F.
    apply fun_extensionality; intro env.
    apply fun_extensionality; intro denv.
    apply fun_extensionality; intro env'.
    apply fun_extensionality; intro t.
    apply fun_extensionality; intro dt.
    apply fun_extensionality; intro t'.
    apply prop_extensionality. split.

    + intros. destruct (H0 k0 Hk v Heval v' H1). rewrite <- H. auto.
    + intros. destruct (H0 k0 Hk v Heval v' H1). rewrite H. auto.
Qed.

(** The following equation is needed to reason about concrete
     instances of the relation. *)
Lemma unfold_drel_value :
  forall k, drel_value k =
            drel_value_F k
                         (fun (j : nat) (P: j < k) => drel_value j)
                         (fun (j : nat) (P: j < k) => drel_term j).
Proof.
  intros.
  unfold drel_value. rewrite unfold_drels.
  reflexivity.
Qed.

Ltac unfold_drel_value :=
  rewrite unfold_drel_value; unfold drel_value_F in * |- *.

Lemma drel_value_literal_inversion:
  forall l l' k dv,
    drel_value k (Literal l) dv (Literal l') ->
    dv = dPrimitiveNil \/
    dv = dReplace (Literal l') \/
    exists dl, dv = dLiteral dl.
Proof.
  intros *. unfold_drel_value. destruct dv; intro; try intuition.
  - destruct d; simpl in * |- *. right. right. exists (dPos n). auto.
  - right. left. congruence.
Qed.

Lemma drel_value_replace:
  forall k v v', [k ⊢ dReplace v' ▷ v ⤳ v'].
Proof.
  intros. unfold_drel_value. destruct v; easy.
Qed.

(** The following equation is needed to reason about concrete
     instances of the relation. *)
Lemma unfold_drel_term :
  forall k, drel_term k =
            drel_term_F k
                        (fun (j : nat) (P: j < k) => drel_value j).
Proof.
  intros.
  unfold drel_term. rewrite unfold_drels. unfold drel_term_F in * |- *.
  auto.
Qed.

Lemma drel_value_antimonotonic :
  forall n {v dv v'},
    forall k, k < n ->
    drel_value n v dv v' -> drel_value k v dv v'.
Proof.
  intros *. intro Hk. do 2 unfold_drel_value.
  destruct v; destruct dv; destruct v'; auto.
  - intros. assert (k0 < n) as Hkn.
    + omega.
    + destruct (H k0 Hkn). intuition.
  -
    intros. split; intuition.
Qed.

Lemma drel_env_antimonotonic :
  forall {n env denv env'},
    forall k, k < n ->
    drel_env n env denv env' ->
    drel_env k env denv env'.
Proof.
  unfold drel_env.
  intros.
  induction H0.
  constructor.
  constructor; try eapply drel_value_antimonotonic; eauto.
Qed.

Lemma drel_env_lookup {env denv env' k x v v'}:
  drel_env k env denv env' ->
  lookup env x = Some v ->
  lookup env' x = Some v' ->
  exists dv, lookup denv x = Some (v, dv) /\ drel_value k v dv v'.
Proof.
  apply pre_drel_env__lookup; auto.
Qed.

Lemma drel_env_lookup2 {env denv env' k x v v' dv}:
  drel_env k env denv env' ->
  lookup env x = Some v ->
  lookup env' x = Some v' ->
  lookup denv x = Some (v, dv) ->
  drel_value k v dv v'.
Proof.
  intros * Hrel Hl Hl' Hdl.
  destruct (drel_env_lookup Hrel Hl Hl').
  intuition.
  rewrite Hdl in H0. inverse H0. eauto.
Qed.

Lemma lookups_nil:
  forall {A} xs (v : list A), lookups nil xs = Some v -> xs = nil.
Proof.
  induction xs; simpl. auto.
  intros. destruct (lookups nil xs); simpl in H; congruence.
Qed.

Ltac case_elim x :=
  destruct x; subst; unfold ErrorMonad.ret, ErrorMonad.error in * |- *;
  simpl in * |- *; try congruence; try omega.

Lemma drel_value_move_value:
  forall {k},
    0 < k ->
    forall { v dv v' },
    [ k ⊢ dv ▷ v ⤳ v' ] ->
    v ⊕ dv = Some v'.
Proof.
  intros * Hk.
  unfold_drel_value.

  case_elim v; case_elim dv; case_elim v'; easy.
  - destruct (H 0 Hk).
    destruct H1.
    rewrite H1. simpl. easy.
  - rewrite H0. easy.
  - rewrite H. easy.
Qed.

Lemma drel_env_dlookups :
  forall k E dE E',
  0 < k ->
  drel_env k E dE E' ->
  forall {xs vs vs'},
  lookups E xs = Some vs ->
  lookups E' xs = Some vs' ->
  exists vdvs,
    lookups dE xs = Some vdvs
    /\ List.map fst vdvs = vs
    /\ let dvs := List.map snd vdvs in
      [ k ⊢ (dTuple (ldvalues_of_list dvs))
          ▷ Tuple (values_of_list vs) ⤳ Tuple (values_of_list vs')
      ].
Proof.
  intros * Hk Hrel.
  induction xs; simpl; unfold ret; intros.

  - inverse H0; inverse H; easy.
    exists nil. intuition.
    unfold_drel_value. easy.

  - destruct (inv_success_mbind H). rewrite H1 in H. simpl in H.
    destruct (inv_success_mbind H). rewrite H2 in H. simpl in H.
    destruct (inv_success_mbind H0). rewrite H3 in H0. simpl in H0.
    destruct (inv_success_mbind H0). rewrite H4 in H0. simpl in H0.
    inverse H. inverse H0.
    destruct (IHxs _ _ H1 H3). intuition. subst.
    rewrite H6. simpl.
    destruct (drel_env_lookup Hrel H2 H4). intuition.
    rewrite H7. simpl.
    eexists. easy.
    unfold_drel_value. easy.
    rewrite unfold_drel_value in H8. unfold drel_value_F in H8. intuition. rewrite H5.
    rewrite (drel_value_move_value Hk H9).
    simpl. easy.
    unfold values_forall2. simpl; easy. eapply drel_value_antimonotonic with (n := k); easy.
    rewrite unfold_drel_value in H8. unfold drel_value_F in H8. intuition.
    generalize (H10 _ Hk0).
    intro Hfl.
    unfold values_forall2 in Hfl.
    eapply (values_forall2_change _ _ _ _ _ _ Hfl); intros.
    Unshelve. intros. easy.
Qed.


Lemma original_env_of_drel_env:
  forall {k E dE E'},
    drel_env k E dE E' -> ⌊ dE ⌋ = E.
Proof.
  unfold drel_env.
  intros.
  induction H; easy.
Qed.

Lemma modified_env_of_drel_env:
  forall {k E dE E'},
    0 < k ->
    drel_env k E dE E' -> ⌈ dE ⌉ = Some E'.
Proof.
  intros.
  induction H0. auto.
  assert (Hk : 0 < k) by omega.
  generalize (drel_value_move_value Hk H0).
  replace ((v, dv) :: denv) with (bind denv (v, dv)); easy.
  erewrite modified_environment_bind; easy.
Qed.

Lemma related_lookups:
  forall env denv env' k x,
    drel_env k env denv env' ->
    drel_term k env denv env' (Var x) (dVar (d x)) (Var x).
Proof.
  intros. rewrite unfold_drel_term in * |- *; unfold drel_term_F in * |- *.
  intros. inversion Heval. inversion H0. subst.
  clear Heval H0.
  destruct (drel_env_lookup H H4 H7) as [dv Hdv].
  exists dv. intuition.
  eapply (drel_value_antimonotonic _ _ _ H1).
  econstructor; eauto.
  Unshelve.
  simpl. omega.
Qed.

Require Import LibTactics.

Lemma drel_value_inversion:
  forall n v dv v',
    drel_value n v dv v' ->
    drel_value_inductive n v dv v'.
Proof.
 intros * Hval.
 rewrite unfold_drel_value in * |- *.
 unfold drel_value_F in *;
   simpl in *;
   destruct v; destruct dv; destruct v';
   try elim Hval; try constructor; auto.
Qed.

Definition valid_dprimitive p :=
  forall v__x v__x' dv__x v v' k,
    k >= 1 ->
    drel_value k v__x dv__x v__x' ->
    eval_primitive p v__x = Some v ->
    eval_primitive p v__x' = Some v' ->
    exists dv, eval_dprimitive p v__x dv__x = Some dv /\ drel_value k v dv v'.

Lemma sound_recompute :
  forall p v__x v__x' dv__x v v' k,
    k >= 1 ->
    drel_value k v__x dv__x v__x' ->
    eval_primitive p v__x = Some v ->
    eval_primitive p v__x' = Some v' ->
    exists dv, recompute_primitive p v__x dv__x = Some dv /\ drel_value k v dv v'.
Proof.
  intros.
  unfold recompute_primitive.
  assert (Hk: 0 < k) by omega.
  erewrite (drel_value_move_value Hk H0). simpl. rewrite H2. simpl.
  eexists; intuition; unfold ret; try congruence.
  eapply drel_value_replace.
Qed.

Lemma sound_dadd : valid_dprimitive Add.
Proof.
  unfold valid_dprimitive; intros * Hk1 HxvValid Hev1 Hev2.
  unfold eval_primitive in * |- *.
  funelim (eval_add v__x);
  funelim (eval_add v__x'); try solve [ simpl_unfold_err; easy ].
  simpl_inv_mbind_some.
  apply drel_value_inversion in HxvValid.
  inverts HxvValid.
  + use sound_recompute. use drel_value_replace. easy.
  + apply invert_move_values_cons in H1.
    inversion_clear H1 as [dv1 [ dvs' [ Heq [ Hdv1 Hdvs ] ] ] ]. subst.
    apply invert_move_values_cons in Hdvs.
    inversion_clear Hdvs as [dv2 [ dvs'' [ Heq [ Hdv2 Hdvs' ] ] ] ]. subst.
    apply invert_move_values_nil in Hdvs'; subst.
    destruct dv1; inverts Hdv1;
      destruct dv2; inverts Hdv2;
        match_case_analysis; simpl_unfold_err; eexists; try split; eauto;
          repeat inverts_some; try constructor.
    rewrite unfold_drel_value.
    simpl in *.
    fequals. fequals. omega.
Qed.

Ltac simply_recompute t :=
  unfold valid_dprimitive; intros v__x v__x' * Hk1 HxvValid Hev1 Hev2;
  unfold eval_primitive in * |- *;
  funelim (t v__x);
  funelim (t v__x'); try solve [ simpl_unfold_err; easy ];
  simpl;
  use sound_recompute.


Lemma sound_dpush : valid_dprimitive Push.
Proof.
  simply_recompute (eval_push).
Qed.

Lemma sound_dcurry : valid_dprimitive Curry.
Proof.
  simply_recompute (eval_curry).
Qed.

Lemma sound_dfixrec : valid_dprimitive FixRec.
Proof.
  simply_recompute (eval_fixrec).
Qed.

Lemma sound_dprimitive:
  forall p, valid_dprimitive p.
Proof.
  destruct p; [
    eapply sound_dadd
  | eapply sound_dpush
  | eapply sound_dcurry
  | eapply sound_dfixrec
  ].
Qed.
