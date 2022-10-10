Require Import Coq.Strings.String.
Require Import Coq.Sets.Ensembles Coq.ZArith.ZArith.
Require Import LambdaANF.Ensembles_util LambdaANF.map_util LambdaANF.List_util.
Require Import LambdaANF.state LambdaANF.alpha_conv LambdaANF.identifiers LambdaANF.functions LambdaANF.shrink_cps LambdaANF.stemctx.
Require Import LambdaANF.Prototype.
Require Import LambdaANF.cps_proto LambdaANF.proto_util.

Require Import Lia.

Require Import Coq.Lists.List.
Import ListNotations.

(* TODO: move to proto_util *)

Fixpoint occurs_free_ces (ces : list (cps.ctor_tag * cps.exp)) :=
  match ces with
  | [] => Empty_set _
  | (c, e) :: ces => occurs_free e :|: occurs_free_ces ces
  end.

Lemma occurs_free_Ecase x ces :
  occurs_free (cps.Ecase x ces) <--> x |: occurs_free_ces ces.
Proof.
  induction ces as [|[c e] ces IHces]; cbn; repeat normalize_occurs_free; [eauto with Ensembles_DB|].
  rewrite IHces; split; eauto 3 with Ensembles_DB.
Qed.

Lemma used_vars_ces_bv_fv ces :
  used_vars_ces ces <--> bound_var_ces ces :|: occurs_free_ces ces.
Proof.
  induction ces as [|[c e] ces IHces]; cbn; eauto with Ensembles_DB.
  rewrite IHces; unfold used_vars; split; eauto with Ensembles_DB.
Qed.

Lemma occurs_free_ctx_mut :
  (forall (c : ctx.exp_ctx) (e e' : cps.exp),
   occurs_free e \subset occurs_free e' ->
   occurs_free (ctx.app_ctx_f c e) \subset occurs_free (ctx.app_ctx_f c e')) /\
  (forall (B : ctx.fundefs_ctx) (e e' : cps.exp),
   occurs_free e \subset occurs_free e' ->
   occurs_free_fundefs (ctx.app_f_ctx_f B e) \subset occurs_free_fundefs (ctx.app_f_ctx_f B e')).
Proof.
  apply ctx.exp_fundefs_ctx_mutual_ind; intros; cbn; repeat normalize_occurs_free;
  rewrite <- ?name_in_fundefs_ctx_ctx; eauto with Ensembles_DB.
Qed.
Corollary occurs_free_exp_ctx c e e' :
  occurs_free e \subset occurs_free e' ->
  occurs_free (ctx.app_ctx_f c e) \subset occurs_free (ctx.app_ctx_f c e').
Proof. apply occurs_free_ctx_mut. Qed.
Corollary occurs_free_fundefs_ctx B e e' :
  occurs_free e \subset occurs_free e' ->
  occurs_free_fundefs (ctx.app_f_ctx_f B e) \subset occurs_free_fundefs (ctx.app_f_ctx_f B e').
Proof. apply occurs_free_ctx_mut. Qed.

Definition well_scoped e := unique_bindings e /\ Disjoint _ (bound_var e) (occurs_free e).
Definition well_scoped_fds fds :=
  unique_bindings_fundefs fds /\ Disjoint _ (bound_var_fundefs fds) (occurs_free_fundefs fds).

(* TODO: Move to Ensembles_util.v *)
Lemma Disjoint_Setminus_bal : forall {A} (S1 S2 S3 : Ensemble A),
  Disjoint _ (S1 \\ S3) (S2 \\ S3) ->
  Disjoint _ (S1 \\ S3) S2.
Proof.
  clear; intros A S1 S2 S3 [Hdis]; constructor; intros arb.
  intros [arb' [HS1 HS3] HS2]; clear arb.
  apply (Hdis arb'); constructor; constructor; auto.
Qed.

Ltac DisInc H := eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply H]].
Lemma stem_not_free_mut :
  (forall (c : ctx.exp_ctx) (e_arb e : cps.exp),
    well_scoped (ctx.app_ctx_f c e_arb) ->
    Disjoint _ (bound_stem_ctx c) (occurs_free (ctx.app_ctx_f c e))) /\
  (forall (B : ctx.fundefs_ctx) (e_arb e : cps.exp),
    well_scoped_fds (ctx.app_f_ctx_f B e_arb) ->
    Disjoint _ (names_in_fundefs_ctx B :|: bound_stem_fundefs_ctx B)
             (occurs_free_fundefs (ctx.app_f_ctx_f B e))).
Proof. 
  apply ctx.exp_fundefs_ctx_mutual_ind; unfold well_scoped.
  - intros e_arb e [Huniq Hdis]; cbn in *.
    normalize_bound_stem_ctx; eauto with Ensembles_DB.
  - intros x c ys C IH e_arb e [Huniq Hdis]; cbn in *.
    normalize_bound_stem_ctx; normalize_occurs_free; eauto with Ensembles_DB.
    inv Huniq; change (~ ?S ?x) with (~ x \in S) in *.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free); intros Hdis.
    apply Union_Disjoint_l; apply Union_Disjoint_r.
    + rewrite bound_var_app_ctx, Union_demorgan in H1.
      rewrite bound_var_app_ctx in Hdis.
      DisInc Hdis; eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_l; apply bound_stem_var.
    + eapply Disjoint_Included_r; [|apply (IH e_arb e)]; eauto with Ensembles_DB; normalize_roundtrips.
      split; auto.
      erewrite <- (Setminus_Disjoint (bound_var _)); [|apply Disjoint_Singleton_r, H1].
      apply Disjoint_Setminus_bal.
      DisInc Hdis; eauto with Ensembles_DB.
    + DisInc Hdis; eauto with Ensembles_DB.
    + eauto with Ensembles_DB.
  - intros x t n y C IH e_arb e [Huniq Hdis].
    specialize (IH e_arb e); cbn in *.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free || normalize_bound_stem_ctx); intros Hdis;
    inv Huniq; change (~ ?S ?x) with (~ x \in S) in *;
    apply Union_Disjoint_l; apply Union_Disjoint_r; try solve [eauto with Ensembles_DB
                                                              |DisInc Hdis; eauto with Ensembles_DB].
    + rewrite bound_var_app_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_l; apply bound_stem_var.
    + eapply Disjoint_Included_r; [|apply IH]; eauto with Ensembles_DB; normalize_roundtrips.
      split; auto.
      erewrite <- (Setminus_Disjoint (bound_var _)); [|apply Disjoint_Singleton_r, H1].
      apply Disjoint_Setminus_bal.
      DisInc Hdis; eauto with Ensembles_DB.
  - intros x f ft ys C IH e_arb e [Huniq Hdis].
    specialize (IH e_arb e); cbn in *.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free || normalize_bound_stem_ctx); intros Hdis;
    inv Huniq; change (~ ?S ?x) with (~ x \in S) in *;
    apply Union_Disjoint_l; apply Union_Disjoint_r; try solve [eauto with Ensembles_DB
                                                              |DisInc Hdis; eauto with Ensembles_DB].
    + rewrite bound_var_app_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_l; apply bound_stem_var.
    + eapply Disjoint_Included_r; [|apply IH]; eauto with Ensembles_DB; normalize_roundtrips.
      split; auto.
      erewrite <- (Setminus_Disjoint (bound_var _)); [|apply Disjoint_Singleton_r, H1].
      apply Disjoint_Setminus_bal.
      DisInc Hdis; eauto with Ensembles_DB.
  - intros x p ys C IH e_arb e [Huniq Hdis].
    specialize (IH e_arb e); cbn in *.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free || normalize_bound_stem_ctx); intros Hdis;
    inv Huniq; change (~ ?S ?x) with (~ x \in S) in *;
    apply Union_Disjoint_l; apply Union_Disjoint_r; try solve [eauto with Ensembles_DB
                                                              |DisInc Hdis; eauto with Ensembles_DB].
    + rewrite bound_var_app_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_l; apply bound_stem_var.
    + eapply Disjoint_Included_r; [|apply IH]; eauto with Ensembles_DB; normalize_roundtrips.
      split; auto.
      erewrite <- (Setminus_Disjoint (bound_var _)); [|apply Disjoint_Singleton_r, H1].
      apply Disjoint_Setminus_bal.
      DisInc Hdis; eauto with Ensembles_DB.
  - intros x ces1 c C IH ces2 e_arb e [Huniq Hdis].
    specialize (IH e_arb e); cbn in *.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free || normalize_bound_stem_ctx); intros Hdis.
    rewrite unique_bindings_Ecase_app in Huniq.
    destruct Huniq as [Huniq1 [Huniq2 Huniq3]].
    inv Huniq2; change (~ ?S ?x) with (~ x \in S) in *.
    apply Union_Disjoint_r; [|apply Union_Disjoint_r; [|apply Union_Disjoint_r]].
    + rewrite bound_var_app_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
      apply Included_Union_preserv_r; do 2 apply Included_Union_preserv_l; apply bound_stem_var.
    + rewrite bound_var_app_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
      apply Included_Union_preserv_r; do 2 apply Included_Union_preserv_l; apply bound_stem_var.
    + eapply Disjoint_Included_r; [|apply IH]; eauto with Ensembles_DB; normalize_roundtrips.
      split; auto. DisInc Hdis; eauto with Ensembles_DB.
    + rewrite bound_var_app_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
      apply Included_Union_preserv_r; do 2 apply Included_Union_preserv_l; apply bound_stem_var.
  - intros fds C IH e_arb e [Huniq Hdis].
    specialize (IH e_arb e); cbn in *.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free || normalize_bound_stem_ctx); intros Hdis;
    inv Huniq; change (~ ?S ?x) with (~ x \in S) in *;
    apply Union_Disjoint_l; apply Union_Disjoint_r; try solve [eauto with Ensembles_DB
                                                              |DisInc Hdis; eauto with Ensembles_DB].
    + rewrite bound_var_app_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
      apply Included_Union_preserv_l; apply name_in_fundefs_bound_var_fundefs.
    + rewrite bound_var_app_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
      apply Included_Union_preserv_r, Included_Union_preserv_l, bound_stem_var.
    + eapply Disjoint_Included_r; [|apply IH]; eauto with Ensembles_DB; normalize_roundtrips.
      split; auto.
      erewrite <- (Setminus_Disjoint (bound_var _) (name_in_fundefs fds)).
      2: { DisInc H3; eauto with Ensembles_DB; apply name_in_fundefs_bound_var_fundefs. }
      apply Disjoint_Setminus_bal.
      DisInc Hdis; eauto with Ensembles_DB.
  - intros C IH e e_arb e0 [Huniq Hdis]. cbn.
    specialize (IH e_arb e0); cbn in *.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free || normalize_bound_stem_ctx); intros Hdis;
    inv Huniq; change (~ ?S ?x) with (~ x \in S) in *;
    apply Union_Disjoint_l; apply Union_Disjoint_r.
    + eapply Disjoint_Union_l; apply IH; split; cbn; normalize_roundtrips; auto.
      rewrite bound_var_app_f_ctx; apply Union_Disjoint_l;
      rewrite bound_var_app_f_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
    + rewrite <- name_in_fundefs_ctx_ctx; eauto with Ensembles_DB.
    + eapply Disjoint_Union_r; apply IH; split; cbn; normalize_roundtrips; auto.
      rewrite bound_var_app_f_ctx; apply Union_Disjoint_l;
      rewrite bound_var_app_f_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
    + rewrite <- name_in_fundefs_ctx_ctx in *; eauto with Ensembles_DB.
      rewrite bound_var_app_f_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_l; apply bound_stem_var.
  - intros f ft xs C IH fds e_arb e [Huniq Hdis].
    specialize (IH e_arb e); cbn in *.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free || normalize_bound_stem_ctx); intros Hdis;
    inv Huniq; change (~ ?S ?x) with (~ x \in S) in *.
    repeat match goal with
           | |- Disjoint _ (_ :|: _) _ => apply Union_Disjoint_l
           | |- Disjoint _ _ (_ :|: _) => apply Union_Disjoint_r
           end; eauto with Ensembles_DB.
    + DisInc Hdis; eauto with Ensembles_DB.
      do 3 apply Included_Union_preserv_r; apply name_in_fundefs_bound_var_fundefs.
    + eapply Disjoint_Included_r; [|apply IH]; eauto with Ensembles_DB; split; auto.
      erewrite <- (Setminus_Disjoint (bound_var _) (name_in_fundefs fds)).
      2: { DisInc H8; eauto with Ensembles_DB; apply name_in_fundefs_bound_var_fundefs. }
      erewrite <- (Setminus_Disjoint (bound_var _) (FromList xs)); auto.
      erewrite <- (Setminus_Disjoint (bound_var _) [set f]); [|apply Disjoint_Singleton_r, H4].
      rewrite !Setminus_Union; apply Disjoint_Setminus_bal.
      DisInc Hdis; eauto with Ensembles_DB.
    + rewrite bound_var_app_ctx in Hdis; DisInc Hdis; eauto with Ensembles_DB.
      do 2 apply Included_Union_preserv_r; do 2 apply Included_Union_preserv_l; apply bound_stem_var.
    + DisInc Hdis; eauto with Ensembles_DB.
  - intros f ft xs e C IH e_arb e0 [Huniq Hdis].
    specialize (IH e_arb e0); cbn in *.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free || normalize_bound_stem_ctx); intros Hdis;
    inv Huniq; change (~ ?S ?x) with (~ x \in S) in *.
    assert (Disjoint cps.var
                     (bound_var_fundefs (ctx.app_f_ctx_f C e_arb))
                     (occurs_free_fundefs (ctx.app_f_ctx_f C e_arb))). {
      rewrite bound_var_app_f_ctx; apply Union_Disjoint_l.
      * rewrite <- (Setminus_Disjoint (bound_var_fundefs_ctx _) [set f]).
        2: { rewrite bound_var_app_f_ctx, Union_demorgan in H5.
             destruct H5 as [H _]; apply Disjoint_Singleton_r in H; auto. }
        apply Disjoint_Setminus_bal; DisInc Hdis; eauto with Ensembles_DB.
        rewrite bound_var_app_f_ctx; eauto with Ensembles_DB.
      * rewrite <- (Setminus_Disjoint (bound_var _) [set f]).
        2: { rewrite bound_var_app_f_ctx, Union_demorgan in H5.
             destruct H5 as [_ H]; apply Disjoint_Singleton_r in H; auto. }
        apply Disjoint_Setminus_bal; DisInc Hdis; eauto with Ensembles_DB.
        rewrite bound_var_app_f_ctx; eauto with Ensembles_DB. }
    repeat match goal with
           | |- Disjoint _ (_ :|: _) _ => apply Union_Disjoint_l
           | |- Disjoint _ _ (_ :|: _) => apply Union_Disjoint_r
           end; eauto with Ensembles_DB.
    + rewrite <- name_in_fundefs_ctx_ctx in *. DisInc Hdis; eauto with Ensembles_DB.
      rewrite bound_var_app_f_ctx.
      do 3 apply Included_Union_preserv_r; apply Included_Union_preserv_l.
      apply name_in_fundefs_ctx_bound_var_fundefs.
    + eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply IH]]; eauto with Ensembles_DB.
      split; cbn; normalize_roundtrips; auto.
    + rewrite <- name_in_fundefs_ctx_ctx in *; DisInc Hdis; eauto with Ensembles_DB.
      rewrite bound_var_app_f_ctx; do 3 apply Included_Union_preserv_r.
      apply Included_Union_preserv_l, bound_stem_var.
    + eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply IH]]; eauto with Ensembles_DB.
      split; cbn; normalize_roundtrips; auto.
Qed.

Corollary stem_not_free c e_arb e :
  well_scoped (ctx.app_ctx_f c e_arb) ->
  Disjoint _ (bound_stem_ctx c) (occurs_free (ctx.app_ctx_f c e)).
Proof. intros; eapply (proj1 stem_not_free_mut); eauto. Qed.

Lemma name_in_fundefs_bound_var_fundefs_ctx : forall C : ctx.fundefs_ctx,
  names_in_fundefs_ctx C \subset bound_var_fundefs_ctx C.
Proof.
  induction C.
  - cbn; normalize_bound_var_ctx; eauto with Ensembles_DB.
    pose (H := name_in_fundefs_bound_var_fundefs f); clearbody H.
    eauto with Ensembles_DB.
  - cbn; normalize_bound_var_ctx; eauto with Ensembles_DB.
Qed.

(* TODO: move to proto_util *)
Lemma used_ces_vars_ces ces : used_ces ces <--> used_vars_ces ces.
Proof. induction ces as [|[c e] ces IHces]; cbn; normalize_roundtrips; eauto with Ensembles_DB. Qed.

Lemma used_c_vars_ces ces : used_c (c_of_ces ces) <--> used_ces ces.
Proof.
  induction ces as [|[c e] ces IHces]; cbn; normalize_roundtrips; eauto with Ensembles_DB.
  change (fold_right _ _ _) with (c_of_ces ces).
  rewrite used_c_comp, IHces; cbn; normalize_roundtrips; eauto with Ensembles_DB.
Qed.

Lemma used_c_of_ces_ctx : forall ces1 ct C ces2,
  used_c (c_of_ces_ctx ces1 ct C ces2) <--> used_vars_ces ces1 :|: used_c [C]! :|: used_vars_ces ces2.
Proof.
  unfold c_of_ces_ctx, c_of_ces_ctx'; cbn; intros; rewrite !used_c_comp; cbn; normalize_sets.
  rewrite used_c_vars_ces, !used_ces_vars_ces; cbn; split; eauto with Ensembles_DB.
Qed.

Lemma name_in_fundefs_c_of_fundefs C : names_in_fundefs_ctx C \subset used_c (c_of_fundefs_ctx C).
Proof.
  induction C; cbn; rewrite !used_c_comp; cbn; normalize_roundtrips; eauto with Ensembles_DB.
  assert (name_in_fundefs f \subset used_vars_fundefs f). {
    apply Included_Union_preserv_l, name_in_fundefs_bound_var_fundefs. }
  apply Included_Union_preserv_l; normalize_sets; eauto with Ensembles_DB.
Qed.

(* TODO: move to Ensembles_util *)
Lemma Disjoint_commut {A} S1 S2 : Disjoint A S1 S2 -> Disjoint A S2 S1.
Proof. eauto with Ensembles_DB. Qed.

Lemma Disjoint_Union {A} S1 S2 S3 :
  Disjoint A S1 (S2 :|: S3) -> Disjoint A S1 S2 /\ Disjoint A S1 S3.
Proof. eauto with Ensembles_DB. Qed.

(* well_scoped(C[e]) ⟹ (BV(e) # vars(C)) ∧ (FV(e) ⊆ BVstem(C) ∪ FV(C[e]) *)
Lemma well_scoped_mut' :
  (forall (c : ctx.exp_ctx) (e : cps.exp),
    well_scoped (ctx.app_ctx_f c e) ->
    Disjoint _ (bound_var e) (used_c [c]!) /\
    occurs_free e \subset bound_stem_ctx c :|: occurs_free (ctx.app_ctx_f c e)) /\
  (forall (B : ctx.fundefs_ctx) (e : cps.exp),
    well_scoped_fds (ctx.app_f_ctx_f B e) ->
    Disjoint _ (bound_var e) (used_c [B]!) /\
    occurs_free e \subset name_in_fundefs (ctx.app_f_ctx_f B e)
                :|: bound_stem_fundefs_ctx B :|: occurs_free_fundefs (ctx.app_f_ctx_f B e)).
Proof.
  apply ctx.exp_fundefs_ctx_mutual_ind; unfold well_scoped.
  - cbn; normalize_roundtrips; intros; eauto with Ensembles_DB.
  - intros x c ys C IH e [Huniq Hdis]; specialize (IH e).
    cbn in *; rewrite !used_c_comp; cbn; inv Huniq.
    revert Hdis; repeat (normalize_bound_var || normalize_occurs_free
                         || normalize_sets || normalize_roundtrips); intros Hdis.
    destruct IH as [IHdis IHfv]; [split; eauto|split].
    { apply Disjoint_Union in Hdis; destruct Hdis as [Hdis1 Hdis2].
      apply Disjoint_commut, Disjoint_Union in Hdis2; destruct Hdis2 as [Hdis2 _].
      eapply Disjoint_Included_r; [apply Included_Union_Setminus
                                  |apply Union_Disjoint_r; [apply Disjoint_commut, Hdis2|]];
      eauto with Decidable_DB Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdis].
      * change (~ ?S ?x) with (~ x \in S) in *.
        rewrite bound_var_app_ctx, Union_demorgan in H1.
        now apply Disjoint_Singleton_r.
      * rewrite bound_var_app_ctx in *.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdis]]; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      repeat rewrite <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_assoc, (Union_commut [set x]), <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_commut; apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros x t n y C IH e [Huniq Hdisj]; specialize (IH e).
    cbn in *; rewrite !used_c_comp; cbn; inv Huniq.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { apply Disjoint_Union in Hdisj; destruct Hdisj as [Hdisj1 Hdisj2].
      apply Disjoint_commut, Disjoint_Union in Hdisj2; destruct Hdisj2 as [Hdisj2 _].
      eapply Disjoint_Included_r; [apply Included_Union_Setminus
                                  |apply Union_Disjoint_r; [apply Disjoint_commut, Hdisj2|]];
      eauto with Decidable_DB Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * change (~ ?S ?x) with (~ x \in S) in *.
        rewrite bound_var_app_ctx, Union_demorgan in H1.
        now apply Disjoint_Singleton_r.
      * rewrite bound_var_app_ctx in *.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      repeat rewrite <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_assoc, (Union_commut [set x]), <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_commut; apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros x f ft ys C IH e [Huniq Hdisj]; specialize (IH e).
    cbn in *; rewrite !used_c_comp; cbn; inv Huniq.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { apply Disjoint_Union in Hdisj; destruct Hdisj as [Hdisj1 Hdisj2].
      apply Disjoint_commut, Disjoint_Union in Hdisj2; destruct Hdisj2 as [Hdisj2 _].
      eapply Disjoint_Included_r; [apply Included_Union_Setminus
                                  |apply Union_Disjoint_r; [apply Disjoint_commut, Hdisj2|]];
      eauto with Decidable_DB Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * change (~ ?S ?x) with (~ x \in S) in *.
        rewrite bound_var_app_ctx, Union_demorgan in H1.
        now apply Disjoint_Singleton_r.
      * rewrite bound_var_app_ctx in *.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      repeat rewrite <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_assoc, (Union_commut [set x]), <- Union_assoc, (Union_assoc [set x]), (Union_commut [set x]),
        <- Union_assoc.
      do 2 apply Included_Union_preserv_r.
      rewrite Union_commut; apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros x p ys C IH e [Huniq Hdisj]; specialize (IH e).
    cbn in *; rewrite !used_c_comp; cbn; inv Huniq.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { apply Disjoint_Union in Hdisj; destruct Hdisj as [Hdisj1 Hdisj2].
      apply Disjoint_commut, Disjoint_Union in Hdisj2; destruct Hdisj2 as [Hdisj2 _].
      eapply Disjoint_Included_r; [apply Included_Union_Setminus
                                  |apply Union_Disjoint_r; [apply Disjoint_commut, Hdisj2|]];
      eauto with Decidable_DB Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * change (~ ?S ?x) with (~ x \in S) in *.
        rewrite bound_var_app_ctx, Union_demorgan in H1.
        now apply Disjoint_Singleton_r.
      * rewrite bound_var_app_ctx in *.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      repeat rewrite <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_assoc, (Union_commut [set x]), <- Union_assoc; apply Included_Union_preserv_r.
      rewrite Union_commut; apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros x ces1 ct C IH ces2 e [Huniq Hdisj]; specialize (IH e).
    cbn in *; rewrite !used_c_comp; cbn.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { rewrite unique_bindings_Ecase_app in Huniq; decompose [and] Huniq; clear Huniq.
      inv H1; auto. }
    { apply Disjoint_Union in Hdisj; destruct Hdisj as [Hdisj1 Hdisj2].
      eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj2]]; eauto with Ensembles_DB. }
    + rewrite unique_bindings_Ecase_app in Huniq; decompose [and] Huniq; clear Huniq.
      inv H1. rewrite used_c_of_ces_ctx; cbn.
      repeat match goal with |- Disjoint _ _ (_ :|: _) => apply Union_Disjoint_r end; auto.
      * rewrite bound_var_app_ctx in Hdisj.
        eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. 
      * rewrite used_vars_ces_bv_fv. apply Union_Disjoint_r.
        -- normalize_bound_var_in_ctx; rewrite !bound_var_Ecase, bound_var_app_ctx in H2.
           apply Disjoint_commut; eapply Disjoint_Included_r; [|eassumption]; eauto with Ensembles_DB.
        -- rewrite occurs_free_Ecase, bound_var_app_ctx in Hdisj.
           eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. 
      * rewrite used_vars_ces_bv_fv. apply Union_Disjoint_r.
        -- rewrite bound_var_app_ctx, bound_var_Ecase in H8. eauto with Ensembles_DB.
        -- rewrite bound_var_app_ctx, !occurs_free_Ecase in Hdisj.
           eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. 
    + normalize_bound_stem_ctx; eapply Included_trans; [apply IHfv|]; eauto with Ensembles_DB.
  - intros fds C IH e [Huniq Hdisj]; specialize (IH e).
    cbn in *; rewrite !used_c_comp; cbn.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { now inv Huniq. }
    { inv Huniq. eapply Disjoint_Included_r;
                   [apply Included_Union_Setminus with (s2 := name_in_fundefs fds); eauto with Decidable_DB|].
      apply Union_Disjoint_r;
        [eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]|]; eauto with Ensembles_DB.
      eapply Disjoint_Included_r; [apply name_in_fundefs_bound_var_fundefs|]; auto. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * inv Huniq. rewrite bound_var_app_ctx in H3; eauto with Ensembles_DB.
      * eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB.
        rewrite bound_var_app_ctx; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      rewrite (Union_commut (name_in_fundefs _)), <- Union_assoc.
      rewrite (Union_assoc (name_in_fundefs _)), (Union_commut (name_in_fundefs _)), <- Union_assoc.
      do 2 apply Included_Union_preserv_r; rewrite Union_commut.
      apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros C IH e1 e [Huniq Hdisj]; specialize (IH e).
    cbn in *; rewrite !used_c_comp; cbn.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free || normalize_roundtrips
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { cbn; normalize_roundtrips; now inv Huniq. }
    { cbn; normalize_roundtrips.
      eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r|apply IHdisj].
      * inv Huniq. rewrite bound_var_app_f_ctx in H3; eauto with Ensembles_DB.
      * rewrite bound_var_app_f_ctx in *.
        eapply Disjoint_Included_r; [apply Included_Union_Setminus with
                                         (s2 := name_in_fundefs (ctx.app_f_ctx_f C e))|]; eauto with Decidable_DB.
        apply Union_Disjoint_r.
        -- eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB.
        -- rewrite <- name_in_fundefs_ctx_ctx.
           eapply Disjoint_Included_r; [apply name_in_fundefs_c_of_fundefs|]; auto.
    + normalize_bound_stem_ctx; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      apply Union_Included; eauto with Ensembles_DB.
      rewrite name_in_fundefs_ctx_ctx; eauto with Ensembles_DB.
  - intros f ft xs C IH fds e [Huniq Hdisj]. specialize (IH e); cbn in *; normalize_roundtrips.
    rewrite !used_c_comp; cbn.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free || normalize_roundtrips
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { now inv Huniq. }
    { inv Huniq. change (~ ?S ?x) with (~ x \in S) in *.
      erewrite <- (Setminus_Disjoint (bound_var (ctx.app_ctx_f C e)));
        [|eapply Disjoint_Included_r; [apply name_in_fundefs_bound_var_fundefs|]; apply H8].
      erewrite <- (Setminus_Disjoint (bound_var (ctx.app_ctx_f C e))); [|apply H6].
      erewrite <- (Setminus_Disjoint (bound_var (ctx.app_ctx_f C e))); [|apply Disjoint_Singleton_r, H4].
      rewrite !Setminus_Union.
      apply Disjoint_Setminus_bal.
      eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. }
    + apply Union_Disjoint_r; [apply Union_Disjoint_r; [|apply Union_Disjoint_r]|apply IHdisj].
      * assert (Hnof : Disjoint _ (bound_var e) [set f]). {
          inv Huniq. change (~ ?S ?x) with (~ x \in S) in *.
          rewrite bound_var_app_ctx, Union_demorgan in H4.
          now apply Disjoint_Singleton_r. }
        apply Union_Disjoint_r; [apply Hnof|].
        inv Huniq; rewrite bound_var_app_ctx in H6; now apply Disjoint_Union_r in H6.
      * inv Huniq; rewrite bound_var_app_ctx in H8; now apply Disjoint_Union_r in H8.
      * assert (Hnof : bound_var e \subset bound_var e \\ [set f]). {
          intros arb Harb; constructor; auto.
          inv Huniq. intros Hc; inv Hc. apply H4. change (?S ?x) with (x \in S).
          rewrite bound_var_app_ctx; now right. }
        eapply Disjoint_Included_l; [apply Hnof|].
        apply Disjoint_Setminus_bal.
        DisInc Hdisj; rewrite ?bound_var_app_ctx; eauto with Ensembles_DB.
    + normalize_bound_stem_ctx; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      eapply Included_trans with (s2 :=
        (f |: FromList xs :|: name_in_fundefs fds) :|: 
        (occurs_free (ctx.app_ctx_f C e) \\ (f |: (FromList xs :|: name_in_fundefs fds)))).
      2: eauto with Ensembles_DB.
      rewrite Union_commut, <- !Union_assoc.
      apply Included_Union_Setminus; eauto with Decidable_DB.
  - intros f ft xs e C IH e0 [Huniq Hdisj]; specialize (IH e0).
    cbn in *; rewrite !used_c_comp; cbn.
    revert Hdisj; repeat (normalize_bound_var || normalize_occurs_free || normalize_roundtrips
                          || normalize_sets || normalize_roundtrips); intros Hdisj.
    destruct IH as [IHdisj IHfv]; [split; auto|split].
    { cbn; normalize_roundtrips; now inv Huniq. }
    { inv Huniq; cbn in *; normalize_roundtrips. change (~ ?S ?x) with (~ x \in S) in *.
      erewrite <- (Setminus_Disjoint (bound_var_fundefs (ctx.app_f_ctx_f C e0))); [|apply Disjoint_Singleton_r, H5].
      apply Disjoint_Setminus_bal.
      eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. }
    { apply Union_Disjoint_r; eauto with Ensembles_DB.
      inv Huniq. change (~ ?S ?x) with (~ x \in S) in *. rewrite bound_var_app_f_ctx in *.
      rewrite Union_demorgan in H5; destruct H5 as [HC He0].
      apply Union_Disjoint_r; [apply Union_Disjoint_r; [apply Disjoint_Singleton_r in He0; apply He0|]|];
       eauto with Ensembles_DB; apply Union_Disjoint_r; eauto with Ensembles_DB.
      rewrite <- (Setminus_Disjoint (bound_var e0) (name_in_fundefs (ctx.app_f_ctx_f C e0))).
      2: { eapply Disjoint_Included_r; [rewrite <- name_in_fundefs_ctx_ctx; apply Included_refl|].
           eapply Disjoint_Included_r; [apply name_in_fundefs_bound_var_fundefs_ctx|].
           rewrite (proj2 (ub_app_ctx_f e0)) in H12; decompose [and] H12.
           eauto with Ensembles_DB. }
      erewrite <- (Setminus_Disjoint (bound_var e0) (FromList xs)); eauto with Ensembles_DB. 
      erewrite <- (Setminus_Disjoint (bound_var e0)); [|apply Disjoint_Singleton_r, He0].
      rewrite !Setminus_Union.
      apply Disjoint_Setminus_bal.
      eapply Disjoint_Included_l; [|eapply Disjoint_Included_r; [|apply Hdisj]]; eauto with Ensembles_DB. }
    + normalize_bound_stem_ctx; eapply Included_trans; [apply IHfv|].
      apply Union_Included; eauto with Ensembles_DB.
      eapply Included_trans with (s2 := (f |: (occurs_free_fundefs (ctx.app_f_ctx_f C e0) \\ [set f]))).
      2: eauto with Ensembles_DB.
      rewrite Union_commut.
      apply Included_Union_Setminus; eauto with Decidable_DB.
Qed.

(* TODO move to proto_util *)
Lemma bound_vars_used_c_mut :
  (forall (c : ctx.exp_ctx) (e : cps.exp),
    bound_var_ctx c \subset used_c [c]!) /\
  (forall (B : ctx.fundefs_ctx) (e : cps.exp),
    bound_var_fundefs_ctx B \subset used_c [B]!).
Proof.
  apply ctx.exp_fundefs_ctx_mutual_ind; intros;
    repeat normalize_bound_var_ctx; cbn in *;
    repeat normalize_sets; eauto with Ensembles_DB;
    rewrite ?used_c_comp in *; cbn; normalize_roundtrips; repeat normalize_sets;
    match goal with H : cps.exp -> _ |- _ => specialize (H (cps.Ehalt 1))%positive end;
    eauto with Ensembles_DB.
  - rewrite used_c_of_ces_ctx; cbn; rewrite !bound_var_Ecase, !used_vars_ces_bv_fv.
    repeat apply Union_Included; eauto with Ensembles_DB.
  - unfold used_vars_fundefs; repeat apply Union_Included; eauto with Ensembles_DB.
  - unfold used_vars; repeat apply Union_Included; eauto with Ensembles_DB.
Qed.
Corollary bound_vars_used_c c : bound_var_ctx c \subset used_c [c]!.
Proof. apply (proj1 bound_vars_used_c_mut c (cps.Ehalt 1%positive)). Qed.
Corollary bound_fds_used_c c : bound_var_fundefs_ctx c \subset used_c [c]!.
Proof. apply (proj2 bound_vars_used_c_mut c (cps.Ehalt 1%positive)). Qed.

Lemma well_scoped_inv c e :
  well_scoped (ctx.app_ctx_f c e) ->
  well_scoped e.
Proof.
  intros Hscope; pose (Hscope' := Hscope); clearbody Hscope';
  apply (proj1 well_scoped_mut') in Hscope'; destruct Hscope as [Huniq Hdis], Hscope' as [Hbv Hfv].
  split.
  - rewrite (proj1 (ub_app_ctx_f _)) in Huniq; now decompose [and] Huniq.
  - eapply Disjoint_Included_r; [apply Hfv|]; apply Union_Disjoint_r.
    + rewrite (proj1 (ub_app_ctx_f _)) in Huniq; destruct Huniq as [HuniqC [Huniqe HdisCe]].
      eapply Disjoint_Included_r; [|apply Hbv].
      eapply Included_trans; [apply bound_stem_var|]; apply bound_vars_used_c.
    + eapply Disjoint_Included_l; [|apply Hdis].
      rewrite bound_var_app_ctx; eauto with Ensembles_DB.
Qed.

Lemma well_scoped_fv c e :
  well_scoped (ctx.app_ctx_f c e) ->
  occurs_free e \subset bound_stem_ctx c :|: occurs_free (ctx.app_ctx_f c e).
Proof. apply well_scoped_mut'. Qed.
