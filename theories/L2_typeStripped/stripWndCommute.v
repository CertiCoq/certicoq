(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_5_box" as L1_5.
Add LoadPath "../L2_typeStripped" as L2.
(******)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import L1_5.L1_5.
Require Import L2.program.
Require Import L2.wndEval.
Require Import L2.stripEvalCommute.
Require Import L2.term.
Require Import L2.compile.

Definition L1_5Term := L1_5.compile.Term.
Definition L1_5Terms := L1_5.compile.Terms.
Definition L1_5Defs := L1_5.compile.Defs.
Definition ecTrm := AstCommon.ecTrm.
Definition ecTyp := AstCommon.ecTyp Term.
Definition ecAx := AstCommon.ecAx Term.



Lemma not_isApp_strip_hom:
  forall (t:L1_5Term), ~ L1_5.term.isApp t -> ~ isApp (strip t).
Proof.
  destruct t; cbn; intros; try not_isApp.
  elim H. unfold L1_5.term.isApp. exists t1, t2, t3. reflexivity.
Qed.


Lemma TApp_mkApp_step_lem:
  forall fn fn' arg args,
    TApp fn arg args = mkApp fn' (tcons arg args) -> fn = fn'.
Proof.
  destruct fn'; cbn; intros; cbn; try myInjection H; try reflexivity.
  injection H. intros.
  assert (j:= f_equal tlength H0). cbn in j.
  rewrite tlength_tappend in j. cbn in j. omega.
Qed.

Lemma mkApp_TApp_step_lem:
  forall fn fn' arg args, ~ isApp fn ->
    fn = fn' -> TApp fn arg args = mkApp fn' (tcons arg args).
Proof.
  destruct fn; intros; subst; cbn; intros; cbn; try reflexivity.
  elim H. exists fn1, fn2, t. reflexivity.
Qed.

(** Since L1_5.wndEval.wndEval may make steps in parts of a term that are
*** erased in L2, and since L2.WndEval is not reflexive, we add <>
***  hypotheses.
**)
Lemma Wnd_hom:
  forall p, L1_5.program.WFaEnv p ->
  (forall (s t:L1_5Term),
     L1_5.wndEval.wndEval p s t ->
     L1_5.term.WFapp s -> strip s <> strip t ->
     wndEval (stripEnv p) (strip s) (strip t)) /\
  (forall (ss ts:L1_5Terms),
     L1_5.wndEval.wndEvals p ss ts ->
     L1_5.term.WFapps ss -> strips ss <> strips ts ->
     wndEvals (stripEnv p) (strips ss) (strips ts)) /\
  (forall (ds es:L1_5Defs),
     L1_5.wndEval.wndDEvals p ds es ->
     L1_5.term.WFappDs ds -> stripDs ds <> stripDs es ->
     wndDEvals (stripEnv p) (stripDs ds) (stripDs es)).
Proof.
  intros p hp.
  apply L1_5.wndEval.wndEvalEvals_ind; intros; try (solve [constructor]);
  try (solve[cbn in H1; elim H1; reflexivity]);
  try (solve[cbn in H1; constructor; apply H; [
    inversion_Clear H0; assumption |
    intros h; elim H1; rewrite h; reflexivity]]);
  cbn.
  - constructor.
    + apply LookupDfn_hom. assumption.
  - rewrite whBetaStep_hom. constructor.
  - rewrite (proj1 instantiate_hom). constructor.
  - refine (sCase _ _ _ _ _ _ _); try eassumption.
    + rewrite <- canonicalP_hom. rewrite e. reflexivity.
    + rewrite <- tskipn_hom. rewrite e0. reflexivity.
    + rewrite <- whCaseStep_hom. rewrite e1. reflexivity.
  - rewrite <- pre_whFixStep_hom. rewrite tcons_hom.
    refine (sFix _ _ _ _ _ _).
    rewrite <- dnthBody_hom. rewrite <- optStripDnth_hom.
    apply f_equal. eassumption.
  - rewrite mkApp_hom. refine (sAppFn _ _ _). inversion_Clear H0.
    apply H. assumption.
    + rewrite TApp_hom in H1. rewrite mkApp_hom in H1.
      rewrite tcons_hom in H1.
      intros h. rewrite <- h in H1.
      elim H1. rewrite <- mkApp_goodFn. reflexivity.
      intros j. elim H5. apply isApp_hom. assumption.
  - refine (sAppArgs _ _).
    rewrite TApp_hom in H1. rewrite TApp_hom in H1.
    rewrite tcons_hom in H. rewrite tcons_hom in H.
    inversion_Clear H0. apply H.
    + constructor; assumption.
    + intros h. myInjection h. elim H1. rewrite H0, H2. reflexivity.
Qed.

Lemma TConst_strip_inv:
  forall nm r, TConst nm = strip r -> r = L1_5.compile.TConst nm.
Proof.
  destruct r; cbn; intros; try discriminate. myInjection H. reflexivity.
Qed.


(**************************
Lemma L2wnd_L1_5wnd:
  forall (p:environ),
  (forall (s t:Term), wndEval p s t ->
     forall pp, p = stripEnv pp ->
     forall ss, s = strip ss ->
     forall tt, t = strip tt ->
     L1_5.wndEval.wndEval pp ss tt) /\
  (forall (s t:Terms), wndEvals p s t ->
     forall pp, p = stripEnv pp ->
     forall ss, s = strips ss ->
     forall tt, t = strips tt ->
     L1_5.wndEval.wndEvals pp ss tt) /\
  (forall (s t:Defs), wndDEvals p s t ->
     forall pp, p = stripEnv pp ->
     forall ss, s = stripDs ss ->
     forall tt, t = stripDs tt ->
     L1_5.wndEval.wndDEvals pp ss tt).
Proof.
  intros p.
  apply wndEvalEvals_ind; intros; subst.
  - rewrite (TConst_strip_inv _ _ H0). constructor.
  


**************************)