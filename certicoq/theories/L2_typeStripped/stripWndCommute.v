
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import L1g.L1g.
Require Import L2.program.
Require Import L2.wndEval.
Require Import L2.stripEvalCommute.
Require Import L2.term.
Require Import L2.compile.

Definition L1gTerm := L1g.compile.Term.
Definition L1gTerms := L1g.compile.Terms.
Definition L1gDefs := L1g.compile.Defs.


Lemma not_isApp_strip_hom:
  forall (t:L1gTerm), ~ L1g.term.isApp t -> ~ isApp (strip t).
Proof.
  intros. intros h. destruct H. apply isApp_hom. assumption.
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

(** Since L1g.wndEval.wndEval may make steps in parts of a term that are
*** erased in L2, and since L2.WndEval is not reflexive, we add <>
***  hypotheses.
**)
Lemma Wnd_hom:
  forall p, L1g.program.WFaEnv p ->
  (forall (s t:L1gTerm),
     L1g.wndEval.wndEval p s t ->
     L1g.term.WFapp s -> strip s <> strip t ->
     wndEval (stripEnv p) (strip s) (strip t)) /\
  (forall (ss ts:L1gTerms),
     L1g.wndEval.wndEvals p ss ts ->
     L1g.term.WFapps ss -> strips ss <> strips ts ->
     wndEvals (stripEnv p) (strips ss) (strips ts)).
Proof.
  intros p hp.
  apply L1g.wndEval.wndEvalEvals_ind; intros; try (solve [constructor]);
  try (solve[cbn in H1; elim H1; reflexivity]);
  try (solve[cbn in H1; constructor; apply H; [
    inversion_Clear H0; assumption |
    intros h; elim H1; rewrite h; reflexivity]]).
  - constructor.
    + apply LookupDfn_hom. assumption.
  - rewrite whBetaStep_hom. constructor.
  - rewrite (proj1 instantiate_hom). constructor.
  - eapply sCase; try eassumption.
    + rewrite <- canonicalP_hom. rewrite e. reflexivity.
    + rewrite <- tskipn_hom. rewrite e0. reflexivity.
    + rewrite <- whCaseStep_hom. rewrite e1. reflexivity.
  - rewrite <- pre_whFixStep_hom. rewrite tcons_hom.
    eapply sFix. Check sFix.
    + rewrite <- dnthBody_hom. rewrite <- optStripDnth_hom. rewrite e.
      reflexivity.
    + rewrite <- tcons_hom. rewrite <- tnth_hom. rewrite <- optStrip_hom.
      rewrite e0. reflexivity.
    + rewrite <- canonicalP_hom. rewrite e1. rewrite <- optStripCanP_hom'.
      reflexivity.
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
  forall nm r, TConst nm = strip r -> r = L1g.compile.TConst nm.
Proof.
  destruct r; intros; try discriminate.
  myInjection H. reflexivity.
Qed.


(**************************
Lemma L2wnd_L1gwnd:
  forall (p:environ),
  (forall (s t:Term), wndEval p s t ->
     forall pp, p = stripEnv pp ->
     forall ss, s = strip ss ->
     forall tt, t = strip tt ->
     L1g.wndEval.wndEval pp ss tt) /\
  (forall (s t:Terms), wndEvals p s t ->
     forall pp, p = stripEnv pp ->
     forall ss, s = strips ss ->
     forall tt, t = strips tt ->
     L1g.wndEval.wndEvals pp ss tt) /\
  (forall (s t:Defs), wndDEvals p s t ->
     forall pp, p = stripEnv pp ->
     forall ss, s = stripDs ss ->
     forall tt, t = stripDs tt ->
     L1g.wndEval.wndDEvals pp ss tt).
Proof.
  intros p.
  apply wndEvalEvals_ind; intros; subst.
  - rewrite (TConst_strip_inv _ _ H0). constructor.
  


**************************)