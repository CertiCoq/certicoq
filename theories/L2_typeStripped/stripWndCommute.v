
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import Common.AstCommon.
Require Import L1g.L1g.
Require Import L2.program.
Require Import L2.wndEval.
Require Import L2.wcbvEval.
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
  forall p,
  (forall (s t:L1gTerm),
     L1g.wndEval.wndEval p s t ->
     L1g.term.WFapp s -> strip s <> strip t ->
     wndEval (stripEnv p) (strip s) (strip t)) /\
  (forall (ss ts:L1gTerms),
     L1g.wndEval.wndEvals p ss ts ->
     L1g.term.WFapps ss -> strips ss <> strips ts ->
     wndEvals (stripEnv p) (strips ss) (strips ts)).
Proof.
  intros p.
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
    eapply sFix.
    + rewrite <- dnthBody_hom. rewrite <- optStripDnth_hom. rewrite e.
      reflexivity.
    + rewrite tlength_hom. assumption. 
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

Lemma Lookup_stripEnv_inv:
  forall p s sec, Lookup s (stripEnv p) sec ->
              exists u, Lookup s p u /\ stripEC u = sec.
Proof.
  induction p; intros.
  - inversion H.
  - destruct a, (string_dec s s0).
    + subst s. cbn in H.
      pose proof (LHit s0 (stripEnv p) (stripEC e)).
      pose proof (Lookup_single_valued H H0). subst sec.
      exists e. intuition.
    + cbn in H. inversion_Clear H.
      * intuition.
      * specialize (IHp s _ H6). destruct IHp as [u [j1u j2u]].
        exists u. intuition.
Qed.

Theorem L2wndEval_sound_for_L1gwndEval:
  forall L2p,
  (forall L2t L2s, wndEval L2p L2t L2s ->
  forall p, L2p = stripEnv p ->
  forall t, L2t = strip t ->
            exists s, L1g.wndEval.wndEval p t s /\ strip s = L2s) /\
  (forall L2t L2s, wndEvals L2p L2t L2s ->
  forall p, L2p = stripEnv p ->
  forall t, L2t = strips t ->
            exists s, L1g.wndEval.wndEvals p t s /\ strips s = L2s).
Proof.
  intros L2p.
  apply (@wndEvalEvals_ind L2p
          (fun (L2t L2s: Term) (prf: wndEval L2p L2t L2s) =>
    forall p: L1gEnv, L2p = stripEnv p ->
    forall t: compile.L1gTerm, L2t = strip t ->
    exists s: L1g.compile.Term, L1g.wndEval.wndEval p t s /\ strip s = L2s)
       (fun (L2t L2s: Terms) (prf: wndEvals L2p L2t L2s) =>
    forall p: L1gEnv, L2p = stripEnv p ->
    forall t: compile.L1gTerms, L2t = strips t ->
    exists s: L1g.compile.Terms, L1g.wndEval.wndEvals p t s /\
                                  strips s = L2s));
    intros.
  - pose proof (Const_strip_inv _ H0). subst. unfold LookupDfn in *.
    destruct (Lookup_stripEnv_inv _ _ _ l) as [x [j1x j2x]].
    destruct x; cbn in j2x.
    + myInjection j2x. exists l0. intuition.
    + discriminate.
  - destruct (App_strip_inv _ H0) as [x0 [x1 [x2 [j1x [j2x [j3x j4x]]]]]].
    subst. clear H0.
    destruct (Lam_strip_inv _ j2x) as [y0 [y1 [j1y j2y]]].
    subst. rewrite <- whBetaStep_hom. exists (L1g.term.whBetaStep y1 x1 x2).
    intuition.
  - destruct (LetIn_strip_inv _ H0) as [x0 [x1 [x2 [j0x [j1x j2x]]]]].
    subst. rewrite <- (proj1 instantiate_hom).
    exists (L1g.term.instantiate x0 0 x2). intuition.
  - destruct (Case_strip_inv _ H0) as [x0 [x1 [j0x [j1x [j2x j3x]]]]].
    clear H0. subst.
    rewrite <- canonicalP_hom in e.
    case_eq (L1g.term.canonicalP x1); intros; rewrite H in e; try discriminate.
    + destruct p0 as [z0 z1]. cbn in e. myInjection e.
      destruct ml. cbn in e0.
      rewrite <- tskipn_hom in e0.
      case_eq (L1g.term.tskipn n0 z1); intros; rewrite H0 in e0;
      try discriminate.
      * { cbn in e0. myInjection e0.
          rewrite <- whCaseStep_hom in e1; try discriminate.
          case_eq (L1g.term.whCaseStep n t j0x); intros; rewrite H1 in e1;
          try discriminate.
          - cbn in e1. myInjection e1. exists t0. intuition.
            econstructor; try eassumption. }
  - destruct (App_strip_inv _ H0) as [x0 [x1 [x2 [j1x [j2x [j3x j4x]]]]]].
    subst. clear H0.
    destruct (Fix_strip_inv _ j2x) as [y0 [j0y j1y]]; intros. subst. clear j2x.
    rewrite <- dnthBody_hom in e.
    case_eq (compile.dnthBody m y0); intros; rewrite H in e; try discriminate.
    + destruct p0. cbn in e. myInjection e. rewrite <- tcons_hom.
      rewrite pre_whFixStep_hom.
      exists (L1g.term.pre_whFixStep t y0 (L1g.compile.tcons x1 x2)).
      intuition. apply (L1g.wndEval.sFix p y0 m x1 x2 H ).
      rewrite tlength_hom in l. assumption.
  - destruct (Cast_strip_inv _ H0) as [x0 [x1 [j0x j1x]]]. subst.
    exists x0. intuition.
  - destruct (Prf_strip_inv _ H0) as [x0 [j0 j1]]. subst.
    exists x0. intuition.
  - destruct (App_strip_inv _ H1) as [x0 [x1 [x2 [j1x [j2x [j3x j4x]]]]]].
    subst. rewrite <- tcons_hom.
    destruct (H p eq_refl x0 eq_refl) as [y0 [j0y j1y]].
    subst. rewrite <- mkApp_hom.
    exists (L1g.term.mkApp y0 (L1g.compile.tcons x1 x2)). intuition.
  - destruct (App_strip_inv _ H1) as [x0 [x1 [x2 [j1x [j2x [j3x j4x]]]]]].
    subst. clear H1.
    destruct (H p eq_refl (L1g.compile.tcons x1 x2) eq_refl) as
        [y [j0y j1y]]. clear H.
    rewrite <- j1y in w. 
    inversion_Clear j0y.
    + rewrite tcons_hom in j1y. myInjection j1y.
      rewrite <- (TApp_hom x0 r x2). exists (L1g.compile.TApp x0 r x2).
      intuition.
    + rewrite tcons_hom in j1y. myInjection j1y.
      rewrite <- (TApp_hom x0 x1 ss). exists (L1g.compile.TApp x0 x1 ss).
      intuition.
  - destruct (LetIn_strip_inv _ H1) as [x0 [x1 [x2 [j0x [j1x j2x]]]]].
    subst. clear H1.
    specialize (H p eq_refl x0 eq_refl).
    destruct H as [y [j0y j1y]]. subst. rewrite <- (TLetIn_hom nm y x1).
    exists (L1g.compile.TLetIn nm y x1 x2). intuition.
  - destruct (Case_strip_inv _ H1) as [x0 [x1 [j0x [j1x [j2x j3x]]]]].
    clear H1. subst.
    specialize (H p eq_refl x1 eq_refl).
    destruct H as [y [j0y j1y]]. subst. rewrite <- (TCase_hom nl x0 y).
    exists (L1g.compile.TCase nl x0 y j0x). intuition.
  - destruct (tcons_strip_inv _ H1) as [x0 [x1 [j0x [j1x j2x]]]]. subst.
    specialize (H p eq_refl x0 eq_refl).
    destruct H as [y [j0y j1y]]. subst.
    rewrite <- tcons_hom. exists (L1g.compile.tcons y x1). intuition.
  - destruct (tcons_strip_inv _ H1) as [x0 [x1 [j0x [j1x j2x]]]]. subst.
    specialize (H p eq_refl x1 eq_refl).
    destruct H as [y [j0y j1y]]. subst.
    rewrite <- tcons_hom. exists (L1g.compile.tcons x0 y). intuition.
Qed.
Print Assumptions L2wndEval_sound_for_L1gwndEval.

(*** not provable ****
Theorem L2WcbvEval_sound_for_L1gwndEval:
  forall p t L2s, WcbvEval (stripEnv p) (strip t) L2s ->
           WFaEnv (stripEnv p) -> WFapp (strip t)  ->        
        exists s, L1g.wndEval.wndEvalRTC p t s /\ L2s = strip s.
Proof.
  intros p t L2s h1 h2 h3.
  pose proof (proj1 (WcbvEval_wndEvalRTC h2) _ _ h1 h3).
  inversion_Clear H.
  - exists t. intuition.
  -  HERE

Qed.
 *************************)
