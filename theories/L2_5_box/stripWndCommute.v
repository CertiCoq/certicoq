
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import L2.L2.
Require Import L2_5.program.
Require Import L2_5.wndEval.
Require Import L2_5.stripEvalCommute.
Require Import L2_5.term.
Require Import L2_5.compile.

Definition L2Term := L2.compile.Term.
Definition L2Terms := L2.compile.Terms.
Definition L2Defs := L2.compile.Defs.


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

(***************
Lemma TConst_strip_inv:
  forall nm r, TConst nm = strip r ->
               (r = L2.compile.TConst nm) \/ (L2.term.isCase r).
Proof.
  destruct r; intros; try discriminate.
  - myInjection H. left. reflexivity.
  - right. exists p, r, d. reflexivity.
Qed.


Lemma Lookup_stripEnv_inv:
  forall p s sec, Lookup s (stripEnv p) sec ->
              exists u, Lookup s p u /\ L2EC_EC u = sec.
Proof.
  induction p; intros.
  - inversion H.
  - destruct a, (string_dec s s0).
    + subst s. cbn in H.
      pose proof (LHit s0 (stripEnv p) (L2EC_EC e)).
      pose proof (Lookup_single_valued H H0). subst sec.
      exists e. intuition.
    + cbn in H. inversion_Clear H.
      * intuition.
      * specialize (IHp s _ H6). destruct IHp as [u [j1u j2u]].
        exists u. intuition.
Qed.
***********************)

(************
Theorem L2_5wndEval_sound_for_L2wndEval:
  forall L2_5p,
  (forall L2_5t L2_5s, wndEval L2_5p L2_5t L2_5s ->
  forall p, L2_5p = stripEnv p ->
  forall t, L2_5t = strip t ->
            exists s, L2.wndEval.wndEval p t s /\ strip s = L2_5s) /\
  (forall L2_5t L2_5s, wndEvals L2_5p L2_5t L2_5s ->
  forall p, L2_5p = stripEnv p ->
  forall t, L2_5t = strips t ->
            exists s, L2.wndEval.wndEvals p t s /\ strips s = L2_5s).
Proof.
  intros L2_5p.
  apply (@wndEvalEvals_ind L2_5p
   (fun (L2_5t L2_5s: Term) (prf: wndEval L2_5p L2_5t L2_5s) =>
    forall p: L2Env, L2_5p = stripEnv p ->
    forall t: compile.L2Term, L2_5t = strip t ->
    exists s: L2.compile.Term, L2.wndEval.wndEval p t s /\ strip s = L2_5s)
   (fun (L2_5t L2_5s: Terms) (prf: wndEvals L2_5p L2_5t L2_5s) =>
    forall p: L2Env, L2_5p = stripEnv p ->
    forall t: compile.L2Terms, L2_5t = strips t ->
    exists s: L2.compile.Terms, L2.wndEval.wndEvals p t s /\
                                  strips s = L2_5s));
    intros.
  - unfold LookupDfn in l.
    pose proof (Const_strip_inv _ H0) as k. destruct k.
    + subst. destruct (Lookup_stripEnv_inv _ _ _ l) as [x [j1x j2x]].
      destruct x; cbn in j2x.
      * myInjection j2x. exists l0. intuition.
      * discriminate.
    + subst. destruct (Lookup_stripEnv_inv _ _ _ l) as [x [j1x j2x]].
      destruct H1 as [x0 [x1 [x2 jx]]]. destruct x.
      *  HERE
      subst. discriminate.
  - destruct (App_strip_inv _ H0) as [x0 [x1 [x2 [j1x [j2x [j3x j4x]]]]]].
    subst. clear H0.
    destruct (Lam_strip_inv _ j2x) as [y0 [y1 [j1y j2y]]].
    subst. rewrite <- whBetaStep_hom. exists (L2.term.whBetaStep y1 x1 x2).
    intuition.
  - destruct (LetIn_strip_inv _ H0) as [x0 [x1 [x2 [j0x [j1x j2x]]]]].
    subst. rewrite <- (proj1 instantiate_hom).
    exists (L2.term.instantiate x0 0 x2). intuition.
  - destruct (Case_strip_inv _ H0) as [x0 [x1 [j0x [j1x [j2x j3x]]]]].
    clear H0. subst.
    rewrite <- canonicalP_hom in e.
    case_eq (L2.term.canonicalP x1); intros; rewrite H in e; try discriminate.
    + destruct p0 as [[z0 z1] z2]. cbn in e. myInjection e.
      destruct ml. cbn in e0.
      rewrite <- tskipn_hom in e0.
      case_eq (L2.term.tskipn n0 z1); intros; rewrite H0 in e0;
      try discriminate.
      * { cbn in e0. myInjection e0.
          rewrite <- whCaseStep_hom in e1; try discriminate.
          case_eq (L2.term.whCaseStep n t j0x); intros; rewrite H1 in e1;
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
      exists (L2.term.pre_whFixStep t y0 (L2.compile.tcons x1 x2)).
      intuition. apply (L2.wndEval.sFix p y0 m x1 x2 H ).
      rewrite tlength_hom in l. assumption.
  - destruct (Cast_strip_inv _ H0) as [x0 [x1 [j0x j1x]]]. subst.
    exists x0. intuition.
  - destruct (Prf_strip_inv _ H0) as [x0 [j0 j1]]. subst.
    exists x0. intuition.
  - destruct (App_strip_inv _ H1) as [x0 [x1 [x2 [j1x [j2x [j3x j4x]]]]]].
    subst. rewrite <- tcons_hom.
    destruct (H p eq_refl x0 eq_refl) as [y0 [j0y j1y]].
    subst. rewrite <- mkApp_hom.
    exists (L2.term.mkApp y0 (L2.compile.tcons x1 x2)). intuition.
  - destruct (App_strip_inv _ H1) as [x0 [x1 [x2 [j1x [j2x [j3x j4x]]]]]].
    subst. clear H1.
    destruct (H p eq_refl (L2.compile.tcons x1 x2) eq_refl) as
        [y [j0y j1y]]. clear H.
    rewrite <- j1y in w. 
    inversion_Clear j0y.
    + rewrite tcons_hom in j1y. myInjection j1y.
      rewrite <- (TApp_hom x0 r x2). exists (L2.compile.TApp x0 r x2).
      intuition.
    + rewrite tcons_hom in j1y. myInjection j1y.
      rewrite <- (TApp_hom x0 x1 ss). exists (L2.compile.TApp x0 x1 ss).
      intuition.
  - destruct (LetIn_strip_inv _ H1) as [x0 [x1 [x2 [j0x [j1x j2x]]]]].
    subst. clear H1.
    specialize (H p eq_refl x0 eq_refl).
    destruct H as [y [j0y j1y]]. subst. rewrite <- (TLetIn_hom nm y x1).
    exists (L2.compile.TLetIn nm y x1 x2). intuition.
  - destruct (Case_strip_inv _ H1) as [x0 [x1 [j0x [j1x [j2x j3x]]]]].
    clear H1. subst.
    specialize (H p eq_refl x1 eq_refl).
    destruct H as [y [j0y j1y]]. subst. rewrite <- (TCase_hom nl x0 y).
    exists (L2.compile.TCase nl x0 y j0x). intuition.
  - destruct (tcons_strip_inv _ H1) as [x0 [x1 [j0x [j1x j2x]]]]. subst.
    specialize (H p eq_refl x0 eq_refl).
    destruct H as [y [j0y j1y]]. subst.
    rewrite <- tcons_hom. exists (L2.compile.tcons y x1). intuition.
  - destruct (tcons_strip_inv _ H1) as [x0 [x1 [j0x [j1x j2x]]]]. subst.
    specialize (H p eq_refl x1 eq_refl).
    destruct H as [y [j0y j1y]]. subst.
    rewrite <- tcons_hom. exists (L2.compile.tcons x0 y). intuition.
Qed.
Print Assumptions L2_5wndEval_sound_for_L2wndEval.

********************)
