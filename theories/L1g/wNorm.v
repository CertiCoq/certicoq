
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Common.AstCommon.
Require Import L1g.term.
Require Import L1g.program.
Require Import L1g.wndEval.
Require Import L1g.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.


(** Weak typed normal form: normal form of wndEval:
*** no wndEval steps possible (including no steps in type fields.
*** TRel is not itself a weak typed normal form, but unbound indices
*** may occur under a binder in a weak typed normal form
**)
Section Sec_environ.
Variable p: environ Term.
  
Inductive WNorm: Term -> Prop :=
| WNLam: forall nm bod, WNorm (TLambda nm bod)
| WNFix: forall ds br, WNorm (TFix ds br)
| WNCase: forall i mch brs,
    WNorm mch -> ~ isCanonical mch -> WNorm (TCase i mch brs)
| WNConstruct: forall i n np na, WNorm (TConstruct i n np na)
| WNProof: WNorm TProof
| WNApp: forall fn t,
    WNorm fn -> ~ isLambda fn -> ~ isFix fn -> ~ isProof fn -> WNorm t ->
    WNorm (TApp fn t).
Hint Constructors WNorm.

Ltac rght := solve [right; intros h; inversion_Clear h;
                    first [contradiction | isLam_inv | isApp_inv]].
Ltac lft := solve [left; constructor; assumption].

(** WNorm is decidable **
Lemma WNorm_dec:
  (forall t, WNorm t \/ ~ WNorm t) /\
  (forall ts, WNorms ts \/ ~ WNorms ts) /\
  (forall (ds:Defs), True).
Proof.
  Local Ltac argNotNorm h1 h2 :=
    right; intro j; inversion_Clear j;
    try (elim h1; auto); try (inversion_Clear h2; contradiction).
  apply TrmTrmsDefs_ind; intros; auto;
  try (solve[right; intros h; inversion h]);
  try (solve[left; constructor]).
  - destruct H; [lft|rght].  
  - destruct H; [lft|rght].
  - destruct (isApp_dec t); try rght.
    destruct (isLambda_dec t); try rght.
    destruct (isFix_dec t).
    + destruct i as [x0 [x1 jx]]; subst.
      destruct H0, H1;
        try (right; intro j; inversion_Clear j;
             inversion_Clear H6; contradiction).
      case_eq (dnthBody x1 x0); intros.
      * { case_eq (tnth (snd p0) (tcons t0 t1)); intros.
          - case_eq (canonicalP t); intros.
            + right. intros j. inversion_Clear j.
              * elim H11. auto.
              * rewrite H2 in H10. myInjection H10.
                unfold snd in H3. rewrite H11 in H3. myInjection H3.
                rewrite H4 in H12. discriminate.
            + left. destruct p0. eapply WNAppFix; try eassumption. intuition.
          - left.

    
  - destruct (isFix_dec t).
    + destruct i as [x0 [x1 jx]]; subst. destruct H.
      * admit.
      * elim H. auto.
    + 
      * { inversion_Clear H. destruct H0, H1.
          - case_eq (dnthBody x1 x0); intros.
            + case_eq (tnth (snd p0) (tcons t0 t1)); intros.
              * { case_eq (canonicalP t); intros.
                  - right. intros j. inversion_Clear j.
                    + elim H10. auto.
                    + rewrite H3 in H11. discriminate.

                      
  - destruct (isLambda_dec t).
    + rght.
    +
      try rght. intros h. inversion_Clear h. contradiction.
    destruct (isFix_dec t). rght.
    destruct (isApp_dec t). rght.
    destruct H, H0, H1; try rght.
    + left. apply WNApp; auto. constructor; assumption.
    + right. intros h; inversion_Clear h. inversion_Clear H6. contradiction.
    + right. intros h; inversion_Clear h. inversion_Clear H6. contradiction.
    + right. intros h; inversion_Clear h. inversion_Clear H6. contradiction.
  - destruct H, H0, H1; try rght.
    + destruct (isCanonical_dec t0); try rght.
      * left. constructor; auto.
  - destruct H, H0; try rght.
    + left. constructor; assumption.
Qed.
 ************)


(************ Wcbv reaches weak normal form ****************)
Lemma Wcbv_WNorm:
  forall p t s, WcbvEval p t s -> WNorm s.
Proof.
  induction 1; simpl; intros;
    try (solve[constructor; try assumption]); try assumption.
  - destruct H0 as [H0|[H0|H0]]; dstrctn H0; subst.
    + inversion_Clear IHWcbvEval1. inversion_Clear H3.
      * elim H4. auto.
      * elim H5. auto.
      * apply WNApp; try assumption. 
        -- apply WNApp; try assumption. constructor; assumption.
        -- intros h; dstrctn h; discriminate.
        -- intros h; dstrctn h; discriminate.
        -- intros h. unfold isProof in h. discriminate.
      * constructor; try assumption.
        -- constructor; try assumption. constructor; assumption.
        -- intros h; dstrctn h; discriminate.
        -- intros h; dstrctn h; discriminate.
        -- intros h. unfold isProof in h. discriminate.
      * elim H6. auto.
      * apply WNApp; try assumption.
        -- apply WNApp; try assumption. constructor; assumption.
        -- intros h; dstrctn h; discriminate.
        -- intros h; dstrctn h; discriminate.
        -- intros h. unfold isProof in h. discriminate.
    + apply WNApp; try assumption.
      * intros h; dstrctn h; discriminate.
      * intros h; dstrctn h; discriminate.
      * intros h; unfold isProof in h; discriminate.
    + constructor; try assumption.
      * intros h; dstrctn h; discriminate.
      * intros h; dstrctn h; discriminate.
      * intros h; unfold isProof in h; discriminate.
Qed.

(** If a program is in weak normal form, it has no wndEval step **
Lemma wNorm_no_wndStep_lem:
  forall t s, wndEval p t s -> ~ WNorm t.
Proof.
  induction 1; intros; intros h; inversion_Clear h; subst.
  - elim H2. auto.
  - elim H4. auto.
  - elim H4. auto.
  - contradiction.
  - inversion_Clear H2.
    + elim H3. auto.
    + elim H4. auto.
    + admit.
    + elim H5. auto.
    +
      
    apply wndEvalEvals_ind; intros; intros h;
      try (solve[inversion h]);
      try (solve[inversion h; subst; contradiction]).
  - inversion h. subst. elim H4. exists nm, ty, bod. reflexivity.
  - inversion_Clear h. elim H5. auto.
  - inversion_Clear h. elim H7. auto.
Qed.

Lemma wNorm_no_wndStep:
  forall t, WNorm t -> no_wnd_step p t.
Proof.
  unfold no_wnd_step, no_wnds_step, no_step. intros t h0 b h1.
  elim (proj1 (wNorm_no_wndStep_lem) _ _ h1). assumption.
Qed.
*********************)

End Sec_environ.
