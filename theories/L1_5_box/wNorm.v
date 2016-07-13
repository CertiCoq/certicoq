(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec.
Require Import L1.term.
Require Import L1.program.
Require Import L1.wndEval.
Require Import L1.awndEval.
Require Import L1.wcbvEval.

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
Variable p:environ.
  
Inductive WNorm: Term -> Prop :=
| WNLam: forall nm ty bod, WNorm ty -> WNorm (TLambda nm ty bod)
| WNProd: forall nm ty bod, WNorm ty -> WNorm (TProd nm ty bod)
| WNFix: forall ds br, WDNorms ds -> WNorm (TFix ds br)
| WNAx: forall nm, LookupAx nm p -> WNorm (TConst nm)
| WNCase: forall mch n ty brs,
            WNorm mch -> WNorm ty -> WNorms brs -> ~ isCanonical mch ->
            WNorm (TCase n ty mch brs)
| WNConstruct: forall i n, WNorm (TConstruct i n)
| WNInd: forall i, WNorm (TInd i)
| WNSort: forall srt, WNorm (TSort srt)
| WNApp: forall fn t ts,
           WNorm fn -> WNorm t -> WNorms ts ->
           ~ isLambda fn -> ~ isFix fn -> ~ isApp fn ->
           WNorm (TApp fn t ts)
with WNorms: Terms -> Prop :=
| WNtnil: WNorms tnil
| WNtcons: forall t ts, WNorm t -> WNorms ts -> WNorms (tcons t ts)
with WDNorms: Defs -> Prop :=
| WDNtnil: WDNorms dnil
| WDNtcons: forall t ds n s i,
              WNorm t -> WNorm s -> WDNorms ds -> WDNorms (dcons n t s i ds).
Hint Constructors WNorm WNorm WDNorms.
Scheme WNorm_ind' := Induction for WNorm Sort Prop
      with WNorms_ind' := Induction for WNorms Sort Prop
      with WDNorms_ind' := Induction for WDNorms Sort Prop.
Combined Scheme WNormWNorms_ind
         from WNorm_ind', WNorms_ind', WDNorms_ind' .

Ltac rght := solve [right; intros h; inversion_Clear h; contradiction].
Ltac lft := solve [left; constructor; assumption].

(*** Is this desirable ??? ***
Lemma WNorm_WFapp:
  (forall s, WNorm s -> WFapp s) /\
  (forall ss, WNorms ss -> WFapps ss) /\
  (forall dts, WDNorms dts -> WFappDs dts).
Proof.
  apply WNormWNorms_ind; intros; constructor; try assumption.
Qed.
 ****)

(** WNorm is decidable **)
Lemma WNorm_dec:
  (forall t, WNorm t \/ ~ WNorm t) /\
  (forall ts, WNorms ts \/ ~ WNorms ts) /\
  (forall (ds:Defs), WDNorms ds \/ ~ WDNorms ds).
Proof.
  apply TrmTrmsDefs_ind; intros; auto;
  try (solve[right; intros h; inversion h]);
  try (solve[left; constructor]).
  - destruct H; [lft|rght].
  - destruct H; [lft|rght].
  - destruct (isLambda_dec t). rght.
    destruct (isFix_dec t). rght.
    destruct (isApp_dec t). rght.
    destruct H, H0, H1; try rght.
    + left. apply WNApp; auto.
  - destruct (Lookup_dec s p).
    + destruct H. destruct (isAx_dec x).
      * left. constructor. subst. assumption.
      * right. intros j. inversion j. elim H0.
        unfold LookupAx in H2. apply (Lookup_single_valued H H2).
    + right. intros h. inversion h. eelim H. apply H1.
  - destruct H, H0, H1; try rght.
    + destruct (isCanonical_dec t0); try rght.
      * left. constructor; auto.
  - destruct H; [lft|rght]. 
  - destruct H, H0; try rght.
    + left. constructor; assumption.
  - destruct H, H0, H1; try rght.
    + left. constructor; assumption.
Qed.

Lemma WNorms_tappendl:
  forall ts us, WNorms (tappend ts us) -> WNorms ts.
Proof.
  induction ts; intros us h.
  - constructor.  - simpl in h. apply WNtcons; inversion_Clear h.
    + assumption.
    + eapply IHts. eassumption.
Qed.

  
Lemma Wcbv_WNorm:
  WFaEnv p ->
  (forall t s, WcbvEval p t s -> WFapp t -> WNorm s) /\
  (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> WNorms ss) /\
  (forall dts dss, WcbvDEvals p dts dss ->  WFappDs dts -> WDNorms dss).
Proof.
  intros hp.
  apply WcbvEvalEvals_ind; simpl; intros; try (solve[constructor]);
  try inversion_Clear H0; intuition.
  - apply H. assert (j:= Lookup_pres_WFapp hp l). inversion j. assumption.
  - inversion_Clear H2. apply H1. 
    assert (j:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H7). inversion_Clear j.
    assert (j: WFapps (tcons a1' args')).
    { apply (proj1 (proj2 (wcbvEval_pres_WFapp hp)) _ _ w0).
      constructor; assumption. }
    inversion_Clear j.
    apply whBetaStep_pres_WFapp; try assumption.
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp.
    + assumption.
    + refine (proj1 (wcbvEval_pres_WFapp hp) _ _ _ _); eassumption.
  - inversion_clear H2. specialize (H H4). inversion_Clear H.
    assert (k:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H4). inversion_Clear k.
    apply H1.
    refine (pre_whFixStep_pres_WFapp _ _ _); try eassumption.
    eapply (dnthBody_pres_WFapp H2 _ e).
    eapply (proj1 (proj2 (wcbvEval_pres_WFapp hp))). eassumption.
    constructor; assumption.
  - inversion_Clear H1. 
    assert (j0: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j0). inversion_Clear H0.
    constructor; try eassumption; intuition.
    + destruct H0 as [x1 [x2 [x3 j]]]. discriminate.
    + destruct H0 as [x1 [x2 j]]. discriminate.
    + destruct H0 as [x1 [x2 [x3 j]]]. discriminate.
  - inversion_Clear H1. 
    assert (j0: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j0). inversion_Clear H0.
    constructor; try eassumption; intuition.
    + destruct H0 as [x1 [x2 [x3 j]]]. discriminate.
    + destruct H0 as [x1 [x2 j]]. discriminate.
    + destruct H0 as [x1 [x2 [x3 j]]]. discriminate.
  - inversion_Clear H1. 
    assert (j0: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j0). inversion_Clear H0.
    constructor; try eassumption; intuition.
    + destruct H0 as [x1 [x2 [x3 j]]]. discriminate.
    + destruct H0 as [x1 [x2 j]]. discriminate.
    + destruct H0 as [x1 [x2 [x3 j]]]. discriminate.
  - inversion_Clear H1. apply H0. refine (whCaseStep_pres_WFapp _ _ _ e1).
    + assumption.
    + refine (tskipn_pres_WFapp _ _ e0).
      refine (canonicalP_pres_WFapp _ e).
      refine (proj1 (wcbvEval_pres_WFapp hp) _ _ w _). assumption.
  - inversion_Clear H2. constructor; try (solve[intuition]).
    intros h. inversion h.
    + rewrite <- H2 in e. simpl in e. discriminate.
    + rewrite <- H2 in e. simpl in e. discriminate.
  - inversion_Clear H1. constructor; intuition.
  - inversion_Clear H2. constructor; intuition.
Qed.

Lemma wcbvEval_no_further:
    (forall t s, WcbvEval p t s -> WcbvEval p s s) /\
    (forall ts ss, WcbvEvals p ts ss -> WcbvEvals p ss ss) /\
    (forall ds es, WcbvDEvals p ds es -> WcbvDEvals p es es).
Proof.
  apply WcbvEvalEvals_ind; simpl; intros; auto.
Qed.


(** If a program is in weak normal form, it has no wndEval step **)
Lemma wNorm_no_wndStep_lem:
  (forall t s, wndEval p t s -> ~ WNorm t) /\
  (forall ts ss, wndEvals p ts ss -> ~ WNorms ts) /\
  (forall ds es, wndDEvals p ds es -> ~ WDNorms ds).
Proof.
  apply wndEvalEvals_ind; intros; intros h;
  try (solve[inversion h]);
  try (solve[inversion h; subst; contradiction]).
  - inversion h.
    inversion l; subst;
    unfold LookupDfn in l; unfold LookupAx in H0;
    assert (j:= Lookup_single_valued l H0); discriminate.
  - inversion h. subst. elim H5. exists nm, ty, bod. reflexivity.
  - inversion h. subst. elim H6.
    eapply canonicalP_isCanonical. eassumption.
  - inversion h. subst. elim H6. apply IsFix.
  - inversion_Clear h. elim H. constructor; assumption.
Qed.

Lemma wNorm_no_wndStep:
  forall t, WNorm t -> no_wnd_step p t.
unfold no_wnd_step, no_wnds_step, no_step. intros t h0 b h1.
elim (proj1 (wNorm_no_wndStep_lem) _ _ h1). assumption.
Qed.

End Sec_environ.
