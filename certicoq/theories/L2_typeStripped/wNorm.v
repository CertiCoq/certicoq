
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import L2.term.
Require Import L2.program.
Require Import L2.wndEval.
Require Import L2.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Local Open Scope program_scope.
Set Implicit Arguments.

(** Weak typed normal form: normal form of wndEval:
*** no wndEval steps possible (including no steps in type fields.
**)
Section Sec_environ.
Variable p:environ Term.
  
Inductive WNorm: Term -> Prop :=
| WNLam: forall nm bod, WNorm (TLambda nm bod)
| WNProd: forall nm bod, WNorm (TProd nm bod)
| WNFix: forall ds br, WNorm (TFix ds br)
| WNAx: WNorm TAx
| WNCase: forall mch n brs,
            WNorm mch -> ~ isCanonical mch ->
            WNorm (TCase n mch brs)
| WNConstruct: forall i n arty, WNorm (TConstruct i n arty)
| WNInd: forall i, WNorm (TInd i)
| WNSort: forall s, WNorm (TSort s)
| WNApp: forall fn t ts,
           WNorm fn -> WNorm t -> WNorms ts ->
           ~ (isLambda fn) -> ~ (isFix fn) -> ~ isApp fn ->
           WNorm (TApp fn t ts)
| WNAppFix: forall ds m t ts x ix,
              WNorms (tcons t ts) ->
              dnthBody m ds = Some (x, ix) ->
              ix > tlength ts ->  (* too few args to see rec arg *)
              WNorm (TApp (TFix ds m) t ts)
with WNorms: Terms -> Prop :=
| WNtnil: WNorms tnil
| WNtcons: forall t ts, WNorm t -> WNorms ts -> WNorms (tcons t ts).
Hint Constructors WNorm WNorm.
Scheme WNorm_ind' := Induction for WNorm Sort Prop
      with WNorms_ind' := Induction for WNorms Sort Prop.
Combined Scheme WNormWNorms_ind from WNorm_ind', WNorms_ind'.

(****************************
(** WNorm is decidable **)
Lemma WNorm_dec: 
  (forall t, WNorm t \/ ~ WNorm t) /\
  (forall ts, WNorms ts \/ ~ WNorms ts) /\
  (forall (ds:Defs), True).
Proof.
  Ltac rght := solve [right; intros h; inversion_Clear h; contradiction].
  Ltac lft := solve [left; constructor; assumption].
  apply TrmTrmsDefs_ind; intros; auto;
  try (solve[right; intros h; inversion h]);
  try (solve[left; constructor]).
  - destruct (isLambda_dec t). rght.
    destruct (isFix_dec t). rght.
    destruct H, H0, H1; try rght.
    + left. apply WNApp; auto.
  - destruct H, H0; try rght.
    + destruct (isCanonical_dec t).
      * right. inversion H1; intros h; inversion h; subst; contradiction.
      * left. constructor; auto.
  - destruct H, H0;
    try (solve [right; intros h; inversion_Clear h; contradiction]).
    + left; constructor; auto.
Qed.
 **********************************)

Lemma WNorms_tappendl:
  forall ts us, WNorms (tappend ts us) -> WNorms ts.
Proof.
  induction ts; intros us h.
  - constructor.
  - simpl in h. apply WNtcons; inversion_Clear h.
    + assumption.
    + eapply IHts. eassumption.
Qed.

(*********************************
Lemma Wcbv_WNorm:
  WFaEnv p ->
  (forall t s, WcbvEval p t s -> WFapp t -> WNorm s) /\
  (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> WNorms ss).
Proof.
  intros hp.
  apply WcbvEvalEvals_ind; simpl; intros; try (solve[constructor]);
  try inversion_Clear H0; intuition.
  - apply H. assert (j:= Lookup_pres_WFapp hp l). inversion j. assumption.
  - inversion_Clear H2. apply H1. 
    assert (j:= proj1 (WcbvEval_pres_WFapp hp) _ _ w H7). inversion_Clear j.
    assert (j: WFapps (tcons a1' args')).
    { apply (proj2 (WcbvEval_pres_WFapp hp) _ _ w0).
      constructor; assumption. }
    inversion_Clear j.
    apply whBetaStep_pres_WFapp; try assumption.
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp.
    + assumption.
    + refine (proj1 (WcbvEval_pres_WFapp hp) _ _ _ _); eassumption.
  - inversion_clear H2. specialize (H H4). inversion_Clear H.
    assert (k:= proj1 (WcbvEval_pres_WFapp hp) _ _ w H4). inversion_Clear k.
    apply H1.
    refine (pre_whFixStep_pres_WFapp _ _ _); try eassumption.
    eapply (dnthBody_pres_WFapp H2 _ e).
    eapply (proj2 (WcbvEval_pres_WFapp hp)). eassumption.
    constructor; assumption.
  - inversion_Clear H2. 
    assert (j0: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j0). inversion_Clear H0.
    specialize (H H7).
    apply H1.
    assert (k:= proj1 (WcbvEval_pres_WFapp hp) _ _ w H7).
    assert (k0:= proj2 (WcbvEval_pres_WFapp hp) _ _ w0 j0).
    apply mkApp_pres_WFapp; assumption.
   - inversion_Clear H1. apply H0. refine (whCaseStep_pres_WFapp _ _ _ e1).
    + assumption.
    + refine (tskipn_pres_WFapp _ _ e0).
      refine (canonicalP_pres_WFapp _ e).
      refine (proj1 (WcbvEval_pres_WFapp hp) _ _ w _). assumption.
  - inversion_Clear H1. constructor; try (solve[intuition]).
    intros h. inversion h.
    + rewrite <- H1 in e. simpl in e. discriminate.
    + rewrite <- H1 in e. simpl in e. discriminate.
  - inversion H.
  - inversion_Clear H1. constructor; intuition.
Qed.
*************************************)

(** If a program is in weak normal form, it has no wndEval step **)
Lemma wNorm_no_wndStep_lem:
  (forall t s, wndEval p t s -> ~ WNorm t) /\
  (forall ts ss, wndEvals p ts ss -> ~ WNorms ts).
Proof.
  apply wndEvalEvals_ind; intros; intros h;
  try (solve[inversion h]);
  try (solve[inversion h; subst; contradiction]).
  - inversion h. subst. elim H5. exists nm, bod. reflexivity.
  - inversion h. subst. elim H3.
    eapply canonicalP_isCanonical. eassumption.
  - inversion_Clear h.
    + elim H6. auto.
    + rewrite e in H4. myInjection H4. omega.
  - inversion_Clear h.
    + contradiction.
    + elim H. constructor.
  - inversion_Clear h.
    + elim H. constructor; assumption.
    + contradiction.
Qed.

Lemma wNorm_no_wndStep:
  forall t, WNorm t -> no_wnd_step p t.
unfold no_wnd_step, no_wnds_step, no_step. intros t h0 b h1.
elim (proj1 wNorm_no_wndStep_lem _ _ h1). assumption.
Qed.

(*** correctness assumption for removing fixpoint unrolling guard ***)
Definition WFfixp (t:Term) :=
  forall (ds:Defs) (m:nat) (arg:Term) (args:Terms),
    t = (TApp (TFix ds m) arg args) ->
  forall x ix, dnthBody m ds = Some (x, ix) ->
  forall t, tnth ix (tcons arg args) = Some t ->
  WNorm t -> exists z, canonicalP t = Some z.
 (*******************)

End Sec_environ.
