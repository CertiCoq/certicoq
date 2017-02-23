
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.omega.Omega.
Require Import Common.Common.
Require Import L2_5.term.
Require Import L2_5.program.
Require Import L2_5.wndEval.
Require Import L2_5.awndEval.
Require Import L2_5.wcbvEval.

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
| WNPrf: WNorm TProof
| WNLam: forall nm bod, WNorm (TLambda nm bod)
| WNProd: forall nm bod, WNorm (TProd nm bod)
| WNFix: forall ds br, WNorm (TFix ds br)
| WNAx: WNorm TAx
| WNCase: forall mch n brs,
            WNorm mch -> ~ isCanonical mch ->
            WNorm (TCase n mch brs)
| WNConstruct: forall i n arty, WNorm (TConstruct i n arty)
| WNInd: forall i, WNorm (TInd i)
| WNSort: forall srt, WNorm (TSort srt)
| WNApp: forall fn t ts,
           WNorm fn -> WNorm t -> WNorms ts ->
           ~ isLambda fn -> ~ isFix fn -> ~ isApp fn ->
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

Ltac rght := solve [right; intros h; inversion_Clear h; contradiction].
Ltac lft := solve [left; constructor; assumption].

(*** Is this desirable ??? ***
Lemma WNorm_WFapp:
  (forall s, WNorm s -> WFapp s) /\
  (forall ss, WNorms ss -> WFapps ss).
Proof.
  apply WNormWNorms_ind; intros; constructor; try assumption.
Qed.
 ****)

(*****
(** WNorm is decidable **)
Lemma WNorm_dec:
  (forall t, WNorm t \/ ~ WNorm t) /\
  (forall ts, WNorms ts \/ ~ WNorms ts) /\
  (forall ds:Defs, True).
Proof.
  apply TrmTrmsDefs_ind; intros; auto;
  try (solve[right; intros h; inversion h]);
  try (solve[left; constructor]).
  - destruct H; [lft|rght].
  - destruct H; [lft|rght].
  - destruct (isLambda_dec t). rght.
    destruct (isFix_dec t). rght.
    destruct H, H0, H1; try rght.
    + left. apply WNApp; auto.
  - destruct H, H0, H1; try rght.
    + destruct (isCanonical_dec t0); try rght.
      * left. constructor; auto.
  - destruct H, H0; try rght.
    + left. constructor; assumption.
Qed.
*****)

Lemma WNorms_tappendl:
  forall ts us, WNorms (tappend ts us) -> WNorms ts.
Proof.
  induction ts; intros us h.
  - constructor.  - simpl in h. apply WNtcons; inversion_Clear h.
    + assumption.
    + eapply IHts. eassumption.
Qed.

Lemma tappend_WNorms:
  forall ts, WNorms ts -> forall us, WNorms us -> WNorms (tappend ts us).
Proof.
  induction 1; intros.
  - cbn. assumption.
  - cbn. constructor; try assumption. apply IHWNorms. assumption.
Qed.

(***************
Lemma WNorm_mkApp:
  (forall fn, WNorm fn -> ~ isLambda fn -> ~ isFix fn -> 
              forall args, WNorms args -> WNorm (mkApp fn args)).
Proof.
  induction 1; intros; destruct args;
  try (solve[rewrite mkApp_tnil_ident; intuition]);
  try (solve[rewrite mkApp_goodFn; try not_isApp]);
  try (solve[inversion_Clear H1; repeat constructor; try assumption;
             try not_isFix; not_isApp]).
  - inversion_Clear H3. constructor; try assumption.
    + constructor; try assumption.
    + not_isApp.
  - inversion_Clear H7. constructor; try assumption.
    + eapply tappend_WNorms; try assumption.  constructor; try assumption.
  - rewrite mkApp_tnil_ident. eapply WNAppFix; try eassumption.
  - inversion_Clear H. cbn.
    case_eq (ix ?= tlength ts); intros.
    + eapply WNApp; try eassumption.
      * constructor.
      * apply tappend_WNorms; try assumption.
      * not_isLambda.
      * rewrite (nat_compare_eq _ _ H) in H1. omega.
      * not_isApp.
    + assert (j:= nat_compare_Lt_lt _ _ H). omega.
    + Check (nat_compare_Gt_gt _ _ H). 

    
    case_eq (ix ?= tlength (tappend ts (tcons t0 args))); intros.
    + eapply WNApp; try eassumption.
      * constructor.
      * apply tappend_WNorms; try assumption.
      * not_isLambda.
      * rewrite (nat_compare_eq _ _ H) in H1.
    eapply WNAppFix; try eassumption.
    + constructor; try assumption. apply tappend_WNorms; try assumption.
    + rewrite tlength_tappend. omega.
Qed.
 **********************)
                          
(*********
Lemma WNorm_TApp:
  (forall fn, WNorm fn -> ~ isLambda fn -> ~ isFix fn -> 
              forall arg, WNorm arg -> forall args, WNorms args ->
                                                    WNorm (TApp fn arg args)).
Proof.
  induction 1; intros;
  try (solve[destruct H3 as [x0 [x1 [x2 j]]]; discriminate]);
  try (solve[repeat constructor; try assumption; not_isApp]).
  - repeat constructor; try assumption.
    
  try (elim H; not_isLambda). destruct args;
  try (solve[rewrite mkApp_tnil_ident; intuition]);
  try (solve[rewrite mkApp_goodFn; try not_isApp]);
  try (solve[inversion_Clear H1; repeat constructor; try assumption;
             try not_isFix; not_isApp]).
  - inversion_Clear H4. constructor; try assumption.
    + constructor; try assumption.
    + not_isApp.
  - inversion_Clear H7. constructor; try assumption.
    + eapply tappend_WNorms; try assumption.  constructor; try assumption.
Qed.
   try (repeat constructor; intuition).

 (***********)
Lemma Wcbv_WNorm:
  WFaEnv p ->
  (forall t s, WcbvEval p t s -> WFapp t -> WNorm s) /\
  (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> WNorms ss).
Proof.
  intros hp.
  apply WcbvEvalEvals_ind; simpl; intros; try (solve[constructor]);
  try inversion_Clear H0; intuition.
  - apply H. assert (j:= e). unfold lookupDfn in e.
    destruct (lookup nm p); try discriminate.
    + destruct e0; try discriminate.
      myInjection e. eapply lookupDfn_pres_WFapp; eassumption.
  - inversion_Clear H2. apply H1. 
    assert (j:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H7). inversion_Clear j.
    assert (j: WFapps (tcons a1' args)).
    { constructor; try assumption.
     eapply (proj1 (wcbvEval_pres_WFapp hp)); eassumption. }
    inversion_Clear j.
    apply whBetaStep_pres_WFapp; try assumption.
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp.
    + assumption.
    + refine (proj1 (wcbvEval_pres_WFapp hp) _ _ _ _); eassumption.
  - inversion_clear H1. specialize (H H3). inversion_Clear H.
    assert (k:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H3). inversion_Clear k.
    apply H0.
    refine (pre_whFixStep_pres_WFapp _ _ _); try eassumption.
    eapply (dnthBody_pres_WFapp H1 _ e).
    constructor; assumption.
  - inversion_Clear H1.
    assert (j0: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j0). inversion_Clear H0.
    specialize (H H6). rewrite mkApp_goodFn.
    + constructor; try eassumption.
    
    apply H1.
    assert (k:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H7).
    assert (k0:= proj2 (wcbvEval_pres_WFapp hp) _ _ w0 j0).
    apply mkApp_pres_WFapp; assumption.

  - inversion_Clear H2. 
    assert (j0: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j0). inversion_Clear H0.
    specialize (H H7).
    apply H1.
    assert (k:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H7).
    assert (k0:= proj2 (wcbvEval_pres_WFapp hp) _ _ w0 j0).
    apply mkApp_pres_WFapp; assumption.
  - inversion_Clear H1. apply H0. refine (whCaseStep_pres_WFapp _ _ _ e1).
    + assumption.
    + refine (tskipn_pres_WFapp _ _ e0).
      refine (canonicalP_pres_WFapp _ e).
      refine (proj1 (wcbvEval_pres_WFapp hp) _ _ w _). assumption.
  - inversion_Clear H2. constructor; try (solve[intuition]).
    intros h. inversion h.
    + rewrite <- H2 in e. simpl in e. discriminate.
    + rewrite <- H2 in e. simpl in e. discriminate.
  - inversion H.
  - inversion_Clear H1. constructor; intuition.
Qed.
**********************)

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
  - inversion_Clear h.  elim H6. apply IsFix.
    rewrite e in H4. myInjection H4. omega.
  - inversion_Clear h. elim H.
    + assumption.
    + elim H. constructor.
  - inversion_Clear h.
    + elim H. constructor; assumption.
    + contradiction.
Qed.

Lemma wNorm_no_wndStep:
  forall t, WNorm t -> no_wnd_step p t.
unfold no_wnd_step, no_wnds_step, no_step. intros t h0 b h1.
elim (proj1 (wNorm_no_wndStep_lem) _ _ h1). assumption.
Qed.

End Sec_environ.
