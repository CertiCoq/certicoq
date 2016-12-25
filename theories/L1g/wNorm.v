
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
Require Import L1g.awndEval.
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
| WNLam: forall nm ty bod, WNorm ty -> WNorm (TLambda nm ty bod)
| WNProd: forall nm ty bod, WNorm ty -> WNorm (TProd nm ty bod)
| WNFix: forall ds br, WNorm (TFix ds br)
| WNAx: WNorm TAx
| WNProof: forall t, WNorm t -> WNorm (TProof t)
| WNCase: forall mch n ty brs,
            WNorm mch -> WNorm ty -> WNorms brs -> ~ isCanonical mch ->
            WNorm (TCase n ty mch brs)
| WNConstruct: forall i n arty, WNorm (TConstruct i n arty)
| WNInd: forall i, WNorm (TInd i)
| WNSort: forall srt, WNorm (TSort srt)
| WNApp: forall fn t ts,
           WNorm fn -> WNorms (tcons t ts) ->
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
Hint Constructors WNorm WNorms.
Scheme WNorm_ind' := Induction for WNorm Sort Prop
      with WNorms_ind' := Induction for WNorms Sort Prop.
Combined Scheme WNormWNorms_ind from WNorm_ind', WNorms_ind'.

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

Lemma WNorms_tappendl:
  forall ts us, WNorms (tappend ts us) -> WNorms ts.
Proof.
  induction ts; intros us h.
  - constructor.  - simpl in h. apply WNtcons; inversion_Clear h.
    + assumption.
    + eapply IHts. eassumption.
Qed.

Lemma tappend_WNorms:
  forall ts, WNorms ts -> forall us, WNorms us ->
                                     WNorms (tappend ts us).
Proof.
  induction 1; intros; cbn. assumption.
  constructor; intuition.
Qed.

(********************
Lemma wcbv_WNorm:
  WFaEnv p ->
  forall n t s, wcbvEval p n t = Ret s -> WNorm s.
Proof.
  intros hp n t.
  functional induction (wcbvEval p n t); intros; try discriminate;
  try (solve[myInjection H; apply IHe0; eassumption]);
  try (solve[apply IHe2; assumption]).
  - apply IHe0. assumption.
  - myInjection H. destruct ergs.
    + constructor.
    + eapply WNAppFix; try eassumption.
      * constructor.

    myInjection H. apply IHe1.

****************)    

(************ hopefully fix this later  ****************
Lemma Wcbv_WNorm:
  WFaEnv p ->
  (forall t s, WcbvEval p t s -> WNorm s) /\
  (forall ts ss, WcbvEvals p ts ss -> WNorms ss).
Proof.
  intros hp.
  apply WcbvEvalEvals_ind; simpl; intros;
  try (solve[constructor; try assumption]); try assumption.
  - destruct (WcbvEvals_tcons_tcons w0) as [y0 [y1 jy]]. subst aargs'.
    inversion_Clear w0. inversion_Clear H0.
    destruct (mkApp_isApp_lem fn' y0 y1) as [x0 [x1 [x2 [k1 k2]]]].
    rewrite k1. clear k1.
    destruct k2; [destruct H0 as  [j1 [j2 [j3 j4]]]; subst |
                  destruct H0 as [j1 [j2 j3]]].
    + cbn. constructor; try assumption. constructor; try assumption.
    + constructor. try assumption.
      * constructor; try assumption.
      * { destruct (mkApp_isApp_lem fn' y0 y1) as [z0 [z1 [z2 [c1 c2]]]].
          rewrite c1 in k1. clear c1. myInjection k1. inversion_Clear w0.
          inversion_Clear H0. destruct c2.
          - destruct H0 as [h1 [hb [hc hd]]]. contradiction.
          - destruct H0 as [h1 [hb hc]]. 
            constructor. myInjection k1. inversion_Clear H. assumption. 

        constructor.


          
      * destruct H1 as [j1 [j2 [j3 j4]]]. subst. assumption.
      * destruct H1 as [j1 [j2 j3]].
        destruct j1 as [z0 [z1 [z2 jz]]]. rewrite jz in k1.
        cbn in k1. myInjection k1. inversion_Clear H. assumption. 
      * destruct H1 as [j1 [j2 [j3 j4]]]. subst. assumption.
      *
        
      destruct i as [x0 [x1 [x2 jx]]]. rewrite jx.

  
  try inversion_Clear H0; intuition.
  - apply H. assert (k:= lookupDfn_LookupDfn _ _ e).
    assert (j:= Lookup_pres_WFapp hp k). inversion_Clear j. assumption.
  - inversion_Clear H2. apply H1.
    assert (j:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H7). inversion_Clear j.
    assert (j: WFapps (tcons a1' args)).
    { apply (proj2 (wcbvEval_pres_WFapp hp) _ _ w0).
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
    eapply (proj2 (wcbvEval_pres_WFapp hp)). eassumption.
    constructor; assumption.
  - inversion_Clear H1. specialize (H H6).
    assert (j: WFapp fn').
    { eapply (proj1 (wcbvEval_pres_WFapp hp)); eassumption. }
    rewrite mkApp_goodFn; try assumption.
    constructor; try assumption.
    + admit.
    +
      
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
*****************)

(** If a program is in weak normal form, it has no wndEval step **)
Lemma wNorm_no_wndStep_lem:
  (forall t s, wndEval p t s -> ~ WNorm t) /\
  (forall ts ss, wndEvals p ts ss -> ~ WNorms ts).
Proof.
  apply wndEvalEvals_ind; intros; intros h;
  try (solve[inversion h]);
  try (solve[inversion h; subst; contradiction]).
  - inversion h. subst. elim H4. exists nm, ty, bod. reflexivity.
  - inversion h. subst. elim H6.
    eapply canonicalP_isCanonical. eassumption.
  - inversion_Clear h.
    + elim H5. auto.
    + rewrite e in H4. myInjection H4. omega.
  - inversion_Clear h.
    + contradiction.
    + elim H. constructor.
Qed.

Lemma wNorm_no_wndStep:
  forall t, WNorm t -> no_wnd_step p t.
Proof.
  unfold no_wnd_step, no_wnds_step, no_step. intros t h0 b h1.
  elim (proj1 (wNorm_no_wndStep_lem) _ _ h1). assumption.
Qed.


End Sec_environ.
