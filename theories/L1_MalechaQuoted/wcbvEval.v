Require Import Lists.List.
Require Import Strings.String.
Require Import Arith.Compare_dec.
Require Import Program.Basics.
Require Import Omega.
Require Import Logic.JMeq.
Require Import L1.term.
Require Import L1.program.
Require Import L1.wndEval.
Require Import L1.awndEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(** Relational version of weak cbv evaluation  **)
Inductive WcbvEval (p:environ) : Term -> Term -> Prop :=
| wLam: forall nm ty ty' bod,
          WcbvEval p ty ty' ->
          WcbvEval p (TLambda nm ty bod) (TLambda nm ty' bod)
| wProd: forall nm ty ty' bod,
          WcbvEval p ty ty' ->
          WcbvEval p (TProd nm ty bod) (TProd nm ty' bod)
| wCast: forall t s ck ty,
          WcbvEval p t s -> WcbvEval p (TCast t ck ty) s
| wConstruct: forall i r, WcbvEval p (TConstruct i r) (TConstruct i r)
| wInd: forall i, WcbvEval p (TInd i) (TInd i) 
| wSort: forall srt, WcbvEval p (TSort srt) (TSort srt)
| wFix: forall dts m, WcbvEval p (TFix dts m) (TFix dts m)
| wConst: forall nm (t s:Term),
            LookupDfn nm p t -> WcbvEval p t s -> WcbvEval p (TConst nm) s
| wAppLam: forall (fn ty bod a1 a1' s:Term) (args:Terms) (nm:name),
               WcbvEval p fn (TLambda nm ty bod) ->
               WcbvEval p a1 a1' ->
               WcbvEval p (whBetaStep bod a1' args) s ->
               WcbvEval p (TApp fn a1 args) s
| wLetIn: forall (nm:name) (dfn ty bod dfn' s:Term),
            WcbvEval p dfn dfn' ->
            WcbvEval p (instantiate dfn' 0 bod) s ->
            WcbvEval p (TLetIn nm dfn ty bod) s
| wAppFix: forall dts m (fn arg fs s:Term) (args:Terms),
               WcbvEval p fn (TFix dts m) ->
               whFixStep dts m (tcons arg args) = Some fs ->
               WcbvEval p fs s ->
               WcbvEval p (TApp fn arg args) s
| wAppCnstr: forall fn i n arg arg1 args args1,
               WcbvEval p fn (TConstruct i n) ->
               WcbvEval p arg arg1 ->
               WcbvEvals p args args1 ->
               WcbvEval p (TApp fn arg args)
                        (TApp (TConstruct i n) arg1 args1)
| wAppInd: forall fn i arg arg1 args args1,
               WcbvEval p fn (TInd i) ->
               WcbvEval p arg arg1 ->
               WcbvEvals p args args1 ->
               WcbvEval p (TApp fn arg args)
                        (TApp (TInd i) arg1 args1)
| wCase0: forall mch i n ty brs cs s,
           WcbvEval p mch (TConstruct i n) ->
           whCaseStep n tnil brs = Some cs ->
           WcbvEval p cs s ->
           WcbvEval p (TCase 0 ty mch brs) s
| wCasen: forall mch i n ty arg args np brs cs s ts,
           WcbvEval p mch (TApp (TConstruct i n) arg args) ->
           tskipn np (tcons arg args) = Some ts ->
           whCaseStep n ts brs = Some cs ->
           WcbvEval p cs s ->
           WcbvEval p (TCase np ty mch brs) s
with WcbvEvals (p:environ) : Terms -> Terms -> Prop :=
| wNil: WcbvEvals p tnil tnil
| wCons: forall t t' ts ts',
           WcbvEval p t t' -> WcbvEvals p ts ts' -> 
           WcbvEvals p (tcons t ts) (tcons t' ts').
Hint Constructors WcbvEval WcbvEvals.
Scheme WcbvEval1_ind := Induction for WcbvEval Sort Prop
  with WcbvEvals1_ind := Induction for WcbvEvals Sort Prop.
Combined Scheme WcbvEvalEvals_ind from WcbvEval1_ind, WcbvEvals1_ind.

(** evaluate omega = (\x.xx)(\x.xx): nontermination **)
Definition xx := (TLambda nAnon prop (TApp (TRel 0) (TRel 0) tnil)).
Definition xxxx := (TApp xx xx tnil).
Goal WcbvEval nil xxxx xxxx.
unfold xxxx, xx.
eapply wAppLam. eapply wLam. eapply wSort. eapply wLam. eapply wSort.
unfold whBetaStep, instantiate.
rewrite (proj2 (nat_compare_eq_iff 0 0) eq_refl).
rewrite mkApp_idempotent. rewrite mkApp_idempotent. simpl.
change (WcbvEval nil xxxx xxxx).
Abort.


Lemma WcbvEval_mkApp_nil:
  forall t, WFapp t -> forall p s, WcbvEval p t s ->
                 WcbvEval p (mkApp t tnil) s.
Proof.
  intros p. induction 1; simpl; intros; try assumption.
  - rewrite tappend_tnil. assumption.
Qed.


(** wcbvEval preserves WFapp **)
Lemma wcbvEval_pres_WFapp:
  forall p, WFaEnv p -> 
  (forall t s, WcbvEval p t s -> WFapp t -> WFapp s) /\
  (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> WFapps ss).
Proof.
  intros p hp. apply WcbvEvalEvals_ind; intros; try assumption.
  - inversion_Clear H0. intuition.
  - inversion_Clear H0. intuition.
  - inversion_Clear H0. apply H. assumption.
  - inversion_Clear H0. apply H.
    assert (j:= Lookup_pres_WFapp hp l). inversion j. assumption.
  - inversion_Clear H2. apply H1.
    apply (whBetaStep_pres_WFapp); try assumption.
    + assert (j:= H H7). inversion_Clear j. assumption.
    + apply H0. assumption. 
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp. assumption.
    + apply H. assumption.
  - inversion_Clear H1. apply H0. unfold whFixStep in e.
    assert (k:= H H6). inversion_Clear k.
    assert (j:= dnthBody_pres_WFapp H2 m). destruct (dnthBody m dts).
    + injection e. intros. rewrite <- H1. apply mkApp_pres_WFapp.
      * constructor; assumption.
      * { apply fold_left_pres_WFapp. intros.
          - apply instantiate_pres_WFapp. assumption.
            + constructor. assumption. 
          - apply j. reflexivity. }
    + discriminate.
  - inversion_Clear H2. apply wfaApp; try intuition. 
    + destruct H2 as [x0 [x1 [x2 j]]]. discriminate.
  - inversion_Clear H2. apply wfaApp; try intuition. 
    + destruct H2 as [x0 [x1 [x2 j]]]. discriminate.
  - apply H0. inversion_Clear H1.
    refine (whCaseStep_pres_WFapp _ _ _ e); auto.
  - apply H0. inversion_Clear H1.
    refine (whCaseStep_pres_WFapp _ _ _ e0); auto.
    assert (j:= H H5). inversion_Clear j.
    refine (tskipn_pres_WFapp _ _ e). intuition.
  - inversion_Clear H1. intuition. 
Qed.


Lemma WcbvEval_weaken:
  forall p,
  (forall t s, WcbvEval p t s -> forall nm ec, fresh nm p ->
                   WcbvEval ((nm,ec)::p) t s) /\
  (forall ts ss, WcbvEvals p ts ss -> forall nm ec, fresh nm p ->
                    WcbvEvals ((nm,ec)::p) ts ss).
intros p. apply WcbvEvalEvals_ind; intros; auto.
- eapply wConst. 
  + apply Lookup_weaken; eassumption.
  + apply H. assumption.
- eapply wAppLam.
  + apply H. assumption.
  + apply H0. assumption.
  + apply H1. assumption.
- eapply wLetIn.
  + apply H. assumption.
  + apply H0. assumption.
- eapply wAppFix.
  + apply H. assumption.
  + apply e.
  + apply H0. assumption.
- eapply wCase0.
  + apply H. assumption.
  + apply e.
  + apply H0. assumption.
- eapply wCasen.
  + apply H. assumption.
  + apply e.
  + apply e0.
  + apply H0. assumption.
Qed.

(****  Could probably finish this, bus see WcbvEval_wndEvalRTC below ***
(** WcbvEval is in the transitive closure of wndEval **)
Lemma WcbvEval_wndEvalTC:
  forall (p:environ), WFaEnv p ->
    (forall t s, WcbvEval p t s -> t <> s ->
        WFapp t -> wndEvalTC p t s) /\
    (forall ts ss, WcbvEvals p ts ss -> ts <> ss ->
        WFapps ts -> wndEvalsTC p ts ss).
Proof.
  intros p hp. apply WcbvEvalEvals_ind; intros; try (nreflexivity H).
  - destruct (Term_dec t s).
    + apply wETCstep. subst. apply sCast.
    + inversion_Clear H1. eapply wETCtrn.
      * apply wETCstep. apply sCast.
      * eapply H; eassumption.
  - destruct (Term_dec t s).
    + apply wETCstep. subst. apply (sConst l). 
    + eapply wETCtrn.
      * apply wETCstep. constructor. eassumption.
      * eapply H. eassumption.
        assert (j:= Lookup_pres_WFapp hp l). inversion j. assumption.
  - destruct (Term_dec fn (TLambda nm ty bod)), (Term_dec a1 a1'),
    (Term_dec (whBetaStep bod a1' args) s). subst.
    + apply wETCstep. constructor.
    + eapply wETCtrn.
      * apply wETCstep. constructor.
      * eapply H1. eassumption.
        inversion_Clear H3. inversion_Clear H9.
        apply whBetaStep_pres_WFapp; assumption.
    + eapply wETCtrn.
      * inversion_Clear H3. 
        apply wndEvalTC_App_arg. apply H0; assumption. 
      * apply wETCstep. apply sBeta.
    + eapply wETCtrn. 
      * apply wndEvalTC_App_arg.
        inversion_Clear H3. inversion_Clear H10.
        eapply H0; eassumption.
      * eapply wETCtrn. constructor. constructor. eapply H1. assumption.
        inversion_Clear H3. inversion_Clear H10.
        apply whBetaStep_pres_WFapp; try eassumption.
        eapply (proj1 (wcbvEval_pres_WFapp hp)); eassumption.
    + eapply wETCtrn. apply wndEval_App_fn.



 (** HERE **) apply wndEvalTC_App_fn. apply H; assumption.
    constructor. constructor.
  + eapply wETCtrn. apply wndEvalTC_App_fn. apply H; assumption.
    eapply wETCtrn. constructor. constructor. apply H1; assumption.
  + eapply wETCtrn. apply wndEvalTC_App_fn. apply H; assumption.
    eapply wETCtrn. apply wndEvalTC_App_arg. apply H0. assumption.
    constructor. constructor.
  + eapply wETCtrn. apply wndEvalTC_App_fn. apply H; assumption.
    eapply wETCtrn. apply wndEvalTC_App_arg. apply H0. assumption.
    eapply wETCtrn. constructor. constructor.
    apply H1. assumption.
- destruct (Term_dec dfn dfn');
  destruct (Term_dec (instantiate dfn' 0 bod) s); subst.
  + apply wETCstep. constructor.
  + eapply wETCtrn. apply wETCstep. constructor. apply H0. assumption.
  + eapply wETCtrn. apply wndEvalTC_LetIn_dfn. apply H. assumption.
    constructor. constructor.
  + eapply wETCtrn. apply wndEvalTC_LetIn_dfn. apply H. assumption.
    eapply wETCtrn. constructor. constructor.
    apply H0. assumption.
- destruct (Term_dec fn (TFix dts m)); destruct (Term_dec fs s); subst.
  + apply wETCstep. constructor. assumption.
  + eapply wETCtrn. apply wETCstep. constructor. eassumption.
    apply H0. assumption.
  + eapply wETCtrn. apply wndEvalTC_App_fn. apply H. assumption.
    constructor. constructor. assumption.
  + eapply wETCtrn. apply wndEvalTC_App_fn. apply H. assumption.
    eapply wETCtrn. constructor. constructor. eassumption.
    apply H0. assumption.
- destruct (Term_dec fn (TConstruct i r)); destruct (Term_dec arg arg');
  destruct (Terms_dec args args'); subst.
  + elim H2. reflexivity.
  + apply wndEvalsTC_App_args. apply H1. assumption.
  + apply wndEvalTC_App_arg. apply H0. assumption.
  + eapply wETCtrn. apply wndEvalTC_App_arg. apply H0. assumption.
    apply wndEvalsTC_App_args. apply H1. assumption.
  + apply wndEvalTC_App_fn. apply H. assumption.
  + eapply wETCtrn. apply wndEvalTC_App_fn. apply H. assumption.
    apply wndEvalsTC_App_args. apply H1. assumption.
  + eapply wETCtrn. apply wndEvalTC_App_fn. apply H. assumption.
    apply wndEvalTC_App_arg. apply H0. assumption.
  + eapply wETCtrn. apply wndEvalTC_App_fn. apply H. assumption.
    eapply wETCtrn. apply wndEvalTC_App_arg. apply H0. assumption.
    apply wndEvalsTC_App_args. apply H1. assumption.



-

- apply H. assumption.
 eapply wERTCtrn. apply wERTCstep. apply sConst. eassumption.
  assumption.
- eapply (@wERTCtrn _ _ (TApp (TLambda nm ty bod) a1 args)).
  + apply wndEvalRTC_App_fn. assumption.
  + eapply (@wERTCtrn _ _ (TApp (TLambda nm ty bod) a1' args)).
    * apply wndEvalRTC_App_arg. assumption.
    * apply (@wERTCtrn _ _ (whBetaStep bod a1' args)).
      apply wERTCstep. apply sBeta. assumption.
- eapply (@wERTCtrn _ _ (TLetIn nm dfn' ty bod)).
  + apply wndEvalRTC_LetIn_dfn. assumption.
  + eapply wERTCtrn. apply wERTCstep. apply sLetIn. assumption.
- eapply (@wERTCtrn _ _ (TApp (TFix dts m) arg args)).
  + apply wndEvalRTC_App_fn. assumption.
  + eapply (@wERTCtrn _ _ fs).
    * apply wERTCstep. apply sFix. assumption.
    * assumption.
- eapply (@wERTCtrn _ _ (TApp (TConstruct i r) arg args)).
  + apply wndEvalRTC_App_fn. assumption.
  + eapply (@wERTCtrn _ _ (TApp (TConstruct i r) arg' args)).
    * apply wndEvalRTC_App_arg. assumption.
    * eapply (@wERTCtrn _ _ (TApp (TConstruct i r) arg' args')).
      apply wndEvalsRTC_App_args. assumption.
      constructor.
- eapply (@wERTCtrn _ _ (TCase 0 ty (TConstruct i n) brs)).
  + apply wndEvalRTC_Case_mch. assumption.
  + eapply (@wERTCtrn _ _ cs).
    * apply wERTCstep. apply sCase0. assumption.
    * assumption.
- eapply (@wERTCtrn _ _ (TCase np ty (TApp (TConstruct i n) arg args) brs)).
  + apply wndEvalRTC_Case_mch. assumption.
  + eapply (@wERTCtrn _ _ cs).
    * apply wERTCstep. eapply sCasen; eassumption.
    * assumption.
- eapply (@wEsRTCtrn _ _ (tcons t' ts)).
  + apply wndEvalsRTC_tcons_hd. assumption.
  +  eapply (@wEsRTCtrn _ _ (tcons t' ts')).
     * apply wndEvalsRTC_tcons_tl. assumption.
     * constructor.
Qed.
*******)

Lemma WcbvEval_wndEvalRTC:
  forall (p:environ), WFaEnv p ->
    (forall t s, WcbvEval p t s -> WFapp t -> wndEvalRTC p t s) /\
    (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> wndEvalsRTC p ts ss).
intros p hp. apply WcbvEvalEvals_ind; intros; try (solve [constructor]).
- inversion_Clear H0. 
  eapply wERTCtrn. 
  + apply wndEvalRTC_Lam_typ. eapply H. assumption.
  + constructor. 
- inversion_Clear H0. 
  eapply wERTCtrn. 
  + apply wndEvalRTC_Prod_typ. eapply H. assumption.
  + constructor. 
- eapply wERTCtrn. apply wERTCstep. apply sCast. apply H. 
  inversion_Clear H0. assumption.
- eapply wERTCtrn. 
  + apply wERTCstep. apply sConst. eassumption.
  + apply H. assert (j:= Lookup_pres_WFapp hp l). inversion j. assumption.
- eapply (@wERTCtrn _ _ (TApp (TLambda nm ty bod) a1 args));
  inversion_Clear H2. 
  + rewrite <- mkApp_goodFn; try assumption.
    rewrite <- mkApp_goodFn; try not_isApp.
    apply wndEvalRTC_App_fn. apply H. assumption. assumption.
  + eapply (@wERTCtrn _ _ (TApp (TLambda nm ty bod) a1' args)).
    * apply wndEvalRTC_App_arg. apply H0. assumption. not_isApp.
    * { apply (@wERTCtrn _ _ (whBetaStep bod a1' args)).
        - apply wERTCstep. apply sBeta. 
        - apply H1. apply whBetaStep_pres_WFapp; try eassumption.
          + assert (j:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H7).
            inversion_Clear j. assumption.
          + eapply wndEvalRTC_pres_WFapp; try eassumption.
            * apply H0. assumption. }
- inversion_Clear H1. eapply (@wERTCtrn _ _ (TLetIn nm dfn' ty bod)).
  + apply wndEvalRTC_LetIn_dfn. intuition.
  + eapply wERTCtrn. apply wERTCstep. apply sLetIn. apply H0.
    apply instantiate_pres_WFapp; try assumption.
    * eapply (proj1 (wcbvEval_pres_WFapp hp)); try eassumption.
- inversion_Clear H1.
  refine (@wERTCtrn _ _ (TApp (TFix dts m) arg args) _ _ _).
  + rewrite <- mkApp_goodFn; try assumption.
    rewrite <- mkApp_goodFn; try not_isApp.
    apply wndEvalRTC_App_fn. apply H. assumption. assumption.
  + refine (@wERTCtrn _ _ fs _ _ _).
    * apply wERTCstep. apply sFix. assumption.
    * { apply H0. refine (whFixStep_pres_WFapp _ _ _ e); try eassumption.
        - assert (j:= wndEvalRTC_pres_WFapp (H H6) hp H6).
          inversion_Clear j. assumption.
        - constructor; assumption. }
- inversion_Clear H2.
  eapply (@wERTCtrn _ _ (TApp (TConstruct i n) arg args)).
  + rewrite <- mkApp_goodFn; try assumption.
    rewrite <- mkApp_goodFn; try not_isApp.
    apply wndEvalRTC_App_fn. apply H. assumption. assumption.
  + eapply (@wERTCtrn _ _ (TApp (TConstruct i n) arg1 args)).
    * { apply wndEvalRTC_App_arg; try not_isApp.
        - apply H0. assumption. }
    * { eapply (@wERTCtrn _ _ (TApp (TConstruct i n) arg1 args1)).
        - apply wndEvalsRTC_App_args; try not_isApp.
          + apply H1. assumption. 
        - apply wERTCrfl. }
- inversion_Clear H2.
  eapply (@wERTCtrn _ _ (TApp (TInd i) arg args)).
  + rewrite <- mkApp_goodFn; try assumption.
    rewrite <- mkApp_goodFn; try not_isApp.
    apply wndEvalRTC_App_fn. apply H. assumption. assumption.
  + eapply (@wERTCtrn _ _ (TApp (TInd i) arg1 args)).
    * { apply wndEvalRTC_App_arg; try not_isApp.
        - apply H0. assumption. }
    * { eapply (@wERTCtrn _ _ (TApp (TInd i) arg1 args1)).
        - apply wndEvalsRTC_App_args; try not_isApp.
          + apply H1. assumption. 
        - apply wERTCrfl. }
- inversion_Clear H1. eapply wERTCtrn. 
  + eapply wndEvalRTC_Case_mch. apply H. assumption.
  + eapply (@wERTCtrn _ _ cs). 
    * apply wERTCstep. apply sCase0. assumption.
    * { apply H0. eapply whCaseStep_pres_WFapp.
        - eapply H7.
        - eapply wfanil.
        - eassumption. }
- inversion_Clear H1. eapply wERTCtrn. 
  + eapply wndEvalRTC_Case_mch. apply H. assumption.
  + eapply (@wERTCtrn _ _ cs). 
    * apply wERTCstep. eapply sCasen; eassumption.
    * { apply H0. eapply whCaseStep_pres_WFapp.
        - eapply H7.
        - assert (j: WFapps (tcons arg args)).
          { assert (k:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H5).
            inversion_clear k. constructor; assumption. }
          eapply tskipn_pres_WFapp. apply j. eassumption. 
        - eassumption. }
- inversion_Clear H1. eapply (@wEsRTCtrn _ _ (tcons t' ts)).
  + apply wndEvalsRTC_tcons_hd. apply H. assumption.
  + eapply (@wEsRTCtrn _ _ (tcons t' ts')).
     * apply wndEvalsRTC_tcons_tl. apply H0. assumption.
     * apply wEsRTCrfl.
Qed.


(************  in progress  ****
Lemma WcbvEval_strengthen:
  forall pp,
  (forall t s, WcbvEval pp t s -> forall nm u p, pp = (nm,ecConstr u)::p ->
        ~ PoccTrm nm t -> WcbvEval p t s) /\
  (forall ts ss, WcbvEvals pp ts ss -> forall nm u p, pp = (nm,ecConstr u)::p ->
        ~ PoccTrms nm ts -> WcbvEvals p ts ss).
intros pp. apply WcbvEvalEvals_ind; intros; auto.
- eapply (@wConst p nm t s pp). eapply (@Lookup_strengthen _ pp); try eassumption.
  + apply (neq_sym (inverse_Pocc_TConstL H1)).
  + eapply H. eassumption.
    admit.
- Check (deMorgan_impl (@PoAppL _ _ _ _) H3).
  assert (hfn:= deMorgan_impl (@PoAppL _ _ _ _) H3).
  assert (harg:= deMorgan_impl (@PoAppA _ _ _ _) H3).
  assert (hargs:= deMorgan_impl (@PoAppR _ _ _ _) H3).
  eapply wAppLam. 
  + eapply H; eassumption.
  + eapply H0; eassumption.
  + eapply H1. eassumption. intros j.



rewrite H0 in l. assert (j:= proj2 (lookupDfn_LookupDfn _ _ _) l).
  simpl in j.
  rewrite (string_eq_bool_neq (neq_sym (inverse_Pocc_TConstL H1))) in j. 
Check (@wConst p _ t).
  eapply (@wConst p _ t).
assert (h:= inverse_Pocc_TConstL H1).

rewrite H0 in l. simpl in l. eapply (wConst pp). 

rewrite H0 in H. simpl in H.
  rewrite (string_eq_bool_neq (neq_sym (inverse_Pocc_TConstL H0))) in e. 
  trivial.
- apply (H nm u); trivial. apply (notPocc_TApp H1).
- apply (H nm u); trivial. apply (notPocc_TApp H1).
- apply (H nm u); trivial. apply (notPocc_TApp H1).
- apply (H nm0 u); trivial; apply (notPocc_TProd H1).
- apply (H nm0 u); trivial; apply (notPocc_TLambda H1).
- apply (H nm0 u); trivial; apply (notPocc_TLetIn H1).
- apply (H nm0 u); trivial; apply (notPocc_TLetIn H1).
- apply (H nm u); trivial; apply (notPocc_TCast H1).
- apply (H nm u); trivial; apply (notPocc_TCast H1).
- apply (H nm u); trivial; apply (notPocc_TCase H1).
- apply (H nm u); trivial; apply (notPocc_TCase H1).
- apply (H nm u); trivial; apply (notPocc_TCase H1).
- apply (H nm u). trivial. apply (notPoccTrms H1).
- apply (H nm u). trivial. apply (notPoccTrms H1).
Qed.
***************)

(** now an executable weak-call-by-value evaluation **)
(** use a timer to make this terminate **)
(****  Working HERE  ****
Definition wcbvEv:
  forall (p:environ) (tmr:nat),
    (forall (t:Term), exception Term) *
    (forall (ts:Terms), exception Terms) *
    (forall (ds:Defs), True).
Proof.
  intros p t. induction t; intros.
  Case "tmr = 0". split; split; intros; apply (Exc "out of time").
  Case "tmr = S n". apply TrmTrmsDefs_Typeind; intros.
  - SCase "TRel". apply (Exc "TRel; free index").
  - SCase "TSort". apply (Ret (TSort s)).
  - SCase "TCast". apply (fst (fst IHt) t0).
  - SCase "TProd". apply (Ret (TProd n t0 t1)).
  - SCase "TLambda". apply (Ret (TLambda n t0 t1)).
  - SCase "TLetIn". destruct H.
    + apply (Exc s).
    + destruct (fst (fst IHt) (instantiate t0 0 t2)).
      * apply (Exc s).
      * apply (Ret t4).
  - SCase "TApp". destruct H.
    + SSCase "fn doesn't eval". apply (Exc s).
    + SSCase "fn evals to ..". destruct t3.
      * SSSCase "TRel". apply (Exc "never result of eval").
      * SSSCase "TSort". apply (Exc "doesn't have functional type").
      * SSSCase "TCast". apply (Exc "never result of eval").
      * SSSCase "TProd". apply (Exc "doesn't have functional type").
      * SSSCase "TLambda". destruct H0.
        SSSSCase "arg doesn't eval". apply (Exc s).
        SSSSCase "arg evals". apply (fst (fst IHt) (whBetaStep t3_2 t3 t2)).
      * SSSCase "TLetIn". apply (Exc "never result of eval").
      * SSSCase "TApp: must mkApp". 
        apply (fst (fst IHt) (mkApp t3_1 (tcons t3_2 t3))).
      * SSSCase "TConst". apply (Exc "never result of eval").
      * SSSCase "TInd".
  -
apply (Exc "").
      * SSSCase "TLetIn". apply (Exc "").
      * SSSCase "TApp". apply (Exc "").
      * SSSCase "TConst". apply (Exc "").
      * SSSCase "TInd". apply (Exc "").
      * SSSCase "TConstruct". apply (Exc "").
      * SSSCase "TCase". apply (Exc "").
      * SSSCase "TFix". apply (Exc "").
  - SCase "TConst". destruct (lookupDfn s p).
    + SSCase "lookup succeeds". apply (IHtmr p
    + SSCase "lookup fails". apply (Exc "").
**************************)

Function wcbvEval
         (tmr:nat) (p:environ) (t:Term) {struct tmr}: exception Term :=
  (match tmr with 
     | 0 => raise "out of time"
     | S n =>
       (match t with      (** look for a redex **)
          | TConst nm => match (lookupDfn nm p) with
                           | Some t => wcbvEval n p t
                           | None => raise "environment miss"
                         end
          | TCast t _ _ =>  wcbvEval n p t
          | TApp fn a1 args =>
            (match wcbvEval n p fn with
               | Exc str => Exc str
               | Ret efn =>
                 (match efn with
                    | TLambda _ _ bod =>
                      match wcbvEval n p a1 with
                        | Exc str => Exc str
                        | Ret wharg => wcbvEval n p (whBetaStep bod wharg args)
                      end
                    | TFix dts m =>
                      match whFixStep dts m (tcons a1 args) with
                        | None => raise "fixpoint step fail"
                        | Some fs => wcbvEval n p fs
                      end
                    | TConstruct i m =>
                      match wcbvEval n p a1, wcbvEvals n p args with
                        | Ret ea1, Ret eargs =>
                              Ret (TApp (TConstruct i m) ea1 eargs)
                        | _, _ => raise "arg of constructor fails to compute"
                      end
                    | TInd i => 
                     match wcbvEval n p a1, wcbvEvals n p args with
                        | Ret ea1, Ret eargs => Ret (TApp (TInd i) ea1 eargs)
                        | _, _ => raise "arg of Ind fails to compute"
                      end
                     | _ => raise "wcbvEval: application"
                  end)
             end)
          | TCase np _ mch brs =>
            (match wcbvEval n p mch with
               | Exc str => Exc str
               | Ret emch =>
                 (match emch, np with 
                    | TConstruct _ r, 0 => 
                      match whCaseStep r tnil brs with
                        | None => raise "case step fails"
                        | Some cs => wcbvEval n p cs
                      end
                    | TApp (TConstruct _ r) arg args, _ =>
                      match tskipn np (tcons arg args) with
                        | None => raise "not enough args for constructor"
                        | Some ts => match whCaseStep r ts brs with
                                       | None => raise "case step fails"
                                       | Some cs => wcbvEval n p cs
                                     end
                      end
                    | _, _ => raise "case match arg not canonical"
                  end)
             end)
          | TLetIn nm df ty bod =>
            match wcbvEval n p df with
              | Exc str => Exc str
              | Ret df' => wcbvEval n p (instantiate df' 0 bod)
            end
          | TLambda nn ty t => 
            match wcbvEval n p ty with
              | Exc str => Exc str
              | Ret ty' => ret (TLambda nn ty' t)
            end
          | TProd nn ty t =>
            match wcbvEval n p ty with
              | Exc str => Exc str
              | Ret ty' => ret (TProd nn ty' t)
            end
          | TFix mfp br => ret (TFix mfp br)
          (** already in whnf ***)
          | TConstruct i cn => ret (TConstruct i cn)
          | TInd i => ret (TInd i)
          | TSort srt => ret (TSort srt)
          (** should never appear **)
          | TRel _ => raise "wcbvEval: unbound Rel"
        end)
   end)
with wcbvEvals (tmr:nat) (p:environ) (ts:Terms) {struct tmr}
     : exception Terms :=
       (match tmr with 
          | 0 => raise "out of time"
          | S n => match ts with             (** look for a redex **)
                     | tnil => ret tnil
                     | tcons s ss =>
                       match wcbvEval n p s, wcbvEvals n p ss with
                         | Ret es, Ret ess => ret (tcons es ess)
                         | _, _ => raise "wcbvEvals fails"
                       end
                   end
        end).
(**
Functional Scheme wcbvEval_ind := Induction for wcbvEval Sort Prop
with wcbvEvals_ind := Induction for wcbvEvals Sort Prop.
Combined Scheme wcbvEvalEvals_ind from wcbvEval_ind, wcbvEvals_ind.
**)

(** wcbvEval and WcbvEval are the same relation **)
Lemma wcbvEval_WcbvEval:
  forall p,
  (forall t n s, wcbvEval n p t = Ret s -> WcbvEval p t s) /\
  (forall ts n ss, wcbvEvals n p ts = Ret ss -> WcbvEvals p ts ss) /\
  (forall (ds:Defs) (n:nat), True).
Admitted.
(***
intros p.
- eapply(TrmTrmsDefs_ind
      (fun t => forall n s, wcbvEval n p t = Ret s -> WcbvEval p t s)
      (fun ts => forall n ss, wcbvEvals n p ts = Ret ss ->
                              WcbvEvals p ts ss)
      (fun (ds:Defs) => forall (n:nat), True)); intros; intuition;
  try (solve [induction n; simpl in *; discriminate]).
  + induction n0; simpl in *; try discriminate.
  + induction n; simpl in *; try discriminate.
    * myInjection H. constructor.
  + induction n; simpl in *; try discriminate.
    * constructor. eapply H.  eassumption. 
  + induction n0; simpl in *; try discriminate.
    * { case_eq (wcbvEval n0 p t); intros; rewrite H2 in H1. 
        - discriminate.
        - myInjection H1. constructor. eapply H. eassumption. }
  + induction n0; simpl in *; try discriminate.
    * { case_eq (wcbvEval n0 p t); intros; rewrite H2 in H1. 
        - discriminate.
        - myInjection H1. constructor. eapply H. eassumption. }
  + induction n0; simpl in *; try discriminate.
    * { case_eq (wcbvEval n0 p t); intros; rewrite H3 in H2.
        - discriminate.
        - eapply wLetIn. 
          + eapply H. eassumption. 
          + eassumption.
          apply IHn0. rewrite <- H2. 

assert (j2:= H _ _ Happly IHn. rewrite <- H1.
  +
***)

(***
Lemma wcbvEval_mono:
  forall p n t s, wcbvEval n p t = Ret s -> wcbvEval (S n) p t = Ret s.
Proof.
  induction t; intros.
  - simpl in H


Lemma wcbvEval_WcbvEval:
  forall p n,
  (forall t s, wcbvEval n p t = Ret s -> WcbvEval p t s) /\
  (forall ts ss, wcbvEvals n p ts = Ret ss -> WcbvEvals p ts ss) /\
  (forall (ds:Defs), True).
intros p. induction n.
- split; try split; simpl; intros; auto; try discriminate.
- eapply(TrmTrmsDefs_ind
      (fun t => forall s, wcbvEval (S n) p t = Ret s -> WcbvEval p t s)
      (fun ts => forall ss, wcbvEvals (S n) p ts = Ret ss -> WcbvEvals p ts ss)
      (fun (ds:Defs) => True));
  intuition; simpl; intros; try discriminate;
  try (solve [myInjection H0; constructor]).
  + simpl in H4. case_eq (wcbvEval n p t); intros tt h; rewrite h in H4.
    * discriminate.
    * myInjection H4. constructor. apply H. assumption.
  + simpl in H4. case_eq (wcbvEval n p t); intros tt h; rewrite h in H4.
    * discriminate.
    * myInjection H4. constructor. apply H. assumption.
  + simpl in H5. case_eq (wcbvEval n p t); intros tt h; rewrite h in H5.
    * discriminate.
    * { case_eq (wcbvEval n p (instantiate tt 0 t1)); intros; rewrite H6 in H5. 
        - discriminate.
        - myInjection H5. eapply wLetIn. 
          + apply H. eassumption.
          + apply H. assumption. }
  + simpl in H5. case_eq (wcbvEval n p t); intros tt h; rewrite h in H5.
    * discriminate.
    * { case_eq tt; intros; subst; try discriminate.
        - case_eq (wcbvEval n p t0); intros ttt hh; rewrite hh in H5.
          + discriminate.
          + eapply wAppLam. apply H0.

rewrite <- H5. unfold wcbvEval.

  + eapply wAppLam. constructor. apply H. 


unfold whBetaStep. instantiate. 

(** wcbvEval and WcbvEval are the same relation **)
Lemma wcbvEval_WcbvEval:
  forall n p,
  (forall t s, wcbvEval n p t = Ret s -> WcbvEval p t s) /\
  (forall ts ss, wcbvEvals n p ts = Ret ss -> WcbvEvals p ts ss).
intros n p.
apply (wcbvEvalEvals_ind 
  (fun n p t o => forall s, o = Ret s -> WcbvEval p t s)
  (fun n p ts os => forall ss, os = Ret ss -> WcbvEvals p ts ss));
  intros; try discriminate;
  try (solve [injection H; intros h; subst; constructor]).
- apply wCast. intuition.
- injection H0. intros. subst. eapply wProd. apply H. assumption.
- injection H0. intros. subst. eapply wLam. apply H. assumption.
- eapply wLetIn.
  + apply H. eassumption.
  + apply H0. assumption.
- subst. eapply wAppLam.
  + eapply H. eassumption.
  + eapply H0. eassumption.
  + eapply H1. eassumption.
- subst. injection H2. intros. rewrite <- H3. eapply wAppInd.
  + eapply H. eassumption.
  + eapply H0. eassumption.
  + eapply H1. eassumption.
- subst. injection H2. intros. rewrite <- H3. eapply wAppCnstr.
  + eapply H. eassumption.
  + eapply H0. eassumption.
  + eapply H1. eassumption.
- subst. eapply wAppFix.
  + apply H. eassumption.
  + eassumption.
  + apply H0. eassumption.
- subst. eapply wConst. apply lookupDfn_LookupDfn. eassumption.
  + apply H. eassumption.
- subst. eapply wCasen; try eassumption.
  + apply H. eassumption.
  + apply H0. eassumption.
- subst. eapply wCase0; try assumption.
  + apply H. eassumption.
  + eassumption.
  + apply H0. eassumption.
- subst. injection H1. intros. rewrite <- H2. constructor.
  + apply H. assumption.
  + apply H0. assumption.
Qed.
***)


(* need this strengthening to large-enough fuel to make the induction
** go through
*)
Lemma pre_WcbvEval_wcbvEval:
  forall p,
    (forall t s, WcbvEval p t s ->
             exists n, forall m, m >= n -> wcbvEval (S m) p t = Ret s) /\
    (forall ts ss, WcbvEvals p ts ss ->
             exists n, forall m, m >= n -> wcbvEvals (S m) p ts = Ret ss).
intros p.
assert (j:forall m x, m > x -> m = S (m - 1)). { induction m; intuition. }
apply WcbvEvalEvals_ind; intros; try (exists 0; intros mx h; reflexivity).
- destruct H. exists (S x). intros m hm. simpl. rewrite (j m x); try omega.
  + rewrite (H (m - 1)); try omega. reflexivity. 
- destruct H. exists (S x). intros m hm. simpl. rewrite (j m x); try omega.
  + rewrite (H (m - 1)); try omega. reflexivity. 
- destruct H. exists (S x). intros m h. simpl.
  rewrite (j m x); try omega. apply H. omega.
- destruct H. exists (S x).
  assert (k:= LookupDfn_lookupDfn). intros m h. simpl.
  erewrite k. rewrite (j m x). apply H. omega. omega.
  eassumption. reflexivity.
- destruct H, H0, H1. exists (S (max x (max x0 x1))). intros m h.
  assert (k:wcbvEval m p fn = Ret (TLambda nm ty bod)).
  + rewrite (j m (max x (max x0 x1))). apply H.
    assert (l:= max_fst x (max x0 x1)); omega. omega.
  + assert (k0:wcbvEval m p a1 = Ret a1').
    rewrite (j m (max x (max x0 x1))). apply H0. 
    assert (l:= max_snd x (max x0 x1)). assert (l':= max_fst x0 x1).
    omega. omega.
    * simpl. rewrite k. rewrite k0.
      rewrite (j m (max x (max x0 x1))). apply H1.
      assert (l:= max_snd x (max x0 x1)). assert (l':= max_snd x0 x1).
      omega. omega.
- destruct H, H0. exists (S (max x x0)). intros m h. simpl.
  assert (k:wcbvEval m p dfn = Ret dfn'). 
  assert (l:= max_fst x x0).
  rewrite (j m (max x x0)). apply H. omega. omega.
  rewrite k.
  assert (l:= max_snd x x0).
  rewrite (j m x0). apply H0. omega. omega.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try rewrite (H (mx - 1)); try omega.
  rewrite e. apply H0. omega.
- destruct H, H0, H1. exists (S (max x (max x0 x1))). intros mx h.
  assert (j1:= max_fst x (max x0 x1)). 
  assert (lx: mx > x). omega.
  assert (j2:= max_snd x (max x0 x1)).
  assert (j3:= max_fst x0 x1).
  assert (lx0: mx > x0). omega.
  assert (j4:= max_snd x0 x1).
  assert (j5:= max_fst x0 x1).
  assert (lx1: mx > x1). omega.
  simpl. rewrite (j mx x); try omega.
  rewrite (H (mx - 1)); try omega.
  rewrite (H0 (mx - 1)); try omega.
  rewrite (H1 (mx - 1)); try omega. reflexivity.
- destruct H, H0, H1. exists (S (max x (max x0 x1))). intros mx h.
  assert (j1:= max_fst x (max x0 x1)). 
  assert (lx: mx > x). omega.
  assert (j2:= max_snd x (max x0 x1)).
  assert (j3:= max_fst x0 x1).
  assert (lx0: mx > x0). omega.
  assert (j4:= max_snd x0 x1).
  assert (j5:= max_fst x0 x1).
  assert (lx1: mx > x1). omega.
  simpl. rewrite (j mx x); try omega.
  rewrite (H (mx - 1)); try omega.
  rewrite (H0 (mx - 1)); try omega.
  rewrite (H1 (mx - 1)); try omega. reflexivity.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try rewrite (H (mx - 1)); try omega.
  rewrite e. apply H0. omega.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try rewrite (H (mx - 1)); try omega.
  rewrite e. rewrite e0. apply H0. omega.
- destruct H, H0. exists (S (max x x0)). intros m h.
  assert (k:wcbvEval m p t = Ret t').
  assert (l:= max_fst x x0).
  rewrite (j m (max x x0)). apply H. omega. omega.
  assert (k0:wcbvEvals m p ts = Ret ts').
  assert (l:= max_snd x x0).
  rewrite (j m (max x x0)). apply H0. omega. omega.
  simpl. rewrite k. rewrite k0. reflexivity.
Qed.

Lemma WcbvEval_wcbvEval:
  forall p t s, WcbvEval p t s ->
             exists n, forall m, m >= n -> wcbvEval m p t = Ret s.
Proof.
  intros p t s h.
  destruct (proj1 (pre_WcbvEval_wcbvEval p) _ _ h).
  exists (S x). intros m hm. assert (j:= H (m - 1)). 
  assert (k: m = S (m - 1)). { omega. }
  rewrite k. apply j. omega.
Qed.


Lemma WcbvEval_single_valued:
  forall p t s, WcbvEval p t s -> forall u, WcbvEval p t u -> s = u.
Proof.
  intros p t s h0 u h1.
  assert (j0:= WcbvEval_wcbvEval h0).
  assert (j1:= WcbvEval_wcbvEval h1).
  destruct j0 as [x0 k0].
  destruct j1 as [x1 k1].
  assert (l0:= k0 (max x0 x1) (max_fst x0 x1)).
  assert (l1:= k1 (max x0 x1) (max_snd x0 x1)).
  rewrite l0 in l1. injection l1. intuition.
Qed.


(**** scratch below here ****
(** wcbvEval is monotonic in fuel **)
Goal
  forall t n p,  wcbvEval n p t = Some s ->
                   wcbvEval n p t = wcbvEval (S n) p t.
induction t; intros. 
- destruct n0; simpl in H; intuition.
- destruct n; simpl in H. intuition. reflexivity.
- destruct n. simpl in H. intuition.  simpl in H. simpl.
  change (TCast (wcbvEval n p t1) c t2 = TCast (wcbvEval (S n) p t1) c t2).
  rewrite IHt1. reflexivity. intros h. rewrite <- h in H.

unfold wcbvEval in H. simpl.


         (forall (t s:Term), wcbvEval p t s ->
             exists n, s = wcbvEval n p t) /\
         (forall ts ss, WcbvEvals p ts ss ->
             exists n, ss = tmap (wcbvEval n p) ts).
Goal
  forall (p:environ),
         (forall (t s:Term), wcbvEval p t s ->
             exists n, s = wcbvEval n p t) /\
         (forall ts ss, WcbvEvals p ts ss ->
             exists n, ss = tmap (wcbvEval n p) ts).

(** WcbvEval and wcbvEval are the same relation **)
Goal
  forall (p:environ),
         (forall (t s:Term), WcbvEval p t s ->
             exists n, s = wcbvEval n p t) /\
         (forall ts ss, WcbvEvals p ts ss ->
             exists n, ss = tmap (wcbvEval n p) ts).
intros p.
apply WcbvEvalEvals_ind; intros; try (exists 1; reflexivity).
- destruct H. exists (S x). subst.
  assert (j:= proj2 (lookupDfn_LookupDfn _ _ _) l).
  simpl. rewrite j. reflexivity.
- destruct H. destruct H0. destruct H1.
  exists (S (x + x0 + x1)). subst. unfold whBetaStep. simpl.



Qed.


(** If wcbvEval has fuel left, then it has reached a weak normal form **)
(**
Goal
  forall (p:environ) t s n m, (wcbvEval n p t) = (S m, s) -> WNorm s.
***)


(***** scratch below here ****************


Goal forall (p:environ) t s, WcbvEval p t s -> crct p t -> wNorm s = true.
induction 1; destruct 1. 
- apply IHWcbvEval. split. assumption. unfold weaklyClosed. intros nmx j.
  unfold weaklyClosed in H2. apply H2. inversion H1. subst.
  + specialize (H2 nm). unfold poccTrm in H2; simpl in H2.
    rewrite string_eq_bool_rfl in H2. intuition.
  + apply sBeta.



HERE

  + destruct (string_dec nmx nm).
    * subst. unfold poccTrm. rewrite string_eq_bool_rfl. reflexivity.
    * inversion H1. subst. inversion_clear H0. inversion H.
  
    simpl in H3.

  + unfold poccTrm. inversion H1. subst. inversion h. unfold weaklyClosed in H3.
    simpl in H3.




Goal forall (p:environ), 
  (forall t s, WcbvEval p t s -> crct p t -> wNorm s = true) /\
  (forall ts ss, WcbvEvals p ts ss ->
        Forall (crct p) ts -> Forall (fun s => wNorm s = true) ss).
intros p.
apply WcbvEvalEvals_ind.
- intros nm t s q h1 h2 h3 h4. apply h3. inversion h2; subst.
  + split.
    * inversion h4. auto.
    * unfold  weaklyClosed. intros nm1 j1.
      simpl in j1. assert (j2:= string_eq_bool_eq _ _ j1). subst.
      assert (j3:= proj2 (lookupDFN_LookupDFN _ _ _) H).
      unfold lookupDfn. rewrite j3. intros j4. discriminate.
  + destruct h4. split. auto. unfold weaklyClosed.
    intros nm1 h4. simpl in h4.

induction 1; inversion 1.
- subst. elim (ncrct_nil_TConst nm _ _ H1); reflexivity.
- subst. apply IHWcbvEval.

HERE




(***
Lemma instantiate_arg_resp_WcbvEval:
  (forall p ia2 s, WcbvEval p ia2 s -> 
    forall a1 a2 bod, ia2 = (instantiate 0 bod a2) -> 
    WcbvEval p a1 a2 -> WcbvEval p (instantiate 0 bod a1) s) /\
  (forall p ia2 s, WcbvEvals p ia2s ss -> 
    forall a1 a2 bod, ia2 = (instantiate 0 bod a2) -> 
    WcbvEval p a1 a2 -> WcbvEval p (instantiate 0 bod a1) s)
induction 1. intros ax a2 bod heq h.
- eapply IHWcbvEval. intuition. assumption.
- eapply IHWcbvEval3. assumption.
- eapply IHWcbvEval2. assumption.
- eapply 
***)

Lemma nat_compare_Gt: forall n, nat_compare (S n) n = Gt.
induction n; intuition.
Qed.
Lemma nat_compare_Lt: forall n, nat_compare n (S n) = Lt.
induction n; intuition.
Qed.
Lemma nat_compare_Eq: forall n, nat_compare n n = Eq.
induction n; intuition.
Qed.


(**
Goal
  forall p ia2 s, WcbvEval p ia2 s -> 
     forall bod a1 a2, ia2 = (instantiate 0 bod a2) -> WcbvEval p a1 a2 ->
                    WcbvEval p (instantiate 0 bod a1) s.
induction 1; intros bodx ax a2 heq h.
- symmetry in heq. case (instantiate_is_Const _ _ _ _ heq); intro j.

Lemma WcbvEval_unique:
  forall (p:environ) (t s1:Term),
    WcbvEval p t s1 -> forall (s2:Term), WcbvEval p t s2 -> s1 = s2.
induction 1.
- inversion_clear 1. eapply IHWcbvEval.
  assert (j: t = t0). rewrite H in H2; injection H2; intuition.
  rewrite j; assumption.
- inversion_clear 1.
  + eapply IHWcbvEval3. unfold whBetaStep. unfold whBetaStep in H5.
    injection (IHWcbvEval1 _ H3); intros; subst.
***)



(**
Ltac Tran_step := eapply Relation_Operators.rt1n_trans.

Ltac const_step :=
  tran_step; [eapply sConst; unfold lookupDfn, lookupDFN; simpl; reflexivity|].
**)
(***
Goal
  forall p fn nm ty bod a1 a1' s args,
    clos_trans_n1 Term (wndEval p) fn (TLambda nm ty bod) ->
    clos_trans_n1 Term (wndEval p) a1 a1' ->
    clos_trans_n1 Term (wndEval p) (whBetaStep nm bod a1' args) s ->
    clos_trans_n1 Term (wndEval p) (TApp fn (a1 :: args)) s.
intros p fn nm ty bod a1 a1' s args hfn ha1 hstep.
inversion hfn; inversion ha1; inversion hstep.
- tran_step. eassumption.
  tran_step. eapply sAppArgs. eapply saHd. eassumption.    
  tran_step. eapply sBeta. eassumption.
- tran_step. eapply sAppFun. eassumption.
  tran_step. eapply sAppArgs. eapply saHd. eassumption.
  tran_step. eapply sBeta. eassumption.
- tran_step. eapply sAppFun. eassumption.
  tran_step. eapply sAppArgs. eapply saHd. eapply tn1_step. eassumption.
  tran_step. eapply sBeta. eassumption.
***)


(**
Goal
  forall p a a',
    clos_refl_trans Term (wndEval p) a a' ->
    forall bod args,
      clos_refl_trans Term (wndEval p) (mkApp (instantiate 0 bod a) args)
                         (mkApp (instantiate 0 bod a') args).
intros p a a' h bod. induction h; intro args.
- apply rt_step.
 Check  Relation_Operators.rt1n_trans.



Goal
  forall p fn nm ty bod a1 a1' s args,
    clos_refl_trans_1n Term (wndEval p) fn (TLambda nm ty bod) ->
    clos_refl_trans_1n Term (wndEval p) a1 a1' ->
    clos_refl_trans_1n Term (wndEval p) (whBetaStep nm bod a1' args) s ->
    clos_refl_trans_1n Term (wndEval p) (TApp fn (a1 :: args)) s.
intros p fn nm ty bod a1 a1' s args hfn ha1 hstep.
inversion hfn; inversion ha1; inversion hstep.
- tran_step. subst. eapply sBeta. subst. auto. 
- tran_step. subst. eapply sBeta. subst. eassumption.
- assert (j: clos_refl_trans_1n Term (wndEval p) a1 a1').
  tran_step; eassumption.
  tran_step. eapply sBeta. rewrite H3. destruct nm.
  + simpl. simpl in H3. rewrite H3. eapply rt1n_refl.
  + simpl. simpl in H3. rewrite <- H3.
-


 tran_step. eapply sAppArgs. eapply saHd. eassumption.
  tran_step.

  eapply (t1n_trans _ (wndEval p)). eapply t1n_step. eapply sAppArgs. eapply saHd.
  eapply clos_t1n_trans. 

eapply (t1n_trans _ (wndEval p)).


 Check (t1n_trans _ _ _ H1).
  tran_step. eapply sAppArgs. eapply saHd. eassumption.
  tran_step. eapply sBeta. eassumption.
- tran_step. eapply sAppFun. eassumption.


Goal
  forall p fn nm ty bod a1 a1' s args,
    clos_trans_1n Term (wndEval p) fn (TLambda nm ty bod) ->
    clos_trans_1n Term (wndEval p) a1 a1' ->
    clos_trans_1n Term (wndEval p) (whBetaStep nm bod a1' args) s ->
    clos_trans_1n Term (wndEval p) (TApp fn (a1 :: args)) s.
intros p fn nm ty bod a1 a1' s args hfn ha1 hstep.
inversion hfn; inversion ha1; inversion hstep.
- tran_step. eapply sAppFun. eassumption.
  tran_step. eapply sAppArgs. eapply saHd. eassumption.    
  tran_step. eapply sBeta. eassumption.
- tran_step. eapply sAppFun. eassumption.
  tran_step. eapply sAppArgs. eapply saHd. eassumption.
  tran_step. eapply sBeta. eassumption.
- tran_step. eapply sAppFun. eassumption.

  tran_step. eapply sAppArgs. eapply saHd. eassumption.
  tran_step. eapply sBeta. eassumption.


Goal
  forall p fn nm ty bod a1 a1' s args,
    clos_trans Term (wndEval p) fn (TLambda nm ty bod) ->
    clos_trans Term (wndEval p) a1 a1' ->
    clos_trans Term (wndEval p) (whBetaStep nm bod a1' args) s ->
    clos_trans Term (wndEval p) (TApp fn (a1 :: args)) s.
intros p fn nm ty bod a1 a1' s args hfn ha1 hstep.
inversion hfn; inversion ha1; inversion hstep.
- tran_step. eapply sAppFun. eassumption.
  tran_step. eapply sAppArgs. eapply saHd. eassumption.    
  tran_step. eapply sBeta.
  eassumption.
unfold whBetaStep in H3.
***)

(**
Ltac Tran_step := eapply Relation_Operators.rt1n_trans.

Goal forall p t t', WcbvEval p t t' -> clos_refl_trans_1n _ (wndEval p) t t'.
induction 1.
- Tran_step. eapply sConst. rewrite H. reflexivity. assumption.
- tran_step. eapply sAppFun.
Check (rt_refl Term (wndEval p)). _ (wndEval p) _ IHWcbvEval1).
**)

(** use a timer to make this Terminate **)
Fixpoint wcbvEval (tmr:nat) (p:environ) (t:Term) {struct tmr} : nat * Term :=
  match tmr with 
    | 0 => (0, t)          (** out of time  **)
    | S n => match t with  (** look for a redex **)
               | TConst nm => match (lookupDfn nm p) with
                                | Some t => wcbvEval n p t
                                | None =>  (0, TUnknown nm)
                              end
               | TApp fn (cons a1 args) =>
                 let efn := snd (wcbvEval n p fn) in
                 match efn with
                   | TLambda _ _ bod =>
                     let wharg := snd (wcbvEval n p a1) in
                     wcbvEval n p (whBetaStep bod wharg args)
                   | TFix dts m => wcbvEval n p (whFixStep dts m args)
                   | TConstruct _ r =>
                     let eargs := map (compose (@snd nat Term) (wcbvEval n p))
                                      (cons a1 args) in
                     (n, mkApp efn eargs)
                   | _ => (n, TUnknown"App")
                 end
               | TCase np _ mch brs =>
                 match evCanon n p mch with
                   | Some (cstr, args) =>
                     wcbvEval n p (whCaseStep cstr (skipn np args) brs)
                   | None => (n, mch)
                 end
               | TLetIn nm df ty bod =>
                 wcbvEval n p (TApp (TLambda nm ty bod) (df::nil))
               | TCast t1 ck t2 => (n, TCast (snd (wcbvEval n p t1)) ck t2)
               (** already in whnf ***)
               | TLambda nn ty t => (n, TLambda nn ty t)
               | TProd nn ty t => (n, TProd nn ty t)
               | TFix mfp br => (n, TFix mfp br)
               | TConstruct i cn => (n, TConstruct i cn)
               | TInd i => (n, TInd i)
               | TSort => (n, TSort)
               (** should never appear **)
               | TApp _ nil => (0, TUnknown "App no args")
               | TRel _ => (0, TUnknown "TRel")
               | TUnknown s => (0, TUnknown s)
             end
  end
(***
with
wcbvEvalArgs tmr p (ts:Terms) {struct ts} : Terms :=
  match ts with
    | nil => nil
    | cons t ts => cons (snd (wcbvEval tmr p t)) (wcbvEvalArgs tmr p ts)
  end
***)
with evCanon tmr p (t:Term) {struct tmr} : option (nat * Terms) :=
  match tmr with
    | 0 => None              (** out of time  **)
    | S n => match (wcbvEval n p t) with
               | (_, TConstruct _ cstr) => Some (cstr, nil)
               | (_, TApp (TConstruct _ cstr) ts) => Some (cstr, ts)
               | x => None
             end
  end.


Definition Nat := nat.
Definition typedef := ((fun (A:Type) (a:A) => a) Nat 1).
Quote Definition q_typedef := Eval compute in typedef.
Quote Recursively Definition p_typedef := typedef.
Definition P_typedef := program_Program p_typedef nil.
Definition Q_typedef := 
  Eval compute in (wcbvEval 100 (env P_typedef) (main P_typedef)).
Goal snd Q_typedef = q_typedef.
reflexivity.
Qed.


Definition II := fun (A:Type) (a:A) => a.
Quote Definition q_II := Eval compute in II.
Quote Recursively Definition p_II := II.
Definition P_II := program_Program p_II nil.
Definition Q_II :=
  Eval compute in (wcbvEval 4 (env P_II)) (main P_II).
Goal snd Q_II = q_II.
reflexivity.
Qed.

(***
Eval cbv in (wcbvEval 4 p_II) (main p_II).
Quote Recursively Definition II_nat_pgm := (II nat).
Print II_nat_pgm.
Eval compute in (wcbvEval 4 II_nat_pgm) (main II_nat_pgm).


Quote Definition II_2_Term := (II nat 2).
Print II_2_Term.
Eval compute in II_2_Term.
Quote Recursively Definition II_2_program := (II nat 2).
Print II_2_program.
Quote Definition two_Term := 2.

Eval cbv in (wcbvEval 4 II_2_program) (main II_2_program).

Quote Recursively Definition p_plus22 := (plus 2 2).
Print p_plus22.
Quote Definition q_ans := 4.
Eval cbv in (wcbvEval 20 p_plus22) (main p_plus22).

Eval compute in (plus 1 2).
Quote Recursively Definition p_plus12 := (plus 1 2).
Eval cbv in (wcbvEval 99 p_plus12) (main p_plus12).

Quote Recursively Definition p_anon := ((fun (_:nat) => 1 + 3) (3 * 3)).
Eval cbv in (wcbvEval 20 p_anon) (main p_anon).

Fixpoint even (n:nat) : bool :=
  match n with
    | 0 => true
    | (S n) => odd n
  end
with
odd (n:nat) : bool :=
  match n with
    | 0 => false
    | (S n) => even n
  end.

Quote Recursively Definition p_even99 := (even 99).
Time Eval cbv in (wcbvEval 500 p_even99) (main p_even99).
Quote Recursively Definition p_odd99 := (odd 99).
Time Eval cbv in (wcbvEval 500 p_odd99) (main p_odd99).


Fixpoint slowFib (n:nat) : nat :=
  match n with
    | 0 => 0
    | S m => match m with
               | 0 => 1
               | S p => slowFib p + slowFib m
             end
  end.
Eval compute in (slowFib 0).
Eval compute in (slowFib 1).
Eval compute in (slowFib 2).
Eval compute in (slowFib 3).
Eval compute in (slowFib 4).
Quote Recursively Definition p_slowFib1 := (slowFib 1).
Quote Recursively Definition p_slowFib2 := (slowFib 2).
Quote Recursively Definition p_slowFib3 := (slowFib 3).
Quote Recursively Definition p_slowFib4 := (slowFib 4).
Quote Recursively Definition p_slowFib5 := (slowFib 5).
Quote Recursively Definition p_slowFib6 := (slowFib 6).
Quote Recursively Definition p_slowFib7 := (slowFib 7).
Quote Recursively Definition p_slowFib10 := (slowFib 10).
Quote Recursively Definition p_slowFib15 := (slowFib 15).
Eval cbv in (wcbvEval 99 p_slowFib3) (main p_slowFib3).
Eval cbv in (wcbvEval 99 p_slowFib4) (main p_slowFib4).
Eval cbv in (wcbvEval 99 p_slowFib5) (main p_slowFib5).
Eval cbv in (wcbvEval 99 p_slowFib6) (main p_slowFib6).
Time Eval cbv in (wcbvEval 99 p_slowFib7) (main p_slowFib7).
Time Eval cbv in (wcbvEval 99 p_slowFib10) (main p_slowFib10).
Time Eval cbv in (wcbvEval 200 p_slowFib15) (main p_slowFib15).


Fixpoint fibrec (n:nat) (fs:nat * nat) {struct n} : nat :=
  match n with
    | 0 => fst fs
    | (S n) => fibrec n (pair ((fst fs) + (snd fs)) (fst fs))
  end.
Definition fib : nat -> nat := fun n => fibrec n (pair 0 1).

Eval compute in (fib 0).
Eval compute in (fib 1).
Eval compute in (fib 2).
Eval compute in (fib 3).
Eval compute in (fib 4).
Eval compute in (fib 6).
Quote Recursively Definition p_fib1 := (fib 1).
Quote Recursively Definition p_fib2 := (fib 2).
Quote Recursively Definition p_fib3 := (fib 3).
Quote Recursively Definition p_fib4 := (fib 4).
Quote Recursively Definition p_fib5 := (fib 5).
Quote Recursively Definition p_fib6 := (fib 6).
Quote Recursively Definition p_fib7 := (fib 7).
Quote Recursively Definition p_fib10 := (fib 10).
Quote Recursively Definition p_fib15 := (fib 15).
Eval cbv in (wcbvEval 20 p_fib1) (main p_fib1).
Eval cbv in (wcbvEval 30 p_fib2) (main p_fib2).
Eval cbv in (wcbvEval 40 p_fib3) (main p_fib3).
Eval cbv in (wcbvEval 50 p_fib4) (main p_fib4).
Eval cbv in (wcbvEval 60 p_fib5) (main p_fib5).
Eval cbv in (wcbvEval 60 p_fib6) (main p_fib6).
Time Eval cbv in (wcbvEval 70 p_fib7) (main p_fib7).
Time Eval cbv in (wcbvEval 70 p_fib10) (main p_fib10).
Time Eval cbv in (wcbvEval 200 p_fib15) (main p_fib15).


Quote Recursively Definition l_fib4 := (let x := 4 in fib x).
Eval cbv in (wcbvEval 50 l_fib4) (main l_fib4).

Fixpoint evenP (n:nat) {struct n} : bool :=
  match n with
    | 0 => true
    | S p => (oddP p)
  end
with oddP (n:nat) : bool :=
  match n with
    | 0 => false
    | S p => evenP p
  end.

Quote Recursively Definition p_evenOdd := (even 100).
Quote Recursively Definition f_evenOdd := (odd 100).
Eval cbv in (wcbvEval 500 p_evenOdd) (main p_evenOdd).
Eval cbv in (wcbvEval 500 f_evenOdd) (main f_evenOdd).

Quote Recursively Definition l_evenOdd := (even (let x := 50 in 2 * x)).
Time Eval cbv in (wcbvEval 500 l_evenOdd) (main l_evenOdd).
Time Eval cbv in (wcbvEval 5000 l_evenOdd) (main l_evenOdd).

Parameter axiom:nat.
Quote Recursively Definition p_axiom := (let x := axiom in 2 * x).
Print p_axiom.
Time Eval cbv in (wcbvEval 100 p_axiom) (main p_axiom).
Time Eval cbv in (wcbvEval 200 p_axiom) (main p_axiom).

***********)

(***
Goal forall p s t,
       WcbvEval p s t -> exists (n m:nat), wcbvEval n p s  = (S m, t).
induction 1.
- destruct IHWcbvEval. destruct H1. exists (S x). exists x0.
  simpl. rewrite H. assumption.
- destruct IHWcbvEval1, IHWcbvEval2, IHWcbvEval3.
  destruct H2, H3, H4.
  exists (S (x + x0 + x1)). exists (S (x2 + x3 + x4)).
  simpl.
***)

(* Coq doesn't evaluate the type of a cast *)
Eval cbv in  3 : ((fun n:Type => nat) Prop).
Eval lazy in  3 : ((fun n:Type => nat) Prop).
Eval hnf in  3 : ((fun n:Type => nat) Prop).
Eval vm_compute in  3 : ((fun n:Type => nat) Prop).

Goal 
  forall (t s:Term) (n m:nat) (e:environ),
  wcbvEval (S n) e t = (S m,s) -> wNorm s = true.
intros t; induction t; intros; try discriminate;
try (injection H; intros h1 h2; rewrite <- h1; auto; subst).
- simpl. simpl in H. rewrite h2 in H. rewrite h1. erewrite IHt1.


Lemma not_ltb_n_0: forall (n:nat), ltb n 0 = false.
induction n; unfold ltb; reflexivity.
Qed.

Lemma wcbvEval_up:
  forall (n:nat) (p:program) (s:Term),
   closedTerm 0 s = true -> fst (wcbvEval n p s) > 0 ->
   snd (wcbvEval n p s) = snd (wcbvEval (S n) p s).
intros n p s h1. induction n. simpl. omega.
intros h2.
induction s; simpl in h1; try rewrite not_ltb_n_0 in h1;
try discriminate; try reflexivity.
Admitted.

(***
intros n p s h. induction n. simpl. intro h1. omega.
intro h1. induction s; try reflexivity.
- rewrite IHs2.
***)

Goal forall (strt:nat) (p:program) (s:Term),
       wNorm s = true -> snd (wcbvEval strt p s) = s.
intros strt p s h. induction strt. reflexivity.
induction s; simpl in h; try discriminate h; try reflexivity.
- rewrite <- IHstrt. rewrite -> IHstrt at 1. rewrite <- wcbvEval_up. reflexivity. simpl.

- rewrite <- IHstrt. rewrite -> IHstrt at 1. admit.
- rewrite <- IHstrt. rewrite -> IHstrt at 1. admit.
- rewrite <- IHstrt. rewrite -> IHstrt at 1. admit.
- rewrite <- IHstrt. rewrite -> IHstrt at 1. admit.
Qed.

Goal forall (strt:nat) (p:program) (s:Term),
       fst (wcbvEval strt p s) > 0 -> wNorm (snd (wcbvEval strt p s)) = true.
intros strt p s h. induction s; unfold wcbvEval; simpl.

*******************)
*****)
