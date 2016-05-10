(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "../L2_typeStrippedL1" as L2.
(****)

Require Import Lists.List.
Require Import Strings.String.
Require Import Arith.Compare_dec.
Require Import Program.Basics.
Require Import Omega.
Require Import JMeq.
Require Import L2.term.
Require Import L2.program.
Require Import L2.wndEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(** Relational version of weak cbv evaluation  **)
Inductive WcbvEval (p:environ) : Term -> Term -> Prop :=
| wPrf: WcbvEval p TProof TProof
| wLam: forall nm bod,
          WcbvEval p (TLambda nm bod) (TLambda nm bod)
| wProd: forall nm bod,
          WcbvEval p (TProd nm bod) (TProd nm bod)
| wCast: forall t s, WcbvEval p t s -> WcbvEval p (TCast t) s
| wConstruct: forall i r, 
                WcbvEval p (TConstruct i r) (TConstruct i r)
| wInd: forall i, WcbvEval p (TInd i) (TInd i) 
| wSort: forall srt, WcbvEval p (TSort srt) (TSort srt)
| wFix: forall dts dts' m,
          WcbvDEvals p dts dts' -> WcbvEval p (TFix dts m) (TFix dts' m)
| wAx: forall nm, LookupAx nm p -> WcbvEval p (TConst nm) (TConst nm)
| wConst: forall nm (t s:Term),
            LookupDfn nm p t -> WcbvEval p t s -> WcbvEval p (TConst nm) s
| wAppLam: forall (fn bod a1 a1' s:Term) (args:Terms) (nm:name),
               WcbvEval p fn (TLambda nm bod) ->
               WcbvEval p a1 a1' ->
               WcbvEval p (whBetaStep bod a1' args) s ->
               WcbvEval p (TApp fn a1 args) s
| wLetIn: forall (nm:name) (dfn bod dfn' s:Term),
            WcbvEval p dfn dfn' ->
            WcbvEval p (instantiate dfn' 0 bod) s ->
            WcbvEval p (TLetIn nm dfn bod) s
| wAppFix: forall dts m (fn arg fs s:Term) (args:Terms),
             WcbvEval p fn (TFix dts m) ->
             whFixStep dts m (tcons arg args) = fs ->
             WcbvEval p fs s ->
             WcbvEval p (TApp fn arg args) s
| wAppAx: forall fn ax arg arg1 args args1,
              WcbvEval p fn (TConst ax) ->
              WcbvEval p arg arg1 ->
              WcbvEvals p args args1 ->
              WcbvEval p (TApp fn arg args) (TApp (TConst ax) arg1 args1)
| wAppCnstr: forall fn i n arg arg1 args args1,
              WcbvEval p fn (TConstruct i n) ->
              WcbvEval p arg arg1 ->
              WcbvEvals p args args1 ->
              WcbvEval p (TApp fn arg args) (TApp (TConstruct i n) arg1 args1)
| wAppInd: forall fn i arg arg1 args args1,
              WcbvEval p fn (TInd i) ->
              WcbvEval p arg arg1 ->
              WcbvEvals p args args1 ->
              WcbvEval p (TApp fn arg args) (TApp (TInd i) arg1 args1)
| wCase0: forall l mch i n brs cs s,
            WcbvEval p mch (TConstruct i n) ->
            whCaseStep n tnil brs = Some cs ->
            WcbvEval p cs s ->
            WcbvEval p (TCase (0,l) mch brs) s
| wCasen: forall mch i n arg args ml brs cs s ts,
           WcbvEval p mch (TApp (TConstruct i n) arg args) ->
           tskipn (fst ml) (tcons arg args) = Some ts ->
           whCaseStep n ts brs = Some cs ->
           WcbvEval p cs s ->
           WcbvEval p (TCase ml mch brs) s
| wCaseAx: forall mch ax ml brs brs',
           WcbvEval p mch (TConst ax) ->
           WcbvEvals p brs brs' ->           
           WcbvEval p (TCase ml mch brs) (TCase ml (TConst ax) brs')
with WcbvEvals (p:environ) : Terms -> Terms -> Prop :=
| wNil: WcbvEvals p tnil tnil
| wCons: forall t t' ts ts',
           WcbvEval p t t' -> WcbvEvals p ts ts' -> 
           WcbvEvals p (tcons t ts) (tcons t' ts')
with WcbvDEvals (p:environ) : Defs -> Defs -> Prop :=
| wDNil: WcbvDEvals p dnil dnil
| wDCons: forall n s s' i ds ds',
           WcbvEval p s s' -> WcbvDEvals p ds ds' -> 
           WcbvDEvals p (dcons n s i ds) (dcons n s' i ds').
Hint Constructors WcbvEval WcbvEvals WcbvDEvals.
Scheme WcbvEval1_ind := Induction for WcbvEval Sort Prop
     with WcbvEvals1_ind := Induction for WcbvEvals Sort Prop
     with WcbvDEvals1_ind := Induction for WcbvDEvals Sort Prop.
Combined Scheme WcbvEvalEvals_ind
         from WcbvEval1_ind, WcbvEvals1_ind, WcbvDEvals1_ind.

(** when reduction stops **)
Definition no_Wcbv_step (p:environ) (t:Term) : Prop :=
  no_step (WcbvEval p) t.
Definition no_Wcbvs_step (p:environ) (ts:Terms) : Prop :=
  no_step (WcbvEvals p) ts.

(** evaluate omega = (\x.xx)(\x.xx): nontermination **)
Definition xx := (TLambda nAnon (TApp (TRel 0) (TRel 0) tnil)).
Definition xxxx := (TApp xx xx tnil).
Goal WcbvEval nil xxxx xxxx.
unfold xxxx, xx. eapply wAppLam. eapply wLam. eapply wLam.
Abort.


Lemma WcbvEval_mkApp_nil:
  forall t, WFapp t -> forall p s, WcbvEval p t s ->
                 WcbvEval p (mkApp t tnil) s.
Proof.
  intros p. induction 1; simpl; intros; try assumption.
  - rewrite tappend_tnil. assumption.
Qed.


(** wcbvEval preserves WFapp **)
Lemma WcbvEval_presWFapp:
  forall p, WFaEnv p -> 
  (forall t s, WcbvEval p t s -> WFapp t -> WFapp s) /\
  (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> WFapps ss) /\
  (forall ds es, WcbvDEvals p ds es -> WFappDs ds -> WFappDs es).
Proof.
  intros p hp. apply WcbvEvalEvals_ind; intros; try assumption.
  - inversion_Clear H0. intuition.
  - inversion_Clear H0. constructor. intuition.
  - apply H. assert (j:= Lookup_pres_WFapp hp l). inversion j. assumption.
  - inversion_Clear H2. apply H1.
    apply (whBetaStep_pres_WFapp); try assumption.
    + assert (j:= H H7). inversion_Clear j. assumption.
    + apply H0. assumption.
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp; intuition.
  - inversion_clear H1. apply H0. rewrite <- e.
    apply whFixStep_pres_WFapp.
    + specialize (H H3). inversion_Clear H. assumption.
    + constructor; assumption.
  - inversion_Clear H2. constructor; intuition.
    destruct H2 as [x1 [x2 [x3 j]]]. discriminate.
  - inversion_Clear H2. constructor; intuition.
    destruct H2 as [x1 [x2 [x3 j]]]. discriminate.
  - inversion_Clear H2. constructor; intuition.
    destruct H2 as [x1 [x2 [x3 j]]]. discriminate.
  - apply H0. inversion_Clear H1.
    refine (whCaseStep_pres_WFapp _ _ _ e); auto.
  - apply H0. inversion_Clear H1.
    refine (whCaseStep_pres_WFapp _ _ _ e0); auto.
    assert (j:= H H4). inversion_Clear j.
    refine (tskipn_pres_WFapp _ _ e). intuition.
  - inversion_Clear H1. intuition. 
  - inversion_Clear H1. constructor; intuition.
  - inversion_Clear H1. intuition.
Qed.

Lemma WcbvEval_weaken:
  forall p,
    (forall t s, WcbvEval p t s -> forall nm ec, fresh nm p ->
          WcbvEval ((nm,ec)::p) t s) /\
    (forall ts ss, WcbvEvals p ts ss -> forall nm ec, fresh nm p ->
          WcbvEvals ((nm,ec)::p) ts ss) /\
    (forall ds es, WcbvDEvals p ds es -> forall nm ec, fresh nm p ->
                   WcbvDEvals ((nm,ec)::p) ds es).
Proof.
  intros p. apply WcbvEvalEvals_ind; intros; auto.
  - apply wAx. apply Lookup_weaken; assumption.
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
  - eapply wAppFix; intuition. rewrite e. apply H0. assumption.
  - eapply wCase0; intuition. assumption.
  - eapply wCasen; intuition; eassumption.
Qed.

Lemma WcbvEval_wndEvalRTC:
  forall (p:environ), WFaEnv p ->
    (forall t s, WcbvEval p t s -> WFapp t -> wndEvalRTC p t s) /\
    (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> wndEvalsRTC p ts ss) /\
    (forall ds es, WcbvDEvals p ds es -> WFappDs ds -> wndDEvalsRTC p ds es).
Proof.
intros p hp. apply WcbvEvalEvals_ind; intros; try (solve [constructor]).
- eapply wERTCtrn. apply wERTCstep. apply sCast. apply H. 
  inversion_Clear H0. assumption.
- inversion_Clear H0. specialize (H H2). eapply wERTCtrn.
  + constructor.
  + eapply wndEvalsRTC_Fix_defs. assumption.
- eapply wERTCtrn. 
  + apply wERTCstep. apply sConst. eassumption.
  + apply H. assert (j:= Lookup_pres_WFapp hp l). inversion j. assumption.
- eapply (@wERTCtrn _ _ (TApp (TLambda nm bod) a1 args));
  inversion_Clear H2. 
  + rewrite <- mkApp_goodFn; try assumption.
    rewrite <- mkApp_goodFn; try not_isApp.
    apply wndEvalRTC_App_fn. apply H. assumption. assumption.
  + eapply (@wERTCtrn _ _ (TApp (TLambda nm bod) a1' args)).
    * apply wndEvalRTC_App_arg. apply H0. assumption. 
    * { apply (@wERTCtrn _ _ (whBetaStep bod a1' args)).
        - apply wERTCstep. apply sBeta. 
        - apply H1. apply whBetaStep_pres_WFapp; try eassumption.
          + assert (j:= proj1 (WcbvEval_presWFapp hp) _ _ w H7).
            inversion_Clear j. assumption.
          + eapply wndEvalRTC_pres_WFapp; try eassumption.
            * apply H0. assumption. }
- inversion_Clear H1. eapply (@wERTCtrn _ _ (TLetIn nm dfn' bod)).
  + apply wndEvalRTC_LetIn_dfn. intuition.
  + eapply wERTCtrn. apply wERTCstep. apply sLetIn. apply H0.
    apply instantiate_pres_WFapp; try assumption.
    * eapply (proj1 (WcbvEval_presWFapp hp)); try eassumption.
- inversion_Clear H1. specialize (H H6).
  assert (j:= wndEvalRTC_pres_WFapp H hp H6). inversion_Clear j.
  refine (@wERTCtrn _ _ (TApp (TFix dts m) arg args) _ _ _).
  + rewrite <- mkApp_goodFn; try assumption.
    rewrite <- mkApp_goodFn; try not_isApp.
    apply wndEvalRTC_App_fn. apply H. assumption.
  + refine (@wERTCtrn _ _ (whFixStep dts m (tcons arg args)) _ _ _).
    * apply wERTCstep. apply sFix. 
    * apply H0. eapply whFixStep_pres_WFapp. assumption.
      constructor; assumption.
- inversion_Clear H2.
  specialize (H1 H9). specialize (H0 H8). specialize (H H7).
  eapply (@wERTCtrn _ _ (TApp (TConst ax) arg args)).
  + rewrite <- mkApp_goodFn; try assumption.
    rewrite <- mkApp_goodFn; try not_isApp.
    apply wndEvalRTC_App_fn. apply H. assumption.
  + eapply (@wERTCtrn _ _ (TApp (TConst ax) arg1 args)).
    * { apply wndEvalRTC_App_arg; try not_isApp; try assumption. }
    * { eapply (@wERTCtrn _ _ (TApp (TConst ax) arg1 args1)).
        - apply wndEvalsRTC_App_args; try not_isApp; try assumption.
        - apply wERTCrfl. }
- inversion_Clear H2.
  specialize (H1 H9). specialize (H0 H8). specialize (H H7).
  eapply (@wERTCtrn _ _ (TApp (TConstruct i n) arg args)).
  + rewrite <- mkApp_goodFn; try assumption.
    rewrite <- mkApp_goodFn; try not_isApp.
    apply wndEvalRTC_App_fn. apply H. assumption.
  + eapply (@wERTCtrn _ _ (TApp (TConstruct i n) arg1 args)).
    * { apply wndEvalRTC_App_arg; try not_isApp; try assumption. }
    * { eapply (@wERTCtrn _ _ (TApp (TConstruct i n) arg1 args1)).
        - apply wndEvalsRTC_App_args; try not_isApp; try assumption.
        - apply wERTCrfl. }
- inversion_Clear H2.
  specialize (H1 H9). specialize (H0 H8). specialize (H H7).
  eapply (@wERTCtrn _ _ (TApp (TInd i) arg args)).
  + rewrite <- mkApp_goodFn; try assumption.
    rewrite <- mkApp_goodFn; try not_isApp.
    apply wndEvalRTC_App_fn. apply H. assumption.
  + eapply (@wERTCtrn _ _ (TApp (TInd i) arg1 args)).
    * { apply wndEvalRTC_App_arg; try not_isApp; try assumption. }
    * { eapply (@wERTCtrn _ _ (TApp (TInd i) arg1 args1)).
        - apply wndEvalsRTC_App_args; try not_isApp; try assumption.
        - apply wERTCrfl. }
- inversion_Clear H1. specialize (H H4).
  specialize (H0 (whCaseStep_pres_WFapp H6 wfanil _ e)).
  eapply wERTCtrn. 
  + eapply wndEvalRTC_Case_mch. eassumption.
  + eapply (@wERTCtrn _ _ cs).
    * apply wERTCstep. apply sCase0. assumption.
    * assumption.
- inversion_Clear H1. eapply wERTCtrn. 
  + eapply wndEvalRTC_Case_mch. apply H. assumption.
  + eapply (@wERTCtrn _ _ cs).
    * apply wERTCstep. eapply sCasen; eassumption.
    * { apply H0. refine (whCaseStep_pres_WFapp _ _ _ e0). assumption.
        - assert (j: WFapps (tcons arg args)).
          { assert (k:= proj1 (WcbvEval_presWFapp hp) _ _ w H4).
            inversion_clear k. constructor; assumption. }
          inversion_Clear j.
          eapply (@tskipn_pres_WFapp (tcons arg args)); try eassumption.
          constructor; assumption. }
- inversion_Clear H1. eapply wERTCtrn.
  + eapply wndEvalRTC_Case_mch. apply H. assumption.
  + eapply (@wERTCtrn _ _  (TCase ml (TConst ax) brs')).
    * apply wndEvalRTC_Case_brs. intuition.
    * apply wERTCrfl. 
- inversion_Clear H1. eapply (@wEsRTCtrn _ _ (tcons t' ts)).
  + apply wndEvalsRTC_tcons_hd. apply H. assumption.
  + eapply (@wEsRTCtrn _ _ (tcons t' ts')).
     * apply wndEvalsRTC_tcons_tl. intuition. 
     * apply wEsRTCrfl.
- inversion_Clear H1. eapply (@wDEsRTCtrn _ _ (dcons n s' i ds)).
  + apply wndDEvalsRTC_dcons_hd. apply H. assumption.
  + eapply (@wDEsRTCtrn _ _ (dcons n s' i ds)).
    * apply wndDEvalsRTC_dcons_hd. intuition.
    * apply wndDEvalsRTC_dcons_tl. intuition.
Qed.


(** WcbvEval makes progress **
Goal
  forall (p:environ),
    (forall t u, WcbvEval p t u ->
         (t = u /\ no_step (wndEval p) t) \/ exists v, wndEval p t v) /\
    (forall ts us, WcbvEvals p ts us ->
         (ts = us /\ no_step (wndEvals p) ts) \/
                      exists vs, wndEvals p ts vs).
Proof.
  intros p. apply WcbvEvalEvals_ind; intros; unfold no_step.
  - left. intuition. inversion H.
    Check (MkApp_tcons_isApp (tcons arg args)).

***)


(***************** ***
Goal
  forall (p:environ),
  (forall t, (no_wnd_step p t /\ (no_Wcbv_step p t \/ WcbvEval p t t)) \/
                 (exists u, wndEvalTC p t u /\ WcbvEval p t u)) /\
  (forall ts, (no_wnds_step p ts /\ WcbvEvals p ts ts) \/
                  (exists us, wndEvalsTC p ts us /\ WcbvEvals p ts us)) /\
  (forall (ds:Defs), True).
induction p; apply TrmTrmsDefs_ind; intros; auto.



Goal
  (forall p n t, Crct p n t -> n = 0 ->
                 (no_wnd_step p t /\ WcbvEval p t t) \/
                 (exists u, wndEvalTC p t u /\ WcbvEval p t u)) /\
  (forall p n ts, Crcts p n ts -> n = 0 ->
                  (no_wnds_step p ts /\ WcbvEvals p ts ts) \/
                  (exists us, wndEvalsTC p ts us /\ WcbvEvals p ts us)) /\
  (forall (p:environ) (n:nat) (ds:Defs), CrctDs p n ds -> True).
apply CrctCrctsCrctDs_ind; intros; try auto; subst.
- left. split.
  + intros x h. inversion h.
  + constructor.
- destruct H0; destruct H2; try reflexivity.
  + left. split. intros x h.
    assert (j1:= proj1 H0). assert (j2:= proj1 H2).
    unfold no_wnd_step in j1. eelim j1.
    eapply (proj1 (wndEval_strengthen _)). eapply h. reflexivity.
    eapply (proj1 (Crct_fresh_Pocc)); eassumption.
    apply WcbvEval_weaken; intuition.
  + left. destruct H0. split.
    * unfold no_wnd_step. intros w j. unfold no_wnd_step in H0.
      elim (H0 w). eapply (proj1 (wndEval_strengthen _)).
      eassumption. reflexivity.
      eapply (proj1 Crct_fresh_Pocc); eassumption.
    * eapply (proj1 (WcbvEval_weaken _)); assumption.
  + right. destruct H0. destruct H0. exists x. split.
    * apply wndEvalTC_weaken; assumption.
    * apply WcbvEval_weaken; assumption.
  + right. destruct H0. destruct H0. exists x. split.
    * apply wndEvalTC_weaken; assumption.
    * apply WcbvEval_weaken; assumption.
- omega.
- left. intuition. intros x h. inversion h.
- left. intuition. intros x h. inversion h.
- right. destruct H0; try reflexivity; destruct H0.
  + unfold no_wnd_step in H0. eelim H0.
***)


(** WcbvEval is in the transitive closure of wndEval **)
(**
Lemma WcbvEval_wndEvalTC:
  forall (p:environ),
    (forall t s, WcbvEval p t s -> t <> s -> wndEvalTC p t s) /\
    (forall ts ss, WcbvEvals p ts ss -> ts <> ss -> wndEvalsTC p ts ss).
intros p. apply WcbvEvalEvals_ind; intros; try (nreflexivity H).
- destruct (Term_dec t s).
  + apply wETCstep. subst. constructor. assumption.
  + eapply wETCtrn.
    * constructor. constructor. eassumption.
    * apply H. assumption.
- destruct (Term_dec fn (TLambda nm bod)); destruct (Term_dec a1 a1');
  destruct (Term_dec (whBetaStep bod a1' args) s); subst.
  + apply wETCstep. constructor.
  + eapply wETCtrn. apply wETCstep. constructor. apply H1. assumption.
  + eapply wETCtrn. apply wndEvalTC_App_arg. apply H0. assumption. 
    constructor. constructor.
  + eapply wETCtrn. apply wndEvalTC_App_arg. apply H0. assumption.
    eapply wETCtrn. constructor. constructor. apply H1. assumption.
  + eapply wETCtrn. apply wndEvalTC_App_fn. apply H; assumption.
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
- destruct (Term_dec mch (TConstruct i n)); destruct (Term_dec cs s); subst.
  + eapply wETCstep. constructor. assumption.
  + eapply wETCtrn. apply wETCstep. constructor. eassumption.
    apply H0. assumption.
  + eapply wETCtrn. apply wndEvalTC_Case_mch. apply H. assumption.
    constructor. constructor. assumption.
  + eapply wETCtrn. apply wndEvalTC_Case_mch. apply H. assumption.
    eapply wETCtrn. constructor. constructor. eassumption.
    apply H0. assumption.
- destruct (Term_dec mch (TApp (TConstruct i n) arg args)); 
  destruct (Term_dec cs s); subst.
  + eapply wETCstep. eapply sCasen. eassumption. assumption.
  + eapply wETCtrn. eapply wETCstep. eapply sCasen. eassumption. eassumption.
    apply H0. assumption.
  + eapply wETCtrn. apply wndEvalTC_Case_mch. apply H. assumption.
    eapply wETCstep. eapply sCasen. eassumption. eassumption.
  + eapply wETCtrn. apply wndEvalTC_Case_mch. apply H. assumption.
    eapply wETCtrn. eapply wETCstep. eapply sCasen. eassumption. 
    apply e0. apply H0. eassumption.
- destruct (Term_dec t t'); destruct (Terms_dec ts ts'); subst.
  + elim H1. reflexivity.
  + eapply wndEvalsTC_tcons_tl. apply H0. assumption.
  + eapply wndEvalsTC_tcons_hd. apply H. assumption. 
  + eapply wEsTCtrn. eapply wndEvalsTC_tcons_hd. apply H. assumption. 
    eapply wndEvalsTC_tcons_tl. apply H0. assumption.
Qed.
**)

(************  in progress  ****
Lemma WcbvEval_strengthen:
  forall pp,
  (forall t s, WcbvEval pp t s -> forall nm u p, pp = (nm,ecConstr u)::p ->
        ~ PoccTrm nm t -> WcbvEval p t s) /\
  (forall ts ss, WcbvEvals pp ts ss -> forall nm u p, pp = (nm,ecConstr u)::p ->
        ~ PoccTrms nm ts -> WcbvEvals p ts ss).
intros pp. apply WcbvEvalEvals_ind; intros; auto; subst.
- admit.
- destruct (notPocc_TApp H3) as (hfn & ha1 & hargs). eapply wAppLam.
  + eapply H. reflexivity. assumption.
  + eapply H0. reflexivity. assumption.
  + eapply H1. reflexivity. unfold whBetaStep.


Lemma WcbvEval_strengthen:
  forall pp,
  (forall t s, WcbvEval pp t s -> forall nm u p, pp = (nm,ecConstr u)::p ->
        forall n, Crct pp n t -> ~ PoccTrm nm t -> WcbvEval p t s) /\
  (forall ts ss, WcbvEvals pp ts ss -> forall nm u p, pp = (nm,ecConstr u)::p ->
        forall n, Crcts pp n ts -> ~ PoccTrms nm ts -> WcbvEvals p ts ss).
intros pp. apply WcbvEvalEvals_ind; intros; auto; subst.
- admit.
(***
- eapply wConst. eapply Lookup_strengthen; try eassumption.
  + destruct (string_dec nm nm0); auto.
    * subst. elim H2. constructor. auto.
  + eapply H. eassumption.
    * instantiate (1:= 0). admit. 
(***
subst.  assert (j:= inverse_Pocc_TConstL H2). inversion_Clear l.
      elim j. reflexivity. inversion_Clear H1.

      Check (proj1 (Crct_strengthen) _ _ _ H1). eapply CrctWk. instantiate (1:= 0). admit.
***)
    * subst. assert (j:= inverse_Pocc_TConstL H2). inversion_Clear l.
  
inversion_Clear H1.
***)
- destruct (notPocc_TApp H4); destruct H5. eapply wAppLam. 
   + eapply H; try reflexivity; try eassumption. eapply CrctWk. 

Check (proj1 Crct_strengthen _ _ _ H3). inversion_Clear H3.
  + injection H8. intros. subst. eapply wAppLam. eapply H. reflexivity.
    * eapply Crct_strengthen. 

HERE


(@wConst p nm t s pp). eapply (@Lookup_strengthen _ pp); try eassumption.
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
- apply (H nm u); trivial; apply (notPocc_TCase H1).
- apply (H nm u); trivial; apply (notPocc_TCase H1).
- apply (H nm u); trivial; apply (notPocc_TCase H1).
- apply (H nm u). trivial. apply (notPoccTrms H1).
- apply (H nm u). trivial. apply (notPoccTrms H1).
Qed.
***************)

Section wcbvEval_sec.
Variable p:environ.

(** now an executable weak-call-by-value evaluation **)
(** use a timer to make this terminate **)
Function wcbvEval (tmr:nat) (t:Term) {struct tmr} : option Term :=
  (match tmr with 
     | 0 => None          (** out of time  **)
     | S n =>
       (match t with      (** look for a redex **)
          | TConst nm => match lookup nm p with
                           | Some (ecTrm t) => wcbvEval n t
                           | Some ecAx => Some (TConst nm)
                           | _ => None
                         end
          | TCast t =>  wcbvEval n t
          | TApp fn a1 args =>
            match wcbvEval n fn, wcbvEval n a1, wcbvEvals n args with
              | None, _, _ => None
              | Some (TFix dts m), _, _ =>
                wcbvEval n (whFixStep dts m (tcons a1 args))
              | Some _, None, _ => None
              | Some (TLambda _ bod), Some ea1, _ =>
                wcbvEval n (whBetaStep bod ea1 args)
              | Some _, Some _, None => None
              | Some (TConst ax), Some ea1, Some eargs =>
                Some (TApp (TConst ax) ea1 eargs)
              | Some (TConstruct i n), Some ea1, Some eargs =>
                Some (TApp (TConstruct i n) ea1 eargs)
              | Some (TInd i), Some ea1, Some eargs =>
                Some (TApp (TInd i) ea1 eargs)
              | Some t, _, _ => None
            end
          | TCase ml mch brs =>
            (match wcbvEval n mch with
               | None => None
               | Some emch =>
                 (match emch, (fst ml) with 
                    | TConstruct _ r, 0 => 
                      match whCaseStep r tnil brs with
                        | None => None
                        | Some cs => wcbvEval n cs
                      end
                    | TApp (TConstruct _ r) arg args, m =>
                      match tskipn m (tcons arg args) with
                        | None => None
                        | Some ts => match whCaseStep r ts brs with
                                       | None => None
                                       | Some cs => wcbvEval n cs
                                     end
                      end
                    | TConst nm, _ => (* mch evals to an axiom *)
                      match wcbvEvals n brs with
                            | Some brs' => Some (TCase ml (TConst nm) brs')
                            | None => None
                      end
                    | _, _ => None
                  end)
             end)
          | TLetIn nm df bod =>
            match wcbvEval n df with
              | None => None
              | Some df' => wcbvEval n (instantiate df' 0 bod)
            end
          | TFix mfp br =>
            match wcbvDEvals n mfp with
              | Some mfp' => Some (TFix mfp' br)
              | None => None
            end
          (** already in whnf ***)
          | TLambda nn t => Some (TLambda nn t)
          | TProd nn t => Some (TProd nn t)
          | TConstruct i cn => Some (TConstruct i cn)
          | TInd i => Some (TInd i)
          | TSort srt => Some (TSort srt)
          | TProof => Some TProof
          (** should never appear **)
          | TRel _ => None
        end)
   end)
with wcbvEvals (tmr:nat) (ts:Terms) {struct tmr}
     : option Terms :=
       (match tmr with 
          | 0 => None                        (** out of time  **)
          | S n => match ts with             (** look for a redex **)
                     | tnil => Some tnil
                     | tcons s ss =>
                       match wcbvEval n s, wcbvEvals n ss with
                         | Some es, Some ess => Some (tcons es ess)
                         | _, _ => None
                       end
                   end
        end)
with wcbvDEvals (tmr:nat) (ds:Defs) {struct tmr}
     : option Defs :=
       (match tmr with 
          | 0 => None
          | S n =>
            match ds with             (** look for a redex **)
              | dnil => Some dnil
              | dcons m t i ss =>
                match wcbvEval n t, wcbvDEvals n ss with
                  | Some et, Some ess => Some (dcons m et i ess)
                  | _, _ => None
                end
            end
        end).
Functional Scheme wcbvEval_ind' := Induction for wcbvEval Sort Prop
with wcbvEvals_ind' := Induction for wcbvEvals Sort Prop
with wcbvDEvals_ind' := Induction for wcbvDEvals Sort Prop.
Combined Scheme wcbvEvalEvalsDEvals_ind
         from wcbvEval_ind', wcbvEvals_ind', wcbvDEvals_ind'.

(** wcbvEval and WcbvEval are the same relation **)
Lemma wcbvEval_WcbvEval:
  forall n,
    (forall t s, wcbvEval n t = Some s -> WcbvEval p t s) /\
    (forall ts ss, wcbvEvals n ts = Some ss -> WcbvEvals p ts ss) /\
    (forall (ds es:Defs), wcbvDEvals n ds = Some es -> WcbvDEvals p ds es).
Proof.
  intros n.
  apply (wcbvEvalEvalsDEvals_ind
           (fun n t o => forall s, o = Some s -> WcbvEval p t s)
           (fun n ts os => forall ss, os = Some ss -> WcbvEvals p ts ss)
           (fun n t su => forall u, su = Some u -> WcbvDEvals p t u));
    intros; try discriminate;
    try (myInjection H); try (myInjection H0);
    try (myInjection H1); try (myInjection H2);
    try(solve[constructor]); intuition.
  - eapply wConst; intuition.
    + unfold LookupDfn. apply lookup_Lookup. eassumption.
  - apply wAx. unfold LookupAx. apply lookup_Lookup. eassumption.
  - eapply wAppFix; intuition.
    + apply H. eassumption.
  - eapply wAppLam; intuition.
    + apply H. eassumption.
    + apply H0. eassumption.
  - destruct ml. simpl in e3. subst. eapply wCase0; intuition.
    + apply H. eassumption.
    + assumption.
  - eapply wCasen; intuition.
    + eapply H. rewrite e1. apply f_equal. eassumption.
    + rewrite e3. rewrite e4. reflexivity.
    + assumption.
  - eapply wLetIn; intuition.
    + apply H. assumption.
Qed.


(* need this strengthening to large-enough fuel to make the induction
** go through
*)
Lemma pre_WcbvEval_wcbvEval:
    (forall t s, WcbvEval p t s ->
             exists n, forall m, m >= n -> wcbvEval (S m) t = Some s) /\
    (forall ts ss, WcbvEvals p ts ss ->
             exists n, forall m, m >= n -> wcbvEvals (S m) ts = Some ss) /\
    (forall ds es, WcbvDEvals p ds es ->
          exists n, forall m, m >= n -> wcbvDEvals (S m) ds = Some es).
assert (j:forall m x, m > x -> m = S (m - 1)). induction m; intuition.
apply WcbvEvalEvals_ind; intros; try (exists 0; intros mx h; reflexivity).
- destruct H. exists (S x). intros m hm. simpl. rewrite (j m x).
  + apply H. omega.
  + omega.
- destruct H. exists (S x). intros mm hmm. simpl. rewrite (j mm x).
  + rewrite H. reflexivity. omega.
  + omega.
- exists 0. intros m hm. simpl. rewrite (LookupAx_lookup l). reflexivity.
- destruct H. exists (S x). intros m h. unfold LookupDfn in l.
  simpl. rewrite (Lookup_lookup l). rewrite (j m x); try omega.
  apply H. omega.
- destruct H, H0, H1. exists (S (max x (max x0 x1))).
  intros m h.
  assert (k:wcbvEval m fn = Some (TLambda nm bod)).
  + rewrite (j m (max x (max x0 x1))). apply H.
    assert (l:= max_fst x (max x0 x1)); omega. omega.
  + assert (k0:wcbvEval m a1 = Some a1').
    rewrite (j m (max x (max x0 x1))). apply H0.
    assert (l:= max_snd x (max x0 x1)). assert (l':= max_fst x0 x1).
    omega. omega.
    * simpl. rewrite k. rewrite k0.
      rewrite (j m (max x (max x0 x1))). apply H1.
      assert (l:= max_snd x (max x0 x1)). assert (l':= max_snd x0 x1).
      omega. omega.
- destruct H, H0. exists (S (max x x0)). intros m h. simpl.
  assert (k:wcbvEval m dfn = Some dfn'). 
  assert (l:= max_fst x x0).
  rewrite (j m (max x x0)). apply H. omega. omega.
  rewrite k.
  assert (l:= max_snd x x0).
  rewrite (j m x0). apply H0. omega. omega.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
  rewrite e. rewrite (H0 (mx - 1)); try omega.
  rewrite <- (H0 mx); try omega. reflexivity.
- destruct H, H0, H1. exists (S (max x (max x0 x1))). intros m h.
  assert (j1:= max_fst x (max x0 x1)). 
  assert (lx: m > x). omega.
  assert (j2:= max_snd x (max x0 x1)).
  assert (j3:= max_fst x0 x1).
  assert (lx0: m > x0). omega.
  assert (j4:= max_snd x0 x1).
  assert (j5:= max_fst x0 x1).
  assert (lx1: m > x1). omega.
  simpl. rewrite (j m x); try omega.
  rewrite H; try omega. rewrite H0; try omega. rewrite H1; try omega.
  reflexivity.
- destruct H, H0, H1. exists (S (max x (max x0 x1))). intros m h.
  assert (j1:= max_fst x (max x0 x1)). 
  assert (lx: m > x). omega.
  assert (j2:= max_snd x (max x0 x1)).
  assert (j3:= max_fst x0 x1).
  assert (lx0: m > x0). omega.
  assert (j4:= max_snd x0 x1).
  assert (j5:= max_fst x0 x1).
  assert (lx1: m > x1). omega.
  simpl. rewrite (j m x); try omega.
  rewrite H; try omega. rewrite H0; try omega. rewrite H1; try omega.
  reflexivity.
- destruct H, H0, H1. exists (S (max x (max x0 x1))). intros m h.
  assert (j1:= max_fst x (max x0 x1)). 
  assert (lx: m > x). omega.
  assert (j2:= max_snd x (max x0 x1)).
  assert (j3:= max_fst x0 x1).
  assert (lx0: m > x0). omega.
  assert (j4:= max_snd x0 x1).
  assert (j5:= max_fst x0 x1).
  assert (lx1: m > x1). omega.
  simpl. rewrite (j m x); try omega.
  rewrite H; try omega. rewrite H0; try omega. rewrite H1; try omega.
  reflexivity.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try rewrite (H (mx - 1)); try omega.
  rewrite e. apply H0. omega.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
  rewrite e. rewrite e0. apply H0. omega.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
  rewrite H0; try omega. reflexivity.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (j1:= max_fst x x0). assert (j2:= max_snd x x0).
  assert (lx: mx > x). omega.  assert (lx0: mx > x0). omega.
  simpl. rewrite (j mx x); try omega.
  rewrite (H (mx - 1)); try omega. rewrite (H0 (mx - 1)); try omega.
  reflexivity.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (j1:= max_fst x x0). assert (j2:= max_snd x x0).
  assert (lx: mx > x). omega.  assert (lx0: mx > x0). omega.
  simpl. rewrite (j mx x); try omega.
  rewrite (H (mx - 1)); try omega. rewrite (H0 (mx - 1)); try omega.
  reflexivity.
Qed.

Lemma WcbvEval_wcbvEval:
  forall t s, WcbvEval p t s ->
             exists n, forall m, m >= n -> wcbvEval m t = Some s.
Proof.
  intros t s h.
  destruct (proj1 pre_WcbvEval_wcbvEval _ _ h).
  exists (S x). intros m hm. assert (j:= H (m - 1)). 
  assert (k: m = S (m - 1)). { omega. }
  rewrite k. apply j. omega.
Qed.

Lemma WcbvEvals_wcbvEvals:
  forall ts ss, WcbvEvals p ts ss ->
             exists n, forall m, m >= n -> wcbvEvals m ts = Some ss.
Proof.
  intros ts ss h.
  destruct (proj1 (proj2 pre_WcbvEval_wcbvEval) _ _ h).
  exists (S x). intros m hm. assert (j:= H (m - 1)). 
  assert (k: m = S (m - 1)). { omega. }
  rewrite k. apply j. omega.
Qed.


(** WcbvEval is single-valued **)
Lemma WcbvEval_single_valued:
  forall t s1, WcbvEval p t s1 -> forall s2, WcbvEval p t s2 -> s1 = s2.
Proof.
  intros t s1 h1 s2 h2.
  assert (j1:= WcbvEval_wcbvEval h1).
  assert (j2:= WcbvEval_wcbvEval h2).
  destruct j1 as [x1 k1]. destruct j2 as [x2 k2].
  specialize (k1 (max x1 x2)). specialize (k2 (max x1 x2)).
  rewrite k1 in k2. injection k2. intuition. 
  apply max_snd. apply max_fst.
Qed.

Lemma WcbvEvals_single_valued:
  forall ts ss1, WcbvEvals p ts ss1 ->
   forall ss2, WcbvEvals p ts ss2 -> ss1 = ss2.
Proof.
  intros ts ss1 h1 ss2 h2.
  assert (j1:= WcbvEvals_wcbvEvals h1).
  assert (j2:= WcbvEvals_wcbvEvals h2).
  destruct j1 as [x1 k1]. destruct j2 as [x2 k2].
  specialize (k1 (max x1 x2)). specialize (k2 (max x1 x2)).
  rewrite k1 in k2. injection k2. intuition. 
  apply max_snd. apply max_fst.
Qed.

End wcbvEval_sec.
