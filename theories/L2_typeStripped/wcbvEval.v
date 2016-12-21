
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.JMeq.
Require Import L2.term.
Require Import L2.program.
Require Import L2.awndEval.
Require Import L2.wndEval.
        
Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.


(** Relational version of weak cbv evaluation  **)
Inductive WcbvEval (p:environ Term) : Term -> Term -> Prop :=
| wLam: forall nm bod, WcbvEval p (TLambda nm bod) (TLambda nm bod)
| wProd: forall nm bod, WcbvEval p (TProd nm bod) (TProd nm bod)
| wCast: forall t s, WcbvEval p t s -> WcbvEval p (TCast t) s
| wProof: forall t s, WcbvEval p t s -> WcbvEval p (TProof t) s
| wConstruct: forall i r arty,
                WcbvEval p (TConstruct i r arty) (TConstruct i r arty)
| wInd: forall i, WcbvEval p (TInd i) (TInd i) 
| wSort: forall srt, WcbvEval p (TSort srt) (TSort srt)
| wFix: forall dts m, WcbvEval p (TFix dts m) (TFix dts m)
| wAx: WcbvEval p TAx TAx
| wConst: forall nm (t s:Term),
            lookupDfn nm p = Ret t -> WcbvEval p t s ->
            WcbvEval p (TConst nm) s
| wAppLam: forall (fn bod a1 a1' s:Term) (args:Terms) (nm:name),
               WcbvEval p fn (TLambda nm bod) ->
               WcbvEval p a1 a1' ->
               WcbvEval p (whBetaStep bod a1' args) s ->
               WcbvEval p (TApp fn a1 args) s
| wLetIn: forall (nm:name) (dfn bod dfn' s:Term),
            WcbvEval p dfn dfn' ->
            WcbvEval p (instantiate dfn' 0 bod) s ->
            WcbvEval p (TLetIn nm dfn bod) s
| wAppFix: forall dts m z (fn arg arg' s x t:Term)
                  (args args':Terms) (ix:nat),
             WcbvEval p fn (TFix dts m) ->
             WcbvEvals p (tcons arg args) (tcons arg' args') ->             
             dnthBody m dts = Some (x, ix) ->
             tnth ix (tcons arg' args') = Some t ->
             canonicalP t = Some z ->   (* test Fix is guarded *)
             WcbvEval p (pre_whFixStep x dts (tcons arg' args')) s ->
             WcbvEval p (TApp fn arg args) s 
| wAppCong: forall fn fn' arg args aargs',
              WcbvEval p fn fn' ->
              ~ isLambda fn' -> ~ isFix fn' ->
              WcbvEvals p (tcons arg args) aargs' ->
              WcbvEval p (TApp fn arg args) (mkApp fn' aargs')
| wAppFixCong: forall dts m (fn arg arg' x t:Term)
                  (args args':Terms) (ix:nat),
             WcbvEval p fn (TFix dts m) ->
             WcbvEvals p (tcons arg args) (tcons arg' args') ->
             dnthBody m dts = Some (x, ix) ->
             tnth ix (tcons arg' args') = Some t ->
             canonicalP t = None ->   (* Fix not guarded *)
             WcbvEval p (TApp fn arg args) (TApp (TFix dts m) arg' args')
| wAppFixCong1: forall dts m (fn arg arg' x:Term)
                  (args args':Terms) (ix:nat),
             WcbvEval p fn (TFix dts m) ->
             WcbvEvals p (tcons arg args) (tcons arg' args') ->
             dnthBody m dts = Some (x, ix) ->
             tnth ix (tcons arg' args') = None ->  (* to few args *)
             WcbvEval p (TApp fn arg args) (TApp (TFix dts m) arg' args')
| wCase: forall mch Mch n args ml ts brs cs s arty,
                WcbvEval p mch Mch ->
                canonicalP Mch = Some (n, args, arty) ->
                tskipn (snd (fst ml)) args = Some ts ->
                whCaseStep n ts brs = Some cs ->
                WcbvEval p cs s ->
                WcbvEval p (TCase ml mch brs) s
| wCaseCong: forall mch Mch ml brs brs',
             WcbvEval p mch Mch ->
             canonicalP Mch = None ->
             WcbvEvals p brs brs' ->           
             WcbvEval p (TCase ml mch brs) (TCase ml Mch brs')
| wWrong: WcbvEval p TWrong TWrong
with WcbvEvals (p:environ Term) : Terms -> Terms -> Prop :=
| wNil: WcbvEvals p tnil tnil
| wCons: forall t t' ts ts',
           WcbvEval p t t' -> WcbvEvals p ts ts' -> 
           WcbvEvals p (tcons t ts) (tcons t' ts').
Hint Constructors WcbvEval WcbvEvals.
Scheme WcbvEval1_ind := Induction for WcbvEval Sort Prop
     with WcbvEvals1_ind := Induction for WcbvEvals Sort Prop.
Combined Scheme WcbvEvalEvals_ind from WcbvEval1_ind, WcbvEvals1_ind.

(** when reduction stops **)
Definition no_Wcbv_step (p:environ Term) (t:Term) : Prop :=
  no_step (WcbvEval p) t.
Definition no_Wcbvs_step (p:environ Term) (ts:Terms) : Prop :=
  no_step (WcbvEvals p) ts.

(** evaluate omega = (\x.xx)(\x.xx): nontermination **)
Definition xx := (TLambda nAnon (TApp (TRel 0) (TRel 0) tnil)).
Definition xxxx := (TApp xx xx tnil).
Goal WcbvEval nil xxxx xxxx.
unfold xxxx, xx.
eapply wAppLam; repeat (try constructor; try omega; try not_isApp).
change (WcbvEval nil xxxx xxxx).
Abort.
             

Lemma WcbvEval_mkApp_nil:
  forall t, WFapp t -> forall p s, WcbvEval p t s ->
                 WcbvEval p (mkApp t tnil) s.
Proof.
  intros p. induction 1; simpl; intros; try assumption.
  - rewrite tappend_tnil. assumption.
Qed.

(*******  move to somewhere  ********)
Lemma lookup_pres_WFapp:
    forall p, WFaEnv p -> forall nm ec, lookup nm p = Some ec -> WFaEc ec.
Proof.
  induction 1; intros nn ed h.
  - inversion_Clear h.
  - case_eq (string_eq_bool nn nm); intros j.
    + cbn in h. rewrite j in h. myInjection h. assumption.
    + cbn in h. rewrite j in h. eapply IHWFaEnv. eassumption.
Qed.
(**************************************************)

Lemma WcbvEvals_tcons_tcons:
  forall p arg args brgs, WcbvEvals p (tcons arg args) brgs ->
                          exists crg crgs, brgs = (tcons crg crgs).
Proof.
  inversion 1. exists t', ts'. reflexivity.
Qed.

Lemma WcbvEvals_tcons_tcons':
  forall p arg brg args brgs,
    WcbvEvals p (tcons arg args) (tcons brg brgs) ->
    WcbvEval p arg brg /\ WcbvEvals p args brgs.
Proof.
  inversion 1. intuition.
Qed.

(** wcbvEval preserves WFapp **)
Lemma WcbvEval_pres_WFapp:
  forall p, WFaEnv p -> 
  (forall t s, WcbvEval p t s -> WFapp t -> WFapp s) /\
  (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> WFapps ss).
Proof.
  intros p hp.
  apply WcbvEvalEvals_ind; intros; try assumption;
  try (solve[inversion_Clear H0; intuition]);
  try (solve[inversion_Clear H1; intuition]).
  - apply H. unfold lookupDfn in e. case_eq (lookup nm p); intros xc.
    + intros k. assert (j:= lookup_pres_WFapp hp _ k)
      . rewrite k in e. destruct xc. 
      * myInjection e. inversion j. assumption.
      * discriminate.
    + rewrite xc in e. discriminate.
  - inversion_clear H2. apply H1.
    specialize (H H4). inversion_Clear H.
    apply (whBetaStep_pres_WFapp); intuition. 
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp; intuition.
  - inversion_clear H2. specialize (H H4). inversion_Clear H.
    assert (j: WFapps (tcons arg args)).
    { constructor; assumption. }
    apply H1. apply pre_whFixStep_pres_WFapp; try eassumption; intuition.
    + eapply dnthBody_pres_WFapp; try eassumption.
  - inversion_Clear H1.
    destruct (WcbvEvals_tcons_tcons w0) as [x0 [x1 jx]]. subst.    
    destruct (mkApp_isApp_lem fn' x0 x1) as
        [y0 [y1 [y2 [ka [[kc1 [kc2 [kc3 kc4]]] | [kd1 [kd2 kd3]]]]]]];
      rewrite ka.
    + subst. cbn.
      assert (j: WFapps (tcons arg args)). constructor; assumption.
      specialize (H0 j). inversion_Clear H0.
      constructor; intuition.
    + destruct kd1 as [z0 [z1 [z2 kz]]]. rewrite kz in ka. cbn in ka.
      myInjection ka. specialize (H H6). inversion_Clear H.
      assert (k:= tappend_tcons_tunit _ _ _ _ H1).
      rewrite <- k. constructor; try assumption.
      rewrite <- tappend_assoc. cbn. apply tappend_pres_WFapps; try assumption.
      apply H0. constructor; try assumption.
  - inversion_Clear H1. specialize (H H6).
    assert (k: WFapps (tcons arg args)). intuition.
    specialize (H0 k). inversion_Clear H0.
    constructor; try assumption. not_isApp.
  - inversion_Clear H1. specialize (H H6).
    assert (k: WFapps (tcons arg args)). intuition.
    specialize (H0 k). inversion_Clear H0.
    constructor; try assumption. not_isApp.
  - apply H0. inversion_Clear H1. 
    refine (whCaseStep_pres_WFapp H6 _ _ e1). 
    refine (tskipn_pres_WFapp _ _ e0).
    refine (canonicalP_pres_WFapp _ e). intuition.
Qed.

Lemma WcbvEval_weaken:
  forall p,
    (forall t s, WcbvEval p t s ->
                 forall nm ec, Crct ((nm,ec)::p) 0 prop ->
                               WcbvEval ((nm,ec)::p) t s) /\
    (forall ts ss, WcbvEvals p ts ss ->
                   forall nm ec, Crct ((nm,ec)::p) 0 prop ->
                                 WcbvEvals ((nm,ec)::p) ts ss).
Proof.
  intros p. apply WcbvEvalEvals_ind; intros; auto.
  - destruct (string_dec nm nm0).
    + subst. inversion_Clear H0.
      * unfold lookupDfn in e.
        rewrite (proj1 (fresh_lookup_None (trm:=Term) _ _) H8) in e.
        discriminate.
      * unfold lookupDfn in e.
        rewrite (proj1 (fresh_lookup_None (trm:=Term) _ _) H8) in e.
        discriminate. 
    + eapply wConst.
      * rewrite <- (lookupDfn_weaken' n). eassumption. 
      * apply H. assumption. 
  - eapply wAppLam.
    + apply H. assumption.
    + apply H0. assumption.
    + apply H1. assumption.
  - eapply wLetIn.
    + apply H. assumption.
    + apply H0. assumption.
  - eapply wAppFix; try eassumption; intuition. 
  - eapply wAppFixCong; try eassumption; intuition.
  - eapply wAppFixCong1; try eassumption; intuition.    
  - eapply wCase; intuition; eassumption.
Qed.


Lemma WcbvEval_strengthen:
  forall pp,
  (forall t s, WcbvEval pp t s -> forall nm ec p, pp = (nm,ec)::p ->
       Crct p 0 t -> WcbvEval p t s) /\
  (forall ts ss, WcbvEvals pp ts ss -> forall nm ec p, pp = (nm,ec)::p ->
       Crcts p 0 ts -> WcbvEvals p ts ss).
Proof.
  Admitted.
(***
  intros pp. apply WcbvEvalEvals_ind; intros; auto; subst.
  - constructor. eapply H. reflexivity.
    destruct ec.
    + econstructor. try econstructor; try assumption.
    intros h. destruct H1. constructor. assumption.
  - assert (j:= not_eq_sym (notPocc_TConst H1)).
    assert (j1:= Lookup_strengthen l eq_refl j).
    econstructor.
    + unfold LookupDfn. eassumption.
    + eapply H. reflexivity. eapply (proj1 Crct_fresh_Pocc). eapply
       
      intros h. destruct H1. constructor. assumption.

Lemma WcbvEval_strengthen:
  forall pp, Crct pp 0 prop ->
  (forall t s, WcbvEval pp t s -> forall nm ec p, pp = (nm,ec)::p ->
       ~ PoccTrm nm t -> WcbvEval p t s) /\
  (forall ts ss, WcbvEvals pp ts ss -> forall nm ec p, pp = (nm,ec)::p ->
       ~ PoccTrms nm ts -> WcbvEvals p ts ss).
Proof.
  intros pp hpp. apply WcbvEvalEvals_ind; intros; auto; subst.
  - constructor. eapply H. reflexivity.
    intros h. destruct H1. constructor. assumption.
  - assert (j:= not_eq_sym (notPocc_TConst H1)).
    assert (j1:= Lookup_strengthen l eq_refl j).
    econstructor.
    + unfold LookupDfn. eassumption.
    + eapply H. reflexivity. eapply (proj1 Crct_fresh_Pocc). eapply
       
      intros h. destruct H1. constructor. assumption.
 **************)

(***
Lemma WcbvEval_pres_Crct:
  (forall p n t, Crct p n t ->
                 forall t', WcbvEval p t t' -> Crct p n t') /\
  (forall p n ts, Crcts p n ts ->
                  forall ts', WcbvEvals p ts ts' -> Crcts p n ts') /\
  (forall p n ds, CrctDs p n ds -> True) /\
  (forall p n itp, CrctTyp p n itp -> True).
Proof.
  apply CrctCrctsCrctDsTyp_ind; intros; try (solve[constructor; trivial]).
  - inversion_Clear H; constructor.
  - inversion_Clear H; constructor.
  - apply CrctWkTrmTrm; try assumption. apply H0.
    eapply (proj1 (WcbvEval_strengthen p)).


Goal    
  forall p, Crct p 0 prop ->
    (forall t t', WcbvEval p t t' -> Crct p 0 t) /\
    (forall ts ts', WcbvEvals p ts ts' -> Crcts p 0 ts).
Proof.
  intros p hp.
  apply WcbvEvalEvals_ind; intros; try (solve[constructor; trivial]).
  - eapply Crct_Prf. eassumption.
  - constructor.
    
Lemma WcbvEval_pres_Crct:
  forall p,
    (forall t t', WcbvEval p t t' -> Crct p 0 t -> Crct p 0 t') /\
    (forall ts ts', WcbvEvals p ts ts' -> Crcts p 0 ts -> Crcts p 0 ts').
Proof.
  intros p.
  apply WcbvEvalEvals_ind; intros; try reflexivity; try assumption;
  try (solve[constructor; trivial]).
  - apply H. inversion_Clear H0; try assumption.
    + apply (proj1 Crct_weaken); try assumption. apply (Crct_invrt_Cast H1).
      reflexivity.
    + apply (proj1 Crct_Typ_weaken); try assumption.
      apply (Crct_invrt_Cast H1). reflexivity.
  - apply H. destruct (Crct_invrt_Const H0 eq_refl) as [j0 [pd [j1 j2]]].
    unfold LookupDfn in *. assert (k:= Lookup_single_valued l j1).
    myInjection k. assumption.
  - apply H1. destruct (Crct_invrt_App H2 eq_refl) as [j0 [j1 [j2 j3]]].
    specialize (H j0).
    assert (j4:= Crct_invrt_Lam H eq_refl).
    apply whBetaStep_pres_Crct; try assumption.
    apply H0. assumption.
  - destruct (Crct_invrt_LetIn H1 eq_refl). apply H0.
    apply instantiate_pres_Crct; try assumption. apply H. assumption.
    omega.
  - destruct (Crct_invrt_App H1 eq_refl) as [j0 [j1 [j2 j3]]]. clear H1.
    specialize (H j0). assert (k:= Crct_invrt_Fix H eq_refl). clear H.    
    apply H0. unfold pre_whFixStep. apply mkApp_pres_Crct.
    apply fold_left_pres_Crct. intros. apply instantiate_pres_Crct; try omega.
    apply Crct_up; assumption.
    constructor; try assumption. eapply Crct_Sort; eassumption.
    refine (CrctDs_invrt _ _ e). cbn in k. admit.
    constructor; assumption.
  -

Qed.
****)

Lemma WcbvEval_wndEvalRTC:
  forall (p:environ Term), WFaEnv p ->
    (forall t s, WcbvEval p t s -> WFapp t -> wndEvalRTC p t s) /\
    (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> wndEvalsRTC p ts ss).
Proof.
  intros p hp. apply WcbvEvalEvals_ind; intros; try (solve [constructor]).
  - eapply wERTCtrn. apply wERTCstep. apply sCast. apply H. 
    inversion_Clear H0. assumption.
  - eapply wERTCtrn. apply wERTCstep. apply sProof. apply H. 
    inversion_Clear H0. assumption.
  - eapply wERTCtrn; intuition.
    eapply wERTCtrn.
    + apply wERTCstep. apply sConst. apply lookupDfn_LookupDfn. eassumption.
    + apply H. eapply (lookupDfn_pres_WFapp hp).  eassumption.
  - inversion_Clear H2.
    eapply (@wERTCtrn _ _ (TApp (TLambda nm bod) a1 args)).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; try assumption. intuition.
    + eapply (@wERTCtrn _ _ (TApp (TLambda nm bod) a1' args)).
      * eapply wndEvalRTC_App_arg; try reflexivity.
        apply H0. assumption.
      * { apply (@wERTCtrn _ _ (whBetaStep bod a1' args)).
          - apply wERTCstep. apply sBeta. 
          - apply H1. apply whBetaStep_pres_WFapp; try eassumption.
            + assert (j:= proj1 (WcbvEval_pres_WFapp hp) _ _ w H7).
              inversion_Clear j. assumption.
            + apply (proj1 (WcbvEval_pres_WFapp hp) _ _ w0 H8). }
  - inversion_Clear H1. eapply (@wERTCtrn _ _ (TLetIn nm dfn' bod)).
    + apply wndEvalRTC_LetIn_dfn. intuition.
    + eapply wERTCtrn. apply wERTCstep. apply sLetIn. apply H0.
      apply instantiate_pres_WFapp; try assumption.
      * eapply (proj1 (WcbvEval_pres_WFapp hp)); try eassumption.
  - inversion_clear H2. specialize (H H4).
    assert (j0: WFapps (tcons arg args)).
    { constructor; assumption. }
    assert (j2: WFapp (TFix dts m)).
    { refine (proj1 (WcbvEval_pres_WFapp hp) _ _ w _). assumption. }
    inversion_clear j2.
    assert (j3: WFapp x).
    { refine (dnthBody_pres_WFapp _ _ e). assumption. }
    specialize (H0 j0).
    assert (j4: WFapp (pre_whFixStep x dts (tcons arg' args'))).
    { refine (pre_whFixStep_pres_WFapp _ _ _); try assumption.
      eapply (proj2 (WcbvEval_pres_WFapp hp)); eassumption. }
    specialize (H1 j4).
    refine (@wERTCtrn _ _ (TApp (TFix dts m) arg args) _ _ _).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; assumption.
    + eapply (@wERTCtrn _ _ (TApp (TFix dts m) arg' args')).
      eapply (wndEvalsRTC_App_args); try reflexivity; try eassumption.
      * not_isApp.
      * { eapply (@wERTCtrn _ _  (pre_whFixStep x dts (tcons arg' args'))).
          - eapply wERTCstep. eapply sFix; try eassumption.
          - assumption. }
  - inversion_Clear H1. specialize (H H6). specialize (H0 (wfacons H7 H8)).
    destruct (WcbvEvals_tcons_tcons w0) as [x0 [x1 jx]]. subst.
    eapply (@wERTCtrn _ _ (TApp fn x0 x1)).
    + eapply wndEvalsRTC_App_args; try reflexivity; try assumption.
    + rewrite <- mkApp_goodFn; try assumption.      
      assert (j: WFapps (tcons x0 x1)).
      { apply (proj2 (WcbvEval_pres_WFapp hp) _ _ w0).
        constructor; assumption. }
      inversion_Clear j.
      eapply wndEvalRTC_App_fn; try assumption.
  - inversion_Clear H1. specialize (H H6).
    assert (k: WFapps (tcons arg args)). intuition.
    specialize (H0 k).
    eapply (@wERTCtrn _ _ (TApp (TFix dts m) arg args)).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; assumption.
    + eapply (@wERTCtrn _ _ (mkApp (TFix dts m) (tcons arg' args'))).
      * rewrite mkApp_goodFn.
        eapply wndEvalsRTC_App_args; try reflexivity; try assumption.
        not_isApp. not_isApp.
      * { eapply (@wERTCtrn _ _ (TApp (TFix dts m) arg' args')).
          - eapply wndEvalsRTC_App_args; try reflexivity.
            + apply wndEvalsRTC_mk_tconsr; try assumption. constructor.
            + not_isApp.
          - constructor. }
  - inversion_Clear H1. specialize (H H6).
    assert (k: WFapps (tcons arg args)). intuition.
    specialize (H0 k).
    eapply (@wERTCtrn _ _ (TApp (TFix dts m) arg args)).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; assumption.
    + eapply (@wERTCtrn _ _ (mkApp (TFix dts m) (tcons arg' args'))).
      * rewrite mkApp_goodFn.
        eapply wndEvalsRTC_App_args; try reflexivity; try assumption.
        not_isApp. not_isApp.
      * { eapply (@wERTCtrn _ _ (TApp (TFix dts m) arg' args')).
          - eapply wndEvalsRTC_App_args; try reflexivity.
            + apply wndEvalsRTC_mk_tconsr; try assumption. constructor.
            + not_isApp.
          - constructor. }
    - inversion_Clear H1. eapply wERTCtrn. 
    + eapply wndEvalRTC_Case_mch. apply H. assumption.
    + eapply (@wERTCtrn _ _ cs). 
      * apply wERTCstep. eapply sCase; eassumption.
      * { apply H0. refine (whCaseStep_pres_WFapp _ _ _ e1). assumption.
          refine (tskipn_pres_WFapp _ _ e0).
          refine (canonicalP_pres_WFapp _ e).
          specialize (H H4).
          refine (wndEvalRTC_pres_WFapp _ _ _); eassumption. }
  - inversion_Clear H1. eapply wERTCtrn.
    + eapply wndEvalRTC_Case_mch. apply H. assumption.
    + eapply (@wERTCtrn _ _  (TCase ml Mch brs)).
      * apply wERTCrfl. 
      * eapply (@wERTCtrn _ _  (TCase ml Mch brs')).
        apply wndEvalRTC_Case_brs. intuition.
        constructor.
  - inversion_Clear H1. eapply (@wEsRTCtrn _ _ (tcons t' ts)).
    + apply wndEvalsRTC_tcons_hd. apply H. assumption.
    + apply wndEvalsRTC_tcons_tl. apply H0. assumption.
Qed.


(** WcbvEval is in the transitive closure of wndEval **)
(**
Lemma WcbvEval_wndEvalTC:
  forall (p:environ),
    (forall t s, WcbvEval p t s -> t <> s -> wndEvalTC p t s) /\
    (forall ts ss, WcbvEvals p ts ss -> ts <> ss -> wndEvalsTC p ts ss).
intros p. apply WcbvEvalEvals_ind; intros; try (nreflexivity H).
**)

(***
Lemma wcbvEval_no_further:
  forall p,
  (forall t s, WcbvEval p t s -> WcbvEval p s s) /\
  (forall ts ss, WcbvEvals p ts ss -> WcbvEvals p ss ss).
Proof.
  intros p.
  apply WcbvEvalEvals_ind; simpl; intros; auto.
Qed.
****)


Section wcbvEval_sec.
Variable p:environ Term.

(** now an executable weak-call-by-value evaluation **)
(** use a timer to make this terminate **)
Function wcbvEval
         (tmr:nat) (t:Term) {struct tmr}: exception Term :=
  match tmr with 
    | 0 => raise ("out of time: " ++ print_term t)
    | S n =>
      match t with      (** look for a redex **)
        | TConst nm =>
          match (lookup nm p) with
            | Some (ecTrm t) => wcbvEval n t
                  (** note hack coding of axioms in environment **)
            | Some (ecTyp _ _ _) => raise ("wcbvEval, TConst ecTyp " ++ nm)
            | _ => raise "wcbvEval: TConst environment miss"
          end
        | TCast t =>
          match wcbvEval n t with
            | Ret et => Ret et
            | Exc s => raise ("wcbvEval: TCast: " ++ s)
          end
        | TProof t =>
          match wcbvEval n t with
            | Ret et => Ret et
            | Exc s => raise ("wcbvEval: TProof: " ++ s)
          end
        | TApp fn a1 args =>
          match wcbvEval n fn with
            | Exc s => raise ("wcbvEval TApp: fn doesn't eval: " ++ s)
            | Ret (TLambda _ bod) =>
              match wcbvEval n a1 with
                | Exc s =>  raise ("wcbvEval TApp: arg doesn't eval: " ++ s)
                | Ret b1 => wcbvEval n (whBetaStep bod b1 args)
              end
            | Ret (TFix dts m) =>           (* Fix redex *)
              match dnthBody m dts with
                | None => raise ("wcbvEval TApp: dnthBody doesn't eval: ")
                | Some (x, ix) =>
                  match wcbvEvals n (tcons a1 args) with
                    | Ret (tcons arg' args') =>
                      match tnth ix (tcons arg' args') with
                        | None => ret (TApp (TFix dts m) arg' args')
                        | Some t =>
                          match canonicalP t with (* test Fix is guarded *)
                            | Some _ =>
                              wcbvEval
                                n (pre_whFixStep x dts (tcons arg' args'))
                            | None => ret (TApp (TFix dts m) arg' args')
                          end
                      end
                    | _ => raise ("wcbvEval TAppFix: args don't eval")
                  end
              end
            | Ret Fn =>              (* no redex; congruence rule *)
              match wcbvEvals n (tcons a1 args) with
                | Exc s => raise ("wcbvEval TApp: args don't eval: " ++ s)
                | Ret ergs => ret (mkApp Fn ergs)
              end
          end
        | TCase ml mch brs =>
          match wcbvEval n mch with
            | Exc str => Exc str
            | Ret emch =>
              match canonicalP emch with
                | None =>
                  match wcbvEvals n brs with
                    | Exc _ => Exc ("wcbvEval; TCase, brs don't eval")
                    | Ret ebrs => Ret (TCase ml emch ebrs)
                  end
                | Some (r, args, arty) =>
                  match tskipn (snd (fst ml)) args with
                    | None => raise "wcbvEval: Case, tskipn"
                    | Some ts =>
                      match whCaseStep r ts brs with
                        | None => raise "wcbvEval: Case, whCaseStep"
                        | Some cs => wcbvEval n cs
                      end
                  end
              end
          end
        | TLetIn nm df bod =>
          match wcbvEval n df with
            | Ret df' => wcbvEval n (instantiate df' 0 bod)
            | Exc s => raise ("wcbvEval: TLetIn: " ++ s)
          end
        (** already in whnf ***)
        | TAx => ret TAx
        | TLambda nn t => ret (TLambda nn t)
        | TProd nn t => ret (TProd nn t)
        | TFix mfp br => ret (TFix mfp br)
        | TConstruct i cn arty => ret (TConstruct i cn arty)
        | TInd i => ret (TInd i)
        | TSort srt => ret (TSort srt)
        (** should never appear **)
        | TRel _ => raise "wcbvEval: unbound Rel"
        | TWrong => ret TWrong
      end
  end
with wcbvEvals (tmr:nat) (ts:Terms) {struct tmr}
     : exception Terms :=
       (match tmr with 
          | 0 => raise "out of time"
          | S n => match ts with             (** look for a redex **)
                     | tnil => ret tnil
                     | tcons s ss =>
                       match wcbvEval n s, wcbvEvals n ss with
                         | Ret es, Ret ess => ret (tcons es ess)
                         | Exc s, _ => raise s
                         | Ret _, Exc s => raise s
                       end
                   end
        end).
Functional Scheme wcbvEval_ind' := Induction for wcbvEval Sort Prop
with wcbvEvals_ind' := Induction for wcbvEvals Sort Prop.
Combined Scheme wcbvEvalEvals_ind from wcbvEval_ind', wcbvEvals_ind'.

(** wcbvEval and WcbvEval are the same relation **)
Lemma wcbvEval_WcbvEval:
  forall tmr,
  (forall t s, wcbvEval tmr t = Ret s -> WcbvEval p t s) /\
  (forall ts ss, wcbvEvals tmr ts = Ret ss -> WcbvEvals p ts ss).
Proof.
  intros tmr.
  apply (wcbvEvalEvals_ind
           (fun tmr t su => forall u (p1:su = Ret u), WcbvEval p t u)
           (fun tmr t su => forall u (p1:su = Ret u), WcbvEvals p t u));
    intros; try discriminate; try (myInjection p1);
    try(solve[constructor]); intuition.
  - eapply wConst; intuition.
    + unfold lookupDfn. rewrite e1. reflexivity. 
  - specialize (H1 _ p1). specialize (H _ e1). specialize (H0 _ e2).
    eapply wAppLam; eassumption.
  - specialize (H _ e1). specialize (H0 _ e3).
    eapply wAppFixCong1; try eassumption.
  - specialize (H1 _ p1). specialize (H _ e1). specialize (H0 _ e3).
    eapply wAppFix; try eassumption.
  - specialize (H _ e1). specialize (H0 _ e3).
    eapply wAppFixCong; try eassumption.
  - specialize (H _ e1). specialize (H0 _ e2).
     eapply wAppCong; try eassumption.
    + destruct Fn; try not_isLambda. auto.
    + destruct Fn; try not_isFix. auto.
  - eapply wCase; try eassumption.
    + apply H; eassumption.
    + apply H0; eassumption. 
  - eapply wLetIn; intuition.
    + apply H. assumption.
Qed.

(** need strengthening to large-enough fuel to make the induction
 *** go through **)
Lemma pre_WcbvEval_wcbvEval:
  (forall t s, WcbvEval p t s ->
               exists n, forall m, m >= n -> wcbvEval (S m) t = Ret s) /\
  (forall ts ss, WcbvEvals p ts ss ->
                 exists n, forall m, m >= n -> wcbvEvals (S m) ts = Ret ss).
  assert (j:forall m x, m > x -> m = S (m - 1)).
  { induction m; intuition. }
  apply WcbvEvalEvals_ind; intros; try (exists 0; intros mx h; reflexivity).
  - destruct H. exists (S x). intros m hm. simpl. rewrite (j m x); try omega.
    + rewrite (H (m - 1)); try omega. reflexivity.
  - destruct H. exists (S x). intros mm h. cbn.
    rewrite (j mm x); try omega. rewrite H. reflexivity. omega.
  - destruct H. exists (S x). intros mm h. simpl.
    rewrite (j mm x); try omega.
    unfold lookupDfn in e. destruct (lookup nm p). destruct e0. myInjection e.
    + rewrite H. reflexivity. omega.
    + discriminate.
    + discriminate.
  - destruct H, H0, H1. exists (S (max x (max x0 x1))). intros m h.
    assert (j1:= max_fst x (max x0 x1)). 
    assert (lx: m > x). omega.
    assert (j2:= max_snd x (max x0 x1)).
    assert (j3:= max_fst x0 x1).
    assert (lx0: m > x0). omega.
    assert (j4:= max_snd x0 x1).
    assert (j5:= max_fst x0 x1).
    assert (lx1: m > x1). omega.
    assert (k:wcbvEval m fn = Ret (TLambda nm bod)).
    + rewrite (j m (max x (max x0 x1))). apply H.
      assert (l:= max_fst x (max x0 x1)); omega. omega.
    + assert (k0:wcbvEval m a1 = Ret a1').
      * rewrite (j m (max x (max x0 x1))). apply H0. 
        assert (l:= max_snd x (max x0 x1)). assert (l':= max_fst x0 x1).
        omega. omega.
      * simpl. rewrite (j m 0); try omega.
        rewrite H; try omega. rewrite H0; try omega. rewrite H1; try omega.
        reflexivity.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
    rewrite H0; try omega. reflexivity.
  - destruct H, H0, H1. exists (S (max x2 (max x0 x1))). intros mx h.
    assert (j1:= max_fst x2 (max x0 x1)). 
    assert (lx: mx > x2). omega.
    assert (j2:= max_snd x2 (max x0 x1)).
    assert (j3:= max_fst x0 x1).
    assert (lx0: mx > x0). omega.
    assert (j4:= max_snd x0 x1).
    assert (j5:= max_fst x0 x1).
    assert (lx1: mx > x1). omega.
    cbn. rewrite (j mx (max x2 (max x0 x1))); try omega.
    rewrite H; try omega. rewrite e. rewrite H0; try omega.
    rewrite H1. destruct ix; cbn in e0.
    + myInjection e0. rewrite e1. reflexivity.
    + rewrite e0. rewrite e1. reflexivity.
    + omega.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    cbn. rewrite (j mx x); try omega. rewrite (H0 (mx - 1)); try omega.
    rewrite (H (mx - 1)); try omega.
    destruct fn'; try reflexivity.
    + elim n; auto.
    + elim n0; auto.
  - destruct H, H0. exists (S (max x1 x0)). intros mx h.
    assert (l1:= max_fst x1 x0). assert (l2:= max_snd x1 x0).
    cbn. rewrite (j mx x1); try omega. rewrite (H (mx - 1)); try omega.
    rewrite e. rewrite H0; try omega. destruct ix; cbn in e0.
    + myInjection e0. rewrite e1. reflexivity.
    + rewrite e0. rewrite e1. reflexivity.
  - destruct H, H0. exists (S (max x1 x0)). intros mx h.
    assert (l1:= max_fst x1 x0). assert (l2:= max_snd x1 x0).
    cbn. rewrite (j mx x1); try omega. rewrite (H (mx - 1)); try omega.
    rewrite e. rewrite H0; try omega. destruct ix; cbn in e0.
    + discriminate.
    + rewrite e0. reflexivity.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    cbn. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
    rewrite e. rewrite e0. rewrite e1. rewrite (H0 (mx - 1)); try omega.
    reflexivity.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    cbn. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
    rewrite e. rewrite H0; try omega.
    reflexivity.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
    rewrite H0; try omega. reflexivity.
Qed.

Lemma WcbvEval_wcbvEval:
  forall t s, WcbvEval p t s ->
             exists n, forall m, m >= n -> wcbvEval m t = Ret s.
Proof.
  intros t s h.
  destruct (proj1 pre_WcbvEval_wcbvEval _ _ h).
  exists (S x). intros m hm. specialize (H (m - 1)).
  assert (k: m = S (m - 1)). { omega. }
  rewrite k. apply H. omega.
Qed.

Lemma WcbvEval_single_valued:
  forall t s, WcbvEval p t s -> forall u, WcbvEval p t u -> s = u.
Proof.
  intros t s h0 u h1.
  assert (j0:= WcbvEval_wcbvEval h0).
  assert (j1:= WcbvEval_wcbvEval h1).
  destruct j0 as [x0 k0].
  destruct j1 as [x1 k1].
  specialize (k0 (max x0 x1) (max_fst x0 x1)).
  specialize (k1 (max x0 x1) (max_snd x0 x1)).
  rewrite k0 in k1. injection k1. intuition.
Qed.
  
End wcbvEval_sec.
