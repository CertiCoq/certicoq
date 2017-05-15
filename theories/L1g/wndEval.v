
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Setoids.Setoid.
Require Import Coq.omega.Omega.
Require Import Common.Common.
Require Import L1g.compile.
Require Import L1g.term.
Require Import L1g.program.
Require Import L1g.awndEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(*** non-deterministic small step evaluation relation ***)
Section Env.
Variable p: environ Term.
Inductive wndEval : Term -> Term -> Prop :=
(*** contraction steps ***)
| sConst: forall (s:string) (t:Term),
            LookupDfn s p t -> wndEval (TConst s) t
| sBeta: forall (nm:name) (ty bod arg:Term) (args:Terms),
           wndEval (TApp (TLambda nm ty bod) arg args)
                   (whBetaStep bod arg args)
     (* note: [instantiate] is total *)
| sLetIn: forall (nm:name) (dfn ty bod:Term),
            wndEval (TLetIn nm dfn ty bod) (instantiate dfn 0 bod)
     (* Case argument must be in Canonical form *)
     (* n is the number of parameters of the datatype *)
| sCase: forall (ml:inductive * nat) (ty s mch:Term)
                 (args ts:Terms) (brs:Brs) (n:nat),
            canonicalP mch = Some (n, args) ->
            tskipn (snd ml) args = Some ts ->
            whCaseStep n ts brs = Some s ->
            wndEval (TCase ml ty mch brs) s
| sFix: forall (dts:Defs) (m:nat) (arg:Term) (args:Terms)
               (x:Term) (ix:nat),
          (** ix is index of recursive argument **)
          dnthBody m dts = Some (x, ix) ->
          ix <= tlength args ->
          wndEval (TApp (TFix dts m) arg args)
                  (pre_whFixStep x dts (tcons arg args))
| sCast: forall t ty, wndEval (TCast t ty) t
| sProof: forall t, wndEval (TProof t) t
(*** congruence steps ***)
(** no xi rules: sLambdaR, sProdR, sLetInR,
*** no congruence on Case branches 
*** congruence on type of Fix ***)
| sAppFn:  forall (t r arg:Term) (args:Terms),
              wndEval t r ->
              wndEval (TApp t arg args) (mkApp r (tcons arg args))
| sAppArgs: forall (t arg brg:Term) (args brgs:Terms),
              wndEvals (tcons arg args) (tcons brg brgs) ->
              wndEval (TApp t arg args) (TApp t brg brgs)
| sProdTy:  forall (nm:name) (t1 t2 bod:Term),
              wndEval t1 t2 ->
              wndEval (TProd nm t1 bod) (TProd nm t2 bod)
| sLamTy:   forall (nm:name) (t1 t2 bod:Term),
              wndEval t1 t2 ->
              wndEval (TLambda nm t1 bod) (TLambda nm t2 bod)
| sLetInTy: forall (nm:name) (t1 t2 d bod:Term),
              wndEval t1 t2 ->
              wndEval (TLetIn nm d t1 bod) (TLetIn nm d t2 bod)
| sLetInDef:forall (nm:name) (t d1 d2 bod:Term),
              wndEval d1 d2 ->
              wndEval (TLetIn nm d1 t bod) (TLetIn nm d2 t bod)
| sCaseTy:  forall (nl:inductive * nat)
                   (ty uy mch:Term) (brs:Brs),
              wndEval ty uy ->
              wndEval (TCase nl ty mch brs) (TCase nl uy mch brs)
| sCaseArg: forall (nl:inductive * nat)
                   (ty mch can:Term) (brs:Brs),
              wndEval mch can ->
              wndEval (TCase nl ty mch brs) (TCase nl ty can brs)
with wndEvals : Terms -> Terms -> Prop :=
     | saHd: forall (t r:Term) (ts:Terms), 
               wndEval t r ->
               wndEvals (tcons t ts) (tcons r ts)
     | saTl: forall (t:Term) (ts ss:Terms),
               wndEvals ts ss ->
               wndEvals (tcons t ts) (tcons t ss).
Hint Constructors wndEval wndEvals.
Scheme wndEval1_ind := Induction for wndEval Sort Prop
     with wndEvals1_ind := Induction for wndEvals Sort Prop.
Combined Scheme wndEvalEvals_ind from wndEval1_ind, wndEvals1_ind.

(** example: evaluate omega = (\x.xx)(\x.xx): nontermination **)
Definition xx := (TLambda nAnon prop (TApp (TRel 0) (TRel 0) tnil)).
Definition xxxx := (TApp xx xx tnil).
Goal wndEval xxxx xxxx.
unfold xxxx, xx. eapply sBeta. 
Qed.

(**************
Lemma wndEval_not_rfl:
  Crct p 0 prop ->
  (forall t t', wndEval t t' -> t <> t') /\
  (forall ts ts', wndEvals ts ts' -> ts <> ts').
Proof.
  intros hp. apply wndEvalEvals_ind; intros.
  - unfold LookupDfn in l. assert (j:= LookupDfn_lookupDfn l eq_refl).
    unfold  lookupDfn in j. destruct (lookup s p).
    + destruct e. myInjection j. Check (proj1 Crct_not_bad_Lookup).
  

  
  apply (wf_ind TrmSize (fun t => ~ wndEval t t)).
  intros t whih. destruct t; intros h; try (solve[inversion h]).
  - inversion h. assert (j := f_equal TrmSize H3). simpl in j. omega.
  - inversion_Clear h. eapply whih; try eassumption.
    simpl. omega.  
  - inversion_Clear h. eapply whih; try eassumption.
    simpl. omega.
  - inversion_Clear h.
    + eapply whih; try eassumption.
      * simpl. admit.
      * 
    +   

    induction t; intros h; try (solve[inversion h]);
  try (solve[inversion h; contradiction]).
  - inversion h.
    assert (j := f_equal TrmSize H3). simpl in j. omega.
  - inversion_Clear h; try contradiction.
    + admit.
  - inversion_Clear h.
    +
Lemma pre_wndEval_not_rfl:
  forall t u, wndEval t u -> t = u -> False.
Proof.
  induction 1; intros.
            
Proof.
  induction t; intros h; try (solve[inversion h]).
  - inversion h.
    assert (j := f_equal TrmSize H3). simpl in j. omega.
  -  inversion h.

     Lemma wndEval_not_rfl:
  forall t, ~ wndEval t t.
Proof.
  induction t; intros h; try (solve[inversion h]).
  - inversion h.
    assert (j := f_equal TrmSize H3). simpl in j. omega.
  -  inversion h.
**********************)
  
Lemma wndEval_tappendl:
  forall bs cs, wndEvals bs cs ->
  forall ds, wndEvals (tappend bs ds) (tappend cs ds).
Proof.
  induction 1; intros.
  - constructor. assumption.
  - simpl. apply saTl. apply IHwndEvals.
Qed.

Lemma wndEval_tappendr:
  forall bs cs, wndEvals bs cs ->
  forall ds, wndEvals (tappend ds bs) (tappend ds cs).
Proof.
  intros bs cs h ds. induction ds; simpl.
  - assumption.
  - apply saTl. apply IHds.
Qed.

Lemma wndEvals_tcons_l:
  forall brgs crgs, wndEvals brgs crgs ->
    forall b bs, brgs = (tcons b bs) ->
                 exists c cs, (crgs = tcons c cs /\
                               ((wndEval b c /\ bs = cs) \/
                                (b = c /\ wndEvals bs cs))).
Proof.
  induction 1; intros; myInjection H0.
  - exists r, bs. auto.
  - exists b, ss. auto.  
Qed.

Lemma wndEvals_tcons_r:
  forall brgs crgs, wndEvals crgs brgs ->
    forall b bs, brgs = (tcons b bs) ->
                 exists c cs, (crgs = tcons c cs /\
                               ((wndEval c b /\ cs = bs) \/
                                (c = b /\ wndEvals cs bs))).
Proof.
  induction 1; intros; myInjection H0.
  - exists t, bs. auto.
  - exists b, ts. auto.  
Qed.

Lemma wndEvals_tcons:
  forall brgs brgs', wndEvals brgs brgs' ->
    forall a1 args, brgs = (tcons a1 args) ->
     forall a1' args', brgs' = (tcons a1' args') ->
    (wndEval a1 a1' /\ args = args') \/ (a1 = a1' /\ wndEvals args args').
Proof.
  induction 1; intros; subst; myInjection H0; myInjection H1; auto.
Qed.

Lemma wndEvals_inside:
  forall fsts lsts t t', wndEval t t' ->
                         wndEvals (tappend fsts (tcons t lsts))
                                  (tappend fsts (tcons t' lsts)).
Proof.
  induction fsts; intros.
  - cbn. constructor. assumption.
  - cbn. constructor. apply IHfsts. assumption.
Qed.

(*************
Lemma wndEval_mkProof_mkProof:
  forall s u, wndEval s u -> WFapp s -> wndEval (mkProof s) (mkProof u).
Proof.
  induction 1; cbn; intros hs; intros;
  inversion_Clear hs; intuition; try discriminate;
  try (constructor; econstructor; eassumption).
  - rewrite mkProof_idempotent. constructor. assumption.
  - rewrite <- (@mkProof_goodProof (TApp t brg brgs)). constructor.
    constructor. assumption. not_isProof.
  - rewrite <- (@mkProof_goodProof (TProd nm t2 bod)). constructor.
    constructor. assumption. not_isProof.
  - rewrite <- (@mkProof_goodProof (TLambda nm t2 bod)). constructor.
    constructor. assumption. not_isProof.
  - rewrite <- (@mkProof_goodProof (TLetIn nm d t2 bod)). constructor.
    constructor. assumption. not_isProof.
  - rewrite <- (@mkProof_goodProof (TLetIn nm d2 t bod)). constructor.
    constructor. assumption. not_isProof.
  - rewrite <- (@mkProof_goodProof (TCase (a, b) uy mch brs)). constructor.
    constructor. assumption. not_isProof.
  - rewrite <- (@mkProof_goodProof (TCase (a, b) ty can brs)). constructor.
    constructor. assumption. not_isProof.
Qed.
 **********************)

Lemma wndEval_mkApp_mkApp:
  forall s u, wndEval s u -> WFapp s ->
  forall a1 args,
     wndEval (mkApp s (tcons a1 args)) (mkApp u (tcons a1 args)).
Proof.
  induction 1; cbn; intros hs; intros;
  inversion hs; subst; auto; try discriminate.
  - rewrite whBetaStep_absorbs_mkApp. apply sBeta.
  - rewrite <- mkApp_goodFn; try not_isApp. apply sAppFn.
    eapply sCase; eassumption.
  - rewrite pre_whFixStep_absorbs_mkApp. simpl. eapply sFix; try eassumption.
    rewrite tlength_tappend. omega.
(***
  - rewrite <- (@mkApp_goodFn (TProof s)). eapply sAppFn.
    + apply sProof. assumption.
    + not_isApp.
****)
  - rewrite mkApp_idempotent. constructor. assumption.
  - inversion_Clear H; eapply sAppArgs. 
    + constructor. eassumption.
    + constructor. apply wndEval_tappendl. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sProdTy. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sLamTy. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sLetInTy. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sLetInDef. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sCaseTy. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sCaseArg. assumption.
    (*****************
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sCaseBrs. assumption.
****************)
Qed.

Lemma wndEvals_old_App_args:
  forall fn arg args args',
    wndEvals args args' -> ~ isApp fn ->
    wndEval (TApp fn arg args) (TApp fn arg args').
Proof.
  induction 1; intros h.
- constructor. apply saTl. apply saHd. assumption.
- apply sAppArgs. apply saTl. apply saTl. assumption. 
Qed.

(** for technical also use equivalent relation awndEval **)
Lemma awndEval_wndEval:
  (forall t s, awndEval p t s -> WFapp t -> wndEval t s) /\
  (forall ts ss, awndEvals p ts ss -> WFapps ts -> wndEvals ts ss).
Proof. 
  apply awndEvalEvals_ind; intros; try (constructor; assumption);
  try (inversion H0; subst; constructor; apply H; assumption).
  - inversion H. subst. eapply sCase; eassumption.
  - inversion_Clear H. eapply sFix; try eassumption.
  - destruct (WFapp_mkApp_WFapp H0 _ _ eq_refl).
    apply wndEval_mkApp_mkApp; try assumption.
    + apply H; assumption.
  - eapply sAppArgs. apply H.
    inversion_Clear H0. constructor; assumption.
Qed.

Lemma wndEval_awndEval:
  (forall t s, wndEval t s -> WFapp t -> awndEval p t s) /\
  (forall ts ss, wndEvals ts ss -> WFapps ts -> awndEvals p ts ss).
Proof. 
  apply wndEvalEvals_ind; intros; try (econstructor; eassumption);
  try (inversion H0; subst; constructor; apply H; assumption).
  - inversion H0. rewrite <- mkApp_goodFn; try assumption.
    eapply aAppFn. intuition.
  - eapply aAppArgs. apply H.
    inversion_Clear H0. constructor; assumption.
Qed.

Lemma wndEval_pres_WFapp:
  WFaEnv p -> forall t s, wndEval t s -> WFapp t -> WFapp s.
Proof.
  intros hp t s hts ht.
  assert (j:= proj1 (awndEval_pres_WFapp hp) t s).
  apply j; try assumption.
  - apply (proj1 wndEval_awndEval); assumption.
Qed.
  
Lemma wndEvals_pres_WFapp:
  WFaEnv p -> forall ts ss, wndEvals ts ss -> WFapps ts -> WFapps ss.
Proof.
  intros hp ts ss hts ht.
  assert (j:= (proj2 (awndEval_pres_WFapp hp) ts ss)).
  apply j; try assumption.
  - apply (proj2 wndEval_awndEval); assumption.
Qed.
  

(***
Lemma wndEval_pres_Crct:
  forall p,
  (forall t s, wndEval p t s -> forall n, Crct p n t -> Crct p n s) /\
  (forall ts ss, wndEvals p ts ss ->
                 forall n, Crcts p n ts -> Crcts p n ss) /\
  (forall ds es, wndDEvals p ds es ->
                 forall n, CrctDs p n ds -> CrctDs p n es).
Proof.
  intros p. apply wndEvalEvals_ind; intros.
  - eapply LookupDfn_pres_Crct; try eassumption.
  - destruct (Crct_invrt_App H eq_refl) as [h1 [h2 [h3 h4]]].
    destruct (Crct_invrt_Lam h1 eq_refl). 
    unfold whBetaStep. apply mkApp_pres_Crct; try assumption. 
    apply instantiate_pres_Crct; try assumption.
    omega.
  - destruct (Crct_invrt_LetIn H eq_refl) as [h1 [h2 h3]].
    apply instantiate_pres_Crct; try assumption. omega.
  - destruct (Crct_invrt_Case H eq_refl) as [h1 [h2 h3]].
    refine (whCaseStep_pres_Crct _ _ _ e); trivial.
    + apply CrctsNil. eapply Crct_Sort. eassumption.
  - destruct (Crct_invrt_Case H eq_refl) as [h1 [h2 h3]].
    refine (whCaseStep_pres_Crct _ _ _ e0); trivial.
    + apply (tskipn_pres_Crct _ e).
      * destruct (Crct_invrt_App h2 eq_refl) as [j1 [j2 [j3 j4]]].
        apply CrctsCons; assumption.
  - destruct (Crct_invrt_App H eq_refl) as [h1 [h2 [h3 h4]]].
    assert (j:= @Crct_invrt_Fix _ _ _ h1 dts m eq_refl).
    refine (whFixStep_pres_Crct _ _ _ _ _).
    + admit.
    + constructor; assumption. 
    +
  - destruct (Crct_invrt_Cast H eq_refl) as [h1 h2]. assumption.
  - destruct (Crct_invrt_App H0 eq_refl) as [h1 [h2 [h3 h4]]].
    apply mkApp_pres_Crct.
    + apply H. assumption.
    + apply CrctsCons; assumption.
  - destruct (Crct_invrt_App H0 eq_refl) as [h1 [h2 [h3 h4]]].
    apply CrctApp; intuition. 
  - destruct (Crct_invrt_App H0 eq_refl) as [h1 [h2 [h3 h4]]].
    apply CrctApp; intuition.
  - destruct (Crct_invrt_Prod H0 eq_refl) as [h1 h2].
    apply CrctProd; try assumption.
    + apply H; assumption.
  - destruct (Crct_invrt_Lam H0 eq_refl) as [h1 h2].
    apply CrctLam; try assumption.
    + apply H; assumption.
  - destruct (Crct_invrt_LetIn H0 eq_refl) as [h1 [h2 h3]].
    apply CrctLetIn; try assumption.
    + apply H; assumption.
  - destruct (Crct_invrt_LetIn H0 eq_refl) as [h1 [h2 h3]].
    apply CrctLetIn; try assumption.
    + apply H; assumption.
  - destruct (Crct_invrt_Case H0 eq_refl) as [h1 [h2 h3]].
    apply CrctCase; try assumption.
    + apply H; assumption.
  - destruct (Crct_invrt_Case H0 eq_refl) as [h1 [h2 h3]].
    apply CrctCase; try assumption.
    + apply H; assumption.
  - destruct (Crct_invrt_Case H0 eq_refl) as [h1 [h2 h3]].
    apply CrctCase; try assumption.
    + apply H; assumption.
  - inversion_Clear H0. apply CrctsCons; try assumption.
    apply H. assumption.
  - inversion_Clear H0. apply CrctsCons; try assumption.
    apply H. assumption.
Qed.
***)


Lemma wndEval_Lam_inv:
  forall nm tp bod s,
    wndEval (TLambda nm tp bod) s ->
    exists tp', wndEval tp tp' /\ s = (TLambda nm tp' bod).
intros nm tp bod s h. inversion_Clear h.
- exists t2. split; [assumption | reflexivity].
Qed.

Lemma wndEval_Prod_inv:
  forall nm tp bod s,
    wndEval (TProd nm tp bod) s ->
    exists tp', wndEval tp tp' /\ s = (TProd nm tp' bod).
intros nm tp bod s h. inversion_Clear h.
- exists t2. split; [assumption | reflexivity].
Qed.

Lemma wndEval_Cast_inv:
  forall tm ty s, wndEval (TCast tm ty) s -> tm = s.
inversion 1.
- reflexivity.
Qed.

(** when reduction stops **)
Definition no_wnd_step (t:Term) : Prop :=
  no_step wndEval t.
Definition no_wnds_step (ts:Terms) : Prop :=
  no_step wndEvals ts.


(** reflexive-transitive closure of wndEval **)
Inductive wndEvalRTC: Term -> Term -> Prop :=
(** | wERTCrfl: forall t, WNorm t -> wndEvalRTC t t ??? **)
| wERTCrfl: forall t, wndEvalRTC t t
| wERTCstep: forall t s, wndEval t s -> wndEvalRTC t s
| wERTCtrn: forall t s u, wndEvalRTC t s -> wndEvalRTC s u ->
                          wndEvalRTC t u.
Inductive wndEvalsRTC: Terms -> Terms -> Prop :=
(** | wEsRTCrfl: forall ts, WNorms ts -> wndEvalsRTC p ts ts ??? **)
| wEsRTCrfl: forall ts, wndEvalsRTC ts ts
| wEsRTCstep: forall ts ss, wndEvals ts ss -> wndEvalsRTC ts ss
| wEsRTCtrn: forall ts ss us, wndEvalsRTC ts ss -> wndEvalsRTC ss us ->
                          wndEvalsRTC ts us.
Hint Constructors wndEvalRTC wndEvalsRTC.


Lemma wndEvalRTC_pres_WFapp:
  WFaEnv p -> forall t s, wndEvalRTC t s -> WFapp t -> WFapp s.
Proof.
  intros hp.
  induction 1; intros; try assumption.
  - eapply (wndEval_pres_WFapp); eassumption.
  - apply IHwndEvalRTC2; try assumption.
    + apply IHwndEvalRTC1; assumption.
Qed.

Lemma wndEvalsRTC_pres_WFapp:
  WFaEnv p -> forall ts ss, wndEvalsRTC ts ss -> WFapps ts -> WFapps ss.
Proof.
  intros hp.
  induction 1; intros; try assumption.
  - eapply (wndEvals_pres_WFapp); eassumption.
  - apply IHwndEvalsRTC2; try assumption.
    + apply IHwndEvalsRTC1; assumption.
Qed.


Lemma awndEvalRTC_wndEvalRTC:
  WFaEnv p -> forall t s, awndEvalRTC p t s-> WFapp t -> wndEvalRTC t s.
Proof.
  intros hp.
  induction 1; intros.
  - constructor.
  - constructor. apply awndEval_wndEval; assumption.
  - eapply wERTCtrn.
    + apply IHawndEvalRTC1. assumption.
    + apply IHawndEvalRTC2. eapply wndEvalRTC_pres_WFapp; intuition.
      * eapply awndEvalRTC_pres_WFapp; try eassumption. 
Qed.

Lemma wndEvalRTC_awndEvalRTC:
  WFaEnv p -> forall t s, wndEvalRTC t s -> WFapp t -> awndEvalRTC p t s.
Proof.
  intros hp.
  induction 1; intros.
  - constructor.
  - constructor. apply wndEval_awndEval; assumption.
  - eapply awERTCtrn.
    + apply IHwndEvalRTC1. assumption.
    + apply IHwndEvalRTC2. eapply wndEvalRTC_pres_WFapp; intuition.
      * eapply awndEvalRTC_pres_WFapp; try eassumption. 
Qed.

Lemma wndEvalsRTC_tcons_l:
  forall brgs crgs, wndEvalsRTC brgs crgs ->
    forall b bs, brgs = tcons b bs ->
     exists c cs, (crgs = tcons c cs /\ wndEvalRTC b c /\ wndEvalsRTC bs cs).
Proof.
  induction 1; intros.
  - exists b, bs. auto.
  - subst. destruct (wndEvals_tcons_l H eq_refl) as [x0 [x1 [j0 j1]]].
    subst. exists x0, x1.
    destruct (wndEvals_tcons H eq_refl eq_refl) as [[k1 k2] | [k1 k2]];
      subst;intuition; subst.
  - subst. destruct (IHwndEvalsRTC1 _ _ eq_refl) as [x0 [x1 [j0 [j1 j2]]]].
    subst. destruct (IHwndEvalsRTC2 _ _ eq_refl) as [y0 [y1 [k0 [k1 k2]]]].
    subst. exists y0, y1. split. reflexivity.
    split. eapply wERTCtrn; eassumption.  eapply wEsRTCtrn; eassumption. 
Qed.

Lemma wndEvalsRTC_tcons_r:
  forall brgs crgs, wndEvalsRTC crgs brgs ->
    forall b bs, brgs = tcons b bs ->
     exists c cs, (crgs = tcons c cs /\ wndEvalRTC c b /\ wndEvalsRTC cs bs).
Proof.
  induction 1; intros.
  - exists b, bs. auto.
  - subst. destruct (wndEvals_tcons_r H eq_refl) as [x0 [x1 [j0 j1]]].
    subst. exists x0, x1.
    destruct (wndEvals_tcons H eq_refl eq_refl) as [[k1 k2] | [k1 k2]];
      subst; intuition; subst.
  - subst. destruct (IHwndEvalsRTC2 _ _ eq_refl) as [x0 [x1 [j0 [j1 j2]]]].
    subst. destruct (IHwndEvalsRTC1 _ _ eq_refl) as [y0 [y1 [k0 [k1 k2]]]].
    subst. exists y0, y1. split. reflexivity.
    split. eapply wERTCtrn; eassumption.  eapply wEsRTCtrn; eassumption. 
Qed.

Lemma wndEvalsRTC_tcons:
  forall brgs brgs', wndEvalsRTC brgs brgs' ->
    forall a1 args, brgs = (tcons a1 args) ->
     forall a1' args', brgs' = (tcons a1' args') ->
                 wndEvalRTC a1 a1' /\ wndEvalsRTC args args'.
Proof.
  induction 1; intros; subst.
  - myInjection H0. auto.
  - destruct (wndEvals_tcons H eq_refl eq_refl) as [j | j].
    + intuition. subst. apply wEsRTCrfl.
    + inversion_Clear H; intuition.
  - destruct (wndEvalsRTC_tcons_l H eq_refl) as [x0 [x1 [j0 [j1 j2]]]].
    subst.
    destruct (wndEvalsRTC_tcons_r H0 eq_refl) as [y0 [y1 [k0 [k1 k2]]]].
    myInjection k0. split.
    + eapply wERTCtrn; eassumption.
    + eapply wEsRTCtrn; eassumption.
Qed.

Lemma wndEvalsRTC_mk_tconsr:
  forall us us',
    wndEvalsRTC us us' ->
    forall t, wndEvalsRTC (tcons t us) (tcons t us').
Proof.
  induction 1; intros.
  - constructor.
  - constructor. constructor. assumption.
  - eapply wEsRTCtrn. apply IHwndEvalsRTC1. apply IHwndEvalsRTC2.
Qed.

Lemma wndEvalsRTC_mk_tconsl:
  forall t t', wndEvalRTC t t' ->
  forall us, wndEvalsRTC (tcons t us) (tcons t' us).
Proof.
  induction 1; intros.
  - constructor.
  - constructor. constructor. assumption.
  - eapply wEsRTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.
      
Lemma wndEvalsRTC_mk_tappendr:
  forall ts us us',
    wndEvalsRTC us us' -> wndEvalsRTC (tappend ts us) (tappend ts us').
Proof.
  induction ts; cbn; intros.
  - assumption.
  - eapply wndEvalsRTC_mk_tconsr. intuition.
Qed.

Inductive wndEvalTCl: Term -> Term -> Prop :=
| wETClstep: forall t s, wndEval t s -> wndEvalTCl t s
| wETCltrn: forall t s, wndEvalTCl t s ->
        forall u, wndEval s u -> wndEvalTCl t u.
Inductive wndEvalsTCl: Terms -> Terms -> Prop :=
| wEsTClstep: forall ts ss, wndEvals ts ss -> wndEvalsTCl ts ss
| wEsTCltrn: forall ts ss, wndEvalsTCl ts ss -> 
         forall us, wndEvals ss us -> wndEvalsTCl ts us.
Hint Constructors wndEvalTCl wndEvalsTCl.


(** transitive congruence rules **)
(*** HERE is a version of the problem  ***)
Lemma wndEvalRTC_App_fn:
  WFaEnv p ->
  forall fn fn', wndEvalRTC fn fn' -> WFapp fn ->
    forall arg args, WFapp arg -> WFapps args ->
      wndEvalRTC (mkApp fn (tcons arg args)) (mkApp fn' (tcons arg args)).
Proof.  
  intros hp fn fn' hfn h1 arg args harg hargs.
  apply (awndEvalRTC_wndEvalRTC). assumption.
  - apply awndEvalRTC_App_fn. apply wndEvalRTC_awndEvalRTC; assumption.
  - apply mkApp_pres_WFapp; try constructor; assumption.
Qed.

Lemma wndEvalRTC_Proof:
  forall t t',
    wndEvalRTC t t' -> wndEvalRTC (TProof t) t'.
Proof.
  induction 1; intros.
  - constructor. constructor.
  - eapply wERTCtrn.
    + eapply wERTCstep. constructor.
    + eapply wERTCstep. assumption.
  - eapply wERTCtrn. apply IHwndEvalRTC1. assumption.
Qed.

Lemma wndEvalsRTC_left_nil_nil:
      forall vs us, wndEvalsRTC vs us -> vs = tnil -> us = tnil.
Proof.
  induction 1; intros; subst. reflexivity.
  + inversion H.
  + intuition.
Qed.

Lemma wndEvalsRTC_right_nil_nil:
      forall vs us, wndEvalsRTC vs us -> us = tnil -> vs = tnil.
Proof.
  induction 1; intros; subst. reflexivity.
  + inversion H.
  + intuition.
Qed.

Lemma wndEvalRTC_App_arg:
  forall fn arg arg',
    wndEvalRTC arg arg' ->
    forall args, 
      wndEvalRTC (TApp fn arg args) (TApp fn arg' args).
Proof.
  induction 1; intros args.
  - constructor.
  - constructor. apply sAppArgs. constructor. assumption.
  - eapply wERTCtrn;
    try apply IHwndEvalRTC1; try apply IHwndEvalRTC2; assumption.
Qed.

Lemma wndEvalsRTC_old_App_args:
  forall fn arg args args',
    wndEvalsRTC args args' ->
      wndEvalRTC (TApp fn arg args) (TApp fn arg args').
induction 1.
- constructor.
- constructor. apply sAppArgs. apply saTl. assumption.
- eapply wERTCtrn. apply IHwndEvalsRTC1. assumption. 
Qed.


Lemma wndEvalsRTC_App_args:
  forall xs ys,
    wndEvalsRTC xs ys ->
    forall arg args, xs = (tcons arg args) ->
                     forall arg' args', ys = (tcons arg' args') ->
                                        forall fn, ~ isApp fn ->
     wndEvalRTC (TApp fn arg args) (TApp fn arg' args').
induction 1; intros.
- subst. myInjection H0. constructor.
- subst. inversion_Clear H; apply wERTCstep; apply sAppArgs.
  + apply saHd. assumption.
  + apply saTl. assumption.
- destruct ss.
  + rewrite (wndEvalsRTC_left_nil_nil H0 eq_refl) in H2. discriminate.
  + subst. eapply wERTCtrn. apply IHwndEvalsRTC1; try reflexivity. assumption.
    apply IHwndEvalsRTC2; try reflexivity. assumption.
Qed.

Lemma wndEvalRTC_Lam_typ:
  forall ty ty',
    wndEvalRTC ty ty' ->
    forall nm bod, 
      wndEvalRTC (TLambda nm ty bod) (TLambda nm ty' bod).
induction 1; intros nm bod.
- constructor.
- constructor. apply sLamTy. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalRTC_Prod_typ:
  forall ty ty',
    wndEvalRTC ty ty' ->
    forall nm bod, 
      wndEvalRTC (TProd nm ty bod) (TProd nm ty' bod).
induction 1; intros nm bod.
- constructor.
- constructor. apply sProdTy. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalRTC_LetIn_dfn:
  forall nm dfn dfn',
    wndEvalRTC dfn dfn' ->
    forall ty bod, 
      wndEvalRTC (TLetIn nm dfn ty bod) (TLetIn nm dfn' ty bod).
induction 1; intros ty bod.
- constructor.
- constructor. apply sLetInDef. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalRTC_Case_mch:
  forall mch mch',
    wndEvalRTC mch mch' -> 
    forall np ty brs, 
      wndEvalRTC (TCase np ty mch brs) (TCase np ty mch' brs).
induction 1; intros.
- constructor.
- constructor. apply sCaseArg. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalRTC_Case_ty:
  forall ty ty',
    wndEvalRTC ty ty' -> 
    forall np mch brs, 
      wndEvalRTC (TCase np ty mch brs) (TCase np ty' mch brs).
induction 1; intros.
- constructor.
- constructor. apply sCaseTy. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

(**************
Lemma wndEvalRTC_Case_brs:
  forall brs brs',
    wndEvalsRTC brs brs' -> 
    forall np mch ty, 
      wndEvalRTC (TCase np ty mch brs) (TCase np ty mch brs').
induction 1; intros.
- constructor.
- constructor. apply sCaseBrs. assumption.
- eapply wERTCtrn. apply IHwndEvalsRTC1. apply IHwndEvalsRTC2.
Qed.
 *****************)

Lemma wndEvalsRTC_tcons_hd:
  forall t ts u,
    wndEvalRTC t u -> wndEvalsRTC (tcons t ts) (tcons u ts).
induction 1.
- constructor.
- constructor. apply saHd. assumption.
- eapply wEsRTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalsRTC_tcons_tl:
  forall t ts ts',
    wndEvalsRTC ts ts' -> wndEvalsRTC (tcons t ts) (tcons t ts').
induction 1.
- constructor.
- constructor. apply saTl. assumption.
- eapply wEsRTCtrn. apply IHwndEvalsRTC1. apply IHwndEvalsRTC2.
Qed.

Lemma wndEvalsRTC_tcons':
  forall t t', wndEvalRTC t t' ->
               forall ts ts', wndEvalsRTC ts ts' ->
                              wndEvalsRTC (tcons t ts) (tcons t' ts').
Proof.
  intros t t' ht ts ts' hts.
  eapply (wEsRTCtrn).
  - eapply wndEvalsRTC_tcons_hd. eassumption.
  - eapply wndEvalsRTC_tcons_tl. assumption.
Qed.

Lemma wndEvalsRTC_appendl:
  forall ts1 ts2,
    wndEvalsRTC ts1 ts2 ->
    forall us, wndEvalsRTC (tappend ts1 us) (tappend ts2 us).
Proof.
  induction ts1; induction ts2; intros; cbn.
  - apply wEsRTCrfl.
  - destruct (wndEvalsRTC_tcons_r H eq_refl) as [c [cs [j1 j2]]].
    discriminate.
  - destruct (wndEvalsRTC_tcons_l H eq_refl) as [c [cs [j1 j2]]].
    discriminate.
  - destruct (wndEvalsRTC_tcons_l H eq_refl) as [c [cs [j1 [j2 j3]]]];
    myInjection j1. 
    apply wndEvalsRTC_tcons'.
    + assumption.
    + apply IHts1. assumption.
Qed.

Lemma wndEvalsRTC_appendr:
  forall ts1 ts2,
    wndEvalsRTC ts1 ts2 ->
    forall us, wndEvalsRTC (tappend us ts1) (tappend us ts2).
Proof.
  induction 1; intros.
  - apply wEsRTCrfl.
  - apply wEsRTCstep. apply wndEval_tappendr. assumption.
  - eapply wEsRTCtrn. apply IHwndEvalsRTC1. apply IHwndEvalsRTC2.
Qed.  

Lemma wndEvalsRTC_mkApp_args:
  forall xs ys,
    wndEvalsRTC xs ys ->
        forall fn, wndEvalRTC (mkApp fn xs) (mkApp fn ys).
Proof.
  induction 1; intros.
  - apply wERTCrfl.
  - destruct (isApp_dec fn).
    + destruct i as [x0 [x1 [x2 j]]]. rewrite j. cbn.
      apply wndEvalsRTC_old_App_args. eapply wndEvalsRTC_appendr.
      apply wEsRTCstep. assumption.
    + destruct ts, ss; cbn.
      * inversion H.
      * destruct (wndEvals_tcons_r H eq_refl) as [c [cs [j1 j2]]].
        discriminate.
      * destruct (wndEvals_tcons_l H eq_refl) as [c [cs [j1 j2]]].
        discriminate.
      * rewrite mkApp_goodFn; try assumption.
        rewrite mkApp_goodFn; try assumption.
        eapply wndEvalsRTC_App_args; try reflexivity; try eassumption.
        apply wEsRTCstep. assumption.
  - eapply wERTCtrn. apply IHwndEvalsRTC1. apply IHwndEvalsRTC2. 
Qed.
    
Lemma wndEvalsRTC_inside:
  forall fsts lsts t t', wndEvalRTC t t' ->
                         wndEvalsRTC (tappend fsts (tcons t lsts))
                                     (tappend fsts (tcons t' lsts)).
Proof.
  intros. apply wndEvalsRTC_appendr. apply wndEvalsRTC_tcons_hd. assumption.
Qed.


End Env.
Hint Constructors wndEval wndEvals.
Hint Constructors wndEvalRTC wndEvalsRTC.


Lemma wndEval_weaken:
  forall p,
    (forall t s, wndEval p t s ->
                 forall nm ec, fresh nm p -> wndEval ((nm,ec)::p) t s) /\
    (forall ts ss, wndEvals p ts ss ->
                   forall nm ec, fresh nm p -> wndEvals ((nm,ec)::p) ts ss).
Proof.
  intros p. apply wndEvalEvals_ind; intros; auto. 
  - apply sConst. apply Lookup_weaken; assumption.
  - eapply sCase; eassumption.
  - eapply (@sFix ((nm, ec) :: p)); try eassumption.
Qed.

Lemma wndEval_strengthen:
  forall (pp: environ Term),
  (forall t s, wndEval pp t s -> forall nm ec p, pp = (nm,ec)::p ->
        ~ PoccTrm nm t -> wndEval p t s) /\
  (forall ts ss, wndEvals pp ts ss -> forall nm ec p, pp = (nm,ec)::p ->
        ~ PoccTrms nm ts -> wndEvals p ts ss).
Proof.
  intros pp. apply wndEvalEvals_ind; intros; auto.
  - apply sConst; subst. unfold LookupDfn in *. destruct (string_dec s nm).
    + subst. elim H0. constructor.
    + refine (Lookup_strengthen l _ _). reflexivity. assumption.
  - eapply sCase; eassumption.
  - eapply sFix; try eassumption.
  - constructor. apply (H nm ec). eassumption.
    intros h. elim H1. constructor. assumption.
  - constructor. subst pp. eapply H. reflexivity.
    intros h. inversion_Clear h; elim H1. 
    + apply PoAppA. assumption.
    + apply PoAppR. assumption.
  - apply sProdTy. apply (H nm0 ec); trivial; apply (notPocc_TProd H1).
  - apply sLamTy. apply (H nm0 ec); trivial; apply (notPocc_TLambda H1).
  - apply sLetInTy. apply (H nm0 ec); trivial; apply (notPocc_TLetIn H1).
  - apply sLetInDef. apply (H nm0 ec); trivial; apply (notPocc_TLetIn H1).
  - apply sCaseTy. apply (H nm ec); trivial; apply (notPocc_TCase H1).
  - apply sCaseArg. apply (H nm ec); trivial; apply (notPocc_TCase H1).
    (************
  - apply sCaseBrs. apply (H nm ec); trivial; apply (notPocc_TCase H1).
*************)
  - apply saHd. apply (H nm ec). trivial. apply (notPoccTrms H1).
  - apply saTl. apply (H nm ec). trivial. apply (notPoccTrms H1).
Qed.

