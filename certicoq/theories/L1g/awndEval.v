(** An alternative definition of wndEval that is extensionally
*** equivalent for well-formed programs
**)

(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1g" as L1g.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Setoids.Setoid.
Require Import Common.Common.
Require Import L1g.compile.
Require Import L1g.term.
Require Import L1g.program.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(*** alrernative non-deterministic small step evaluation relation ***)
Section Env.
Variable p: environ Term.
Inductive awndEval : Term -> Term -> Prop :=
(** contraction steps **)
| aConst: forall (s:string) (t:Term),
         LookupDfn s p t -> awndEval (TConst s) t
| aBeta: forall (nm:name) (ty bod arg:Term) (args:Terms),
           awndEval (TApp (TLambda nm ty bod) arg args)
                   (whBetaStep bod arg args)
     (* note: [instantiate] is total *)
| aLetIn: forall (nm:name) (dfn ty bod:Term),
            awndEval (TLetIn nm dfn ty bod) (instantiate dfn 0 bod)
     (* Case argument must be in Canonical form *)
     (* np is the number of parameters of the datatype *)
| aCase: forall (ml: inductive * nat * list nat) (ty s mch:Term)
                 (args brs ts:Terms) (n:nat),
            canonicalP mch = Ret (n, args) ->
            tskipn (snd (fst ml)) args = Some ts ->
            whCaseStep n ts brs = Some s ->
            awndEval (TCase ml ty mch brs) s
| aFix: forall (dts:Defs) (m:nat) (arg:Term) (args:Terms)
               (x:Term) (ix:nat) (t:Term) z,
          (** ix is index of recursive argument **)
          dnthBody m dts = Some (x, ix) ->
          tnth ix (tcons arg args) = Some t -> canonicalP t = Ret z ->
          awndEval (TApp (TFix dts m) arg args)
                  (pre_whFixStep x dts (tcons arg args))
| aCast: forall t ck ty, awndEval (TCast t ck ty) t
(** congruence steps **)
(** no xi rules: sLambdaR, sProdR, sLetInR,
*** no congruence on Case branches or Fix ***)
| aAppFn:  forall (t r arg:Term) (args:Terms),
              awndEval t r ->
              awndEval (mkApp t (tcons arg args)) (mkApp r (tcons arg args))
| aAppArgs: forall (t arg brg:Term) (args brgs:Terms),
              awndEvals (tcons arg args) (tcons brg brgs) ->
              awndEval (TApp t arg args) (TApp t brg brgs)
| aProdTy:  forall (nm:name) (t1 t2 bod:Term),
              awndEval t1 t2 ->
              awndEval (TProd nm t1 bod) (TProd nm t2 bod)
| aLamTy:   forall (nm:name) (t1 t2 bod:Term),
              awndEval t1 t2 ->
              awndEval (TLambda nm t1 bod) (TLambda nm t2 bod)
| aLetInTy: forall (nm:name) (t1 t2 d bod:Term),
              awndEval t1 t2 ->
              awndEval (TLetIn nm d t1 bod) (TLetIn nm d t2 bod)
| aLetInDef:forall (nm:name) (t d1 d2 bod:Term),
              awndEval d1 d2 ->
              awndEval (TLetIn nm d1 t bod) (TLetIn nm d2 t bod)
| aCaseTy:  forall (ml: inductive * nat * list nat) (ty uy mch:Term) (brs:Terms),
              awndEval ty uy ->
              awndEval (TCase ml ty mch brs) (TCase ml uy mch brs)
| aCaseArg: forall (ml: inductive * nat * list nat) (ty mch can:Term) (brs:Terms),
              awndEval mch can ->
              awndEval (TCase ml ty mch brs) (TCase ml ty can brs)
| aCaseBrs: forall (ml: inductive * nat * list nat) (ty mch:Term) (brs brs':Terms),
              awndEvals brs brs' ->
              awndEval (TCase ml ty mch brs) (TCase ml ty mch brs')
with awndEvals : Terms -> Terms -> Prop :=
     | aaHd: forall (t r:Term) (ts:Terms), 
               awndEval t r ->
               awndEvals (tcons t ts) (tcons r ts)
     | aaTl: forall (t:Term) (ts ss:Terms),
               awndEvals ts ss ->
               awndEvals (tcons t ts) (tcons t ss).
Hint Constructors awndEval awndEvals.
Scheme awndEval1_ind := Induction for awndEval Sort Prop
     with awndEvals1_ind := Induction for awndEvals Sort Prop.
Combined Scheme awndEvalEvals_ind from awndEval1_ind, awndEvals1_ind.

Definition no_awnd_step (t:Term) : Prop :=
  no_step awndEval t.
Definition no_awnds_step (ts:Terms) : Prop :=
  no_step awndEvals ts.

Lemma awndEval_tappendl:
  forall bs cs, awndEvals bs cs ->
  forall ds, awndEvals (tappend bs ds) (tappend cs ds).
Proof.
  induction 1; intros.
  - constructor. assumption.
  - simpl. apply aaTl. apply IHawndEvals.
Qed.

Lemma awndEval_tappendr:
  forall bs cs, awndEvals bs cs ->
  forall ds, awndEvals (tappend ds bs) (tappend ds cs).
Proof.
  intros bs cs h ds. induction ds; simpl.
  - assumption.
  - apply aaTl. apply IHds.
Qed.

Lemma awndEval_Lam_inv:
  forall nm tp bod s,
    awndEval (TLambda nm tp bod) s ->
    exists tp', awndEval tp tp' /\ s = (TLambda nm tp' bod).
intros nm tp bod s h. inversion_Clear h.
- assert (j:= mkApp_isApp t arg args).
  destruct j as [x0 [x1 [x2 k]]]. rewrite k in H. discriminate.
- exists t2. split; [assumption | reflexivity].
Qed.

Lemma awndEval_Prod_inv:
  forall nm tp bod s,
    awndEval (TProd nm tp bod) s ->
    exists tp', awndEval tp tp' /\ s = (TProd nm tp' bod).
intros nm tp bod s h. inversion_Clear h.
- assert (j:= mkApp_isApp t arg args).
  destruct j as [x0 [x1 [x2 k]]]. rewrite k in H. discriminate.
- exists t2. split; [assumption | reflexivity].
Qed.

Lemma awndEval_Cast_inv:
  forall tm ck ty s, awndEval (TCast tm ck ty) s -> tm = s.
  inversion 1.
  - reflexivity.
  - destruct (mkApp_isApp t arg args) as [x0 [x1 [x2 j]]].
  rewrite H0 in j. discriminate.
Qed.

Lemma awndEval_pres_WFapp:
  WFaEnv p ->
  (forall t s, awndEval t s -> WFapp t -> WFapp s) /\
  (forall ts ss, awndEvals ts ss -> WFapps ts -> WFapps ss).
Proof.
  intros hp.
  apply awndEvalEvals_ind; intros; try assumption;
  try (solve [inversion_Clear H0; constructor; intuition]).
  - unfold LookupDfn in l. assert (j:= Lookup_pres_WFapp hp l).
    inversion j. assumption.
  - inversion_Clear H. inversion_Clear H4.
    apply whBetaStep_pres_WFapp; assumption.
  - inversion_Clear H. apply instantiate_pres_WFapp; assumption.
  - inversion_Clear H.
    refine (whCaseStep_pres_WFapp _ _ _ e1). assumption.
    refine (tskipn_pres_WFapp _ _ e0).
    refine (canonicalP_pres_WFapp _ e). assumption.
  - inversion_Clear H. inversion_Clear H4.
    assert (j:= dnthBody_pres_WFapp H0 m).
    apply pre_whFixStep_pres_WFapp; try assumption.
    + eapply j. eassumption.
    + constructor; assumption.
  - inversion_Clear H. assumption.
  - destruct (WFapp_mkApp_WFapp H0 _ _ eq_refl). inversion_Clear H2.
    apply mkApp_pres_WFapp.
    + constructor; assumption.
    + intuition.
  - inversion_Clear H0. 
    assert (j: WFapps (tcons arg args)).
    { constructor; assumption. }
    specialize (H j). inversion_Clear H.
    constructor; assumption.
Qed.

(** reflexive-transitive closure of wndEval **)
Inductive awndEvalRTC: Term -> Term -> Prop :=
(** | wERTCrfl: forall t, WNorm t -> awndEvalRTC p t t ??? **)
| awERTCrfl: forall t, awndEvalRTC t t
| awERTCstep: forall t s, awndEval t s -> awndEvalRTC t s
| awERTCtrn: forall t s u,
              awndEvalRTC t s -> awndEvalRTC s u -> awndEvalRTC t u.
Inductive awndEvalsRTC : Terms -> Terms -> Prop :=
(** | wEsRTCrfl: forall ts, WNorms ts -> wndEvalsRTC p ts ts ??? **)
| awEsRTCrfl: forall ts, awndEvalsRTC ts ts
| awEsRTCstep: forall ts ss, awndEvals ts ss -> awndEvalsRTC ts ss
| awEsRTCtrn: forall ts ss us,
       awndEvalsRTC ts ss -> awndEvalsRTC ss us -> awndEvalsRTC ts us.
Hint Constructors awndEvalRTC awndEvalsRTC.


Lemma awndEvalRTC_pres_WFapp:
  WFaEnv p ->
  forall t s, awndEvalRTC t s -> WFapp t -> WFapp s.
Proof.
  intros hp.
  induction 1; intros; try assumption.
  - eapply (proj1 (awndEval_pres_WFapp hp)); eassumption.
  - apply IHawndEvalRTC2; try assumption.
    + apply IHawndEvalRTC1; assumption.
Qed.

Lemma awndEvalRTC_App_fn:
  forall fn fn',
    awndEvalRTC fn fn' -> 
    forall a1 args,
      awndEvalRTC (mkApp fn (tcons a1 args)) (mkApp fn' (tcons a1 args)).
induction 1; intros.
- apply awERTCrfl.
- constructor. apply aAppFn. assumption.
- eapply awERTCtrn. 
  + apply IHawndEvalRTC1.
  + apply IHawndEvalRTC2.
Qed.


End Env.
Hint Constructors awndEval awndEvals.
Hint Constructors awndEvalRTC awndEvalsRTC.
(***
Hint Constructors awndEvalTC awndEvalsTC.
Hint Constructors awndEvalTCl awndEvalsTCl.
***)



(**
Lemma awndEval_mkApp_mkApp:
  forall p s u, awndEval p s u -> WFaEnv p -> WFapp s ->
  forall a1 args,
     awndEval p (mkApp s (tcons a1 args)) (mkApp u (tcons a1 args)).
Proof.
  induction 1; simpl; intros hp; intros hs; intros;
  inversion hs; subst; auto; try discriminate.
  - rewrite whBetaStep_absorbs_mkApp. apply aBeta.
  - rewrite <- mkApp_goodFn; try not_isApp. apply aAppFn.
    eapply aCasen; eassumption.
  - rewrite whFixStep_absorbs_mkApp. simpl. constructor.
  - rewrite mkApp_idempotent. simpl. rewrite <- (mkApp_goodFn _ _ H3).
    apply IHawndEval; assumption.
  - apply aAppArgs. apply awndEval_tappendl. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply aAppFn. 
    eapply aProdTy. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply aAppFn. 
    eapply aLamTy. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply aAppFn. 
    eapply aLetInTy. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply aAppFn. 
    eapply aLetInDef. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply aAppFn. 
    eapply aCaseTy. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply aAppFn. 
    eapply aCaseArg. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply aAppFn. 
    eapply aCaseBrs. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply aAppFn. 
    eapply aFixDefs. assumption.
Qed.
 ***)


(*******
Lemma wndEval_awndEval:
  forall p, WFaEnv p -> 
  (forall t s, wndEval p t s -> WFapp t -> awndEval p t s) /\
  (forall ts ss, wndEvals p ts ss -> WFapps ts -> awndEvals p ts ss) /\
  (forall ds es, wndDEvals p ds es -> WFappDs ds -> awndDEvals p ds es).
Proof. 
  intros p hp. apply wndEvalEvals_ind; intros; try (econstructor; eassumption);
               try (inversion H0; subst; constructor; apply H; assumption).
Qed.

Lemma awndEval_wndEval:
  forall p, WFaEnv p -> 
  (forall t s, awndEval p t s -> WFapp t -> wndEval p t s) /\
  (forall ts ss, awndEvals p ts ss -> WFapps ts -> wndEvals p ts ss) /\
  (forall ds es, awndDEvals p ds es -> WFappDs ds -> wndDEvals p ds es).
Proof. 
  intros p hp. apply awndEvalEvals_ind; intros; try (econstructor; eassumption);
              try (inversion H0; subst; constructor; apply H; assumption).
Qed.

(** Here is the reason for this alternative definition of wndEval **)
Lemma awndEval_App_inv:
  forall p t u, awndEval p t u ->
  forall fn arg args, t = mkApp fn (tcons arg args) ->
                      ~ isApp fn -> WFapp t -> WFaEnv p ->
    (exists nm ty bod, fn = TLambda nm ty bod) \/
    (exists ds m, fn = TFix ds m) \/
    (exists fn', wndEval p fn fn') \/
    (exists arg', wndEval p arg arg') \/
    (exists args', wndEvals p args args').
Proof.
  induction 1; intros;
  try (rewrite (mkApp_goodFn _ _ H1) in H0; try discriminate);
  try (rewrite (mkApp_goodFn _ _ H0) in H; try discriminate);
  try (rewrite (mkApp_goodFn _ _ H2) in H1; try discriminate).
  - left. exists nm, ty, bod. injection H. intros. subst. reflexivity.
  - right. left. exists dts, m. rewrite mkApp_cons_App in H2; try assumption.
    myInjection H2. reflexivity.
  - right. right. left. injection H0. intros. subst.
    exists r. inversion H2. apply awndEval_wndEval; assumption.
  - right. right. right. left. injection H0. intros. subst.
    exists brg. inversion H2. apply awndEval_wndEval; assumption.
  - right. right. right. right. inversion H2. injection H0. intros. subst.
    exists brgs. apply awndEval_wndEval; assumption.
Qed.

(***
Lemma wndEval_pres_WFapp:
  forall p, WFaEnv p -> 
  (forall t s, wndEval p t s -> WFapp t -> WFapp s) /\
  (forall ts ss, wndEvals p ts ss -> WFapps ts -> WFapps ss).
Proof.
  intros p hp.
  apply wndEvalEvals_ind; intros;
  try (solve [inversion_Clear H0; constructor; intuition]).
  - assert (j:= Lookup_pres_WFapp hp l). inversion j. intuition.
  - inversion_Clear H. inversion_Clear H4.
    apply whBetaStep_pres_WFapp; assumption.
  - inversion_Clear H. apply instantiate_pres_WFapp; assumption.
  - inversion_Clear H. eapply (whCaseStep_pres_WFapp H5). eapply wfanil.
    eassumption.
  - inversion_Clear H. inversion_Clear H3. unfold whCaseStep in e0.
    assert (j:= tnth_pres_WFapp H5 n). destruct (tnth n brs).
    + injection e0. intros. rewrite <- H. apply mkApp_pres_WFapp.
      * eapply (tskipn_pres_WFapp). apply wfacons. apply H7. apply H8. apply e.
      * apply j. reflexivity.
    + discriminate.
  - inversion_Clear H. inversion_Clear H4. unfold whFixStep in e.
    assert (j:= dnthBody_pres_WFapp H0 m). destruct (dnthBody m dts).
    injection e. intros. rewrite <- H. apply mkApp_pres_WFapp.
    + apply wfacons; assumption.
    + apply fold_left_pres_WFapp. intros.
      * { apply instantiate_pres_WFapp. 
          - assumption.
          - auto. }
      * eapply j. reflexivity.
    + discriminate.
  - inversion_Clear H. assumption.
  - destruct (WFapp_mkApp_WFapp H0 _ _ eq_refl). inversion_Clear H2.
    apply mkApp_pres_WFapp.
    + constructor; assumption.
    + intuition.
Qed.

Lemma wndEval_tappendl:
  forall p bs cs, wndEvals p bs cs ->
  forall ds, wndEvals p (tappend bs ds) (tappend cs ds).
Proof.
  induction 1; intros.
  - constructor. assumption.
  - simpl. apply saTl. apply IHwndEvals.
Qed.

Lemma wndEval_tappendr:
  forall p bs cs, wndEvals p bs cs ->
  forall ds, wndEvals p (tappend ds bs) (tappend ds cs).
Proof.
  intros p bs cs h ds. induction ds; simpl.
  - assumption.
  - apply saTl. apply IHds.
Qed.

(***
Lemma wndEval_pres_Crct:
  forall p,
  (forall t s, wndEval p t s -> forall n, Crct p n t -> Crct p n s) /\
  (forall ts ss, wndEvals p ts ss ->
                   forall n, Crcts p n ts -> Crcts p n ss).
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
    refine (whFixStep_pres_Crct _ _ _ e); try assumption.
    + constructor; assumption. 
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

(** reduction preserves WFTrm **
Goal forall p t s, wndEval p t s -> forall n, WFTrm t n -> WFTrm s n.
Proof.
  induction 1; intros nx h. try (solve [apply wfa1; not_isApp]);
  try (solve [apply mkApp_WFApp]);
  try (solve [eapply whCaseStep_WFApp; eassumption]);
  try (solve [apply wfa2; assumption]).
- apply inst_WFApp.
- eapply whFixStep_WFApp. eassumption.
Qed.
**)

Lemma wndEval_Lam_inv:
  forall p nm tp bod s,
    wndEval p (TLambda nm tp bod) s ->
    exists tp', wndEval p tp tp' /\ s = (TLambda nm tp' bod).
intros p nm tp bod s h. inversion_Clear h.
- assert (j:= mkApp_isApp t arg args).
  destruct j as [x0 [x1 [x2 k]]]. rewrite k in H. discriminate.
- exists t2. split; [assumption | reflexivity].
Qed.


(** when reduction stops **)
Definition no_wnd_step (p:environ) (t:Term) : Prop :=
  no_step (wndEval p) t.
Definition no_wnds_step (p:environ) (ts:Terms) : Prop :=
  no_step (wndEvals p) ts.




(** transitive closure of wndEval **)
(***
Definition wndEvalTC (p:environ) := clos_trans Term (wndEval p).
Definition wndEvalTC1n (p:environ) := clos_trans_1n Term (wndEval p).
Definition wndEvalTCn1 (p:environ) := clos_trans_n1 Term (wndEval p).
Hint Constructors clos_trans clos_trans_1n clos_trans_n1.
Notation wETCstep := (t_step).
Notation wETCtrn := (t_trans).
****)
Inductive wndEvalTC (p:environ): Term -> Term -> Prop :=
| wETCstep: forall t s, wndEval p t s -> wndEvalTC p t s
| wETCtrn: forall t s, wndEvalTC p t s -> forall u, wndEvalTC p s u ->
                          wndEvalTC p t u.
Inductive wndEvalsTC (p:environ): Terms -> Terms -> Prop :=
| wEsTCstep: forall ts ss, wndEvals p ts ss -> wndEvalsTC p ts ss
| wEsTCtrn: forall ts ss, wndEvalsTC p ts ss -> forall us, wndEvalsTC p ss us ->
                          wndEvalsTC p ts us.
Hint Constructors wndEvalTC wndEvalsTC.

Lemma wndEvalTC_pres_WFapp:
  forall p t s, wndEvalTC p t s -> WFaEnv p -> WFapp t -> WFapp s.
Proof.
  induction 1; intros.
  - eapply (proj1 (wndEval_pres_WFapp H0)); eassumption.
  - apply IHwndEvalTC2; try assumption.
    + apply IHwndEvalTC1; assumption.
Qed.

Inductive wndEvalTCl (p:environ): Term -> Term -> Prop :=
| wETClstep: forall t s, wndEval p t s -> wndEvalTCl p t s
| wETCltrn: forall t s, wndEvalTCl p t s -> forall u, wndEval p s u ->
                          wndEvalTCl p t u.
Inductive wndEvalsTCl (p:environ): Terms -> Terms -> Prop :=
| wEsTClstep: forall ts ss, wndEvals p ts ss -> wndEvalsTCl p ts ss
| wEsTCltrn: forall ts ss, wndEvalsTCl p ts ss -> 
                           forall us, wndEvals p ss us ->
                          wndEvalsTCl p ts us.
Hint Constructors wndEvalTCl wndEvalsTCl.



(** transitive congruence rules **)
(***
Lemma wndEvalRTC_App_fn:
  forall p fn fn' a1 args,
    wndEvalRTC p fn fn' -> ~ (isLambda fn') -> ~ (isFix fn') -> 
      wndEvalRTC p (TApp fn a1 args) (TApp fn' a1 args).
induction 1; intros.
- eapply (@wERTCtrn _ _ (TApp t a1 args)). apply wERTCrfl. apply WNApp; auto. inversion H.
- constructor. apply sAppFn. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.
***)


(***
***)

(**
Lemma wndEval_App_fn:
  forall p fn fn', wndEval p fn fn' ->
    forall a1 args, WFapp (TApp fn a1 args) ->
    (~ isApp fn' /\ wndEval p (TApp fn a1 args) (TApp fn' a1 args)) \/
    (isApp fn' /\ wndEval p (TApp fn a1 args) (mkApp fn' (tcons a1 args))). 
Proof.
  induction 1; simpl; intros h; intros.
  - destruct (isApp_dec t) as [j0 | j0].
    + right. intuition. 
    + left. rewrite <- (mkApp_goodFn _ _ j0). intuition. 
  - inversion_clear H. elim H0. exists (TLambda nm ty bod), arg, args. 
    reflexivity.
  - inversion_Clear H. destruct (isApp_dec (instantiate dfn 0 bod)). 
    + right. destruct i as [x0 [x1 [x2 j1]]]. intuition. 
      rewrite j1. intuition. 
    + left. rewrite <- (mkApp_goodFn _ _ n). intuition. 
  - inversion_Clear H0. destruct (isApp_dec s).
    + right. intuition. 
    + left. intuition. rewrite <- (mkApp_goodFn _ _ n0). apply sAppFn.
      apply sCase0. assumption.
  - inversion_Clear H1. destruct (isApp_dec s).
    + right. intuition. apply sAppFn. eapply sCasen; eassumption. 
    + left. intuition. rewrite <- (mkApp_goodFn _ _ n0). apply sAppFn. 
      eapply sCasen; eassumption.
  - inversion_clear H0. elim H1. exists (TFix dts m), arg, args. reflexivity.
  - inversion_Clear H. destruct (isApp_dec t).
    + right. intuition. 
    + left. rewrite <- (mkApp_goodFn _ _ n). intuition. 
  - inversion_clear H0. elim H1. exists t, arg, args. reflexivity.
  - inversion_clear H0. elim H1. exists t, arg, args. reflexivity.
  - inversion_clear H0. elim H1. exists t, arg, args. reflexivity.
  - left. rewrite <- (@mkApp_goodFn (TProd nm t2 bod)).
    + intuition. destruct H1 as [x0 [x1 [x2 j]]]. discriminate.
    + not_isApp.
  - left. rewrite <- (@mkApp_goodFn (TLambda nm t2 bod)).
    + intuition. destruct H1 as [x0 [x1 [x2 j]]]. discriminate.
    + not_isApp.
  - left. rewrite <- (@mkApp_goodFn (TLetIn nm d t2 bod)).
    + intuition. destruct H1 as [x0 [x1 [x2 j]]]. discriminate.
    + not_isApp.
  - left. rewrite <- (@mkApp_goodFn (TLetIn nm d2 t bod)).
    + intuition. destruct H1 as [x0 [x1 [x2 j]]]. discriminate.
    + not_isApp.
  - left. rewrite <- (@mkApp_goodFn (TCase np uy mch brs)).
    + intuition. destruct H1 as [x0 [x1 [x2 j]]]. discriminate.
    + not_isApp.
  - left. rewrite <- (@mkApp_goodFn (TCase np ty can brs)).
    + intuition.  destruct H1 as [x0 [x1 [x2 j]]]. discriminate.
    + not_isApp.
  - left. rewrite <- (@mkApp_goodFn (TCase np ty mch brs')).
    + intuition.  destruct H1 as [x0 [x1 [x2 j]]]. discriminate.
    + not_isApp.
Qed.


(**
Lemma wndEval_App_fn_cor:
  forall p fn fn', wndEval p fn fn' ->
    forall a1 args, WFapp (TApp fn a1 args) ->
      wndEval p (TApp fn a1 args) (mkApp fn' (tcons a1 args)).
Proof.
  intros p fn fn' h1 a1 args h2. 
  destruct (isApp_dec fn'); destruct (wndEval_App_fn h1 h2).
***)


Lemma wndEvalTC_App_fn:
  forall p fn fn', wndEval p fn fn' ->
    forall a1 args, WFapp (TApp fn a1 args) ->
    (~ isApp fn' /\ wndEvalTC p (TApp fn a1 args) (TApp fn' a1 args)) \/
    (isApp fn' /\ wndEvalTC p (TApp fn a1 args) (mkApp fn' (tcons a1 args))).
Proof.
  intros. destruct (wndEval_App_fn H H0). 
  - left. intuition.
  - right. intuition.
Qed.
***)

Lemma wndEval_mkApp_mkApp:
  forall p s u, wndEval p s u ->
  forall a1 args,
     wndEval p (mkApp s (tcons a1 args)) (mkApp u (tcons a1 args)).
Proof.
  induction 1; simpl; intros; auto; try discriminate.
  - rewrite <- mkApp_goodFn; try not_isApp. apply sAppFn.
    apply sConst. assumption.
  - rewrite whBetaStep_absorbs_mkApp. apply sBeta.
  - rewrite <- mkApp_goodFn; try not_isApp. apply sAppFn.
    apply sLetIn.
  - rewrite <- mkApp_goodFn; try not_isApp. apply sAppFn.
    apply sCase0. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp. apply sAppFn.
    eapply sCasen; eassumption.
  - unfold whFixStep in H. case_eq (dnthBody m dts); intros; rewrite H0 in H.
    + apply sFix. injection H. intros.
      rewrite <- H1. rewrite pre_whFixStep_absorbs_mkApp. 
      simpl. unfold whFixStep. rewrite H0. reflexivity. 
    + discriminate.
  - rewrite <- mkApp_goodFn; try not_isApp. apply sAppFn.
    eapply sCast; eassumption.
  - eapply sAppArgs. eapply wndEval_tappendl. assumption.
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
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sCaseBrs. assumption.
Qed.


(**
(****  HERE is the problem  ******)
Goal
  forall p s u, wndEval p s u ->
  forall fs bs bss, s = TApp fs bs bss -> ~ isApp u ->
  forall a1 args,
     wndEval p (mkApp s (tcons a1 args)) (TApp u a1 args).
Proof.
  induction 1; simpl; intros; auto; try discriminate.
  - destruct (not_isApp_whBetaStep _ _ _ H0). subst. simpl.
    injection H. intros. subst. clear H. 
  - rewrite whBetaStep_absorbs_mkApp. apply sBeta.
  - unfold whFixStep in H. case_eq (dnthBody m dts); intros; rewrite H2 in H.
    + apply sFix. injection H. intros.
      rewrite <- H3. rewrite pre_whFixStep_absorbs_mkApp. 
      simpl. unfold whFixStep. rewrite H2. reflexivity. 
    + discriminate.
  - rewrite mkApp_idempotent. apply sAppFn. assumption.
  - injection H0. intros. subst. clear H0.
    injection H1. intros. subst. clear H1. apply sAppArgs.
    apply wndEval_tappendl. assumption.
Qed.
***)

(****  HERE is the problem  ******
Lemma wndEvalTC_App_fn':
  forall p fn fn', wndEvalTC p fn fn' -> WFaEnv p ->
  forall a1 args, WFapp (TApp fn a1 args) ->
    (~ isApp fn' /\ wndEvalTC p (TApp fn a1 args) (TApp fn' a1 args)) \/
    (isApp fn' /\ wndEvalTC p (TApp fn a1 args) (mkApp fn' (tcons a1 args))).
Proof.
  induction 1; intros.
  - destruct (wndEvalTC_App_fn H H1) as [[j1 j2]|[j1 j2]].
    + left. intuition.
    + right. intuition.
  - inversion H2. subst.

    destruct (IHwndEvalTC1 H1 _ _ H2) as [[j1 j2]|[j1 j2]].
    assert (j: WFapp (TApp s a1 args)).
    { constructor; try assumption.
      eapply wndEvalTC_pres_WFapp; eassumption. }
    destruct (IHwndEvalTC2 H1 _ _ j) as [[k1 k2]|[k1 k2]].
    + left. intuition. eapply wETCtrn; eassumption.
    + right. intuition. eapply wETCtrn; eassumption.
    +  Check (IHwndEvalTC2 H1). as [[k1 k2]|[k1 k2]].



  - destruct (isApp_dec s) as [hs|hs].
    + right. intuition.
    + left. intuition.
      rewrite <- (@mkApp_goodFn s). apply wETClstep. apply sAppFn. assumption.
      assumption.
  - destruct (isApp_dec u) as [hu|hu].
    + right. intuition. destruct (H3 _ _ H2) as [[j1 j2]|[j1 j2]].
    + left. intuition.

destruct (IHwndEvalTCl H1 _ _ H2); destruct H3.
    + contradiction.
    + destruct (isApp_dec u) as [hu|hu]. 
      * right. intuition. eapply wETCltrn. eapply H4.
        destruct hs as [s0 [s1 [s2 js]]].
        destruct hu as [u0 [u1 [u2 ju]]].
        eapply wndEval_mkApp_mkApp; eassumption.
      * left. intuition. inversion H2. subst. eapply wETCltrn. eassumption.
        destruct hs as [s0 [s1 [s2 js]]]. rewrite js. simpl.
        rewrite js in H0. rewrite js in H.


        rewrite (@mkApp_goodFn s).

Check (wndEvalTC_App_fn).

Lemma wndEvalTC_App_fn':
  forall p fn fn', wndEvalTCl p fn fn' -> WFaEnv p ->
  forall a1 args, WFapp (TApp fn a1 args) ->
    (~ isApp fn' /\ wndEvalTCl p (TApp fn a1 args) (TApp fn' a1 args)) \/
    (isApp fn' /\ wndEvalTCl p (TApp fn a1 args) (mkApp fn' (tcons a1 args))).
Proof.
  induction 1; intros. destruct (isApp_dec s) as [hs|hs]. 
  - right. intuition.
  - left. intuition.
    rewrite <- (@mkApp_goodFn s). apply wETClstep. apply sAppFn. assumption.
    assumption.
  - destruct (IHwndEvalTCl H1 _ _ H2).
    + destruct H3. contradiction.
    + destruct H3. destruct (isApp_dec u) as [hu|hu]. 
      * right. intuition. eapply wETCltrn. eapply H4.
        eapply wndeval_mkApp_mkApp. assumption.


  destruct hs as [s0 [s1 [s2 js]]].
  - right. exists s0, s1, s2. intuition.
  - left. destruct (wndEvalTC_App_fn H H1). assumption.
    + rewrite <- (@mkApp_goodFn s). apply wETCstep. apply sAppFn. assumption.
      assumption.
  - destruct (IHwndEvalTC1 H1 _ _ H2) as [k|k].


Lemma wndEvalTC_App_fn':
  forall p fn fn', wndEvalTC p fn fn' -> WFaEnv p ->
  forall a1 args, WFapp (TApp fn a1 args) ->
    (~ isApp fn' /\ wndEvalTC p (TApp fn a1 args) (TApp fn' a1 args)) \/
    (isApp fn' /\ wndEvalTC p (TApp fn a1 args) (mkApp fn' (tcons a1 args))).
Proof.
  induction 1; intros; destruct (isApp_dec s) as [hs|hs]. 
  - right. intuition.
  - left. intuition.
    rewrite <- (@mkApp_goodFn s). apply wETCstep. apply sAppFn. assumption.
    assumption.
  - destruct (IHwndEvalTC1 H1 _ _ H2).
    + destruct H3. contradiction.
    + destruct H3.


  destruct hs as [s0 [s1 [s2 js]]].
  - right. exists s0, s1, s2. intuition.
  - left. destruct (wndEvalTC_App_fn H H1). assumption.
    + rewrite <- (@mkApp_goodFn s). apply wETCstep. apply sAppFn. assumption.
      assumption.
  - destruct (IHwndEvalTC1 H1 _ _ H2) as [k|k].





Proof.
  induction 1; intros;
  destruct (isApp_dec s) as [hs|hs]. destruct hs as [s0 [s1 [s2 js]]].
  - right. exists s0, s1, s2. intuition.
  - left. destruct (wndEvalTC_App_fn H H1). assumption.
    + rewrite <- (@mkApp_goodFn s). apply wETCstep. apply sAppFn. assumption.
      assumption.
  - destruct hs as [s0 [s1 [s2 js]]].
    destruct (isApp_dec u) as [hu|hu]. destruct hu as [u0 [u1 [u2 ju]]].
    + right. exists u0, u1, u2. split. assumption.
      * { eapply wETCtrn. destruct (IHwndEvalTC1 H1 _ _ H2) as [k|k]. 
          - rewrite js in k.  
            assert (l:WFapp (TApp (TApp s0 s1 s2) a1 args)).
            { eapply wndEvalTC_pres_WFapp; eassumption. }
            inversion_Clear l. eassumption.
          -

subst. eassumption.
          -

  intros p fn fn' h1 hp a1 args h4.
  induction h1; intros;
  destruct (isApp_dec s) as [hs|hs]. destruct hs as [s0 [s1 [s2 js]]].
  - right. exists s0, s1, s2. intuition.
  - left. assert (j:= wndEvalTC_App_fn H h4).
    rewrite mkApp_goodFn in j; try assumption.
    + inversion_Clear h4. left. rewrite <- (@mkApp_goodFn s). 
      apply sAppFn. assumption. assumption.
  - destruct hs as [s0 [s1 [s2 js]]].
    destruct (isApp_dec u) as [hu|hu]. destruct hu as [u0 [u1 [u2 ju]]].
    + right. exists u0, u1, u2. split. assumption.
      * { eapply wETCtrn. destruct (IHh1_1 h4) as [k|k]. 
          - eassumption.
          - subst.

  - destruct (isApp_dec u).
    + right. destruct i0 as [x0 [x1 [x2 j]]]. exists x0, x1, x2. split.
      * assumption.
      * { destruct (IHh1_1 h4) as [j0 | j0]. 
          - assert (j1:= wndEvalTC_pres_WFapp j0 hp h4). inversion_Clear j1.
            contradiction.
          - destruct j0 as [y0 [y1 [y2 j1]]]. destruct j1 as [j2 j3].
            eapply wETCtrn.
            + eassumption.
            + subst. simpl.
            simpl in IHh1_2. simpl in IHh1_2.
Check (IHh1_1 h4).

eapply wETCtrn. apply (IHh1_1 h4).


 destruct (IHh1_1 h4) as [j0 | j0].
    + assert (j1:= wndEvalTC_pres_WFapp j0 hp h4). inversion_Clear j1.
      contradiction.
    + destruct j0 as [x0 [x1 [x2 j]]]; destruct (isApp_dec u). 



right. exists x0, x1, x2.
      destruct j as [j1 j2].



  - right. destruct i as [x0 [x1 [x2 j]]]. exists x0, x1, x2. intuition.
  - inversion h4. subst. eapply wETCtrn.

Check (proj1 (wndEval_pres_WFapp hp) _ _ H).
  - inversion h4. subst. eapply wETCtrn.
    + inversion_Clear h1_1. 
      * apply wETCstep. apply sAppFn. eassumption.
      *
    + apply IHh1_1. apply wndEvalTC_preserves_WFapp. assumption.



    + apply wndEval_App_fn; eassumption.
    + assert (j:= proj1 (wndEval_pres_WFapp _) _ _ (sAppFn _ _ h1)).
    + destructj:=  (isApp_dec s).
      * destruct i as [x0 [x1 [x2 j]]]. rewrite j. simpl.


Lemma wndEvalTC_App_fn':
  forall p fn fn', wndEvalTC p fn fn' -> WFaEnv p ->
    forall a1 args, WFapp (TApp fn a1 args) ->
      wndEvalTC p (mkApp fn (tcons a1 args)) (mkApp fn' (tcons a1 args)).
Proof.
  Check (mkApp_goodFn).
  induction 1; intros.
  - apply wndEvalTC_App_fn. 
    + assumption.
    + assumption.
  - eapply wETCtrn.
    + apply wndEval_App_fn; eassumption.
    + assert (j:= proj1 (wndEval_pres_WFapp H1) _ _ (sAppFn _ _ H) H2).
    + destructj:=  (isApp_dec s).
      * destruct i as [x0 [x1 [x2 j]]]. rewrite j. simpl.


    + Check (wndEval_App_fn).

    + inversion_Clear H.
      * apply wndEval_App_fn; eassumption.
      * apply IHwndEvalTC1; assumption.
    + destruct (isApp_dec s).
      * destruct i as [x0 [x1 [x2 j]]]. rewrite j. simpl.


      *    + inversion H. apply wndEvalTC_App_fn. apply H3. assumption.
      apply IHwndEvalTC1. assumption. assumption.

    + inversion_Clear H2. assert (j:= wndEvalTC_preserves_WFapp H H1 H7).
      rewrite mkApp_goodFn. apply IHwndEvalTC2. assumption.
      constructor; try assumption.
Qed.
*******)

(****  HERE is the problem  ******
Lemma wndEvalTC_App_fn:
  forall p fn fn', wndEvalTC p fn fn' -> WFaEnv p ->
    forall a1 args, WFapp (TApp fn a1 args) ->
      wndEvalTC p (TApp fn a1 args) (mkApp fn' (tcons a1 args)).
Proof.
  induction 1; intros.
  - apply wndEvalTC_App_fn'.
    + assumption.
    + assumption.
  - eapply wETCtrn.
    + apply IHwndEvalTC1; assumption.
    + inversion_Clear H2. assert (j:= wndEvalTC_preserves_WFapp H H1 H7).
      rewrite mkApp_goodFn. apply IHwndEvalTC2. assumption.
      constructor; try assumption.
Qed.
*******)

(****
Lemma wndEvalTC_App_fn:
  forall p fn fn', wndEval p fn fn' ->
    forall a1 args, 
      wndEvalTC p (mkApp fn (tcons a1 args)) (mkApp fn' (tcons a1 args)).
Proof.
  induction 1; simpl; intros h; intros.
  - apply wETCstep. apply sAppFn; constructor. trivial.
  - apply wETCstep. unfold whBetaStep.
    rewrite mkApp_idempotent. apply sBeta.
  - apply wETCstep. apply sAppFn. apply sLetIn.
  - apply wETCstep. apply sAppFn. apply sCase0. assumption.
  - apply wETCstep. apply sAppFn. eapply sCasen; eassumption.
  - unfold whFixStep in H.
    case_eq (dnthBody m dts); intros; rewrite H0 in H.
    + injection H. intros. rewrite <- H1.
      rewrite mkApp_idempotent. apply wETCstep. apply sFix. unfold whFixStep.
      rewrite H0. reflexivity.
    + discriminate.
  - apply wETCstep. apply sAppFn. apply sCast.
  - apply wETCstep. rewrite mkApp_idempotent. simpl. apply sAppFn.

destruct (dnthBody m dts).
    + injection H. intros. rewrite <- H0. rewrite mkApp_idempotent.
      apply wETCstep. apply sFix. unfold whFixStep.


Lemma wndEvalTC_App_fn:
  forall p fn fn', wndEvalTC p fn fn' ->
   forall a1 args, WFapp (TApp fn a1 args) ->
    wndEvalTC p (mkApp fn (tcons a1 args)) (mkApp fn' (tcons a1 args)).
Proof.
  induction 1; intros. 
  - rewrite (WFapp_mkApp_TApp H0 eq_refl).
    constructor. apply sAppFn; trivial.
  - eapply wETCtrn. 
    + apply IHwndEvalTC1. assumption.
    + eapply IHwndEvalTC2. inversion_Clear H1. constructor; try assumption.
      * 



Lemma wndEvalTC_App_fn:
  forall p fn fn', wndEvalTC p fn fn' -> ~ isApp fn' ->
   forall n a1 args, Crct p n (TApp fn a1 args) ->
    wndEvalTC p (TApp fn a1 args) (TApp fn' a1 args).
Proof.
  unfold wndEvalTC. intros p fn fn1 h0. 
  assert (j0:= clos_trans_t1n Term (wndEval p) _ _ h0).
  apply clos_t1n_trans.
  induction 1; intros.
  - constructor. apply sAppFn; trivial.
  - eapply wETCtrn. eapply IHclos_trans1; trivial.
    + admit.


  - eapply wETCtrn. 
    + eapply wETCstep. apply sAppFn; trivial.
      *
    +

  - eapply wETCtrn. apply IHwndEvalTC1; trivial.
    + admit.
Qed.
***)

(*************
Goal
  forall fn p fn',
    wndEvalTC p fn fn' -> ~ isApp fn ->
    forall  a1 args,
      wndEvalTC p (TApp fn a1 args) (mkApp fn' (tcons a1 args)).
Proof.
  apply (@wf_ind Term TrmSize
           (fun fn:Term => forall p fn', wndEvalTC p fn fn' -> ~ isApp fn ->
            forall a1 args, 
             wndEvalTC p (TApp fn a1 args) (mkApp fn' (tcons a1 args)) )).
  intros t wih p fn' h1 a1 args h2.
  induction h1.
  - constructor. apply sAppFn; assumption.
  - eapply wETCtrn. apply IHh1_1; trivial.
*********)

(*************
apply sAppFn. assumption. inversion H; try (solve [not_isApp]).
    + destruct H1. unfold isApp. exists t, a1, args. reflexivity.
    + assumption.
  - eapply wETCtrn.
    + apply IHwndEvalTC1. assumption.
    + assert (j0:= wndEvalTC_WFApp H). 
      assert (j1:= mkApp_isApp_lem s a1 args).
      destruct j1. destruct H2. destruct H2. destruct H2 as [k1 [k2 | k3]].
      * rewrite k1. destruct k2 as [l1 [l2 [l3 l4]]].
        rewrite l2. rewrite <- l3. rewrite l4. simpl.
        apply IHwndEvalTC2.



Lemma wndEvalTC_App_fn:
  forall fn p fn',
    wndEvalTC p fn fn' ->
    forall  a1 args, WFApp (TApp fn a1 args) ->
      wndEvalTC p (TApp fn a1 args) (mkApp fn' (tcons a1 args)).
Proof.
  induction 1; intros.
  - constructor. apply sAppFn. assumption. inversion H0.
    + destruct H1. unfold isApp. exists t, a1, args. reflexivity.
    + assumption.
  - eapply wETCtrn.
    + apply IHwndEvalTC1. assumption.
    + assert (j0:= wndEvalTC_WFApp H). 
      assert (j1:= mkApp_isApp_lem s a1 args).
      destruct j1. destruct H2. destruct H2. destruct H2 as [k1 [k2 | k3]].
      * rewrite k1. destruct k2 as [l1 [l2 [l3 l4]]].
        rewrite l2. rewrite <- l3. rewrite l4. simpl.
        apply IHwndEvalTC2.

apply IHwndEvalTC2. assumption.


  apply (@wf_ind Term TrmSize
           (fun fn:Term => forall p fn', wndEvalTC p fn fn' ->
            forall  a1 args, WFApp (TApp fn a1 args) ->
             wndEvalTC p (TApp fn a1 args) (mkApp fn' (tcons a1 args)) )).
  intros t wih p fn' h1 a1 args h2.
  destruct h1.
  - constructor. apply sAppFn; try assumption.
    eapply WFApp_goodFn. eassumption.
  - apply wih.


induction 1; intros.
- constructor. apply sAppFn. assumption. inversion H0.
  + destruct H1. unfold isApp. exists t, a1, args. reflexivity.
  + assumption.
- eapply wETCtrn. 
  + apply IHwndEvalTC1. assumption.
  + assert (j:= wndEvalTC_WFApp H). apply IHwndEvalTC2. assumption.


rewrite mkApp_goodFn; trivial.
  apply sAppFn; assumption.
- eapply wERTCtrn. 
  + apply IHwndEvalRTC1. assumption.
  + apply IHwndEvalRTC2. assumption.
Qed.
***)

(***
Lemma wndEvalRTC_App_fn:
  forall p fn fn', wndEvalRTC p fn fn' ->
    forall a1 args, WFapp (TApp fn a1 args) ->
    (~ isApp fn' /\ wndEval p (TApp fn a1 args) (TApp fn' a1 args)) \/
    (isApp fn' /\ wndEval p (TApp fn a1 args) (mkApp fn' (tcons a1 args))). 
Proof.
***)

(*** HERE is another version of the problem  ***)
Lemma wndEvalRTC_App_fn:
  forall p fn fn', wndEvalRTC p fn fn' -> WFaEnv p ->
    forall  a1 args, 
      wndEvalRTC p (mkApp fn (tcons a1 args)) (mkApp fn' (tcons a1 args)).
induction 1; intros.
- apply wERTCrfl. 
- apply wERTCstep. eapply wndEval_mkApp_mkApp. assumption.
- eapply wERTCtrn. eapply IHwndEvalRTC1; assumption.
  eapply IHwndEvalRTC2. assumption. 
Qed.


Lemma wndEvalRTC_App_arg:
  forall p fn arg arg',
    wndEvalRTC p arg arg' -> ~ isApp fn ->
    forall args, 
      wndEvalRTC p (TApp fn arg args) (TApp fn arg' args).
induction 1; intros h args.
- constructor.
- constructor. apply sAppArg; assumption.
- eapply wERTCtrn;
  try apply IHwndEvalRTC1; try apply IHwndEvalRTC2; assumption.
Qed.

Lemma wndEvalTC_App_arg:
  forall p fn arg arg',
    wndEvalTC p arg arg' ->
    forall args, 
      wndEvalTC p (TApp fn arg args) (TApp fn arg' args).
induction 1; intros args.
- constructor. apply sAppArg. assumption.
- eapply wETCtrn. apply IHwndEvalTC1. apply IHwndEvalTC2.
Qed.

Lemma wndEvalsRTC_App_args:
  forall p fn arg args args',
    wndEvalsRTC p args args' -> ~ isApp fn ->
      wndEvalRTC p (TApp fn arg args) (TApp fn arg args').
induction 1; intros h.
- constructor.
- constructor. apply sAppArgs; assumption.
- eapply wERTCtrn. apply IHwndEvalsRTC1. assumption. 
  apply IHwndEvalsRTC2. assumption. 
Qed.

Lemma wndEvalsTC_App_args:
  forall p fn arg args args',
    wndEvalsTC p args args' -> ~ isApp fn ->
      wndEvalTC p (TApp fn arg args) (TApp fn arg args').
induction 1; intros h.
- constructor. apply sAppArgs; assumption.
- eapply wETCtrn. apply IHwndEvalsTC1. assumption. 
  apply IHwndEvalsTC2. assumption. 
Qed.

Lemma wndEvalRTC_Lam_typ:
  forall p ty ty',
    wndEvalRTC p ty ty' ->
    forall nm bod, 
      wndEvalRTC p (TLambda nm ty bod) (TLambda nm ty' bod).
induction 1; intros nm bod.
- constructor.
- constructor. apply sLamTy. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalRTC_Prod_typ:
  forall p ty ty',
    wndEvalRTC p ty ty' ->
    forall nm bod, 
      wndEvalRTC p (TProd nm ty bod) (TProd nm ty' bod).
induction 1; intros nm bod.
- constructor.
- constructor. apply sProdTy. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalRTC_LetIn_dfn:
  forall p nm dfn dfn',
    wndEvalRTC p dfn dfn' ->
    forall ty bod, 
      wndEvalRTC p (TLetIn nm dfn ty bod) (TLetIn nm dfn' ty bod).
induction 1; intros ty bod.
- constructor.
- constructor. apply sLetInDef. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalTC_LetIn_dfn:
  forall p nm dfn dfn',
    wndEvalTC p dfn dfn' ->
    forall ty bod, 
      wndEvalTC p (TLetIn nm dfn ty bod) (TLetIn nm dfn' ty bod).
induction 1; intros ty bod.
- constructor. apply sLetInDef. assumption.
- eapply wETCtrn. apply IHwndEvalTC1. apply IHwndEvalTC2.
Qed.

Lemma wndEvalRTC_Case_mch:
  forall p mch mch',
    wndEvalRTC p mch mch' -> 
    forall np ty brs, 
      wndEvalRTC p (TCase np ty mch brs) (TCase np ty mch' brs).
induction 1; intros.
- constructor.
- constructor. apply sCaseArg. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalTC_Case_mch:
  forall p mch mch',
    wndEvalTC p mch mch' -> 
    forall np ty brs, 
      wndEvalTC p (TCase np ty mch brs) (TCase np ty mch' brs).
induction 1; intros.
- constructor. apply sCaseArg. assumption.
- eapply wETCtrn. apply IHwndEvalTC1. apply IHwndEvalTC2.
Qed.

Lemma wndEvalsRTC_tcons_hd:
  forall p t t' ts,
    wndEvalRTC p t t' -> wndEvalsRTC p (tcons t ts) (tcons t' ts).
induction 1.
- constructor.
- constructor. apply saHd. assumption.
- eapply wEsRTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalsTC_tcons_hd:
  forall p t t' ts,
    wndEvalTC p t t' -> wndEvalsTC p (tcons t ts) (tcons t' ts).
induction 1.
- constructor. apply saHd. assumption.
- eapply wEsTCtrn. apply IHwndEvalTC1. apply IHwndEvalTC2.
Qed.

Lemma wndEvalsRTC_tcons_tl:
  forall p t ts ts',
    wndEvalsRTC p ts ts' -> wndEvalsRTC p (tcons t ts) (tcons t ts').
induction 1.
- constructor.
- constructor. apply saTl. assumption.
- eapply wEsRTCtrn. apply IHwndEvalsRTC1. apply IHwndEvalsRTC2.
Qed.

Lemma wndEvalsTC_tcons_tl:
  forall p t ts ts',
    wndEvalsTC p ts ts' -> wndEvalsTC p (tcons t ts) (tcons t ts').
induction 1.
- constructor. apply saTl. assumption.
- eapply wEsTCtrn. apply IHwndEvalsTC1. apply IHwndEvalsTC2.
Qed.


Lemma wndEval_weaken:
  forall p,
  (forall t s, wndEval p t s -> forall nm ec, fresh nm p ->
                   wndEval ((nm,ec)::p) t s) /\
  (forall ts ss, wndEvals p ts ss -> forall nm ec, fresh nm p ->
                    wndEvals ((nm,ec)::p) ts ss).
intros p. apply wndEvalEvals_ind; intros; auto. 
- apply sConst. apply Lookup_weaken; assumption.
- eapply sCasen; eassumption.
Qed.

Lemma wndEval_strengthen:
  forall (pp:environ),
  (forall t s, wndEval pp t s -> forall nm ec p, pp = (nm,ec)::p ->
        ~ PoccTrm nm t -> wndEval p t s) /\
  (forall ts ss, wndEvals pp ts ss -> forall nm ec p, pp = (nm,ec)::p ->
        ~ PoccTrms nm ts -> wndEvals p ts ss).
intros pp. apply wndEvalEvals_ind; intros; auto.
- apply sConst. 
  assert (j:= neq_sym (inverse_Pocc_TConstL H0)). inversion_Clear l.
  + injection H2; intros. contradiction.
  + injection H4; intros. subst. assumption.
- eapply sCasen; eassumption.
- apply sAppFn; trivial. apply (H nm ec). trivial.
  apply (proj1 (notPocc_mkApp _ _ H1)). 
- apply sAppArg. apply (H nm ec); trivial. apply (notPocc_TApp H1).
- apply sAppArgs. apply (H nm ec); trivial. apply (notPocc_TApp H1).
- apply sProdTy. apply (H nm0 ec); trivial; apply (notPocc_TProd H1).
- apply sLamTy. apply (H nm0 ec); trivial; apply (notPocc_TLambda H1).
- apply sLetInTy. apply (H nm0 ec); trivial; apply (notPocc_TLetIn H1).
- apply sLetInDef. apply (H nm0 ec); trivial; apply (notPocc_TLetIn H1).
- apply sCaseTy. apply (H nm ec); trivial; apply (notPocc_TCase H1).
- apply sCaseArg. apply (H nm ec); trivial; apply (notPocc_TCase H1).
- apply sCaseBrs. apply (H nm ec); trivial; apply (notPocc_TCase H1).
- apply saHd. apply (H nm ec). trivial. apply (notPoccTrms H1).
- apply saTl. apply (H nm ec). trivial. apply (notPoccTrms H1).
Qed.

***)
******)