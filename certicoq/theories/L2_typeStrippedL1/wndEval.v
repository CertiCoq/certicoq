

Require Import Lists.List.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Arith.Compare_dec.
Require Import L2.term.
Require Import L2.program.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(*** non-deterministic small step evaluation relation ***)
Inductive wndEval (p:environ) : Term -> Term -> Prop :=
(** contraction steps **)
| sConst: forall (s:string) (t:Term),
            LookupDfn s p t -> wndEval p (TConst s) t
| sBeta: forall (nm:name) (bod arg:Term) (args:Terms),
           wndEval p (TApp (TLambda nm bod) arg args)
                   (whBetaStep bod arg args)
     (* note: [instantiate] is total *)
| sLetIn: forall (nm:name) (dfn bod:Term),
            wndEval p (TLetIn nm dfn bod) (instantiate dfn 0 bod)
     (* Case argument must be in Canonical form *)
     (* np is the number of parameters of the datatype *)
| sCase0: forall (n:nat) (s:Term) (i:inductive) l (brs:Terms),
            whCaseStep n tnil brs = Some s ->
            wndEval p (TCase (0, l) (TConstruct i n) brs) s
| sCasen: forall (np:nat * list nat) (s arg:Term) (i:inductive)
                 (args brs ts:Terms) (n:nat),
            tskipn (fst np) (tcons arg args) = Some ts ->
            whCaseStep n ts brs = Some s ->
            wndEval p (TCase np (TApp (TConstruct i n) arg args) brs) s
| sFix: forall (dts:Defs) (m:nat) (arg s:Term) (args:Terms),
          whFixStep dts m (tcons arg args) = Some s ->
          wndEval p (TApp (TFix dts m) arg args) s
| sCast: forall t, wndEval p (TCast t) t
(** congruence steps **)
(** no xi rules: sLambdaR, sProdR, sLetInR,
*** no congruence on Case branches or Fix ***)
| sAppFn:  forall (t r arg:Term) (args:Terms),
              wndEval p t r ->
              wndEval p (mkApp t (tcons arg args)) (mkApp r (tcons arg args))
| sAppArg: forall (t arg brg:Term) (args:Terms),
              wndEval p arg brg ->
              wndEval p (TApp t arg args) (TApp t brg args)
| sAppArgs: forall (t arg:Term) (args brgs:Terms),
              wndEvals p args brgs ->
              wndEval p (TApp t arg args) (TApp t arg brgs)
| sLetInDef:forall (nm:name) (d1 d2 bod:Term),
              wndEval p d1 d2 ->
              wndEval p (TLetIn nm d1 bod) (TLetIn nm d2 bod)
| sCaseArg: forall (np:nat * list nat) (mch can:Term) (brs:Terms),
              wndEval p mch can ->
              wndEval p (TCase np mch brs) (TCase np can brs)
| sCaseBrs: forall (np:nat * list nat) (mch:Term) (brs brs':Terms),
              wndEvals p brs brs' ->
              wndEval p (TCase np mch brs) (TCase np mch brs')
with  (** step any term in a list of terms **)
wndEvals (p:environ) : Terms -> Terms -> Prop :=
    | saHd: forall (t r:Term) (ts:Terms), 
              wndEval p t r ->
              wndEvals p (tcons t ts) (tcons r ts)
    | saTl: forall (t:Term) (ts ss:Terms),
              wndEvals p ts ss ->
              wndEvals p (tcons t ts) (tcons t ss).
Hint Constructors wndEval wndEvals.
Scheme wndEval1_ind := Induction for wndEval Sort Prop
  with wndEvals1_ind := Induction for wndEvals Sort Prop.
Combined Scheme wndEvalEvals_ind from wndEval1_ind, wndEvals1_ind.

(** example: evaluate omega = (\x.xx)(\x.xx): nontermination **)
Definition xx := (TLambda nAnon (TApp (TRel 0) (TRel 0) tnil)).
Definition xxxx := (TApp xx xx tnil).
Goal wndEval nil xxxx xxxx.
unfold xxxx, xx. eapply sBeta. 
Qed.


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
  - inversion_Clear H. eapply (whCaseStep_pres_WFapp H4). eapply wfanil.
    eassumption.
  - inversion_Clear H. inversion_Clear H2. unfold whCaseStep in e0.
    assert (j:= tnth_pres_WFapp H4 n). destruct (tnth n brs).
    + injection e0. intros. rewrite <- H. apply mkApp_pres_WFapp.
      * eapply (tskipn_pres_WFapp). apply wfacons. apply H6. apply H7. apply e.
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


(** when reduction stops **)
Definition no_step {A:Set} (R:A -> A -> Prop) (a:A) :=
  forall (b:A), ~ R a b.
Definition no_wnd_step (p:environ) (t:Term) : Prop :=
  no_step (wndEval p) t.
Definition no_wnds_step (p:environ) (ts:Terms) : Prop :=
  no_step (wndEvals p) ts.


(** reflexive-transitive closure of wndEval **)
Inductive wndEvalRTC (p:environ): Term -> Term -> Prop :=
| wERTCrfl: forall t, wndEvalRTC p t t
| wERTCstep: forall t s, wndEval p t s -> wndEvalRTC p t s
| wERTCtrn: forall t s u, wndEvalRTC p t s -> wndEvalRTC p s u ->
                          wndEvalRTC p t u.
Inductive wndEvalsRTC (p:environ): Terms -> Terms -> Prop :=
(** | wEsRTCrfl: forall ts, WNorms ts -> wndEvalsRTC p ts ts ??? **)
| wEsRTCrfl: forall ts, wndEvalsRTC p ts ts
| wEsRTCstep: forall ts ss, wndEvals p ts ss -> wndEvalsRTC p ts ss
| wEsRTCtrn: forall ts ss us, wndEvalsRTC p ts ss -> wndEvalsRTC p ss us ->
                          wndEvalsRTC p ts us.
Hint Constructors wndEvalRTC wndEvalsRTC.

Lemma wndEvalRTC_pres_WFapp:
  forall p t s, wndEvalRTC p t s -> WFaEnv p -> WFapp t -> WFapp s.
Proof.
  induction 1; intros; try assumption.
  - eapply (proj1 (wndEval_pres_WFapp H0)); eassumption.
  - apply IHwndEvalRTC2; try assumption.
    + apply IHwndEvalRTC1; assumption.
Qed.


Inductive wndEvalTC (p:environ): Term -> Term -> Prop :=
| wETCstep: forall t s, wndEval p t s -> wndEvalTC p t s
| wETCtrn: forall t s u, wndEvalTC p t s -> wndEvalTC p s u ->
                          wndEvalTC p t u.
Inductive wndEvalsTC (p:environ): Terms -> Terms -> Prop :=
| wEsTCstep: forall ts ss, wndEvals p ts ss -> wndEvalsTC p ts ss
| wEsTCtrn: forall ts ss us, wndEvalsTC p ts ss -> wndEvalsTC p ss us ->
                          wndEvalsTC p ts us.
Hint Constructors wndEvalTC wndEvalsTC.

Lemma wndEvalTC_preserves_WFapp:
  forall p t s, wndEvalTC p t s -> WFaEnv p -> WFapp t -> WFapp s.
Proof.
  induction 1; intros.
  - eapply (proj1 (wndEval_pres_WFapp H0)); eassumption.
  - apply IHwndEvalTC2; try assumption.
    + apply IHwndEvalTC1; assumption.
Qed.


(** transitive congruence rules **)
(**
Lemma wndEvalRTC_App_fn:
  forall p fn fn' a1 args,
    wndEvalRTC p fn fn' -> wndEvalRTC p (TApp fn a1 args) (TApp fn' a1 args).
induction 1; intros.
- apply wERTCrfl. 
- constructor. apply sAppFn. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalTC_App_fn:
  forall p fn fn' a1 args,
    wndEvalTC p fn fn' -> wndEvalTC p (TApp fn a1 args) (TApp fn' a1 args).
induction 1; intros.
- constructor. apply sAppFn. assumption.
- eapply wETCtrn. apply IHwndEvalTC1. apply IHwndEvalTC2.
Qed.
**)

(*************
Lemma wndEval_App_fn:
  forall p fn fn', wndEval p fn fn' ->
    forall a1 args, WFapp (TApp fn a1 args) ->
      wndEval p (TApp fn a1 args) (mkApp fn' (tcons a1 args)).
Proof.
  induction 1; simpl; intros h; intros.
  - apply sAppFn; constructor. trivial.
  - inversion_clear H. elim H0. exists (TLambda nm bod), arg, args. 
    reflexivity.
  - apply sAppFn. apply sLetIn.
  - apply sAppFn. apply sCase0. assumption.
  - apply sAppFn. eapply sCasen; eassumption.
  - inversion_clear H0. elim H1. exists (TFix dts m), arg, args. 
    reflexivity.
  - apply sAppFn. apply sCast.
  - inversion_clear H0. elim H1. exists t, arg, args. reflexivity.
  - inversion_clear H0. elim H1. exists t, arg, args. reflexivity.
  - inversion_clear H0. elim H1. exists t, arg, args. reflexivity.
  - change (wndEval p (TApp (TLetIn nm d1 bod) h args)
                     (mkApp (TLetIn nm d2 bod) (tcons h args))).
    apply sAppFn. apply sLetInDef. assumption.
  - change (wndEval p (TApp (TCase np mch brs) h args)
                    (mkApp (TCase np can brs) (tcons h args))).
    apply sAppFn. apply sCaseArg. assumption.
  - change (wndEval p (TApp (TCase np mch brs) h args)
                    (mkApp (TCase np mch brs') (tcons h args))).
    apply sAppFn. apply sCaseBrs. assumption.
Qed.

Lemma wndEvalTC_App_fn:
  forall p fn fn', wndEval p fn fn' ->
    forall a1 args, WFapp (TApp fn a1 args) ->
      wndEvalTC p (TApp fn a1 args) (mkApp fn' (tcons a1 args)).
Proof.
  intros. apply wETCstep. apply wndEval_App_fn; assumption.
Qed.


****  HERE is the problem ???? ******
Lemma wndEvalTC_App_fn':
  forall p fn fn', wndEvalTC p fn fn' -> WFaEnv p -> ~ isApp fn' ->
  forall a1 args, WFapp (TApp fn a1 args) ->
    wndEvalTC p (TApp fn a1 args) (TApp fn' a1 args).
*****)

(** essential lemma **)
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
(***
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sProdTy. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sLamTy. assumption.
**)
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sLetInDef. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sCaseArg. assumption.
  - rewrite <- mkApp_goodFn; try not_isApp.
    rewrite <- mkApp_goodFn; try not_isApp. eapply sAppFn. 
    eapply sCaseBrs. assumption.
Qed.

(*** We solve the problem using modified wndEval and RTC  ***)
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
    wndEvalRTC p arg arg' ->
    forall args, 
      wndEvalRTC p (TApp fn arg args) (TApp fn arg' args).
induction 1; intros args.
- constructor.
- constructor. apply sAppArg. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
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
    wndEvalsRTC p args args' ->
      wndEvalRTC p (TApp fn arg args) (TApp fn arg args').
induction 1.
- constructor.
- constructor. apply sAppArgs. assumption.
- eapply wERTCtrn. apply IHwndEvalsRTC1. apply IHwndEvalsRTC2.
Qed.

Lemma wndEvalsTC_App_args:
  forall p fn arg args args',
    wndEvalsTC p args args' ->
      wndEvalTC p (TApp fn arg args) (TApp fn arg args').
induction 1.
- constructor. apply sAppArgs. assumption.
- eapply wETCtrn. apply IHwndEvalsTC1. apply IHwndEvalsTC2.
Qed.

Lemma wndEvalRTC_LetIn_dfn:
  forall p nm dfn dfn',
    wndEvalRTC p dfn dfn' ->
    forall bod, 
      wndEvalRTC p (TLetIn nm dfn bod) (TLetIn nm dfn' bod).
induction 1; intros bod.
- constructor.
- constructor. apply sLetInDef. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalTC_LetIn_dfn:
  forall p nm dfn dfn',
    wndEvalTC p dfn dfn' ->
    forall bod, 
      wndEvalTC p (TLetIn nm dfn bod) (TLetIn nm dfn' bod).
induction 1; intros bod.
- constructor. apply sLetInDef. assumption.
- eapply wETCtrn. apply IHwndEvalTC1. apply IHwndEvalTC2.
Qed.

Lemma wndEvalRTC_Case_mch:
  forall p mch mch',
    wndEvalRTC p mch mch' -> 
    forall np brs, 
      wndEvalRTC p (TCase np mch brs) (TCase np mch' brs).
induction 1; intros.
- constructor.
- constructor. apply sCaseArg. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalTC_Case_mch:
  forall p mch mch',
    wndEvalTC p mch mch' -> 
    forall np brs, 
      wndEvalTC p (TCase np mch brs) (TCase np mch' brs).
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


(*** weakening and strengthening ***)
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
- apply sAppFn. apply (H nm ec); trivial.
  apply (proj1 (notPocc_mkApp _ _ H1)). 
- apply sAppArg. apply (H nm ec); trivial. apply (notPocc_TApp H1).
- apply sAppArgs. apply (H nm ec); trivial. apply (notPocc_TApp H1).
- apply sLetInDef. apply (H nm0 ec); trivial; apply (notPocc_TLetIn H1).
- apply sCaseArg. apply (H nm ec); trivial; apply (notPocc_TCase H1).
- apply sCaseBrs. apply (H nm ec); trivial; apply (notPocc_TCase H1).
- apply saHd. apply (H nm ec). trivial. apply (notPoccTrms H1).
- apply saTl. apply (H nm ec). trivial. apply (notPoccTrms H1).
Qed.

Lemma wndEvalTC_weaken:
  forall p t s, wndEvalTC p t s -> forall nm ec, fresh nm p ->
                   wndEvalTC ((nm,ec)::p) t s.
induction 1; intros nm ecx h.
- constructor. apply wndEval_weaken; assumption.
- eapply wETCtrn. apply IHwndEvalTC1; assumption.
  apply IHwndEvalTC2; assumption.
Qed.

