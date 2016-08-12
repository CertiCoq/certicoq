
(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_MalechaQuoted" as L1.
Add LoadPath "../L1_5_box" as L1_5.
Add LoadPath "../L2_typeStripped" as L2.
Add LoadPath "../L3_flattenedApp" as L3.
(******)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import L3.term.
Require Import L3.program.
Require Import L3.compile.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(*** non-deterministic small step evaluation relation ***)
Inductive wndEval (p:environ Term) : Term -> Term -> Prop :=
(** contraction steps **)
| sConst: forall (s:string) (t:Term),
            LookupDfn s p t -> wndEval p (TConst s) t
| sBeta: forall (nm:name) (bod arg:Term),
           wndEval p (TApp (TLambda nm bod) arg) (whBetaStep bod arg)
     (* note: [instantiate] is total *)
| sLetIn: forall (nm:name) (dfn bod:Term),
            wndEval p (TLetIn nm dfn bod) (instantiate dfn 0 bod)
     (* Case argument must be in Canonical form *)
     (* np is the number of parameters of the datatype *)
| sCase: forall (n arty:nat) (ml : inductive * nat * list nat) (s:Term)
                (i:inductive) (args brs ts:Terms),
           tskipn (snd (fst ml)) args = Some ts ->
           whCaseStep n ts brs = Some s ->
           wndEval p (TCase ml (TConstruct i n arty args) brs) s
| sFix: forall (dts:Defs) (m:nat) (arg f:Term),
          whFixStep dts m = Some f ->
          wndEval p (TApp (TFix dts m) arg) (TApp f arg)
(** congruence steps **)
(** no xi rules: sLambdaR, sProdR, sLetInR,
*** no congruence on Case branches or Fix ***)
| sAppFn:  forall (t r arg:Term),
              wndEval p t r -> wndEval p (TApp t arg) (TApp r arg)
| sAppArg: forall (t arg brg:Term),
              wndEval p arg brg ->
              wndEval p (TApp t arg) (TApp t brg)
| sLetInDef:forall (nm:name) (d1 d2 bod:Term),
              wndEval p d1 d2 ->
              wndEval p (TLetIn nm d1 bod) (TLetIn nm d2 bod)
| sCaseArg: forall (ml: inductive * nat * list nat) (mch can:Term) (brs:Terms),
              wndEval p mch can ->
              wndEval p (TCase ml mch brs) (TCase ml can brs)
| sCaseBrs: forall (ml: inductive * nat * list nat) (mch:Term) (brs brs':Terms),
              wndEvals p brs brs' ->
              wndEval p (TCase ml mch brs) (TCase ml mch brs')
with  (** step any term in a list of terms **)
wndEvals (p:environ Term) : Terms -> Terms -> Prop :=
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
Definition xx := (TLambda nAnon (TApp (TRel 0) (TRel 0))).
Definition xxxx := (TApp xx xx).
Goal wndEval nil xxxx xxxx.
unfold xxxx, xx. eapply sBeta. 
Qed.


(** when reduction stops **)
Definition no_step {A:Set} (R:A -> A -> Prop) (a:A) :=
  forall (b:A), ~ R a b.
Definition no_wnd_step (p:environ Term) (t:Term) : Prop :=
  no_step (wndEval p) t.
Definition no_wnds_step (p:environ Term) (ts:Terms) : Prop :=
  no_step (wndEvals p) ts.


(** reflexive-transitive closure of wndEval **)
Inductive wndEvalRTC (p:environ Term): Term -> Term -> Prop :=
| wERTCrfl: forall t, wndEvalRTC p t t
| wERTCstep: forall t s, wndEval p t s -> wndEvalRTC p t s
| wERTCtrn: forall t s u, wndEvalRTC p t s -> wndEvalRTC p s u ->
                          wndEvalRTC p t u.
Inductive wndEvalsRTC (p:environ Term): Terms -> Terms -> Prop :=
(** | wEsRTCrfl: forall ts, WNorms ts -> wndEvalsRTC p ts ts ??? **)
| wEsRTCrfl: forall ts, wndEvalsRTC p ts ts
| wEsRTCstep: forall ts ss, wndEvals p ts ss -> wndEvalsRTC p ts ss
| wEsRTCtrn: forall ts ss us, wndEvalsRTC p ts ss -> wndEvalsRTC p ss us ->
                          wndEvalsRTC p ts us.
Hint Constructors wndEvalRTC wndEvalsRTC.

Inductive wndEvalTC (p:environ Term): Term -> Term -> Prop :=
| wETCstep: forall t s, wndEval p t s -> wndEvalTC p t s
| wETCtrn: forall t s u, wndEvalTC p t s -> wndEvalTC p s u ->
                          wndEvalTC p t u.
Inductive wndEvalsTC (p:environ Term): Terms -> Terms -> Prop :=
| wEsTCstep: forall ts ss, wndEvals p ts ss -> wndEvalsTC p ts ss
| wEsTCtrn: forall ts ss us, wndEvalsTC p ts ss -> wndEvalsTC p ss us ->
                          wndEvalsTC p ts us.
Hint Constructors wndEvalTC wndEvalsTC.
(**
Combined Scheme wndEvalEvalsTC from wndEvalTC_ind, wndEvalsTC_ind.
**)

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

Lemma wndEvalRTC_App_arg:
  forall p fn arg arg',
    wndEvalRTC p arg arg' -> wndEvalRTC p (TApp fn arg) (TApp fn arg').
induction 1.
- constructor.
- constructor. apply sAppArg. assumption.
- eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalTC_App_arg:
  forall p fn arg arg',
    wndEvalTC p arg arg' -> wndEvalTC p (TApp fn arg) (TApp fn arg').
induction 1.
- constructor. apply sAppArg. assumption.
- eapply wETCtrn. apply IHwndEvalTC1. apply IHwndEvalTC2.
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
- eapply sCase; eassumption.
Qed.

Lemma wndEval_strengthen:
  forall (pp:environ Term),
  (forall t s, wndEval pp t s -> forall nm ec p, pp = (nm,ec)::p ->
        ~ PoccTrm nm t -> wndEval p t s) /\
  (forall ts ss, wndEvals pp ts ss -> forall nm ec p, pp = (nm,ec)::p ->
        ~ PoccTrms nm ts -> wndEvals p ts ss).
intros pp. apply wndEvalEvals_ind; intros; auto.
- apply sConst. 
  assert (j:= neq_sym (inverse_Pocc_TConstL H0)). inversion_Clear l.
  + injection H2; intros. contradiction.
  + injection H4; intros. subst. assumption.
- eapply sCase; eassumption.
- apply sAppFn. apply (H nm ec); trivial. apply (notPocc_TApp H1).
- apply sAppArg. apply (H nm ec); trivial. apply (notPocc_TApp H1).
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


(***
Lemma Instantiate_pres_Crct:
  forall p tin bod n,
    Crct p n tin -> Crct p (S n) bod -> Crct p n (instantiate tin n bod).
induction bod; intros; unfold instantiate.
- destruct (lt_eq_lt_dec n0 n). destruct s.
  + rewrite (proj1 (nat_compare_lt _ _) l). apply (IRelLt l).


Admitted.

Lemma wndEval_pres_Crct:
  (forall p n t, Crct p n t -> forall s, wndEval p t s -> Crct p n s) /\
  (forall p n ts, Crcts p n ts -> forall ss, wndEvals p ts ss ->
                                             Crcts p n ss) /\
  (forall (p:environ Term) (n:nat) (ds:Defs), CrctDs p n ds -> True).
apply CrctCrctsCrctDs_ind; intros; auto.
- inversion H.
- constructor; auto. apply H0.
  assert (j2:= proj1 (Crct_fresh_Pocc) _ _ _ H _ H3).
  eapply (proj1 (wndEval_strengthen ((nm, ecConstr s) :: p))); try eassumption.
  + reflexivity.
- inversion H0.
- inversion H3; subst; apply CrctCast.
  + apply H0. assumption.
  + assumption.
  + assumption.
  + apply H2. assumption.
- inversion H3; subst; apply CrctProd.
  + assumption.
  + apply H2. assumption.
- inversion H3; subst; apply CrctLam.
  + assumption.
  + apply H2. assumption.
- inversion H5; subst.
  + apply Instantiate_pres_Crct; assumption.
  + apply CrctLetIn; try assumption.
    * apply H4. assumption.
  + apply CrctLetIn; try assumption.
    * apply H0. assumption.
- inversion H5; subst.


***)

(***
Goal
  forall p,
    (forall t u, wndEval p t u -> ~ (exists str, t = TConst str) ->
                 forall nm, PoccTrm nm u -> PoccTrm nm t) /\
    (forall ts us, wndEvals p ts us ->
                   forall nm, PoccTrms nm us -> PoccTrms nm ts).
intros p; apply wndEvalEvals_ind; intros; try (intros h).
- elim H. exists s. reflexivity.
- 
Lemma wndEval_Pocc:
  (forall p n t, Crct p n t -> forall s, wndEval p t s ->
      forall nm, PoccTrm nm s -> PoccTrm nm t) /\
  (forall p n ts, Crcts p n ts -> forall ss, wndEvals p ts ss ->
      forall nm, PoccTrms nm ss -> PoccTrms nm ts) /\
  (forall (p:environ Term) (n:nat) (ds:Defs), CrctDs p n ds -> True).
apply CrctCrctsCrctDs_ind; intros; auto.
- inversion H.
- 


Lemma wndEval_pres_Crct:
  (forall p n t, Crct p n t -> forall s, wndEval p t s -> Crct p n s) /\
  (forall p n ts, Crcts p n ts -> forall ss, wndEvals p ts ss ->
                                             Crcts p n ss) /\
  (forall (p:environ Term) (n:nat) (ds:Defs), CrctDs p n ds -> True).
apply CrctCrctsCrctDs_ind; intros; auto; try (solve [constructor]).
- inversion H.
- constructor; auto. apply H2.
  assert (j:= proj1 (Crct_fresh_Pocc) _ _ _ H1 _ H3).
***)
