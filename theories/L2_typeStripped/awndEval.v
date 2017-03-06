(** An alternative definition of wndEval that is extensionally
*** equivalent for well-formed programs
**)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Setoids.Setoid.
Require Import L2.term.
Require Import L2.program.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(*** alrernative non-deterministic small step evaluation relation ***)
Section Env.
Variable p:environ Term.
Inductive awndEval : Term -> Term -> Prop :=
(** contraction steps **)
| aConst: forall (s:string) (t:Term),
          LookupDfn s p t -> awndEval (TConst s) t
| aBeta: forall (nm:name) (bod arg:Term) (args:Terms),
           awndEval (TApp (TLambda nm bod) arg args)
                   (whBetaStep bod arg args)
     (* note: [instantiate] is total *)
| aLetIn: forall (nm:name) (dfn bod:Term),
            awndEval (TLetIn nm dfn bod) (instantiate dfn 0 bod)
     (* Case argument must be in Canonical form *)
     (* np is the number of parameters of the datatype *)
| aCase: forall (ml:inductive * nat) (s mch:Term)
                 (args ts:Terms) (brs:Defs) (n arty:nat),
            canonicalP mch = Some (n, args, arty) ->
            tskipn (snd ml) args = Some ts ->
            whCaseStep n ts brs = Some s ->
            awndEval (TCase ml mch brs) s
| aFix: forall (dts:Defs) (m:nat) (arg:Term) (args:Terms)
               (x:Term) (ix:nat),
          (** ix is index of recursive argument **)
          dnthBody m dts = Some (x, ix) ->
          ix <= tlength args ->
          awndEval (TApp (TFix dts m) arg args)
                   (pre_whFixStep x dts (tcons arg args))
| aCast: forall t, awndEval (TCast t) t
| aProof: forall t, awndEval (TProof t) t
(** congruence steps **)
(** no xi rules: sLambdaR, sProdR, sLetInR,
*** no congruence on Case branches or Fix ***)
| aAppFn:  forall (t r arg:Term) (args:Terms),
              awndEval t r ->
              awndEval (mkApp t (tcons arg args)) (mkApp r (tcons arg args))
| aAppArgs: forall (t arg brg:Term) (args brgs:Terms),
              awndEvals (tcons arg args) (tcons brg brgs) ->
              awndEval (TApp t arg args) (TApp t brg brgs)
| aLetInDef:forall (nm:name) (d1 d2 bod:Term),
              awndEval d1 d2 ->
              awndEval (TLetIn nm d1 bod) (TLetIn nm d2 bod)
| aCaseArg: forall (ml:inductive * nat) (mch can:Term) (brs:Defs),
              awndEval mch can ->
              awndEval (TCase ml mch brs) (TCase ml can brs)
    (****
| aCaseBrs: forall (ml:inductive * nat * list nat) (mch:Term) (brs brs':Terms),
              awndEvals brs brs' ->
              awndEval (TCase ml mch brs) (TCase ml mch brs')
***************)
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
  forall nm bod s,
    awndEval (TLambda nm bod) s -> s = (TLambda nm bod).
intros nm bod s h. inversion_Clear h. 
- assert (j:= mkApp_isApp t arg args).
  destruct j as [x0 [x1 [x2 k]]]. rewrite k in H. discriminate.
Qed.

Lemma awndEval_Prod_inv:
  forall nm bod s,
    awndEval (TProd nm bod) s -> s = (TProd nm bod).
intros nm bod s h. inversion_Clear h.
- assert (j:= mkApp_isApp t arg args).
  destruct j as [x0 [x1 [x2 k]]]. rewrite k in H. discriminate.
Qed.

Lemma awndEval_Cast_inv:
  forall tm s, awndEval (TCast tm) s -> tm = s.
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
  intros hp. apply awndEvalEvals_ind; intros; try assumption;
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

