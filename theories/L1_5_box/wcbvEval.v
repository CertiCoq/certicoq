(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_5_box" as L1_5.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.JMeq.
Require Import Common.Common.
Require Import L1_5.term.
Require Import L1_5.program.
Require Import L1_5.wndEval.
Require Import L1_5.awndEval.

Delimit Scope string_scope with string.
Open Scope string_scope.
Open Scope string_scope.
Open Scope bool.
Open Scope list.
Set Implicit Arguments.

(** Big step relation of weak cbv evaluation  **)
(** every field must evaluate **)
Inductive WcbvEval (p:environ) : Term -> Term -> Prop :=
| wPrf: WcbvEval p TProof TProof
| wLam: forall nm ty ty' bod,
          WcbvEval p ty ty' ->
          WcbvEval p (TLambda nm ty bod) (TLambda nm ty' bod)
| wProd: forall nm ty ty' bod,
          WcbvEval p ty ty' ->
          WcbvEval p (TProd nm ty bod) (TProd nm ty' bod)
| wCast: forall t s ck ty,
           WcbvEval p t s ->  WcbvEval p (TCast t ck ty) s
| wConstruct: forall i r, WcbvEval p (TConstruct i r) (TConstruct i r)
| wInd: forall i, WcbvEval p (TInd i) (TInd i) 
| wSort: forall srt, WcbvEval p (TSort srt) (TSort srt)
| wFix: forall dts dts' m,
          WcbvDEvals p dts dts' -> WcbvEval p (TFix dts m) (TFix dts' m)
| wAx: forall nm, LookupAx nm p -> WcbvEval p (TConst nm) (TConst nm)
| wConst: forall nm (t s:Term),
            LookupDfn nm p t -> WcbvEval p t s -> WcbvEval p (TConst nm) s
| wAppLam: forall (fn ty bod a1 a1' s:Term) (args args':Terms) (nm:name),
               WcbvEval p fn (TLambda nm ty bod) ->
               WcbvEvals p (tcons a1 args) (tcons a1' args') ->
               WcbvEval p (whBetaStep bod a1' args') s ->
               WcbvEval p (TApp fn a1 args) s
| wLetIn: forall (nm:name) (dfn ty bod dfn' s:Term),
            WcbvEval p dfn dfn' ->
            WcbvEval p (instantiate dfn' 0 bod) s ->
            WcbvEval p (TLetIn nm dfn ty bod) s
| wAppFix: forall dts m (fn arg arg' s x:Term) (args args':Terms) (ix:nat),
             WcbvEval p fn (TFix dts m) ->
             dnthBody m dts = Some (x, ix) ->
             WcbvEvals p (tcons arg args) (tcons arg' args') ->
             WcbvEval p (pre_whFixStep x dts (tcons arg' args')) s ->
             WcbvEval p (TApp fn arg args) s
| wAppAx: forall fn ax arg args arg' args',
              WcbvEval p fn (TConst ax) ->
              WcbvEvals p (tcons arg args) (tcons arg' args') ->
              WcbvEval p (TApp fn arg args) (TApp (TConst ax) arg' args')
| wAppCstr: forall fn i n arg args arg' args',
              WcbvEval p fn (TConstruct i n) ->
              WcbvEvals p (tcons arg args) (tcons arg' args') ->
              WcbvEval p (TApp fn arg args) (TApp (TConstruct i n) arg' args')
| wAppInd: forall fn i arg args arg' args',
              WcbvEval p fn (TInd i) ->
              WcbvEvals p (tcons arg args) (tcons arg' args') ->
              WcbvEval p (TApp fn arg args) (TApp (TInd i) arg' args')
| wCase: forall mch Mch n args ml ts brs cs s ty,
                WcbvEval p mch Mch ->
                canonicalP Mch = Some (n, args) ->
                tskipn (fst ml) args = Some ts ->
                whCaseStep n ts brs = Some cs ->
                WcbvEval p cs s ->
                WcbvEval p (TCase ml ty mch brs) s
| wCaseAx: forall mch Mch ty ty' ml brs brs',
             WcbvEval p mch Mch ->
             appliedAxiomP Mch = true ->
             WcbvEval p ty ty' ->
             WcbvEvals p brs brs' ->           
             WcbvEval p (TCase ml ty mch brs) (TCase ml ty' Mch brs')
with WcbvEvals (p:environ) : Terms -> Terms -> Prop :=
| wNil: WcbvEvals p tnil tnil
| wCons: forall t t' ts ts',
           WcbvEval p t t' -> WcbvEvals p ts ts' -> 
           WcbvEvals p (tcons t ts) (tcons t' ts')
with WcbvDEvals (p:environ) : Defs -> Defs -> Prop :=
| wDNil: WcbvDEvals p dnil dnil
| wDCons: forall n t t' s s' i ds ds',
           WcbvEval p t t' -> WcbvEval p s s' -> WcbvDEvals p ds ds' -> 
           WcbvDEvals p (dcons n t s i ds) (dcons n t' s' i ds').
Hint Constructors WcbvEval WcbvEvals WcbvDEvals.
Scheme WcbvEval1_ind := Induction for WcbvEval Sort Prop
     with WcbvEvals1_ind := Induction for WcbvEvals Sort Prop
     with WcbvDEvals1_ind := Induction for WcbvDEvals Sort Prop.
Combined Scheme WcbvEvalEvals_ind
         from WcbvEval1_ind, WcbvEvals1_ind, WcbvDEvals1_ind.

(** evaluate omega = (\x.xx)(\x.xx): nontermination **)
Definition xx := (TLambda nAnon prop (TApp (TRel 0) (TRel 0) tnil)).
Definition xxxx := (TApp xx xx tnil).
Goal WcbvEval nil xxxx xxxx.
unfold xxxx, xx.
eapply wAppLam. eapply wLam. eapply wSort. eapply wCons.
eapply wLam. eapply wSort. eapply wNil. cbn.
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
   (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> WFapps ss) /\
   (forall ds es, WcbvDEvals p ds es -> WFappDs ds -> WFappDs es).
Proof.
  intros p hp.
  apply WcbvEvalEvals_ind; intros; try assumption;
  try (solve[inversion_Clear H0; intuition]);
  try (solve[inversion_Clear H1; intuition]).
  - apply H.
    assert (j:= Lookup_pres_WFapp hp l). inversion j. assumption.
  - inversion_Clear H2. specialize (H H7). inversion_Clear H.
    assert (j0: WFapps (tcons a1 args)). constructor; assumption.
    specialize (H0 j0). inversion_Clear H0.
    apply H1.
    apply (whBetaStep_pres_WFapp); try assumption.
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp. assumption.
    + apply H. assumption.
  - inversion_clear H2. apply H1.
    specialize (H H4). inversion_Clear H.
    apply pre_whFixStep_pres_WFapp; try assumption.
    + apply (dnthBody_pres_WFapp H7 _ e).
    + apply H0. constructor; assumption.
  - inversion_Clear H1.
    assert (j0: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j0). inversion_Clear H0.
    constructor; try assumption. not_isApp. constructor.
  - inversion_Clear H1.
    assert (j0: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j0). inversion_Clear H0.
    constructor; intuition.
    destruct H0 as [x1 [x2 [x3 j]]]. discriminate.
  - inversion_Clear H1.
    assert (j0: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j0). inversion_Clear H0.
    constructor; intuition.
    destruct H0 as [x1 [x2 [x3 j]]]. discriminate.
  - apply H0. inversion_Clear H1. 
    refine (whCaseStep_pres_WFapp H7 _ _ e1). 
    refine (tskipn_pres_WFapp _ _ e0).
    refine (canonicalP_pres_WFapp _ e). intuition.
  - inversion_Clear H2. constructor; intuition.
  - inversion_Clear H2. intuition.
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
  - eapply wAx. 
    + apply Lookup_weaken; eassumption.
  - eapply wConst. 
    + apply Lookup_weaken; eassumption.
    + apply H. assumption.
  - eapply wAppLam.
    + apply H. assumption.
    + apply H0. assumption.
    + apply H1. assumption.
  - eapply wLetIn; intuition.
  - eapply wAppFix; try eassumption; intuition.
  - eapply wCase; intuition; eassumption.
Qed.

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
Qed.
*******)

Lemma WcbvEval_wndEvalRTC:
  forall (p:environ), WFaEnv p ->
   (forall t s, WcbvEval p t s -> WFapp t -> wndEvalRTC p t s) /\
   (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> wndEvalsRTC p ts ss) /\
   (forall ds es, WcbvDEvals p ds es -> WFappDs ds -> wndDEvalsRTC p ds es).
Proof.
  intros p hp. apply WcbvEvalEvals_ind; intros; try (solve [constructor]).
  - inversion_Clear H0. 
    eapply wERTCtrn. 
    + apply wndEvalRTC_Lam_typ. eapply H. assumption.
    + constructor. 
  - inversion_Clear H0. 
    eapply wERTCtrn. 
    + apply wndEvalRTC_Prod_typ. eapply H. assumption.
    + constructor. 
  - eapply wERTCtrn; inversion_Clear H0.
    + apply wERTCstep. apply sCast.
    + apply H. assumption.
  - inversion_Clear H0. specialize (H H2). eapply wERTCtrn.
    + constructor.
    + eapply  wndEvalsRTC_Fix_defs. assumption.
  - eapply wERTCtrn; intuition.
    assert (j: WFapp t).
    { unfold LookupDfn in l.
      assert (k:= Lookup_pres_WFapp hp l). inversion k. assumption. }
    eapply wERTCtrn.
    + apply wERTCstep. apply sConst; eassumption.
    + apply H. assert (k:= Lookup_pres_WFapp hp l). inversion k. assumption.
  - inversion_Clear H2.
    assert (k0: WFapps (tcons a1' args')).
    { eapply (proj1 (proj2 (wcbvEval_pres_WFapp hp)) _ _ w0).
      constructor; assumption. }
    inversion_Clear k0.
    eapply (@wERTCtrn _ _ (TApp (TLambda nm ty bod) a1 args)).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; try assumption. intuition.
    + eapply (@wERTCtrn _ _ (TApp (TLambda nm ty bod) a1' args')).
      * eapply wndEvalsRTC_App_args; try reflexivity.
        apply H0. constructor; assumption. not_isApp.
      * { apply (@wERTCtrn _ _ (whBetaStep bod a1' args')).
          - apply wERTCstep. apply sBeta. 
          - apply H1. apply whBetaStep_pres_WFapp; try eassumption.
            + assert (j:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H7).
              inversion_Clear j. assumption. }
  - inversion_Clear H1. eapply (@wERTCtrn _ _ (TLetIn nm dfn' ty bod)).
    + apply wndEvalRTC_LetIn_dfn. intuition.
    + eapply wERTCtrn. apply wERTCstep. apply sLetIn. apply H0.
      apply instantiate_pres_WFapp; try assumption.
      * eapply (proj1 (wcbvEval_pres_WFapp hp)); try eassumption.
  - inversion_clear H2. specialize (H H4).
    assert (j0: WFapps (tcons arg' args')).
    { refine (proj1 (proj2 (wcbvEval_pres_WFapp hp)) _ _ _ _). eassumption.
      constructor; eassumption. }
    assert (j2: WFapp (TFix dts m)).
    { refine (proj1 (wcbvEval_pres_WFapp hp) _ _ w _). assumption. }
    inversion_clear j2.
    assert (j3: WFapp x).
    { refine (dnthBody_pres_WFapp _ _ e). assumption. }
    assert (j4: WFapp (pre_whFixStep x dts (tcons arg' args'))).
    { refine (pre_whFixStep_pres_WFapp _ _ _); assumption. }
    specialize (H1 j4).
    refine (@wERTCtrn _ _ (TApp (TFix dts m) arg args) _ _ _).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; assumption.
    + destruct (WcbvEvals_tcons_tcons w0) as [x0 [x1 j]]. subst.
      eapply wERTCtrn.
      refine (wndEvalsRTC_App_args _ eq_refl eq_refl _);
        try not_isApp. try intuition.
      refine (wERTCtrn _ H1).
      apply wERTCstep. eapply sFix; try eassumption.
  - inversion_Clear H1.
    assert (j: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j). specialize (H H6).
    eapply (@wERTCtrn _ _ (TApp (TConst ax) arg args)).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; try assumption.
    + eapply (@wERTCtrn _ _ (TApp (TConst ax) arg' args')).
      * { eapply wndEvalsRTC_App_args; try not_isApp;
          try reflexivity. assumption. }
      * { apply wERTCrfl. }
  - inversion_Clear H1.
    assert (j: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j). specialize (H H6).
    eapply (@wERTCtrn _ _ (TApp (TConstruct i n) arg args)).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; try assumption.
    + eapply (@wERTCtrn _ _ (TApp (TConstruct i n) arg' args')).
      * { eapply wndEvalsRTC_App_args; try not_isApp;
          try reflexivity. assumption. }
      * { apply wERTCrfl. }
  - inversion_Clear H1.
    assert (j: WFapps (tcons arg args)). constructor; assumption.
    specialize (H0 j). specialize (H H6).
    eapply (@wERTCtrn _ _ (TApp (TInd i) arg args)).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; try assumption.
    + eapply (@wERTCtrn _ _ (TApp (TInd i) arg' args')).
      * { eapply wndEvalsRTC_App_args; try not_isApp;
          try reflexivity. assumption. }
      * { apply wERTCrfl. }
  - inversion_Clear H1. eapply wERTCtrn. 
    + eapply wndEvalRTC_Case_mch. apply H. assumption.
    + eapply (@wERTCtrn _ _ cs). 
      * apply wERTCstep. eapply sCase; eassumption.
      * { apply H0. refine (whCaseStep_pres_WFapp _ _ _ e1). assumption.
          refine (tskipn_pres_WFapp _ _ e0).
          refine (canonicalP_pres_WFapp _ e).
          specialize (H H5).
          refine (wndEvalRTC_pres_WFapp H _). assumption. }
  - inversion_Clear H2. eapply wERTCtrn.
    + eapply wndEvalRTC_Case_mch. apply H. intuition.
    + eapply (@wERTCtrn _ _  (TCase ml ty' Mch brs)).
      * apply wndEvalRTC_Case_ty. intuition.
      * eapply (@wERTCtrn _ _  (TCase ml ty' Mch brs')).
        apply wndEvalRTC_Case_brs. intuition.
        constructor.
  - inversion_Clear H1. eapply (@wEsRTCtrn _ _ (tcons t' ts)).
    + apply wndEvalsRTC_tcons_hd. apply H. assumption.
    + apply wndEvalsRTC_tcons_tl. apply H0. assumption.
  - inversion_Clear H2. eapply (@wDEsRTCtrn _ _ (dcons n t' s i ds)).
    + apply wndDEvalsRTC_dcons_hd. apply H. assumption.
    + eapply (@wDEsRTCtrn _ _ (dcons n t' s' i ds)).
      * apply wndDEvalsRTC_dcons_hd2. intuition.
      * apply wndDEvalsRTC_dcons_tl. intuition.
Qed.


Section wcbvEval_sec.
Variable p:environ.

Function wcbvEval
         (tmr:nat) (t:Term) {struct tmr}: exception Term :=
  match tmr with 
    | 0 => raise ("out of time: " ++ print_term t)
    | S n =>
      match t with      (** look for a redex **)
        | TConst nm =>
          match (lookup nm p) with
            | Some (AstCommon.ecTrm t) => wcbvEval n t
                  (** note hack coding of axioms in environment **)
            | Some (AstCommon.ecTyp _ 0 nil) => ret (TConst nm)
            | Some (AstCommon.ecTyp _ _ _) =>
              raise ("wcbvEval, TConst ecTyp " ++ nm)
            | _ => raise "wcbvEval: TConst environment miss"
          end
        | TCast t ck _ =>
          match wcbvEval n t with
            | Ret et => Ret et
            | Exc s => raise ("wcbvEval: TCast: " ++ s)
          end
        | TApp fn a1 args =>
          match wcbvEvals n (tcons a1 args) with
            | Exc s =>
              raise ("wcbvEval TApp: args don't eval: " ++ s)
            | Ret tnil => raise ("wcbvEval TApp: args eval to tnil")
            | Ret ((tcons b1 brgs)  as ergs) =>
              match wcbvEval n fn with
                | Exc s => raise ("wcbvEval TApp: fn doesn't eval: " ++ s)
                | Ret (TFix dts m) =>
                  match dnthBody m dts with
                    | None => raise ("wcbvEval TApp: dnthBody doesn't eval: ")
                    | Some (x, ix) =>
                      wcbvEval n (pre_whFixStep x dts ergs)
                  end
                | Ret (TLambda _ _ bod) => wcbvEval n (whBetaStep bod b1 brgs)
                | Ret ((TConst _) as fn) (* mch evals to an axiom *)
                | Ret ((TConstruct _ _) as fn)
                | Ret ((TInd _) as fn) => Ret (TApp fn b1 brgs)
                | Ret t =>
                  raise ("wcbvEval TApp: fn not Fix, Lam, constructor, inductive type or axiom: "
                       ++ (print_term t))
              end
          end
        | TCase ml x mch brs =>
          match wcbvEval n mch with
            | Exc str => Exc str
            | Ret emch =>
              match canonicalP emch with
                | Some (r, args) =>
                  match tskipn (fst ml) args with
                    | None => raise "wcbvEval: Case, tskipn"
                    | Some ts =>
                      match whCaseStep r ts brs with
                        | None => raise "wcbvEval: Case, whCaseStep"
                        | Some cs => wcbvEval n cs
                      end
                  end
                | None =>
                  match appliedAxiomP emch with
                    | true =>
                      match wcbvEval n x, wcbvEvals n brs with
                        | Ret X, Ret Brs =>
                          ret (TCase ml X emch Brs)
                        | _, _ => raise "wcbvEval: Case, axiom"
                      end
                    | false => raise "wcbvEval: Case, axiom args"
                  end
              end
          end
        | TLetIn nm df _ bod =>
          match wcbvEval n df with
            | Ret df' => wcbvEval n (instantiate df' 0 bod)
            | Exc s => raise ("wcbvEval: TLetIn: " ++ s)
          end
        | TLambda nn ty t => 
          match wcbvEval n ty with
            | Exc str => Exc str
            | Ret ty' => ret (TLambda nn ty' t)
          end
        | TProd nn ty t =>
          match wcbvEval n ty with
            | Exc str => Exc str
            | Ret ty' => ret (TProd nn ty' t)
          end
        | TFix mfp br =>
          match wcbvDEvals n mfp with
            | Exc str => Exc str
            | Ret mfp' => ret (TFix mfp' br)
          end
        (** already in whnf ***)
        | TConstruct i cn => ret (TConstruct i cn)
        | TInd i => ret (TInd i)
        | TSort srt => ret (TSort srt)
        | TProof => ret TProof
        (** should never appear **)
        | TRel _ => raise "wcbvEval: unbound Rel"
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
        end)
with wcbvDEvals (tmr:nat) (ds:Defs) {struct tmr}
     : exception Defs :=
       (match tmr with 
          | 0 => raise "out of time"
          | S n =>
            match ds with             (** look for a redex **)
              | dnil => ret dnil
              | dcons m s t i ss =>
                match wcbvEval n s, wcbvEval n t, wcbvDEvals n ss with
                  | Ret es, Ret et, Ret ess => ret (dcons m es et i ess)
                  | _, _, _ => raise "wcbvDEvals ??"
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
  forall tmr,
  (forall t s, wcbvEval tmr t = Ret s -> WcbvEval p t s) /\
  (forall ts ss, wcbvEvals tmr ts = Ret ss -> WcbvEvals p ts ss) /\
  (forall (ds es:Defs), wcbvDEvals tmr ds = Ret es -> WcbvDEvals p ds es).
Proof.
  intros tmr.
  apply (wcbvEvalEvalsDEvals_ind
           (fun tmr t su => forall u (p1:su = Ret u), WcbvEval p t u)
           (fun tmr t su => forall u (p1:su = Ret u), WcbvEvals p t u)
           (fun tmr t su => forall u (p1:su = Ret u), WcbvDEvals p t u));
    intros; try discriminate; try (myInjection p1);
    try(solve[constructor]); intuition.
  - eapply wConst; intuition.
    + unfold LookupDfn. apply lookup_Lookup. eassumption.
  - apply wAx. unfold LookupAx. apply lookup_Lookup. eassumption.
  - specialize (H1 _ p1). specialize (H _ e1). specialize (H0 _ e2).
    refine (wAppFix _ _ _ _); try eassumption.
  - specialize (H1 _ p1). specialize (H _ e1). specialize (H0 _ e2).
    eapply wAppLam; try eassumption.
  - eapply wCase. eapply H. eapply e1. eapply e2. eapply e3. eapply e4.
    intuition.
  - eapply wLetIn; intuition.
    + apply H. assumption.
Qed.


(** need strengthening to large-enough fuel to make the induction
 *** go through **)
Lemma pre_WcbvEval_wcbvEval:
    (forall t s, WcbvEval p t s ->
          exists n, forall m, m >= n -> wcbvEval (S m) t = Ret s) /\
    (forall ts ss, WcbvEvals p ts ss ->
          exists n, forall m, m >= n -> wcbvEvals (S m) ts = Ret ss) /\
    (forall ds es, WcbvDEvals p ds es ->
          exists n, forall m, m >= n -> wcbvDEvals (S m) ds = Ret es).
assert (j:forall m x, m > x -> m = S (m - 1)). { induction m; intuition. }
apply WcbvEvalEvals_ind; intros; try (exists 0; intros mx h; reflexivity).
- destruct H. exists (S x). intros m hm. simpl. rewrite (j m x); try omega.
  + rewrite (H (m - 1)); try omega. reflexivity. 
- destruct H. exists (S x). intros m hm. simpl. rewrite (j m x); try omega.
  + rewrite (H (m - 1)); try omega. reflexivity.
- destruct H.  exists (S x). intros m h. simpl.
  rewrite (j m x); try omega. rewrite H; try omega. reflexivity.    
- destruct H. exists (S x). intros m0 h. simpl.
  rewrite (j m0 x); try omega. rewrite H; try omega. reflexivity.
- exists 0. intros m h. simpl.
  unfold LookupAx in l. unfold lookup. rewrite (Lookup_lookup l). reflexivity.
- destruct H. exists (S x). intros mm h. simpl.
  rewrite (j mm x); try omega.
  unfold LookupDfn in l. unfold lookup. rewrite (Lookup_lookup l).
  apply H. omega.
- destruct H, H0, H1. exists (S (max x (max x0 x1))). intros m h.
  assert (j1:= max_fst x (max x0 x1)). 
  assert (lx: m > x). omega.
  assert (j2:= max_snd x (max x0 x1)).
  assert (j3:= max_fst x0 x1).
  assert (lx0: m > x0). omega.
  assert (j4:= max_snd x0 x1).
  assert (j5:= max_fst x0 x1).
  assert (lx1: m > x1). omega.
  assert (k:wcbvEval m fn = Ret (TLambda nm ty bod)).
  + rewrite (j m (max x (max x0 x1))). apply H.
    assert (l:= max_fst x (max x0 x1)); omega. omega.
  + assert (k0:wcbvEvals m (tcons a1 args) = Ret (tcons a1' args')).
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
- destruct H, H0, H1. exists (S (max x0 (max x1 x2))). intros mx h.
  assert (j1:= max_fst x0 (max x1 x2)). 
  assert (lx: mx > x0). omega.
  assert (j2:= max_snd x0 (max x1 x2)).
  assert (j3:= max_fst x1 x2).
  assert (lx0: mx > x1). omega.
  assert (j4:= max_snd x1 x2).
  assert (j5:= max_fst x1 x2).
  assert (lx1: mx > x2). omega.
  destruct (WcbvEvals_tcons_tcons w0) as [y0 [y1 k0]].
  simpl. rewrite (j mx x0); try omega. rewrite H0; try omega.
  rewrite k0 in *. rewrite H; try omega. rewrite e.
  apply H1. omega.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try omega.
  rewrite (H (mx - 1)); try omega.
  rewrite (H0 (mx - 1)); try omega.
  reflexivity.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try omega.
  rewrite (H (mx - 1)); try omega.
  rewrite (H0 (mx - 1)); try omega.
  reflexivity.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try omega.
  rewrite (H (mx - 1)); try omega.
  rewrite (H0 (mx - 1)); try omega.
  reflexivity.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
  rewrite e. rewrite e0. rewrite e1. rewrite (H0 (mx - 1)); try omega.
  reflexivity.
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
  rewrite H; try omega.
  assert (k:= appliedAxiomP_canonicalP _ e).
  rewrite k. rewrite e.
  rewrite H0; try omega.
  rewrite H1; try omega. reflexivity.
- destruct H, H0. exists (S (max x x0)). intros mx h.
  assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
  simpl. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
  rewrite H0; try omega. reflexivity.
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
  rewrite H; try omega. rewrite H0; try omega. rewrite H1; try omega.
  reflexivity.
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
