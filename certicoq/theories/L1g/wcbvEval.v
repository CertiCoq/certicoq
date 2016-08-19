(****)
Add LoadPath "../common" as Common.
Add LoadPath "../L1g" as L1g.
(****)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.JMeq.
Require Import Common.AstCommon.
Require Import L1g.term.
Require Import L1g.program.
Require Import L1g.wndEval.
Require Import L1g.awndEval.

Delimit Scope string_scope with string.
Open Scope string_scope.
Open Scope string_scope.
Open Scope bool.
Open Scope list.
Set Implicit Arguments.

(** Big step relation of weak cbv evaluation  **)
(** every field must evaluate **)
Inductive WcbvEval (p:environ Term) : Term -> Term -> Prop :=
| wLam: forall nm ty ty' bod,
          WcbvEval p ty ty' ->
          WcbvEval p (TLambda nm ty bod) (TLambda nm ty' bod)
| wProd: forall nm ty ty' bod,
          WcbvEval p ty ty' ->
          WcbvEval p (TProd nm ty bod) (TProd nm ty' bod)
| wCast: forall t s ck ty,
           WcbvEval p t s ->  WcbvEval p (TCast t ck ty) s
| wConstruct: forall i r arty,
                WcbvEval p (TConstruct i r arty) (TConstruct i r arty)
| wInd: forall i, WcbvEval p (TInd i) (TInd i) 
| wSort: forall srt, WcbvEval p (TSort srt) (TSort srt)
| wFix: forall dts m, WcbvEval p (TFix dts m) (TFix dts m)
| wAx: WcbvEval p TAx TAx
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
| wAppFix: forall dts m z (fn arg arg' s x t:Term) (args args':Terms) (ix:nat),
             WcbvEval p fn (TFix dts m) ->
             dnthBody m dts = Some (x, ix) ->
             (* eval all args here for convenient test Fix is guarded *)
             WcbvEvals p (tcons arg args) (tcons arg' args') ->
             tnth ix (tcons arg' args') = Some t ->
             canonicalP t = Some z ->   (* test Fix is guarded *)
             WcbvEval p (pre_whFixStep x dts (tcons arg' args')) s ->
             WcbvEval p (TApp fn arg args) s
| wAppCong: forall fn fn' arg args arg' args',
              WcbvEval p fn fn' ->
              ~ isLambda fn' -> ~ isFix fn' ->
              WcbvEvals p (tcons arg args) (tcons arg' args') ->
              WcbvEval p (TApp fn arg args) (mkApp fn' (tcons arg' args'))
| wCase: forall mch Mch n args ml ts brs cs s ty,
                WcbvEval p mch Mch ->
                canonicalP Mch = Some (n, args) ->
                tskipn (snd (fst ml)) args = Some ts ->
                whCaseStep n ts brs = Some cs ->
                WcbvEval p cs s ->
                WcbvEval p (TCase ml ty mch brs) s
| wCaseCong: forall mch Mch ty ty' ml brs brs',
             WcbvEval p mch Mch ->
             canonicalP Mch = None ->
             WcbvEval p ty ty' ->
             WcbvEvals p brs brs' ->           
             WcbvEval p (TCase ml ty mch brs) (TCase ml ty' Mch brs')
| wWrong: forall str, WcbvEval p (TWrong str) (TWrong str)
with WcbvEvals (p:environ Term) : Terms -> Terms -> Prop :=
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
eapply wAppLam. eapply wLam. eapply wSort. 
eapply wLam. eapply wSort. 
unfold whBetaStep, instantiate.
rewrite (proj2 (nat_compare_eq_iff 0 0) eq_refl).
rewrite mkApp_idempotent. simpl. 
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
  intros p hp.
  apply WcbvEvalEvals_ind; intros; try assumption;
  try (solve[inversion_Clear H0; intuition]);
  try (solve[inversion_Clear H1; intuition]);
  try (solve[inversion_Clear H2; intuition]).
  - apply H.
    assert (j:= Lookup_pres_WFapp hp l). inversion j. assumption.
  - inversion_clear H2. apply H1.
    specialize (H H4). inversion_Clear H.
    apply (whBetaStep_pres_WFapp); intuition. 
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp. assumption.
    + apply H. assumption.
  - inversion_clear H2. apply H1.
    specialize (H H4). inversion_Clear H.
    apply pre_whFixStep_pres_WFapp; try assumption.
    + apply (dnthBody_pres_WFapp H7 _ e).
    + apply H0. constructor; assumption.
  - inversion_Clear H1.
    destruct (mkApp_isApp_lem fn' arg' args') as
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
  - apply H0. inversion_Clear H1. 
    refine (whCaseStep_pres_WFapp H7 _ _ e1). 
    refine (tskipn_pres_WFapp _ _ e0).
    refine (canonicalP_pres_WFapp _ e). intuition.
Qed.

Lemma WcbvEval_weaken:
  forall p,
  (forall t s, WcbvEval p t s -> forall nm ec, fresh nm p ->
                   WcbvEval ((nm,ec)::p) t s) /\
  (forall ts ss, WcbvEvals p ts ss -> forall nm ec, fresh nm p ->
                   WcbvEvals ((nm,ec)::p) ts ss).
Proof.
  intros p. apply WcbvEvalEvals_ind; intros; auto.
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

*******)

Lemma WcbvEval_wndEvalRTC:
  forall (p:environ Term), WFaEnv p ->
    (forall t s, WcbvEval p t s -> WFapp t -> wndEvalRTC p t s) /\
    (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> wndEvalsRTC p ts ss).
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
  - eapply wERTCtrn; intuition.
    assert (j: WFapp t).
    { unfold LookupDfn in l.
      assert (k:= Lookup_pres_WFapp hp l). inversion k. assumption. }
    eapply wERTCtrn.
    + apply wERTCstep. apply sConst; eassumption.
    + apply H. assert (k:= Lookup_pres_WFapp hp l). inversion k. assumption.
  - inversion_Clear H2.
    eapply (@wERTCtrn _ _ (TApp (TLambda nm ty bod) a1 args)).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; try assumption. intuition.
    + eapply (@wERTCtrn _ _ (TApp (TLambda nm ty bod) a1' args)).
      * eapply wndEvalRTC_App_arg; try reflexivity.
        apply H0. assumption.
      * { apply (@wERTCtrn _ _ (whBetaStep bod a1' args)).
          - apply wERTCstep. apply sBeta. 
          - apply H1. apply whBetaStep_pres_WFapp; try eassumption.
            + assert (j:= proj1 (wcbvEval_pres_WFapp hp) _ _ w H7).
              inversion_Clear j. assumption.
            + apply (proj1 (wcbvEval_pres_WFapp hp) _ _ w0 H8). }
  - inversion_Clear H1. eapply (@wERTCtrn _ _ (TLetIn nm dfn' ty bod)).
    + apply wndEvalRTC_LetIn_dfn. intuition.
    + eapply wERTCtrn. apply wERTCstep. apply sLetIn. apply H0.
      apply instantiate_pres_WFapp; try assumption.
      * eapply (proj1 (wcbvEval_pres_WFapp hp)); try eassumption.
  - inversion_clear H2. specialize (H H4).
    assert (j0: WFapps (tcons arg' args')).
    { refine (proj2 (wcbvEval_pres_WFapp hp) _ _ _ _). eassumption.
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
  - inversion_Clear H1. specialize (H H6). specialize (H0 (wfacons H7 H8)).
    eapply (@wERTCtrn _ _ (TApp fn arg' args')).
    + eapply wndEvalsRTC_App_args; try reflexivity; try assumption.
    + rewrite <- mkApp_goodFn; try assumption.      
      assert (j: WFapps (tcons arg' args')).
      { apply (proj2 (wcbvEval_pres_WFapp hp) _ _ w0).
        constructor; assumption. }
      inversion_Clear j.
      eapply wndEvalRTC_App_fn; try assumption.
  - inversion_Clear H1. eapply wERTCtrn. 
    + eapply wndEvalRTC_Case_mch. apply H. assumption.
    + eapply (@wERTCtrn _ _ cs). 
      * apply wERTCstep. eapply sCase; eassumption.
      * { apply H0. refine (whCaseStep_pres_WFapp _ _ _ e1). assumption.
          refine (tskipn_pres_WFapp _ _ e0).
          refine (canonicalP_pres_WFapp _ e).
          specialize (H H5).
          refine (wndEvalRTC_pres_WFapp _ _ _); eassumption. }
  - inversion_Clear H2. eapply wERTCtrn.
    + eapply wndEvalRTC_Case_mch. apply H. assumption.
    + eapply (@wERTCtrn _ _  (TCase ml ty' Mch brs)).
      * apply wndEvalRTC_Case_ty. intuition.
      * eapply (@wERTCtrn _ _  (TCase ml ty' Mch brs')).
        apply wndEvalRTC_Case_brs. intuition.
        constructor.
  - inversion_Clear H1. eapply (@wEsRTCtrn _ _ (tcons t' ts)).
    + apply wndEvalsRTC_tcons_hd. apply H. assumption.
    + apply wndEvalsRTC_tcons_tl. apply H0. assumption.
Qed.



(*************************
Goal
  forall t, WFapp t ->
            forall fn arg args, t = (mkApp fn (tcons arg args)) ->
                                WFapp fn /\ WFapp arg /\ WFapps args.
Proof.
  induction 1; intros; destruct (mkApp_isApp fn arg args) as [y [y0 [y1 jy]]];
  try (solve[rewrite jy in *;  discriminate]).
  - rewrite mkApp_goodFn in jy; try assumption. myInjection jy.
    apply IHWFapp1.
  
Lemma wcbvEval_no_further:
  forall p,
    (forall t s, WcbvEval p t s -> WFapp s -> WcbvEval p s s) /\
    (forall ts ss, WcbvEvals p ts ss -> WFapps ss -> WcbvEvals p ss ss).
Proof.
  intros p.
  apply WcbvEvalEvals_ind; cbn; intros. Focus 13.
  - Check mkApp_pres_WFapp.
  
  try inversion_Clear H0; try inversion_Clear H1;
  try (solve [constructor; intuition]); intuition;
  try (assert (j:= mkApp_isApp fn' arg' args');
       destruct j as [x0 [x1 [x2 k]]]; rewrite k in *; discriminate).
  - rewrite mkApp_goodFn in H2.
    + myInjection H2.
      rewrite <- mkApp_goodFn at 2; try assumption.
      apply wAppCong; intuition.
    + intros h. destruct h as [y0 [y1 [y2 ky]]]. rewrite ky in H2.
      cbn in H2. myInjection H2.

  - rewrite <- mkApp_goodFn at 2; try assumption.
    apply wAppCong; try assumption.
    
  - destruct (mkApp_isApp_lem fn' arg' args') as
        [y0 [y1 [y2 [ka [[kc1 [kc2 [kc3 kc4]]] | [kd1 [kd2 kd3]]]]]]].
    + subst. rewrite <- mkApp_goodFn at 2; try assumption.
      apply wAppCong; try assumption.
      rewrite ka.


Check (mkApp_isApp_lem fn' arg' args').
    
  - admit. (** rewrite H2 at 2. apply wAppCong; try assumption. *)
  - inversion_Clear H2.
    specialize (H1 H8). specialize (H0 H9). specialize (H H6).
    eapply wCaseCong; try eassumption.
Qed.
 *********************)

Section wcbvEval_sec.
Variable p : environ Term.

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
          match wcbvEval n fn with
            | Exc s => raise ("wcbvEval TApp: fn doesn't eval: " ++ s)
            | Ret (TLambda _ _ bod) =>
              match wcbvEval n a1 with
                | Exc s =>  raise ("wcbvEval TApp: arg doesn't eval: " ++ s)
                | Ret b1 => wcbvEval n (whBetaStep bod b1 args)
              end
            | Ret Fn =>
              match wcbvEvals n (tcons a1 args) with
                | Exc s => raise ("wcbvEval TApp: args don't eval: " ++ s)
                | Ret ergs =>
                  match Fn with
                    | TFix dts m =>  
                      match dnthBody m dts with
                        | None =>
                          raise ("wcbvEval TApp: dnthBody doesn't eval: ")
                        | Some (x, ix) =>
                          match tnth ix ergs with
                            | None => raise ("wcbvEval TApp: tnth not defined")
                            | Some t =>
                              match canonicalP t with (* test Fix is guarded *)
                                | Some _ =>
                                  wcbvEval n (pre_whFixStep x dts ergs)
                                | None => raise ("wcbvEval TFix: rec arg ")
                              end
                          end
                      end
                    | Fn => ret (mkApp Fn ergs)
                  end
              end
          end
            (****************
        | TApp fn a1 args =>
          match wcbvEval n fn with
            | Exc s => raise ("wcbvEval TApp: fn doesn't eval: " ++ s)
            | Ret (TLambda _ _ bod) =>
              match wcbvEval n a1 with
                | Exc s =>  raise ("wcbvEval TApp: arg doesn't eval: " ++ s)
                | Ret b1 => wcbvEval n (whBetaStep bod b1 args)
              end
            | Ret (TFix dts m) =>
              match dnthBody m dts with
                | None => raise ("wcbvEval TApp: dnthBody doesn't eval: ")
                | Some (x, ix) =>
                  match tnth ix (tcons a1 args) with
                    | None => raise ("wcbvEval TApp: tnth not defined")
                    | Some t =>
                      match wcbvEval n t with
                        | Ret t' =>
                          match canonicalP t' with
                            | Some _ => wcbvEval n (pre_whFixStep x dts args)
                            | None => raise ("wcbvEval TFix: rec arg")
                          end
                      end
                  end
              end
            | Ret Fn =>
              match wcbvEvals n (tcons a1 args) with
                | Exc s => raise ("wcbvEval TApp: args don't eval: " ++ s)
                | Ret ergs => ret (mkApp Fn ergs)
              end
          end
*********************)
        | TCase ml tp mch brs =>
          match wcbvEval n mch with
            | Exc str => Exc str
            | Ret emch =>
              match canonicalP emch with
                | None =>
                  match wcbvEval n tp with
                    | Exc str => Exc str
                    | Ret etp =>
                      match wcbvEvals n brs with
                        | Exc _ => Exc ("wcbvEval; TCase, brs don't eval")
                        | Ret ebrs => Ret (TCase ml etp emch ebrs)
                      end
                  end
                | Some (r, args) =>
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
        (** already in whnf ***)
        | TAx => ret TAx
        | TFix mfp br => ret (TFix mfp br)
        | TConstruct i cn arty => ret (TConstruct i cn arty)
        | TInd i => ret (TInd i)
        | TSort srt => ret (TSort srt)
        (** should never appear **)
        | TRel _ => raise "wcbvEval: unbound Rel"
        | TWrong str => ret (TWrong str)
      end
  end
with wcbvEvals (tmr:nat) (ts:Terms) {struct tmr} : exception Terms :=
       match tmr with 
         | 0 => raise "out of time"
         | S n => match ts with             (** look for a redex **)
                    | tnil => ret tnil
                    | tcons s ss =>
                      match wcbvEval n s with
                        | Exc s => raise ("wcbEvals: tconsl " ++ s)
                        | Ret es =>
                          match wcbvEvals n ss with
                            | Exc s => raise ("wcbEvals: tconsr " ++ s)
                            | Ret ess => ret (tcons es ess)
                          end
                      end
                  end
       end.
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
    + unfold LookupDfn. apply lookup_Lookup. eassumption.
  - specialize (H1 _ p1). specialize (H _ e1). specialize (H0 _ e2).
    eapply wAppLam; eassumption.
  - specialize (H1 _ p1). specialize (H _ e1). specialize (H0 _ e2).
    destruct (isFix_dec Fn); subst.
    + destruct (WcbvEvals_tcons_tcons H0) as [g0 [g1 hg]]. subst.
      refine (wAppFix _ _ _ _ _ _); try eassumption.
    + elim n0. auto.
  - specialize (H _ e1). specialize (H0 _ e2).
    destruct (WcbvEvals_tcons_tcons H0) as [g0 [g1 hg]]. subst.
    eapply wAppCong; try eassumption.
    + destruct Fn0; try not_isLambda. auto.
    + destruct Fn0; try not_isFix. auto.
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
Proof.
  assert (j:forall m x, m > x -> m = S (m - 1)). { induction m; intuition. }
                                                 apply WcbvEvalEvals_ind; intros; try (exists 0; intros mx h; reflexivity).
  - destruct H. exists (S x). intros m hm. simpl. rewrite (j m x); try omega.
    + rewrite (H (m - 1)); try omega. reflexivity. 
  - destruct H. exists (S x). intros m hm. simpl. rewrite (j m x); try omega.
    + rewrite (H (m - 1)); try omega. reflexivity.
  - destruct H.  exists (S x). intros m h. simpl.
    rewrite (j m x); try omega. rewrite H; try omega. reflexivity.    
  - destruct H. exists (S x). intros mm h. simpl.
    rewrite (j mm x); try omega.
    unfold LookupDfn in l. rewrite (Lookup_lookup l).
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
    rewrite k0 in *. rewrite H; try omega. rewrite e. rewrite e0. rewrite e1.
    apply H1. omega.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    cbn. rewrite (j mx x); try omega. rewrite (H0 (mx - 1)); try omega.
    rewrite (H (mx - 1)); try omega.
    destruct fn'; try reflexivity.
    + elim n; auto.
    + elim n0; auto.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    cbn. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
    rewrite e. rewrite e0. rewrite e1. rewrite (H0 (mx - 1)); try omega.
    reflexivity.
  - destruct H as [x0 jx0], H0 as [x1 jx1], H1 as [x2 jx2].
    exists (S (max x0 (max x1 x2))). intros mx h.
    assert (j1:= max_fst x0 (max x1 x2)). 
    assert (lx: mx > x0). omega.
    assert (j2:= max_snd x0 (max x1 x2)).
    assert (j3:= max_fst x1 x2).
    assert (lx0: mx > x1). omega.
    assert (j4:= max_snd x1 x2).
    assert (j5:= max_fst x1 x2).
    assert (lx1: mx > x2). omega.
    simpl. rewrite (j mx x0); try omega.
    rewrite jx0; try omega. rewrite e.
    rewrite jx1; try omega.
    rewrite jx2; try omega. reflexivity.
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
