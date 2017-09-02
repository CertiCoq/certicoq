
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
| wProof: forall t et, WcbvEval p t et -> WcbvEval p (TProof t) et
| wLam: forall nm ty ty' bod,
          WcbvEval p ty ty' ->
          WcbvEval p (TLambda nm ty bod) (TLambda nm ty' bod)
| wProd: forall nm ty ty' bod,
          WcbvEval p ty ty' ->
          WcbvEval p (TProd nm ty bod) (TProd nm ty' bod)
| wConstruct: forall i r np na,
                WcbvEval p (TConstruct i r np na) (TConstruct i r np na)
| wInd: forall i, WcbvEval p (TInd i) (TInd i) 
| wSort: forall srt, WcbvEval p (TSort srt) (TSort srt)
| wFix: forall dts m, WcbvEval p (TFix dts m) (TFix dts m)
| wAx: forall t, WcbvEval p (TAx t) (TAx t)
| wConst: forall nm (t s:Term),
            lookupDfn nm p = Ret t -> WcbvEval p t s ->
            WcbvEval p (TConst nm) s
| wAppLam: forall (fn ty bod a1 a1' s:Term) (args:Terms) (nm:name),
               WcbvEval p fn (TLambda nm ty bod) ->
               WcbvEval p a1 a1' ->
               WcbvEval p (whBetaStep bod a1' args) s ->
               WcbvEval p (TApp fn a1 args) s
| wLetIn: forall (nm:name) (dfn ty bod dfn' s:Term),
            WcbvEval p dfn dfn' ->
            WcbvEval p (instantiate dfn' 0 bod) s ->
            WcbvEval p (TLetIn nm dfn ty bod) s
| wAppFix: forall dts m (fn arg s x:Term) (args:Terms) (ix:nat),
             WcbvEval p fn (TFix dts m) ->
             dnthBody m dts = Some (x, ix) ->
             WcbvEval p (pre_whFixStep x dts (tcons arg args)) s ->
             WcbvEval p (TApp fn arg args) s 
| wAppCons: forall fn i m np na arg arg' args args', 
              WcbvEval p fn (TConstruct i m np na) ->
              WcbvEval p arg arg' ->
              WcbvEvals p args args' ->
              WcbvEval p (TApp fn arg args)
                       (TApp (TConstruct i m np na) arg' args')
| wCase: forall mch Mch n args ml ts brs cs s ty,
                WcbvEval p mch Mch ->
                canonicalP Mch = Some (n, args) ->
                tskipn (snd ml) args = Some ts ->
                whCaseStep n ts brs = Some cs ->
                WcbvEval p cs s ->
                WcbvEval p (TCase ml ty mch brs) s
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

Lemma WcbvEvals_pres_tlength:
  forall p args brgs, WcbvEvals p args brgs -> tlength args = tlength brgs.
Proof.
  induction 1. reflexivity. cbn. rewrite IHWcbvEvals. reflexivity.
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
  - apply H. unfold lookupDfn in e. case_eq (lookup nm p); intros xc.
    + intros k. assert (j:= lookup_pres_WFapp hp _ k)
      . rewrite k in e. destruct xc. 
      * myInjection e. inversion j. assumption.
      * discriminate.
    + rewrite xc in e. discriminate.
  - inversion_clear H2. apply H1.
    specialize (H H4). inversion_Clear H.
    apply (whBetaStep_pres_WFapp); intuition. 
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp. assumption.
    + apply H. assumption.
  - inversion_clear H1. specialize (H H3). inversion_Clear H.
    apply H0. apply pre_whFixStep_pres_WFapp; try eassumption; intuition.
    + eapply dnthBody_pres_WFapp; try eassumption.
  - inversion_Clear H2. econstructor; intuition.
    destruct H2 as [x0 [x1 [x2 jx]]]. discriminate.
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
   - destruct (string_dec nm nm0).
    + subst. inversion_Clear H0.
      * unfold lookupDfn in e.
        rewrite (proj1 (fresh_lookup_None (trm:=Term) _ _)) in e.
        discriminate.
        constructor; assumption.
      * unfold lookupDfn in e.
        rewrite (proj1 (fresh_lookup_None (trm:=Term) _ _)) in e.
        discriminate.  constructor.
    + eapply wConst.
      * rewrite <- (lookupDfn_weaken' n). eassumption. 
      * apply H. assumption. 
   - eapply wAppLam.
    + apply H. assumption.
    + apply H0. assumption.
    + apply H1. assumption.
  - eapply wLetIn; intuition.
  - eapply wAppFix; try eassumption; intuition.
  - eapply wCase; intuition; eassumption.
Qed.

  
Lemma WcbvEval_wndEvalRTC:
  forall (p:environ Term), WFaEnv p ->
    (forall t s, WcbvEval p t s -> WFapp t -> wndEvalRTC p t s) /\
    (forall ts ss, WcbvEvals p ts ss -> WFapps ts -> wndEvalsRTC p ts ss).
Proof.
  intros p hp. apply WcbvEvalEvals_ind; intros; try (solve [constructor]).
  - inversion_Clear H0. eapply wndEvalRTC_Proof. intuition. 
  - inversion_Clear H0. eapply wERTCtrn. 
    + apply wndEvalRTC_Lam_typ. eapply H. assumption.
    + constructor. 
  - inversion_Clear H0. 
    eapply wERTCtrn. 
    + apply wndEvalRTC_Prod_typ. eapply H. assumption.
    + constructor. 
  - eapply wERTCtrn; intuition.
    eapply wERTCtrn.
    + apply wERTCstep. apply sConst. apply lookupDfn_LookupDfn. eassumption.
    + apply H. eapply (lookupDfn_pres_WFapp hp).  eassumption. 
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
 - inversion_clear H1. specialize (H H3).
    assert (j0: WFapps (tcons arg args)).
    { constructor; assumption. }
    assert (j2: WFapp (TFix dts m)).
    { refine (proj1 (wcbvEval_pres_WFapp hp) _ _ w _). assumption. }
    inversion_clear j2.
    assert (j3: WFapp x).
    { refine (dnthBody_pres_WFapp _ _ e). assumption. }
    assert (j4: WFapp (pre_whFixStep x dts (tcons arg args))).
    { refine (pre_whFixStep_pres_WFapp _ _ _); try assumption. }
    specialize (H0 j4).
    refine (@wERTCtrn _ _ (TApp (TFix dts m) arg args) _ _ _).
    + rewrite <- mkApp_goodFn; try assumption.
      rewrite <- mkApp_goodFn; try not_isApp.
      apply wndEvalRTC_App_fn; assumption.
    + eapply (@wERTCtrn _ _  (pre_whFixStep x dts (tcons arg args))).
      * eapply wERTCstep. eapply sFix; try eassumption.
      * assumption.
 - inversion_Clear H2.
   specialize (H H7). specialize (H0 H8). specialize (H1 H9).
    eapply (@wERTCtrn _ _ (TApp fn arg' args')).
   + eapply wndEvalsRTC_App_args; try reflexivity; try assumption.
     eapply (@wEsRTCtrn _  _ (tcons arg' args)).
     eapply wndEvalsRTC_mk_tconsl; assumption.
     eapply wndEvalsRTC_mk_tconsr; assumption.
   + rewrite <- (mkApp_goodFn _ _ H6). rewrite <- mkApp_goodFn.
     eapply wndEvalRTC_App_fn; try assumption.
     * eapply (proj1 (wcbvEval_pres_WFapp hp)). eapply w0. assumption.
     * eapply (proj2 (wcbvEval_pres_WFapp hp)). eapply w1. eassumption.
     * not_isApp.
  - inversion_Clear H1. eapply wERTCtrn. 
    + eapply wndEvalRTC_Case_mch. apply H. assumption.
    + eapply (@wERTCtrn _ _ cs). 
      * apply wERTCstep. eapply sCase; eassumption.
      * { apply H0. refine (whCaseStep_pres_WFapp _ _ _ e1). assumption.
          refine (tskipn_pres_WFapp _ _ e0).
          refine (canonicalP_pres_WFapp _ e).
          specialize (H H5).
          refine (wndEvalRTC_pres_WFapp _ _ _); eassumption. }
  - inversion_Clear H1. eapply (@wEsRTCtrn _ _ (tcons t' ts)).
    + apply wndEvalsRTC_tcons_hd. apply H. assumption.
    + apply wndEvalsRTC_tcons_tl. apply H0. assumption.
Qed.


(*************************  
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
         (tmr:nat) (topt:Term) {struct tmr}: exception Term :=
  match tmr with 
  | 0 => raise ("out of time: " ++ print_term topt)
  | S n =>
    match topt with      (** look for a redex **)
    | TProof t =>
      match wcbvEval n t with
      | Ret et => Ret et
      | _ => raise ("wcbvEval: TProof")
      end
    | TConst nm =>
      match (lookup nm p) with
      | Some (AstCommon.ecTrm t) => wcbvEval n t
      (** note hack coding of axioms in environment **)
      | Some _ => raise ("wcbvEval, TConst ecTyp " ++ nm)
      | _ => raise ("wcbvEval: TConst environment miss:  "
                      ++ nm ++ print_term topt)
      end
    | TApp fn a1 args =>
      match wcbvEval n fn with
      | Ret (TLambda _ _ bod) =>      (* beta redex *)
        match wcbvEval n a1 with
        | Exc s =>
          raise ("wcbvEval TApp: arg doesn't eval: " ++ print_term topt)
        | Ret b1 => wcbvEval n (whBetaStep bod b1 args)
        end
      | Ret (TFix dts m) =>           (* Fix redex *)
        match dnthBody m dts with
        | None => raise ("wcbvEval TApp: dnthBody doesn't eval: ")
        | Some (x, ix) => wcbvEval n (pre_whFixStep x dts (tcons a1 args))
        end
      | Ret ((TConstruct _ _ _ _) as tc) =>   (* applied constructor *)
        match wcbvEvals n (tcons a1 args) with
        | Exc s =>
          raise ("wcbvEval TApp: args don't eval: " ++ print_term topt)
        | Ret (tcons a1' args') => ret (TApp tc a1' args')
        | _ => raise "wcbvEval TApp: args"
        end
      | _ => raise "wcbvEval TApp: fn"
      end
    | TCase ml tp mch brs =>
      match wcbvEval n mch with
      | Exc str => Exc str
      | Ret emch =>
        match canonicalP emch with
        | None => raise ("wcbvEval: Case, discriminee not canonical")
        | Some (r, args) =>
          match tskipn (snd ml) args with
          | None => raise ("wcbvEval: Case, tskipn " ++ print_term topt)
          | Some ts =>
            match whCaseStep r ts brs with
            | None => raise ("wcbvEval: Case, whCaseStep" ++ print_term topt)
            | Some cs => wcbvEval n cs
            end
          end
        end
      end
    | TLetIn _ df _ bod =>
      match wcbvEval n df with
      | Ret df' => wcbvEval n (instantiate df' 0 bod)
      | Exc s => raise ("wcbvEval: TLetIn:" ++ print_term topt)
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
    | TAx t => ret (TAx t)
    | TFix mfp br => ret (TFix mfp br)
    | TConstruct i cn np na => ret (TConstruct i cn np na)
    | TInd i => ret (TInd i)
    | TSort srt => ret (TSort srt)
    (** should never appear **)
    | TRel _ => raise "wcbvEval: unbound Rel"
    | TWrong str => raise "wcbvEval: TWrong"
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
    + unfold lookupDfn. rewrite e1. reflexivity.
  - specialize (H1 _ p1). specialize (H _ e1). specialize (H0 _ e2).
    eapply wAppLam; eassumption.
  - specialize (H0 _ p1). specialize (H _ e1). 
    eapply wAppFix; try eassumption.
  - specialize (H _ e1). specialize (H0 _ e2).
    inversion_Clear H0. eapply wAppCons; eassumption. 
  - eapply wCase; try eassumption.
    + apply H; eassumption.
    + apply H0; eassumption. 
  - eapply wLetIn; intuition.
    + apply H. assumption.
Qed.

Lemma wcbvEvals_tcons_tcons:
  forall m args brg brgs,
    wcbvEvals m args = Ret (tcons brg brgs) ->
    forall crg crgs, args = (tcons crg crgs) ->
                     wcbvEval (pred m) crg = Ret brg.
Proof.
  intros m args.
  functional induction (wcbvEvals m args); intros; try discriminate.
  myInjection H0. myInjection H. assumption.
Qed.

(** need strengthening to large-enough fuel to make the induction
 *** go through **)
Lemma pre_WcbvEval_wcbvEval:
    (forall t s, WcbvEval p t s ->
          exists n, forall m, m >= n -> wcbvEval (S m) t = Ret s) /\
    (forall ts ss, WcbvEvals p ts ss ->
                   exists n, forall m, m >= n -> wcbvEvals (S m) ts = Ret ss).
Proof.
  assert (j:forall m, m > 0 -> m = S (m - 1)).
  { induction m; intuition. }
  apply WcbvEvalEvals_ind; intros; try (exists 0; intros mx h; reflexivity).
  - destruct H. exists (S x). intros m hm. simpl. rewrite (j m); try omega.
    + rewrite (H (m - 1)); try omega. reflexivity. 
  - destruct H. exists (S x). intros m hm. simpl. rewrite (j m); try omega.
    + rewrite (H (m - 1)); try omega. reflexivity.
  - destruct H.  exists (S x). intros m h. simpl.
    rewrite (j m); try omega. rewrite H; try omega. reflexivity.
  - destruct H. exists (S x). intros mm h. cbn.
    rewrite (j mm); try omega.
    unfold lookupDfn in e. destruct (lookup nm p); try discriminate.
    + destruct e0; try discriminate. myInjection e. rewrite H.
      reflexivity. omega.
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
    { rewrite (j m). apply H. omega. omega. }
    assert (k0:wcbvEval m a1 = Ret a1').
    { rewrite (j m). apply H0. omega. omega. }
    simpl. rewrite (j m); try omega.
    rewrite H; try omega. rewrite H0; try omega. rewrite H1; try omega.
    reflexivity.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx); try omega. rewrite (H (mx - 1)); try omega.
    rewrite H0; try omega. reflexivity.
  - destruct H, H0. exists (S (max x0 x1)). intros mx h.
    assert (l1:= max_fst x0 x1). assert (l2:= max_snd x0 x1).
    cbn. rewrite (j mx); try omega. rewrite (H (mx - 1)); try omega.
    rewrite e. rewrite H0; try omega. reflexivity.
  - destruct H, H0, H1. exists (S (S (max x (max x0 x1)))). intros mx h.
    assert (j1:= max_fst x (max x0 x1)). 
    assert (lx: mx > x). omega.
    assert (j2:= max_snd x (max x0 x1)).
    assert (j3:= max_fst x0 x1).
    assert (lx0: mx > x0). omega.
    assert (j4:= max_snd x0 x1).
    assert (j5:= max_fst x0 x1).
    assert (lx1: mx > x1). omega.
    assert (k: wcbvEvals mx (tcons arg args) = Ret (tcons arg' args')).
    { erewrite (j mx); try omega. simpl.
      erewrite (j (mx - 1)); try omega. rewrite H0; try omega.
      rewrite H1. reflexivity. omega. }
    simpl. rewrite (j mx). rewrite H.
    rewrite (j mx) in k. rewrite k. reflexivity. omega. omega. omega.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    cbn. rewrite (j mx); try omega. rewrite (H (mx - 1)); try omega.
    rewrite e. rewrite e0. rewrite e1. rewrite (H0 (mx - 1)); try omega.
    reflexivity.
  - destruct H as [x1 jx1], H0 as [x0 jx0].
    exists (S (max x1 x0)). intros mx h.
    assert (l1:= max_fst x1 x0). assert (l2:= max_snd x1 x0).
    simpl. rewrite (j mx); try omega; try omega. 
    rewrite jx1; try omega. rewrite jx0; try omega.
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

Lemma wcbvEval_up:
 forall t s tmr,
   wcbvEval tmr t = Ret s ->
   exists n, forall m, m >= n -> wcbvEval m t = Ret s.
Proof.
  intros. 
  destruct (WcbvEval_wcbvEval (proj1 (wcbvEval_WcbvEval tmr) t s H)).
  exists x. apply H0.
Qed.

End wcbvEval_sec.
