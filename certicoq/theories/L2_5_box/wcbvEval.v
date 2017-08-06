
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.JMeq.
Require Import Common.Common.
Require Import L2_5.term.
Require Import L2_5.program.

Delimit Scope string_scope with string.
Open Scope string_scope.
Open Scope string_scope.
Open Scope bool.
Open Scope list.
Set Implicit Arguments.


(** Big step relation of weak cbv evaluation  **)
(** every field must evaluate **)
Inductive WcbvEval (p:environ Term) : Term -> Term -> Prop :=
| wLam: forall nm bod, WcbvEval p (TLambda nm bod) (TLambda nm bod)
| wProof: WcbvEval p TProof TProof
| waPrf: forall fn arg args,
    WcbvEval p fn TProof -> WcbvEval p (TApp fn arg args) TProof
| wConstruct: forall i r args args',
    WcbvEvals p args args' ->
    WcbvEval p (TConstruct i r args) (TConstruct i r args')
| wFix: forall dts m, WcbvEval p (TFix dts m) (TFix dts m)
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
| wAppFix: forall dts m (fn arg s x:Term) (args:Terms) (ix:nat),
    WcbvEval p fn (TFix dts m) ->
    dnthBody m dts = Some (x, ix) ->
    WcbvEval p (pre_whFixStep x dts (tcons arg args)) s ->
    WcbvEval p (TApp fn arg args) s 
| wAppCong: forall fn fn' arg arg' args args',
    WcbvEval p fn fn' ->
    ~ isLambda fn' -> ~ isFix fn' -> TProof <> fn' ->
    WcbvEval p arg arg' ->
    WcbvEvals p args args' ->
    WcbvEval p (TApp fn arg args) (mkApp fn' (tcons arg' args'))
| wCase: forall mch i n args brs cs s,
    WcbvEval p mch (TConstruct i n args) ->
    whCaseStep n args brs = Some cs ->
    WcbvEval p cs s ->
    WcbvEval p (TCase i mch brs) s
| wCaseCong: forall mch Mch ml brs,
    WcbvEval p mch Mch ->
    ~ (isCanonical Mch) ->
    WcbvEval p (TCase ml mch brs) (TCase ml Mch brs)
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

(** evaluate omega = (\x.xx)(\x.xx): nontermination **)
Definition xx := (TLambda nAnon (TApp (TRel 0) (TRel 0) tnil)).
Definition xxxx := (TApp xx xx tnil).
Goal WcbvEval nil xxxx xxxx.
unfold xxxx, xx.
eapply wAppLam. eapply wLam. 
eapply wLam. 
change (WcbvEval nil xxxx xxxx).
Abort.


Lemma WcbvEval_mkApp_nil:
  forall t, WFapp t -> forall p s, WcbvEval p t s ->
                 WcbvEval p (mkApp t tnil) s.
Proof.
  intros p. induction 1; simpl; intros; try assumption.
  - rewrite tappend_tnil. assumption.
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
  try (solve[inversion_Clear H1; intuition]).
  - apply H. unfold lookupDfn in e. case_eq (lookup nm p); intros xc.
    + intros k. assert (j:= lookup_pres_WFapp hp _ k).
      rewrite k in e. destruct xc. 
      * myInjection e. inversion j. assumption.
      * discriminate.
    + rewrite xc in e. discriminate.
  - inversion_clear H2. apply H1.
    specialize (H H4). inversion_Clear H.
    apply (whBetaStep_pres_WFapp); intuition. 
  - inversion_Clear H1. apply H0. apply instantiate_pres_WFapp; intuition.
  - inversion_clear H1. specialize (H H3). inversion_Clear H.
    assert (j: WFapps (tcons arg args)).
    { constructor; assumption. }
    apply H0. apply pre_whFixStep_pres_WFapp; try eassumption; intuition.
    + eapply dnthBody_pres_WFapp; try eassumption.
  - inversion_Clear H2.
    destruct (mkApp_isApp_lem fn' arg' args') as
        [y0 [y1 [y2 [ka [[kc1 [kc2 [kc3 kc4]]] | [kd1 [kd2 kd3]]]]]]];
      rewrite ka.
    + subst. cbn.
      assert (j: WFapps (tcons arg args)). constructor; assumption.
      constructor; intuition.
    + destruct kd1 as [z0 [z1 [z2 kz]]]. rewrite kz in ka. cbn in ka.
      myInjection ka. specialize (H H7). inversion_Clear H.
      assert (k:= tappend_tcons_tunit _ _ _ _ H2).
      rewrite <- k. constructor; try assumption.
      rewrite <- tappend_assoc. cbn. apply tappend_pres_WFapps; try assumption.
      constructor; intuition.
  - apply H0. inversion_Clear H1. 
    refine (whCaseStep_pres_WFapp H6 _ _ e).
    specialize (H H4). inversion_Clear H. assumption.
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
    + subst. 
      * unfold lookupDfn in e.
        rewrite (proj1 (fresh_lookup_None (trm:=Term) _ _) H0) in e.
        discriminate.
    + eapply wConst.
      * rewrite <- (lookupDfn_weaken' n). eassumption. 
      * apply H. assumption. 
  - eapply wAppLam.
    + apply H. assumption.
    + apply H0. assumption.
    + apply H1. assumption.
  - eapply wLetIn; intuition.
  - eapply wAppFix; try eassumption; intuition.
    (****************
  - eapply wAppFixCong1; try eassumption; intuition.   
***************)       
  - eapply wCase; intuition; eassumption.
Qed.


Definition ii := TLambda nAnon (TRel 0).
Goal
  WcbvEval nil (TApp ii ii (tcons ii (tunit ii))) ii.
Proof.
  eapply wAppLam.
  - unfold ii. eapply wLam.
  - unfold ii. eapply wLam.
  - cbn. eapply wAppLam.
    + eapply wLam.
    + unfold ii. eapply wLam.
    + cbn. eapply wAppLam.
      * eapply wLam.
      * unfold ii. eapply wLam.
      * cbn. eapply wLam.
Qed.

      
(*****
Lemma WcbvEval_no_further:
  forall p,
  (forall t s, WcbvEval p t s -> WcbvEval p s s) /\
  (forall ts ss, WcbvEvals p ts ss -> WcbvEvals p ss ss).
Proof.
  intros p.
  apply WcbvEvalEvals_ind; cbn; intros; auto.
  destruct (WcbvEvals_tcons_tcons w0) as [x0 [x1 jx]]. subst.
  rewrite mkApp_goodFn.
  destruct (WcbvEvals_tcons_tcons w0) as [x0 [x1 jx]]. subst.
  destruct (mkApp_isApp_lem fn' x0 x1) as [y0 [y1 [y2 jy]]].
  destruct jy. rewrite H1. destruct H2.
  - destruct H2 as [z0 [z1 [z2 z3]]]. subst. cbn.

  econstructor.
Qed.
*****)

Section wcbvEval_sec.
Variable p:environ Term.

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
    | TApp fn a1 args =>
      match wcbvEval n fn with
      | Exc s => raise ("wcbvEval TApp, fn: " ++ s)
      | Ret (TLambda _ bod) =>
        match wcbvEval n a1 with
        | Exc s =>  raise ("wcbvEval, TAppLam, arg: " ++ s)
        | Ret b1 => wcbvEval n (whBetaStep bod b1 args)
        end
      | Ret (TFix dts m) =>           (* Fix redex *)
        match dnthBody m dts with
        | None => raise ("wcbvEval TApp: dnthBody doesn't eval: ")
        | Some (x, ix) => wcbvEval n (pre_whFixStep x dts (tcons a1 args))
        end
      | Ret TProof => Ret TProof  (* proof redex *)
      | Ret Fn =>              (* no redex; congruence rule *)
        match wcbvEval n a1, wcbvEvals n args with
        | Ret erg, Ret ergs => Ret (mkApp Fn (tcons erg ergs))
        | _, _ => raise ("wcbvEval TAppCong, args")
        end
      end
    | TCase ml mch brs =>
      match wcbvEval n mch with
      | Exc str => Exc str
      | Ret (TConstruct i ix args) =>
        match inductive_dec i ml with
        | left _ =>
          match whCaseStep ix args brs with
          | None => raise "wcbvEval: Case, whCaseStep"
          | Some cs => wcbvEval n cs
          end
        | right _ => raise "wcbvEval: Case, constructor of wrong type"
        end
      | Ret mch' => ret (TCase ml mch' brs)
      end
    | TLetIn nm df bod =>
      match wcbvEval n df with
      | Ret df' => wcbvEval n (instantiate df' 0 bod)
      | Exc s => raise ("wcbvEval, TLetIn, def: " ++ s)
      end
    | TConstruct i cn args =>
      match wcbvEvals n args with
      | Ret args' => ret (TConstruct i cn args')
      | Exc s => raise ("wcbvEval: TConstruct, args: " ++ s)
      end
    (** already in whnf ***)
    | TLambda nn t => ret (TLambda nn t)
    | TFix mfp br => ret (TFix mfp br)
    | TProof => ret TProof
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
                   | Exc s, _ => raise ("wcbvEvals, hd: " ++ s)
                   | Ret _, Exc s => raise ("wcbvEvals, tl: " ++ s)
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
  - specialize (H0 _ p1). specialize (H _ e1).
    eapply wAppFix; try eassumption.
  - specialize (H _ e1). specialize (H0 _ e2). 
    eapply wAppCong; try eassumption.
    + destruct Fn; try not_isLambda. contradiction.
    + destruct Fn; try not_isFix. contradiction.
    + destruct (isProof_dec Fn); try assumption. unfold isProof in H2.
      * subst. contradiction.
      * apply neq_sym. intros h. unfold isProof in H2. contradiction. 
    + intuition. 
  - eapply wCase; try eassumption.
    + apply H. destruct _x. eassumption.
    + apply H0; eassumption. 
  - eapply wCaseCong.
    + apply H. assumption.
    + intros h. destruct h as [x0 [x1 [x2 j]]]. subst. assumption.
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
  assert (j:forall m x, m > x -> m = S (m - 1)).
  { induction m; intuition. }
  apply WcbvEvalEvals_ind; intros; try (exists 0; intros mx h; reflexivity).
  - destruct H. exists (S x). intros m hm. simpl. rewrite (j m x); try omega.
    + rewrite (H (m - 1)); try omega. reflexivity.
  - destruct H. exists (S x). intros m h. simpl.
    rewrite (j m x); try omega. rewrite H; try omega. reflexivity.
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
  - destruct H, H0. exists (S (max x0 x1)). intros mx h.
    assert (l1:= max_fst x0 x1). assert (l2:= max_snd x0 x1).
    simpl. rewrite (j mx x0); try omega. rewrite H; try omega.
    rewrite e. rewrite H0; try omega. reflexivity.
  - destruct H, H0, H1. exists (S (max x (max x0 x1))). intros mx h.
    assert (j1:= max_fst x (max x0 x1)). 
    assert (lx: mx > x). omega.
    assert (j2:= max_snd x (max x0 x1)).
    assert (j3:= max_fst x0 x1).
    assert (lx0: mx > x0). omega.
    assert (j4:= max_snd x0 x1).
    assert (j5:= max_fst x0 x1).
    assert (lx1: mx > x1). omega.
    simpl. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
    rewrite (H0 (mx - 1)); try omega.
    rewrite (H1 (mx - 1)); try omega.
    destruct fn'; try reflexivity. 
    + contradiction.
    + elim n. auto.
    + elim n0. auto.
  - destruct H, H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    cbn. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
    rewrite e. rewrite (H0 (mx - 1)); try omega.
    destruct (inductive_dec i i). reflexivity.
    elim n0. reflexivity.
  - destruct H. exists (S x). intros mx h.
    cbn. rewrite (j mx x); try omega. rewrite (H (mx - 1)); try omega.
    destruct Mch; try reflexivity.
    elim n. auto.
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
