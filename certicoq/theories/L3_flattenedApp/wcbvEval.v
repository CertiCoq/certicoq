
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Program.Basics.
Require Import Coq.omega.Omega.
Require Import Coq.Logic.JMeq.
Require Import L3.term.
Require Import L3.program.
Require Import L3.wndEval.
Require Import L3.compile.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(** Relational version of weak cbv evaluation  **)
Inductive WcbvEval (p:environ Term) : Term -> Term -> Prop :=
| wPrf: WcbvEval p TProof TProof
| wLam: forall nm bod,
          WcbvEval p (TLambda nm bod) (TLambda nm bod)
| wProd: forall nm bod,
          WcbvEval p (TProd nm bod) (TProd nm bod)
| wConstruct: forall i r args args',
                WcbvEvals p args args' ->
                WcbvEval p (TConstruct i r args) (TConstruct i r args')
| wInd: forall i, WcbvEval p (TInd i) (TInd i) 
| wSort: forall s, WcbvEval p (TSort s) (TSort s)
| wFix: forall dts m, WcbvEval p (TFix dts m) (TFix dts m)
| wAx: WcbvEval p TAx TAx
| wConst: forall nm (t s:Term),
            LookupDfn nm p t -> WcbvEval p t s -> WcbvEval p (TConst nm) s
| wAppLam: forall (fn bod a1 a1' s:Term) (nm:name),
               WcbvEval p fn (TLambda nm bod) ->
               WcbvEval p a1 a1' ->
               WcbvEval p (whBetaStep bod a1') s ->
               WcbvEval p (TApp fn a1) s
| wLetIn: forall (nm:name) (dfn bod dfn' s:Term),
            WcbvEval p dfn dfn' ->
            WcbvEval p (instantiate dfn' 0 bod) s ->
            WcbvEval p (TLetIn nm dfn bod) s
| wAppFix: forall dts m (fn arg fs s:Term),
               WcbvEval p fn (TFix dts m) ->
               whFixStep dts m = Some fs ->
               WcbvEval p (TApp fs arg) s ->
               WcbvEval p (TApp fn arg) s
| wAppCong: forall fn efn arg arg1,
              WcbvEval p fn efn ->
              ~ isLambda efn -> ~ isFix efn ->
              WcbvEval p arg arg1 ->
              WcbvEval p (TApp fn arg) (TApp efn arg1)
| wCase: forall mch i n ml args args' brs cs s,
           WcbvEval p mch (TConstruct i n args) ->
           i = fst ml ->
           tskipn (snd ml) args = Some args' ->  (* drop parameters *)
           whCaseStep n args' brs = Some cs ->
           WcbvEval p cs s ->
           WcbvEval p (TCase ml mch brs) s
| wCaseCong: forall ml mch emch brs,
           WcbvEval p mch emch ->
           ~ isConstruct emch ->
           (*************
           WcbvEvals p brs ebrs ->
*********************)
           WcbvEval p (TCase ml mch brs) (TCase ml emch brs)
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

Inductive WcbvEval_env : environ Term -> environ Term -> Prop :=
| WcbvEval_env_nil : WcbvEval_env nil nil
| WcbvEval_env_trm nm e e' t t' :
    WcbvEval_env e e' ->
    WcbvEval e t t' -> WcbvEval_env ((nm, ecTrm t) :: e) ((nm, ecTrm t') :: e')
| WcbvEval_env_typ nm e e' n t :
    WcbvEval_env e e' ->
    WcbvEval_env ((nm, ecTyp _ n t) :: e) ((nm, ecTyp _ n t) :: e').

(** when reduction stops **)
Definition no_Wcbv_step (p:environ Term) (t:Term) : Prop :=
  no_step (WcbvEval p) t.
Definition no_Wcbvs_step (p:environ Term) (ts:Terms) : Prop :=
  no_step (WcbvEvals p) ts.

(** evaluate omega = (\x.xx)(\x.xx): nontermination **)
Definition xx := (TLambda nAnon (TApp (TRel 0) (TRel 0))).
Definition xxxx := (TApp xx xx).
Goal WcbvEval nil xxxx xxxx.
unfold xxxx, xx. eapply wAppLam. eapply wLam. eapply wLam.
Abort.

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
  - eapply wLetIn.
    + apply H. assumption.
    + apply H0. assumption.
  - eapply wAppFix.
    + apply H. assumption.
    + apply e.
    + apply H0. assumption.
  - eapply wCase; intuition; try eassumption.
Qed.


(************  in progress  ****
Lemma WcbvEval_strengthen:
  forall pp,
  (forall t s, WcbvEval pp t s -> forall nm u p, pp = (nm,ecConstr u)::p ->
        ~ PoccTrm nm t -> WcbvEval p t s) /\
  (forall ts ss, WcbvEvals pp ts ss -> forall nm u p, pp = (nm,ecConstr u)::p ->
        ~ PoccTrms nm ts -> WcbvEvals p ts ss).
intros pp. apply WcbvEvalEvals_ind; intros; auto.
- assert (j1:= neq_sym (inverse_Pocc_TConstL H1)).
  assert (j2:= Lookup_strengthen l H0 j1).
  eapply wConst. apply j2. eapply H. eassumption.
  subst.

- eapply wConst.
  assert (j1:= (neq_sym (inverse_Pocc_TConstL H1))). inversion_clear l.
  rewrite H0 in l. assert (j2:= LookupDfn_neq j1 l).
  eapply wConst. eassumption.
  inversion l. eapply H. eassumption.
  + eapply wConst. eassumption.
  eapply wConst. eassumption.
  eapply H. eassumption. intros h.
eapply wConst. subst. eassumption.  (@wConst p nm t s pp).
  eapply (@Lookup_strengthen _ pp); try eassumption.
  + apply (neq_sym (inverse_Pocc_TConstL H1)).
  + eapply H. eassumption.
    admit.
- Check (deMorgan_impl (@PoAppL _ _ _ _) H3).
  assert (hfn:= deMorgan_impl (@PoAppL _ _ _ _) H3).
  assert (harg:= deMorgan_impl (@PoAppA _ _ _ _) H3).
  assert (hargs:= deMorgan_impl (@PoAppR _ _ _ _) H3).
  eapply wAppLam. 
  + eapply H; eassumption.
  + eapply H0; eassumption.
  + eapply H1. eassumption. intros j.

*************)


(** WcbvEval makes progress **)
(******************  HERE  ***
Goal
  forall (p:environ Term),
  (forall t, (no_wnd_step p t /\ (no_Wcbv_step p t \/ WcbvEval p t t)) \/
                 (exists u, wndEvalTC p t u /\ WcbvEval p t u)) /\
  (forall ts, (no_wnds_step p ts /\ WcbvEvals p ts ts) \/
                  (exists us, wndEvalsTC p ts us /\ WcbvEvals p ts us)) /\
  (forall (ds:Defs), True).
induction p; apply TrmTrmsDefs_ind; intros; auto.



Goal
  (forall p n t, Crct p n t -> n = 0 ->
                 (no_wnd_step p t /\ WcbvEval p t t) \/
                 (exists u, wndEvalTC p t u /\ WcbvEval p t u)) /\
  (forall p n ts, Crcts p n ts -> n = 0 ->
                  (no_wnds_step p ts /\ WcbvEvals p ts ts) \/
                  (exists us, wndEvalsTC p ts us /\ WcbvEvals p ts us)) /\
  (forall (p:environ Term) (n:nat) (ds:Defs), CrctDs p n ds -> True).
apply CrctCrctsCrctDs_ind; intros; try auto; subst.
- left. split.
  + intros x h. inversion h.
  + constructor.
- destruct H0; destruct H2; try reflexivity.
  + left. split. intros x h.
    assert (j1:= proj1 H0). assert (j2:= proj1 H2).
    unfold no_wnd_step in j1. eelim j1.
    eapply (proj1 (wndEval_strengthen _)). eapply h. reflexivity.
    eapply (proj1 (Crct_fresh_Pocc)); eassumption.
    apply WcbvEval_weaken; intuition.
  + left. destruct H0. split.
    * unfold no_wnd_step. intros w j. unfold no_wnd_step in H0.
      elim (H0 w). eapply (proj1 (wndEval_strengthen _)).
      eassumption. reflexivity.
      eapply (proj1 Crct_fresh_Pocc); eassumption.
    * eapply (proj1 (WcbvEval_weaken _)); assumption.
  + right. destruct H0. destruct H0. exists x. split.
    * apply wndEvalTC_weaken; assumption.
    * apply WcbvEval_weaken; assumption.
  + right. destruct H0. destruct H0. exists x. split.
    * apply wndEvalTC_weaken; assumption.
    * apply WcbvEval_weaken; assumption.
- omega.
- left. intuition. intros x h. inversion h.
- left. intuition. intros x h. inversion h.
- right. destruct H0; try reflexivity; destruct H0.
  + unfold no_wnd_step in H0. eelim H0.
***)


(** WcbvEval is in the transitive closure of wndEval **)
(**
Lemma WcbvEval_wndEvalTC:
  forall (p:environ Term),
    (forall t s, WcbvEval p t s -> t <> s -> wndEvalTC p t s) /\
    (forall ts ss, WcbvEvals p ts ss -> ts <> ss -> wndEvalsTC p ts ss).
intros p. apply WcbvEvalEvals_ind; intros; try (nreflexivity H).
**)

(************  in progress  ****
Lemma WcbvEval_strengthen:
  forall pp,
  (forall t s, WcbvEval pp t s -> forall nm u p, pp = (nm,ecConstr u)::p ->
        ~ PoccTrm nm t -> WcbvEval p t s) /\
  (forall ts ss, WcbvEvals pp ts ss -> forall nm u p, pp = (nm,ecConstr u)::p ->
        ~ PoccTrms nm ts -> WcbvEvals p ts ss).
intros pp. apply WcbvEvalEvals_ind; intros; auto; subst.
- admit.
- destruct (notPocc_TApp H3) as (hfn & ha1 & hargs). eapply wAppLam.
  + eapply H. reflexivity. assumption.
  + eapply H0. reflexivity. assumption.
  + eapply H1. reflexivity. unfold whBetaStep.


Lemma WcbvEval_strengthen:
  forall pp,
  (forall t s, WcbvEval pp t s -> forall nm u p, pp = (nm,ecConstr u)::p ->
        forall n, Crct pp n t -> ~ PoccTrm nm t -> WcbvEval p t s) /\
  (forall ts ss, WcbvEvals pp ts ss -> forall nm u p, pp = (nm,ecConstr u)::p ->
        forall n, Crcts pp n ts -> ~ PoccTrms nm ts -> WcbvEvals p ts ss).
intros pp. apply WcbvEvalEvals_ind; intros; auto; subst.
- admit.
(***
- eapply wConst. eapply Lookup_strengthen; try eassumption.
  + destruct (string_dec nm nm0); auto.
    * subst. elim H2. constructor. auto.
  + eapply H. eassumption.
    * instantiate (1:= 0). admit. 
(***
subst.  assert (j:= inverse_Pocc_TConstL H2). inversion_Clear l.
      elim j. reflexivity. inversion_Clear H1.

      Check (proj1 (Crct_strengthen) _ _ _ H1). eapply CrctWk. instantiate (1:= 0). admit.
***)
    * subst. assert (j:= inverse_Pocc_TConstL H2). inversion_Clear l.
  
inversion_Clear H1.
***)
- destruct (notPocc_TApp H4); destruct H5. eapply wAppLam. 
   + eapply H; try reflexivity; try eassumption. eapply CrctWk. 

Check (proj1 Crct_strengthen _ _ _ H3). inversion_Clear H3.
  + injection H8. intros. subst. eapply wAppLam. eapply H. reflexivity.
    * eapply Crct_strengthen. 

HERE


(@wConst p nm t s pp). eapply (@Lookup_strengthen _ pp); try eassumption.
  + apply (neq_sym (inverse_Pocc_TConstL H1)).
  + eapply H. eassumption.
    admit.
- Check (deMorgan_impl (@PoAppL _ _ _ _) H3).
  assert (hfn:= deMorgan_impl (@PoAppL _ _ _ _) H3).
  assert (harg:= deMorgan_impl (@PoAppA _ _ _ _) H3).
  assert (hargs:= deMorgan_impl (@PoAppR _ _ _ _) H3).
  eapply wAppLam. 
  + eapply H; eassumption.
  + eapply H0; eassumption.
  + eapply H1. eassumption. intros j.



rewrite H0 in l. assert (j:= proj2 (lookupDfn_LookupDfn _ _ _) l).
  simpl in j.
  rewrite (string_eq_bool_neq (neq_sym (inverse_Pocc_TConstL H1))) in j. 
Check (@wConst p _ t).
  eapply (@wConst p _ t).
assert (h:= inverse_Pocc_TConstL H1).

rewrite H0 in l. simpl in l. eapply (wConst pp). 

rewrite H0 in H. simpl in H.
  rewrite (string_eq_bool_neq (neq_sym (inverse_Pocc_TConstL H0))) in e. 
  trivial.
- apply (H nm u); trivial. apply (notPocc_TApp H1).
- apply (H nm u); trivial. apply (notPocc_TApp H1).
- apply (H nm u); trivial. apply (notPocc_TApp H1).
- apply (H nm0 u); trivial; apply (notPocc_TProd H1).
- apply (H nm0 u); trivial; apply (notPocc_TLambda H1).
- apply (H nm0 u); trivial; apply (notPocc_TLetIn H1).
- apply (H nm0 u); trivial; apply (notPocc_TLetIn H1).
- apply (H nm u); trivial; apply (notPocc_TCast H1).
- apply (H nm u); trivial; apply (notPocc_TCase H1).
- apply (H nm u); trivial; apply (notPocc_TCase H1).
- apply (H nm u); trivial; apply (notPocc_TCase H1).
- apply (H nm u). trivial. apply (notPoccTrms H1).
- apply (H nm u). trivial. apply (notPoccTrms H1).
Qed.
***************)

Section wcbvEval_sec.
Variable p:environ Term.

(** now an executable weak-call-by-value evaluation **)
(** use a timer to make this terminate **)
Function wcbvEval
         (tmr:nat) (t:Term) {struct tmr} : exception Term :=
  match tmr with 
    | 0 => Exc "out of time"          (** out of time  **)
    | S n =>
      match t with      (** look for a redex **)
        | TConst nm =>
          match (lookup nm p) with
            | Some (ecTrm t) => wcbvEval n t
            | Some (ecTyp _ _ _) => raise ("wcbvEval, TConst ecTyp " ++ nm)
            | _ => raise "wcbvEval: TConst environment miss"
          end
        | TConstruct i cn args => 
          match wcbvEvals n args with
            | Ret args' => Ret (TConstruct i cn args')
            | Exc s => raise s
          end
        | TApp fn a1 =>
          match wcbvEval n fn with
            | Ret (TFix dts m) =>
              match whFixStep dts m with
                | None => raise ""
                | Some fs => wcbvEval n (TApp fs a1)
              end
            | Ret Fn =>
              match wcbvEval n a1 with
                | Exc s =>  raise "wcbvEval: TApp, arg doesn't eval"
                | Ret ea1 =>
                  match Fn with
                    | TLambda _ bod => wcbvEval n (whBetaStep bod ea1)
                    | T => Ret (TApp T ea1)
                  end
              end
            | Exc _ => raise "wcbvEval: TApp, fn doesn't eval"
          end
        | TCase ml mch brs =>
          match wcbvEval n mch with
            | Ret (TConstruct i r args) =>
              if eq_dec i (fst ml) then
                match tskipn (snd ml) args with
                  | None => raise "wcbvEval: Case, tskipn"
                  | Some ts => match whCaseStep r ts brs with
                                 | None => raise "wcbvEval: Case, whCaseStep"
                                 | Some cs => wcbvEval n cs
                               end
                end
              else raise "wcbvEval: TCase: i doesn't match"
            | Ret emch => Ret (TCase ml emch brs)
            | Exc s => Exc s
          end
        | TLetIn nm df bod =>
          match wcbvEval n df with
            | Exc s => raise s
            | Ret df' => wcbvEval n (instantiate df' 0 bod)
          end
        (** already in whnf ***)
        | TAx => ret TAx
        | TLambda nn t => ret (TLambda nn t)
        | TProd nn t => ret (TProd nn t)
        | TFix mfp br => ret (TFix mfp br)
        | TInd i => ret (TInd i)
        | TSort srt => ret (TSort srt)
        | TProof => ret TProof
        (** should never appear **)
        | TRel _ => raise "wcbvEval: unbound Rel"
        | TWrong => ret TWrong
      end
  end
with wcbvEvals (tmr:nat) (ts:Terms) {struct tmr}
     : exception Terms :=
       (match tmr with 
          | 0 => raise "out of time"         (** out of time  **)
          | S n => match ts with             (** look for a redex **)
                     | tnil => ret tnil
                     | tcons s ss =>
                       match wcbvEval n s, wcbvEvals n ss with
                         | Ret es, Ret ess => Ret (tcons es ess)
                         | _, _ => Exc ""
                       end
                   end
        end).
Functional Scheme wcbvEval_ind' := Induction for wcbvEval Sort Prop
with wcbvEvals_ind' := Induction for wcbvEvals Sort Prop.
Combined Scheme wcbvEvalEvals_ind from wcbvEval_ind', wcbvEvals_ind'.


(** wcbvEval and WcbvEval are the same relation **)
Lemma wcbvEval_WcbvEval:
  forall n,
  (forall t s, wcbvEval n t = Ret s -> WcbvEval p t s) /\
  (forall ts ss, wcbvEvals n ts = Ret ss -> WcbvEvals p ts ss).
Proof.
  intros n.
  apply (wcbvEvalEvals_ind 
           (fun n t (o:exception Term) =>
              forall (s:Term) (p1:o = Ret s), WcbvEval p t s)
           (fun n ts (os:exception Terms) =>
              forall (ss:Terms) (p2:os = Ret ss), WcbvEvals p ts ss));
    intros; try discriminate; try (myInjection p1); try (myInjection p2);
    try(solve[constructor]); intuition.
  - eapply wConst. unfold LookupDfn.
    eapply lookup_Lookup. eassumption. apply H. assumption.
  - specialize (H _ e1). specialize (H0 _ p1).
    eapply wAppFix; try eassumption.
  - specialize (H _ e1). specialize (H0 _ e2). specialize (H1 _ p1).
    eapply wAppLam; try eassumption.
    destruct Fn; try discriminate. myInjection e3. eassumption.
  - specialize (H _ e1). specialize (H0 _ e2).
    destruct T; try contradiction;
    try (myInjection H1); try (apply wAppCong); try assumption;
    try (solve[not_isApp]).
  - subst. specialize (H _ e1). specialize (H0 _ p1). 
    refine (wCase _ _ _ _ _ _ _); eassumption || reflexivity.
  - specialize (H _ e1). 
    eapply wCaseCong; try assumption. 
    destruct emch; try not_isConstruct. contradiction. 
  - eapply wLetIn.
    + apply H. eassumption.
    + apply H0. assumption.
Qed.

(* need this strengthening to large-enough fuel to make the induction
** go through
*)
Lemma pre_WcbvEval_wcbvEval:
    (forall t s, WcbvEval p t s ->
        exists n, forall m, m >= n -> wcbvEval (S m) t = Ret s) /\
    (forall ts ss, WcbvEvals p ts ss ->
        exists n, forall m, m >= n -> wcbvEvals (S m) ts = Ret ss).
Proof.
  assert (j:forall m x, m > x -> m = S (m - 1)). induction m; intuition.
  apply WcbvEvalEvals_ind; intros; try (exists 0; intros mx h; reflexivity).
  - destruct H. exists (S x). intros m h. simpl.
    rewrite (j m x); try omega. rewrite H; try omega. reflexivity.
  - destruct H. exists (S x). intros mx hm. simpl. unfold LookupDfn in l.
    rewrite (Lookup_lookup l). rewrite (j mx 0); try omega. apply H.
    omega.
  - destruct H; destruct H0; destruct H1. exists (S (max x (max x0 x1))).
    intros m h.
    assert (k:wcbvEval m fn = Ret (TLambda nm bod)).
    { rewrite (j m (max x (max x0 x1))). apply H.
      assert (l:= max_fst x (max x0 x1)); omega. omega. }
    assert (k0:wcbvEval m a1 = Ret a1').
    { rewrite (j m (max x (max x0 x1))). apply H0.
      assert (l:= max_snd x (max x0 x1)). assert (l':= max_fst x0 x1).
      omega. omega. }
    simpl. rewrite k0. rewrite k.
    rewrite (j m (max x (max x0 x1))). apply H1. 
    assert (l:= max_snd x (max x0 x1)). assert (l':= max_snd x0 x1).
    omega. omega.
  - destruct H; destruct H0. exists (S (max x x0)). intros m h. simpl.
    assert (k:wcbvEval m dfn = Ret dfn'). 
    assert (l:= max_fst x x0).
    rewrite (j m (max x x0)). apply H. omega. omega.
    rewrite k.
    assert (l:= max_snd x x0).
    rewrite (j m x0). apply H0. omega. omega.
  - destruct H; destruct H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    simpl. rewrite (j mx x); try rewrite (H (mx - 1)); try omega.
    rewrite e. apply H0. omega.
  - destruct H; destruct H0. exists (S (max x x0)). intros mx h.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    cbn. rewrite (j mx x); try omega.
    rewrite (H (mx - 1)); try omega.
    rewrite (H0 (mx - 1)); try omega.
    destruct efn; try reflexivity.
    + elim n. auto.
    + elim n0. auto.
  - destruct H as [x hx]. destruct H0 as [x0 hx0].
    exists (S (max x x0)). intros m hm. cbn.
    assert (l1:= max_fst x x0). assert (l2:= max_snd x x0).
    rewrite (j m (max x x0)); try omega.
    rewrite hx; try omega. rewrite e0; try omega. rewrite e1; try omega.
    destruct (inductive_dec i (fst ml)).
    + apply hx0; try omega.
    + elim n0; assumption.
  - destruct H. exists (S x). intros m h. cbn.
    rewrite (j m x); try omega. rewrite (H (m - 1)); try omega.
    destruct emch; try rewrite H0; try reflexivity; try omega.
    elim n. auto.
  - destruct H; destruct H0. exists (S (max x x0)). intros m h.
    assert (l:= max_fst x x0). assert (l2:= max_snd x x0). simpl.
    rewrite (j m (max x x0)); try omega. rewrite H; try omega.
    rewrite H0. reflexivity. omega.
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

