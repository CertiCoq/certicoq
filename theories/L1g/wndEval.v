
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Setoids.Setoid.
Require Import Coq.omega.Omega.
Require Import Coq.micromega.Lia.
Require Import Common.Common.
Require Import L1g.compile.
Require Import L1g.term.
Require Import L1g.program.
(* Require Import L1g.awndEval. *)

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

(*** non-deterministic small step evaluation relation ***)
Section Env.
Variable p: environ Term.
Inductive wndEval : Term -> Term -> Prop :=
(*** contraction steps ***)
| sConst: forall (kn:kername) (t:Term),
    LookupDfn kn p t -> wndEval (TConst kn) t
| sBeta: forall (nm:name) (bod arg:Term),
    wndEval (TApp (TLambda nm bod) arg) (whBetaStep bod arg)
(* note: [instantiate] is total *)
| sLetIn: forall (nm:name) (dfn bod:Term),
    wndEval (TLetIn nm dfn bod) (instantiate dfn 0 bod)
(* Case argument must be in Canonical form *)
(* n is the number of parameters of the datatype *)
| sCase: forall (ml:inductive * nat) (s mch:Term)
                (args ts:Terms) (brs:Brs) (n npars nargs:nat),
    canonicalP mch = Some (n, npars, nargs, args) ->
    tskipn (snd ml) args = Some ts ->
    whCaseStep n ts brs = Some s ->
    wndEval (TCase ml mch brs) s
| sFix: forall (dts:Defs) (m:nat) (arg:Term) (x:Term) (ix:nat),
    (** ix is index of recursive argument **)
    dnthBody m dts = Some (x, ix) ->
    wndEval (TApp (TFix dts m) arg) (pre_whFixStep x dts arg)
| sProofApp arg: wndEval (TApp TProof arg) TProof
| sProj: forall bod r npars nargs args arg x ind,
    canonicalP bod = Some (r, npars, nargs, args) ->
    List.nth_error args (npars + arg) = Some x ->
    wndEval (TProj (ind, npars, arg) bod) x          
(*** congruence steps ***)
(** no xi rules: sLambdaR, sLetInR,
 *** no congruence on Case branches ***)
| sAppFn:  forall (t r arg:Term),
    wndEval t r -> wndEval (TApp t arg) (TApp r arg)
| sAppArg: forall (t arg brg:Term),
    wndEval arg brg -> wndEval (TApp t arg) (TApp t brg)
| sLetInDef:forall (nm:name) (d1 d2 bod:Term),
    wndEval d1 d2 -> wndEval (TLetIn nm d1 bod) (TLetIn nm d2 bod)
| sCaseArg: forall (nl:inductive * nat) (mch can:Term) (brs:Brs),
    wndEval mch can -> wndEval (TCase nl mch brs) (TCase nl can brs)
| sProjBod: forall prj bod Bod,
    wndEval bod Bod -> wndEval (TProj prj bod) (TProj prj Bod).
Hint Constructors wndEval : core.

(**********
with wndEvals : Terms -> Terms -> Prop :=
     | saHd: forall (t r:Term) (ts:Terms), 
         wndEval t r ->
         wndEvals (tcons t ts) (tcons r ts)
     | saTl: forall (t:Term) (ts ss:Terms),
         wndEvals ts ss ->
         wndEvals (tcons t ts) (tcons t ss).
Hint Constructors wndEval wndEvals : core.
Scheme wndEval1_ind := Induction for wndEval Sort Prop
  with wndEvals1_ind := Induction for wndEvals Sort Prop.
Combined Scheme wndEvalEvals_ind from wndEval1_ind, wndEvals1_ind.
 ******************)

(** example: evaluate lia = (\x.xx)(\x.xx): nontermination **)
Definition xx := (TLambda nAnon (TApp (TRel 0) (TRel 0))).
Definition xxxx := (TApp xx xx).
Goal wndEval xxxx xxxx.
unfold xxxx, xx. eapply sBeta. 
Qed.

Lemma Lookup_Lkup_index_pos:
  forall nm ec, Lookup nm p ec -> Lkup_index nm p > 0.
Proof.
  induction 1; intros.
  - cbn. rewrite eq_kername_refl. lia.
  -  cbn. rewrite (eq_kername_bool_neq H).
     destruct (Lkup_index s2 p); lia.
Qed.

Lemma Lookup_hd:
  forall nm s t,
    Lookup nm ((nm, ecTrm s) :: p) (ecTrm t) -> s = t.
Proof.
  intros. inversion_Clear H.
  - reflexivity.
  - elim H5. reflexivity.
Qed.


(***************
Goal  WRONG
  forall nm t, PoccTrm nm t ->  Lkup_index nm p > 0.
Proof.
  induction 1; intros; try assumption.
  -

  
Goal
  crctEnv p ->
forall nm t, Lookup nm p (ecTrm t) ->
             forall nm', PoccTrm nm' t ->
                         Lkup_index nm p < Lkup_index nm' p.
Proof.
  induction 1; intros.
  - unfold LookupDfn in H. inversion H.
  - destruct (string_dec nm0 nm).
    + subst nm0. cbn. rewrite string_eq_bool_rfl.
      rewrite (Lookup_hd H2) in *.
      destruct (string_dec nm' nm).
      * subst nm'. rewrite string_eq_bool_rfl.


        inversion_Clear H1. unfold LookupDfn in IHcrctEnv, H6.




        Goal
  forall s t u, Lookup s p u -> u = (ecTrm (TConst t)) ->
                  crctEnv p -> Lkup_index s p < Lkup_index t p.
Proof.
  induction 1; intros.
  - subst t0. inversion_Clear H0. cbn. rewrite string_eq_bool_rfl.
    inversion_Clear H5.
  - unfold LookupDfn in H. inversion H.
  - destruct (string_dec s0 nm).
    + subst s0. unfold LookupDfn in H2. inversion_Clear H2.
      * inversion_Clear H1. unfold LookupDfn in IHcrctEnv, H6.




        Goal
  crctEnv p ->
forall s t u, Lookup s p u -> u = (ecTrm (TConst t)) ->
                            Lkup_index s p < Lkup_index t p.
Proof.
  induction 1; intros.
  - unfold LookupDfn in H. inversion H.
  - destruct (string_dec s0 nm).
    + subst s0. unfold LookupDfn in H2. inversion_Clear H2.
      * inversion_Clear H1. unfold LookupDfn in IHcrctEnv, H6.

  Goal
  crctEnv p -> forall s, ~ (LookupDfn s p (TConst s)).
Proof.
  induction 1; intros; intros h; unfold LookupDfn in h.
  - inversion h.
  - destruct (string_dec s0 nm).
    + subst. pose proof (Lookup_lookup h) as j0. cbn in j0.
      rewrite string_eq_bool_rfl in j0. injection j0. intros j1.
      subst s. unfold LookupDfn in IHcrctEnv.    





      (**************)
Lemma wndEval_not_rfl:
  crctEnv p -> forall t t', wndEval t t' -> t <> t'.
Proof.
  intros hp. induction 1; intros.
  - unfold LookupDfn in H. intros h. subst t.
                                  
                                  


    assert (j:= LookupDfn_lookupDfn l eq_refl).
    unfold  lookupDfn in j. destruct (lookup s p).
    + destruct e. myInjection j. Check (proj1 Crct_not_bad_Lookup).
  

  
  apply (wf_ind TrmSize (fun t => ~ wndEval t t)).
  intros t whih. destruct t; intros h; try (solve[inversion h]).
  - inversion h. assert (j := f_equal TrmSize H3). simpl in j. lia.
  - inversion_Clear h. eapply whih; try eassumption.
    simpl. lia.  
  - inversion_Clear h. eapply whih; try eassumption.
    simpl. lia.
  - inversion_Clear h.
    + eapply whih; try eassumption.
      * simpl. admit.
      * 
    +   

    induction t; intros h; try (solve[inversion h]);
  try (solve[inversion h; contradiction]).
  - inversion h.
    assert (j := f_equal TrmSize H3). simpl in j. lia.
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
    assert (j := f_equal TrmSize H3). simpl in j. lia.
  -  inversion h.

     Lemma wndEval_not_rfl:
  forall t, ~ wndEval t t.
Proof.
  induction t; intros h; try (solve[inversion h]).
  - inversion h.
    assert (j := f_equal TrmSize H3). simpl in j. lia.
  -  inversion h.
**********************)
  
(************
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
******************)
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

(**********
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
(***
  - rewrite <- (@mkApp_goodFn (TProof s)). eapply sAppFn.
    + apply sProof. assumption.
    + not_isApp.
****)
  (* - apply (@sAppFn TProof TProof a1 args). constructor. *)
  - destruct args; simpl.
    + constructor.
    + constructor.
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
 *******************)

Lemma wndEval_pres_WFapp:
  WFaEnv p -> forall t s, wndEval t s -> WFapp t -> WFapp s.
Proof.
  intros hp.
  induction 1; intros;
    try (solve [inversion_Clear H0; constructor; intuition]).
  - unfold LookupDfn in H. assert (j:= Lookup_pres_WFapp hp H).
    inversion j. assumption.
  - inversion_Clear H. inversion_Clear H2.
    apply whBetaStep_pres_WFapp; assumption.
  - inversion_Clear H. apply instantiate_pres_WFapp; assumption.
  - inversion_Clear H2.
    refine (whCaseStep_pres_WFapp _ _ _ H1). assumption.
    refine (tskipn_pres_WFapp _ _ H0).
    refine (canonicalP_pres_WFapp _ _ _); try eassumption. reflexivity.
  - inversion_Clear H0. inversion_Clear H3.
    assert (j:= dnthBody_pres_WFapp H1 m).
    apply pre_whFixStep_pres_WFapp; try assumption.
    + eapply j. eassumption.
  - constructor.
  - eapply WFapps_all; try eassumption.
    eapply canonicalP_pres_WFapp; try reflexivity; try eassumption.
    inversion_Clear H1. assumption.
Qed.
  
(*********
Lemma wndEvals_pres_WFapp:
  WFaEnv p -> forall ts ss, wndEvals ts ss -> WFapps ts -> WFapps ss.
Proof.
  intros hp ts ss hts ht.
  assert (j:= (proj2 (awndEval_pres_WFapp hp) ts ss)).
  apply j; try assumption.
  - apply (proj2 wndEval_awndEval); assumption.
Qed.
****************) 

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
    lia.
  - destruct (Crct_invrt_LetIn H eq_refl) as [h1 [h2 h3]].
    apply instantiate_pres_Crct; try assumption. lia.
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
  forall nm bod s,
    wndEval (TLambda nm bod) s -> s = (TLambda nm bod).
Proof.
intros nm bod s h. inversion_Clear h.
Qed.


(** when reduction stops **)
Definition no_wnd_step (t:Term) : Prop :=
  no_step wndEval t.


(** reflexive-transitive closure of wndEval **)
Inductive wndEvalRTC: Term -> Term -> Prop :=
(** | wERTCrfl: forall t, WNorm t -> wndEvalRTC t t ??? **)
| wERTCrfl: forall t, wndEvalRTC t t
| wERTCstep: forall t s, wndEval t s -> wndEvalRTC t s
| wERTCtrn: forall t s u, wndEvalRTC t s -> wndEvalRTC s u ->
                          wndEvalRTC t u.
Hint Constructors wndEvalRTC : core.
(***********
Inductive wndEvalsRTC: Terms -> Terms -> Prop :=
(** | wEsRTCrfl: forall ts, WNorms ts -> wndEvalsRTC p ts ts ??? **)
| wEsRTCrfl: forall ts, wndEvalsRTC ts ts
| wEsRTCstep: forall ts ss, wndEvals ts ss -> wndEvalsRTC ts ss
| wEsRTCtrn: forall ts ss us, wndEvalsRTC ts ss -> wndEvalsRTC ss us ->
                          wndEvalsRTC ts us.
Hint Constructors wndEvalRTC wndEvalsRTC : core.
*******************)

Lemma wndEvalRTC_pres_WFapp:
  WFaEnv p -> forall t s, wndEvalRTC t s -> WFapp t -> WFapp s.
Proof.
  intros hp.
  induction 1; intros; try assumption.
  - eapply (wndEval_pres_WFapp); eassumption.
  - apply IHwndEvalRTC2; try assumption.
    + apply IHwndEvalRTC1; assumption.
Qed.

(********
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
 **********************)

Inductive wndEvalTCl: Term -> Term -> Prop :=
| wETClstep: forall t s, wndEval t s -> wndEvalTCl t s
| wETCltrn: forall t s, wndEvalTCl t s ->
                        forall u, wndEval s u -> wndEvalTCl t u.
Hint Constructors wndEvalTCl : core.
(*********************
Inductive wndEvalsTCl: Terms -> Terms -> Prop :=
| wEsTClstep: forall ts ss, wndEvals ts ss -> wndEvalsTCl ts ss
| wEsTCltrn: forall ts ss, wndEvalsTCl ts ss -> 
         forall us, wndEvals ss us -> wndEvalsTCl ts us.
Hint Constructors wndEvalsTCl : core.
*********************)

(** transitive congruence rules **)
(*** HERE is a version of the problem  ***)

Lemma wndEvalRTC_App_fn:
  WFaEnv p ->
  forall fn fn', wndEvalRTC fn fn' -> WFapp fn ->
    forall arg, WFapp arg -> wndEvalRTC (TApp fn arg) (TApp fn' arg).
Proof.
  intros hp. induction 1; intros.
  - apply wERTCrfl.
  - apply wERTCstep. apply sAppFn. assumption.
  - eapply wERTCtrn.
    + apply IHwndEvalRTC1; assumption.
    + pose proof (wndEvalRTC_pres_WFapp hp H H1) as j.
      apply IHwndEvalRTC2; assumption.
Qed.

Lemma wndEvalRTC_Proj_bod:
  WFaEnv p ->
  forall bod bod', wndEvalRTC bod bod' -> WFapp bod ->
    forall prj, wndEvalRTC (TProj prj bod) (TProj prj bod').
Proof.
  intros hp. induction 1; intros.
  - apply wERTCrfl.
  - apply wERTCstep. apply sProjBod. assumption.
  - eapply wERTCtrn.
    + apply IHwndEvalRTC1; assumption.
    + pose proof (wndEvalRTC_pres_WFapp hp H H1) as j.
      apply IHwndEvalRTC2; assumption.
Qed.

Lemma wndEvalRTC_App_arg:
  forall fn arg arg',
    wndEvalRTC arg arg' ->
      wndEvalRTC (TApp fn arg) (TApp fn arg').
Proof.
  induction 1.
  - constructor.
  - constructor. apply sAppArg. assumption.
  - eapply wERTCtrn;
    try apply IHwndEvalRTC1; try apply IHwndEvalRTC2; assumption.
Qed.

Lemma wndEvalRTC_App_fn_arg:
  WFaEnv p ->
  forall fn fn', wndEvalRTC fn fn' -> WFapp fn ->
                 forall arg arg', wndEvalRTC arg arg' -> WFapp arg ->
                                  wndEvalRTC (TApp fn arg) (TApp fn' arg').
Proof.
  intros. eapply wERTCtrn.
  - instantiate (1:= (TApp fn' arg)). apply wndEvalRTC_App_fn; assumption.
  - apply wndEvalRTC_App_arg. assumption.
Qed.

Lemma wndEvalRTC_App_Proof:
  WFaEnv p ->
  forall fn fn', wndEvalRTC fn fn' -> fn' = TProof -> WFapp fn ->
                 forall arg, WFapp arg -> wndEvalRTC (TApp fn arg) TProof.
Proof.
  intros hp. induction 1; intros; subst.
  - constructor. constructor.
  - eapply wERTCtrn. instantiate (1:= (TApp TProof arg)).
    + apply wndEvalRTC_App_fn; try assumption. constructor. assumption.
    + constructor. constructor.
  - eapply wERTCtrn. 
    + apply wndEvalRTC_App_fn; try eassumption.
    + apply IHwndEvalRTC2; try assumption. reflexivity.
      eapply wndEvalRTC_pres_WFapp; eassumption.
Qed.

Lemma wndEvalRTC_Proof: wndEvalRTC TProof TProof.
Proof.
  constructor.
Qed.


Lemma wndEvalRTC_LetIn_dfn:
  forall nm dfn dfn',
    wndEvalRTC dfn dfn' ->
    forall bod, 
      wndEvalRTC (TLetIn nm dfn bod) (TLetIn nm dfn' bod).
Proof.
  induction 1; intros.
  - apply wERTCrfl. 
  - apply wERTCstep. apply sLetInDef. assumption.
  - eapply wERTCtrn. apply IHwndEvalRTC1. apply IHwndEvalRTC2.
Qed.

Lemma wndEvalRTC_Case_mch:
  forall mch mch',
    wndEvalRTC mch mch' -> 
    forall np brs, 
      wndEvalRTC (TCase np mch brs) (TCase np mch' brs).
Proof.
  induction 1; intros.
  - constructor.
  - constructor. apply sCaseArg. assumption.
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
 
End Env.
Hint Constructors wndEval wndEvalRTC : core.


Lemma wndEval_weaken:
  forall p t s, wndEval p t s ->
                 forall nm ec, fresh nm p -> wndEval ((nm,ec)::p) t s.
Proof.
  induction 1; intros; auto.
  - apply sConst. apply Lookup_weaken; assumption.
  - eapply sCase; eassumption.
  - eapply sFix; eassumption.
  - eapply sProj; eassumption.
Qed.

Lemma wndEval_strengthen:
  forall pp t s, wndEval pp t s -> forall nm ec p, pp = (nm,ec)::p ->
        ~ PoccTrm nm t -> wndEval p t s.
Proof.
  induction 1; intros; auto.
  - apply sConst; subst. unfold LookupDfn in *. destruct (kername_eq_dec kn nm).
    + subst. elim H1. constructor.
    + refine (Lookup_strengthen H _ _). reflexivity. assumption.
  - eapply sCase; eassumption.
  - eapply sFix; eassumption.
  - econstructor; eassumption.
  - constructor. eapply IHwndEval. eassumption.
    intros h. elim H1. constructor. assumption.
  - constructor. subst pp. eapply IHwndEval. reflexivity.
    intros h. elim H1. apply PoAppA. assumption.
  - apply sLetInDef. eapply IHwndEval. eassumption.
    intros h. elim H1. apply PoLetInDfn. assumption.
  - apply sCaseArg. eapply IHwndEval. eassumption.
    intros h. elim H1. apply PoCaseL. assumption.
  - apply sProjBod. eapply IHwndEval. eassumption.
    intros h. elim H1. apply PoProj. assumption.
Qed.
