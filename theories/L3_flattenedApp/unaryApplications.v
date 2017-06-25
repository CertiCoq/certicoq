
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Arith.
Require Import Coq.Logic.JMeq.
Require Import Omega.
Require Import L2_5.L2_5.
Require Import L3.term.
Require Import L3.program.
Require Import L3.wcbvEval.
Require Import L3.wNorm.
Require Import L3.compile.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2_5Term := L2_5.compile.Term.
Definition L2_5Terms := L2_5.compile.Terms.
Definition L2_5Brs := L2_5.compile.Brs.
Definition L2_5Defs := L2_5.compile.Defs.
Definition L2_5Environ := AstCommon.environ L2_5.compile.Term.


Definition optStrip (t:option L2_5Term) : option Term :=
  match t with
    | None => None
    | Some t => Some (strip t)
  end.
Definition optStrips (ts:option L2_5Terms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (strips ts)
  end.
Definition optStripBnth (b: option (nat * L2_5Term)) : option (nat * Term) :=
                           match b with
                             | None => None
                             | Some (n, t) => Some (n, strip t)
                           end.
Definition optStripDnth (b: option (L2_5Term * nat)) : option (Term * nat) :=
                           match b with
                             | None => None
                             | Some (t, n) => Some (strip t, n)
                           end.
Definition optStripCanP (b: option (nat * L2_5Terms)) : option (nat * Terms) :=
                           match b with
                             | None => None
                             | Some (n, t) => Some (n, strips t)
                           end.

Lemma optStrip_hom: forall y, optStrip (Some y) = Some (strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optStrips_hom: forall y, optStrips (Some y) = Some (strips y).
induction y; simpl; reflexivity.
Qed.
Lemma optStripBnth_hom:
  forall y n, optStripBnth (Some (n, y)) = Some (n, strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optStripDnth_hom:
  forall y n, optStripDnth (Some (y, n)) = Some (strip y, n).
induction y; simpl; reflexivity.
Qed.
Lemma optStripCanP_hom:
  forall y n, optStripCanP (Some (n, y)) = Some (n, strips y).
induction y; simpl; reflexivity.
Qed.

Lemma isConstruct_hom:
  forall t, isConstruct (strip t) ->
            L2_5.term.isConstruct t \/ L2_5.term.isCast t.
Proof.
  destruct t; intros h;
    try (cbn; destruct h as [x0 [x1 [x2 h]]]; discriminate). 
  - cbn in h. right. auto.
  - change
      (isConstruct (mkApp (strip t1) (tcons (strip t2) (strips t3)))) in h.
    pose proof (mkApp_isApp (strips t3) (strip t1) (strip t2)) as k.
    destruct k as [x0 [x1 jx]]. rewrite jx in h.
    destruct h as [y0 [y1 [y2 jy]]]. discriminate.
  - destruct h as [x0 [x1 [x2 h]]]. cbn in h. myInjection h. auto.
Qed.

Lemma tlength_hom:
  forall ts, tlength (strips ts) = L2_5.term.tlength ts.
Proof.
  induction ts.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, strips (L2_5.compile.tcons t ts) =
               tcons (strip t) (strips ts).
reflexivity.
Qed.

Lemma bcons_hom:
  forall t m ts, stripBs (L2_5.compile.bcons m t ts) =
               bcons m (strip t) (stripBs ts).
reflexivity.
Qed.

Lemma dcons_hom:
  forall nm t m ts, stripDs (L2_5.compile.dcons nm t m ts) =
               dcons nm (strip t)m  (stripDs ts).
reflexivity.
Qed.


Lemma mkApp_hom:
  forall ts t,
    strip (L2_5.compile.mkApp t ts) = mkApp (strip t) (strips ts).
Proof.
  intros. functional induction (L2_5.compile.mkApp t ts).
  - change
      (mkApp (TApp (strip fn) (strip b))
             (strips (L2_5.compile.tappend bs args)) =
       mkApp (strip (L2_5.compile.TApp fn b bs)) (strips args)).
    change
      (mkApp (TApp (strip fn) (strip b))
             (strips (L2_5.compile.tappend bs args)) =
       mkApp (mkApp (TApp (strip fn) (strip b)) (strips bs)) (strips args)).
    rewrite mkApp_idempotent. rewrite L3.compile.tappend_hom. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(******
Lemma mkApp_hom':
  forall ts t fn s, strip t = TApp fn s ->
        strip (L2_5.term.mkApp t ts) = tfold_left (strips ts) (strip t).
Proof.
  induction ts; intros.
  - cbn. rewrite L2_5.term.mkApp_tnil_ident. reflexivity.
  - cbn. rewrite <- mkApp_tfold.
    destruct (mkApp_isApp_lem t0 t ts) as
        [x0 [x1 [x2 [k0 [ [k1 [k2 [k3 k4]]] | [k1 [k2 k3]]]]]]].
    + subst. rewrite k0. cbn. rewrite (stripApp_notCnstr _ H).
      reflexivity.
    + subst. destruct k1 as [y0 [y1 [y2 l]]]. subst.
      rewrite k0. cbn. destruct (isL2_5Cnstr x0).
      * destruct p. destruct p. rewrite (stripAppApp_notCnstr _ _ _ H).
        
      Check (stripApp_notCnstr _ H).

    rewrite L2_5.term.mkApp_goodFn.
    cbn. rewrite (stripApp_notCnstr _ H). reflexivity. assumption.
Qed.
 *****)

Lemma Lookup_hom:
  forall (p:environ L2_5Term) (s:string) ec,
    Lookup s p ec -> Lookup s (stripEnv p) (stripEC ec).
Proof.
  induction 1; destruct t.
  - cbn. apply LHit.
  - cbn. apply LHit.
  - cbn. apply LMiss; assumption. 
  - cbn. apply LMiss; assumption. 
Qed.

Lemma lookup_hom:
  forall p nm ec,
    lookup nm p = Some ec -> lookup nm (stripEnv p) = Some (stripEC ec).
Proof.
  intros p nm ec h. apply Lookup_lookup.
  apply Lookup_hom. apply (lookup_Lookup _ _ h).
Qed.
  
Lemma lookup_hom_None:
  forall p nm,
    lookup nm p = None -> lookup nm (stripEnv p) = None.
Proof.
  induction p; intros.
  - cbn. reflexivity.
  - destruct a. destruct (string_dec nm s).
    + subst. cbn in H. rewrite string_eq_bool_rfl in H. discriminate.
    + cbn. rewrite (string_eq_bool_neq n).
      cbn in H. rewrite (string_eq_bool_neq n) in H.
      apply IHp. assumption.
Qed.
  
Lemma LookupDfn_hom:
  forall p s t, LookupDfn s p t -> LookupDfn s (stripEnv p) (strip t).
Proof.
  unfold LookupDfn. intros.
  assert (j:= Lookup_hom H). exact j.
Qed.

Lemma lookupDfn_hom:
  forall p nm t,
    lookupDfn nm p = Ret t -> lookupDfn nm (stripEnv p) = Ret (strip t).
Proof.
  induction p; intros.
  - cbn in *. discriminate.
  - destruct a. unfold lookupDfn. cbn. unfold lookupDfn in H. cbn in H.
    destruct (string_dec nm s).
    + subst. cbn. cbn in H.
      rewrite string_eq_bool_rfl. rewrite string_eq_bool_rfl in H.
      destruct e; try discriminate.
      * myInjection H. cbn. reflexivity.
    + rewrite (string_eq_bool_neq n). rewrite (string_eq_bool_neq n) in H.
      case_eq (lookup nm p); intros; rewrite H0 in H; try discriminate.
      * rewrite (lookup_hom _ _ H0). destruct e0; try discriminate.
        cbn. myInjection H. reflexivity.
Qed.

(***
Lemma mkApp_hom_TApp:
  forall fn arg t args brgs,
    strip (L2_5.term.mkApp (L2_5.compile.TApp fn arg args)) =
    mkApp (strip (L2_5.compile.TApp fn arg args)) (strips brgs).
Proof.
  induction args; cbn; intros; destruct (isL2_5Cnstr fn); try reflexivity.
  - 

    rewrite <- TApp_hom.
  - rewrite tunit_hom. rewrite L2_5.term.mkApp_tnil_ident.
    destruct (strip fn); cbn; try reflexivity.
    rewrite tappend_tnil. reflexivity.
  
  - destruct (L2_5.term.isApp_dec fn).
    + admit.

    + destruct fn; cbn; try reflexivity. destruct (strip fn1); cbn.


      + destruct i as [w0 [w1 [w2 wj]]]. subst.
      unfold L2_5.term.mkApp at 1. cbn. 
    
    rewrite L2_5.term.mkApp_goodFn; destruct fn;
    try L2_5.term.not_isApp; cbn; try reflexivity.
    + admit.
    +
    rewrite etaExp_cnstr_tnil.
    try L2_5.term.not_isApp.
    auto.

    
  - rewrite L2_5.term.mkApp_goodFn.
    rewrite TApp_hom. destruct (strip fn); cbn; try reflexivity.
    rewrite etaExp_cnstr_tnil. cbn.


    
    destruct (L2_5.term.isConstruct_dec fn).
    * destruct H as [ix [nx [artyx jx]]].
        subst. cbn. rewrite etaExp_cnstr_tnil.
        destruct (mkEta (TConstruct ix nx (etaArgs artyx)) artyx);
          try reflexivity.
        rewrite tappend_tnil. reflexivity.
    * destruct (strip fn); cbn; try reflexivity.


      
    destruct fn; cbn; try reflexivity.
    + destruct (L2_5.term.isConstruct_dec fn).
      * destruct H as [ix [nx [artyx jx]]].
        subst. cbn. rewrite etaExp_cnstr_tnil.
        destruct (mkEta (TConstruct ix nx (etaArgs artyx)) artyx);
          try reflexivity.
        rewrite tappend_tnil. reflexivity.
      * destruct (strip fn); try reflexivity.
      * case_eq fn; intros; cbn; try reflexivity.

      * destruct fn; cbn; try reflexivity.


        
  destruct fn; try reflexivity; cbn.
  - cbn. destruct fn; cbn; try reflexivity.
  - cbn. destruct (L2_5.term.isConstruct_dec fn).
    + destruct fn; try reflexivity;
      destruct H as [ix [nx [artyx jx]]]; try discriminate.
      * cbn. rewrite etaExp_cnstr_tnil.
        destruct (mkEta (TConstruct i n (etaArgs n0)) n0); try reflexivity.
        rewrite tappend_tnil. reflexivity.
    + 
        
      * destruct H as [i [n [arty j]]]. discriminate.
      * subst. cbn.
      rewrite etaExp_cnstr_tnil. cbn.

Admitted.
  induction args; cbn; intros; try reflexivity.
  - destruct fn; try reflexivity. unfold L2_5.term.mkApp.
    rewrite L2_5.term.tappend_tnil. reflexivity.
  - unfold L2_5.term.mkApp, mkApp. destruct fn; cbn; try unfold mkApp at 1; try reflexivity. rewrite IHargs.
    assert (k := IHargs (L2_5.compile.TApp t L2_5.compile.prop L2_5.compile.tnil)).
    unfold mkApp in k. cbn in k. destruct t; cbn.
    destruct fn; cbn; try reflexivity.
    + unfold mkApp. destruct fn1. destruct mkApp. destruct mkApp.


    induction args; cbn; intros.
  - discriminate.
  - destruct fn; try reflexivity.
    unfold etaExp_cnstr in *. cbn.
    cbn in *.
 ****************)

Lemma mkApp_goodFn:
  forall fn arg args,
    ~ L2_5.term.isApp fn ->
    strip (L2_5.compile.mkApp fn (L2_5.compile.tcons arg args)) =
    strip (L2_5.compile.TApp fn arg args).
Proof.
  destruct fn; intros; try reflexivity.
  cbn. destruct H. exists fn1, fn2, t. reflexivity.
Qed.


(*********************
Lemma mkApp_instantiate_hom:
  forall fn tin arg args n,
    ~ L2_5.term.isApp fn -> isL2_5Cnstr fn = None ->
    isL2_5Cnstr tin = None -> ~ L2_5.term.isApp tin ->
    strip
      (L2_5.compile.mkApp
         (L2_5.term.instantiate tin n fn)
         (L2_5.term.instantiates tin n (L2_5.compile.tcons arg args))) =
    mkApp (strip (L2_5.term.instantiate tin n fn))
          (strips (L2_5.term.instantiates tin n (L2_5.compile.tcons arg args))).
Proof.
  induction fn; intros; try reflexivity.
  - unfold L2_5.term.instantiate at 1. unfold L2_5.term.instantiate at 1.
    case_eq (n0 ?= n); intros.
    + Compare_Prop. subst. rewrite L2_5.compile.mkApp_tnil_ident.
      rewrite mkApp_hom; try assumption. reflexivity.
    + rewrite (L2_5.stripEvalCommute.instantiates_tcons_commute).
      rewrite L2_5.compile.mkApp_goodFn.
      * rewrite TApp_mkApp_hom; reflexivity. 
      * intros h. destruct h as [x0 [x1 [x2 k]]]. discriminate.
    + rewrite (L2_5.stripEvalCommute.instantiates_tcons_commute).
      rewrite L2_5.compile.mkApp_goodFn.
      * rewrite TApp_mkApp_hom; reflexivity. 
      * intros h. destruct h as [x0 [x1 [x2 k]]]. discriminate.
  - rewrite mkApp_hom.
    + reflexivity.
    + cbn in H0. cbn. destruct fn; try reflexivity.
      * cbn. destruct (n ?= n0); try reflexivity.
        rewrite L2_5.compile.mkApp_tnil_ident. assumption.
      * apply isL2_5Cnstr_instantiate_None.
        cbn in H0. assumption. right. assumption.
      * { change
            (isL2_5Cnstr (L2_5.compile.mkApp
                          (L2_5.term.instantiate tin n fn1)
                          (L2_5.term.instantiates tin n
                                                (L2_5.compile.tcons fn2 t))) =
             None).
          destruct fn1; try (cbn; reflexivity).
          apply isL2_5Cnstr_mkApp_None.
          - cbn. destruct (n ?= n0); try reflexivity.
            rewrite L2_5.compile.mkApp_tnil_ident. assumption.
          - 

      
    + change
        (isL2_5Cnstr (L2_5.compile.mkApp
                      (L2_5.term.instantiate tin n fn1)
                      (L2_5.term.instantiates tin n (L2_5.compile.tcons fn2 t))) =
         None).
      destruct fn1; try (cbn; reflexivity).
        (***
  - rewrite mkApp_hom.
    + reflexivity.
    + change
        (isL2_5Cnstr (L2_5.compile.mkApp
                      (L2_5.term.instantiate tin n fn1)
                      (L2_5.term.instantiates tin n (L2_5.compile.tcons fn2 t))) =
         None).
      destruct fn1; try (cbn; reflexivity).
      * { unfold L2_5.term.instantiate.
          case_eq (n ?= n0); intros; Compare_Prop; subst.
          - rewrite L2_5.compile.mkApp_tnil_ident. unfold L2_5.compile.mkApp.
            destruct tin; reflexivity.
          - unfold L2_5.compile.mkApp.
            rewrite L2_5.stripEvalCommute.instantiates_tcons_commute.
            auto.
          - unfold L2_5.compile.mkApp.
            rewrite L2_5.stripEvalCommute.instantiates_tcons_commute.
            auto. }
      * change
          (isL2_5Cnstr
             (L2_5.compile.mkApp
                (L2_5.compile.mkApp (L2_5.term.instantiate tin n fn1_1)
                               (L2_5.term.instantiates
                                  tin n (L2_5.compile.tcons fn1_2 t0)))
                (L2_5.term.instantiates tin n (L2_5.compile.tcons fn2 t)))
           = None).
        rewrite L2_5.compile.mkApp_idempotent.
        destruct fn1_1; cbn; try reflexivity.
*****)
  - elim H. auto.
  - cbn in H0. discriminate.
Qed.
*********************)

Lemma instantiate_hom:
  (forall bod arg n,
     strip (L2_5.compile.instantiate arg n bod) =
     instantiate (strip arg) n (strip bod)) /\
  (forall bods arg n,
     strips (L2_5.compile.instantiates arg n bods) =
     instantiates (strip arg) n (strips bods)) /\
  (forall bods arg n,
     stripBs (L2_5.compile.instantiateBrs arg n bods) =
     instantiateBrs (strip arg) n (stripBs bods)) /\
  (forall ds arg n,
          stripDs (L2_5.compile.instantiateDefs arg n ds) =
     instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L2_5.compile.TrmTrmsBrsDefs_ind; intros; try (cbn; reflexivity);
  try (cbn; rewrite H; reflexivity).
  - cbn. destruct (lt_eq_lt_dec n0 n); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_lt n0 n)); try omega. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
    + rewrite (proj1 (nat_compare_gt n0 n)); trivial.
  - cbn. rewrite H. rewrite H0. reflexivity.
  - change
      (strip (L2_5.compile.mkApp (L2_5.compile.instantiate arg n t)
                                 (L2_5.compile.tcons
                                    (L2_5.compile.instantiate arg n t0)
                                    (L2_5.compile.instantiates arg n t1))) =
       instantiate (strip arg) n
                   (mkApp (TApp (strip t) (strip t0)) (strips t1))).
    rewrite instantiate_mkApp_commute.
    change
      (strip
         (L2_5.compile.mkApp (compile.instantiate arg n t)
                             (L2_5.compile.tcons
                                (compile.instantiate arg n t0)
                                (compile.instantiates arg n t1))) =
       mkApp (TApp (instantiate (strip arg) n (strip t))
                   (instantiate (strip arg) n (strip t0)))
             (instantiates (strip arg) n (strips t1))).
    rewrite mkApp_hom.
    rewrite <- H; trivial. rewrite <- H0; trivial. rewrite <- H1; trivial.
  - change
      (strip (compile.instantiate arg n0 (L2_5.compile.TConstruct i n t)) =
       TConstruct i n (instantiates (strip arg) n0 (strips t))).
    rewrite <- H; trivial.
  - change
     (TCase i (strip (L2_5.term.instantiate arg n t))
            (stripBs (L2_5.compile.instantiateBrs arg n b)) =
      TCase i (instantiate (strip arg) n (strip t))
            (instantiateBrs (strip arg) n (stripBs b))).
    rewrite H; trivial. rewrite H0; trivial.
  - change
      (TFix
         (stripDs (L2_5.term.instantiateDefs
                     arg (n0 + (L2_5.compile.dlength d)) d)) n =
       TFix (instantiateDefs
               (strip arg) (n0 + (dlength (stripDs d))) (stripDs d)) n).
    rewrite H. rewrite stripDs_pres_dlength. reflexivity. 
  - rewrite L2_5.stripEvalCommute.instantiates_tcons_commute.
    rewrite tcons_hom. rewrite tcons_hom. rewrite instantiates_tcons.
    rewrite <- H; trivial. rewrite H0; trivial.
  - rewrite L2_5.stripEvalCommute.instantiates_bcons_commute.
    rewrite bcons_hom. rewrite bcons_hom. rewrite instantiateBs_bcons.
    rewrite <- H; trivial. rewrite H0; trivial.
  - rewrite L2_5.stripEvalCommute.instantiates_dcons_commute.
    rewrite dcons_hom. rewrite dcons_hom. rewrite instantiateDs_dcons.
    rewrite <- H; trivial. rewrite H0; trivial.
Qed.


Lemma tnth_hom:
  forall ts n, optStrip (L2_5.term.tnth n ts) = tnth n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.

Lemma bnth_hom:
  forall ts n, optStripDnth (L2_5.term.bnth n ts) = bnth n (stripBs ts).
induction ts; cbn; intros m; case m; try reflexivity; trivial.
Qed. 

Lemma tskipn_hom:
  forall ts n, optStrips (L2_5.term.tskipn n ts) = tskipn n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.

    
Lemma whCaseStep_hom:
  forall n brs ts,
    optStrip (L2_5.term.whCaseStep n ts brs) =
    whCaseStep n (strips ts) (stripBs brs).
Proof.
  destruct n, brs; intros; simpl; try reflexivity.
  - unfold whCaseStep. cbn. apply f_equal. rewrite mkApp_hom.
    reflexivity.
  - unfold whCaseStep. unfold L2_5.term.whCaseStep. cbn. 
    rewrite <- bnth_hom. destruct (L2_5.term.bnth n brs); simpl.
    + destruct p. cbn. rewrite mkApp_hom. reflexivity. 
    + reflexivity.
Qed.

(****************
Lemma whBetaStep_tnil_hom:
  forall bod arg, WFTrm (strip arg) 0 -> L2_5.term.WFapp bod ->
    strip (L2_5.term.whBetaStep bod arg L2_5.compile.tnil) =
    whBetaStep (strip bod) (strip arg).
Proof.
  intros. unfold L2_5.term.whBetaStep, whBetaStep.
  rewrite mkApp_hom.
  Check (proj1 instantiate_hom).
  rewrite <- (proj1 instantiate_hom); try assumption.
  rewrite L2_5.term.mkApp_tnil_ident.
  reflexivity.
Qed.
 *******************)

Lemma whBetaStep_hom:
  forall bod arg args,
    strip (L2_5.term.whBetaStep bod arg args) =
    mkApp (whBetaStep (strip bod) (strip arg)) (strips args).
Proof.
  intros. unfold L2_5.term.whBetaStep, whBetaStep.
  rewrite mkApp_hom. rewrite <- (proj1 instantiate_hom). reflexivity.
Qed.


(***
Goal
  forall args fn arg,
    strip (L2_5.compile.TApp fn arg args) =
    TApp (strip fn) (strips args)) (strip arg).
Proof.
  destruct fn; cbn; induction args; cbn; intros;
  try reflexivity; try rewrite <- tappend_assoc; cbn.
  - rewrite IHargs. unfold pre_mkApp. unfold pre_mkApp in IHt.
 ***)

Lemma isApp_mkApp_TApp:
  forall args fn arg, isApp (mkApp (TApp fn arg) args).
Proof.
  induction args; intros.
  - cbn. auto.
  - cbn. apply IHargs.
Qed.
      
Lemma TProof_mkApp_invrt:
  forall fn args, TProof = mkApp fn args -> fn = TProof /\ args = tnil.
Proof.
  intros fn args. destruct args; cbn; intros.
  - intuition.
  - pose proof (isApp_mkApp_TApp args fn t) as k.
    destruct (k) as [x0 [x1 jx]]. rewrite jx in H. discriminate.
Qed.

Lemma WcbvEval_mkApp_invrt:
  forall p fn args t,
    WcbvEval p (mkApp fn args) t -> WcbvEval p fn fn ->
    (exists s, WcbvEval p fn s /\ WcbvEval p (mkApp s args) t).
Proof.
  intros p fn args t. destruct args; cbn; intros.
  - exists t. intuition. eapply (proj1 (WcbvEval_no_further p)). eassumption.
  - exists fn. intuition.
Qed.

(*****                                               
Lemma WcbvEval_hom:
  forall p,
    (forall t t', L2_5.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L2_5.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (strips ts) (strips ts')).
Proof.
  intros p.
  apply L2_5.wcbvEval.WcbvEvalEvals_ind; intros; try reflexivity;
    try (solve[constructor; trivial]); try assumption.
  - cbn. econstructor; try eassumption. apply LookupDfn_hom.
    unfold LookupDfn. unfold lookupDfn in e. case_eq (lookup nm p); intros.
    + rewrite H0 in e. destruct e0.
      * myInjection e. apply lookup_Lookup. assumption.
      * discriminate.
    + rewrite H0 in e. discriminate.
  - (* beta step in L2_5 *)
    change
      (WcbvEval (stripEnv p)
                (mkApp (TApp (strip fn) (strip a1)) (strips args))
                (strip s)).
    cbn in H.
    eapply WcbvEval_mkApp_step. eapply wAppLam; try eassumption.
    rewrite whBetaStep_hom in H1. unfold whBetaStep in *.
    + instantiate (1:= whBetaStep (strip bod) (strip a1')).
      unfold whBetaStep.
    + rewrite whBetaStep_hom in H1. apply H1.
  -

    Check WcbvEval_mkApp_step.

    cbn in H.
    unfold L2_5.term.whBetaStep in w1.
    rewrite whBetaStep_hom in H1. unfold whBetaStep in H1.
    destruct args.
    + cbn. econstructor; eassumption.
    + rewrite tcons_hom.
      eapply WcbvEval_mkApp_step.
      Check tcons_has_last. Check mkApp_out.


      cbn.
      
    admit.
  - cbn. eapply wLetIn; try eassumption.
    rewrite <- (proj1 (instantiate_hom)). assumption.
  - (* Fix step in L2_5 *)
    change
      (WcbvEval (stripEnv p)
                (mkApp (TApp (strip fn) (strip arg)) (strips args))
                (strip s)).
    admit.
  - (* App congruence in L2_5 *)
    change
      (WcbvEval (stripEnv p)
                (mkApp (TApp (strip fn) (strip arg)) (strips args))
                (strip (L2_5.compile.mkApp fn' aargs'))).
    admit.
  - change
      (WcbvEval (stripEnv p)
                (TCase ml (strip mch) (stripBs brs)) (strip s)).
    eapply (@wCase (stripEnv p)
                  (strip mch) ml i _ _
                  (stripBs brs) (strip cs) (strip s));
      try assumption.
    + exact H. 
    + rewrite <- whCaseStep_hom. rewrite e. reflexivity.
  - (* case congruence in L2_5 *)
    change
      (WcbvEval (stripEnv p)
                (TCase ml (strip mch) (stripBs brs))
                (TCase ml (strip Mch) (stripBs brs))).
    constructor; try assumption.
    intros h. elim n. destruct (isConstruct_hom _ h).
    + destruct H0 as [x0 [x1 [x2 jx]]]. subst. econstructor.
      exists x1, x2. reflexivity.
    + destruct H0 as [x0 jx]. subst. cbn in h. cbn in H.
      elim (proj1 (L2_5.wcbvEval.WcbvEval_not_Cast p) _ _ w). auto.
Admitted.
 *********************)

(*****
Lemma whBetaStep_hom:
  forall bod arg args,
    strip (L2_5.term.whBetaStep bod arg args) =
    whBetaStep (strip bod) (strip arg) (strips args).
intros bod arg args.
unfold L2_5.term.whBetaStep, whBetaStep.
rewrite mkApp_hom. rewrite <- (proj1 instantiate_hom). reflexivity.
Qed.
 *****)


(*********************
Lemma WcbvEval_hom:
  forall (p:L2_5Env), 
  (forall t t': L2_5Term, L2_5.wcbvEval.WcbvEval p t t' ->
                        L3.wcbvEval.WcbvEval (L3.compile.stripEnv p)
                                             (L3.compile.strip t)
                                             (L3.compile.strip t')) /\
  (forall ts ts', L2_5.wcbvEval.WcbvEvals p ts ts' ->
                  L3.wcbvEval.WcbvEvals (L3.compile.stripEnv p)
                                        (L3.compile.strips ts)
                                        (L3.compile.strips ts')).
Proof.
  intros p.
  apply L2_5.wcbvEval.WcbvEvalEvals_ind; cbn; intros; try reflexivity;
  try intuition; try (rewrite <- H; rewrite <- H0; constructor).
  - induction arty.
    + constructor. constructor.
    + cbn. rewrite mkEta_under_Lambda. constructor. 
  - econstructor. unfold LookupDfn in l. unfold LookupDfn. apply (Lookup_hom l).
    assumption.
  - destruct (L2_5.term.isLambda_dec fn).
    + destruct i as [x0 [x1 j0]]. rewrite j0. induction args; cbn.
      * repeat econstructor. inversion_Clear H0. eassumption.
        rewrite whBetaStep_hom in H1.
        
exact H1.
    


    
  - destruct (L2_5.term.isLambda_dec fn).
    + destruct i as [x0 [x1 j0]]. rewrite j0. cbn; destruct a1; cbn.
      assert (k:= TApp_hom (L2_5.compile.TLambda x0 x1)). cbn in k.


    ; destruct args; cbn.
    + econstructor. inversion w. 
    
  - unfold LookupDfn in l. rewrite (Lookup_lookup l).
    econstructor. unfold LookupDfn. apply Lookup_hom.
    inversion_Clear l.

    
    inversion_Clear l. cbn. rewrite string_eq_bool_rfl.
    unfold program.ecAx. unfold AstCommon.ecAx. cbn.
    constructor.
    Check (stripEnv_not_LookupAx p).
    Check (Lookup_hom l). destruct (lookup nm p).
    + constructor. 
    + destruct e.
      * unfold AstCommon.LookupDfn.inversion l.
      * eapply wConst. unfold AstCommon.LookupDfn. Print AstCommon.ecAx.
        unfold AstCommon.ecAx in l.
        change ((@AstCommon.Lookup Term) nm p (AstCommon.ecAx Term)) in l.
        Check (Lookup_hom l).

        rewrite <- H. eapply wConst.
        unfold AstCommon.LookupDfn.
        Check Lookup_hom. apply Lookup_hom.
      unfold LookupAx in l.

    rewrite <- H0. rewrite <- H1.
    
  - myInjection H. myInjection H0. constructor.
  - case_eq (strip p bod); intros x hx; rewrite hx in *.
    + discriminate.
    + myInjection H. myInjection H0. constructor.
  - case_eq (strip p bod); intros x hx; rewrite hx in *.
    + discriminate.
    + myInjection H. myInjection H0. constructor.
  - intuition.
  - case_eq (etaExp_cnstr p i r tnil); intros x hx; rewrite hx in *.
    + discriminate.
    + myInjection H. myInjection H0. constructor.
*******)


(**** L2_5 and L3 agree on cbv evaluation  ****
Lemma wndEval_types_irrelevant:
  forall (p:L2_5Environ),
    (forall (t s:L2_5Term),
       L2_5.wcbvEval.WcbvEval p t s ->
       WcbvEval (stripEnv p) (strip p t) (strip p s))  /\
    (forall ts ss,
       L2_5.wcbvEval.WcbvEvals p ts ss ->
       WcbvEvals (stripEnv p) (strips p ts) (strips p ss)).
Proof.
  intros p.
  apply L2_5.wcbvEval.WcbvEvalEvals_ind; intros; try reflexivity;
  try (solve[constructor; trivial]); try assumption.
  - admit. (** rewrite TConstruct_hom.  cbn. **)
  - unfold LookupAx in l. cbn. assert (j:= Lookup_lookup l). 
    Check j. Check (lookup nm p).
    destruct (lookup nm p).
    + destruct e. refine (wConst _ _). unfold AstCommon.LookupDfn.
    rewrite j.

    
  - rewrite TFix_hom. rewrite TFix_hom. 
    
  - change (strip p t = Some tt) in H0. eapply H; assumption.
  - unfold strip in H. unfold strip in H0. rewrite H in H0.
    myInjection H0. clear H0. unfold etaExp_cnstr in H.
    destruct (cnstrArity p i r).
    + destruct (PeanoNat.Nat.compare (tlength tnil) n).
      * myInjection H. constructor. constructor.
      * myInjection H. clear H. rewrite <- minus_n_O.
        { induction n.
          - simpl. constructor. constructor.
          - change 
              (WcbvEval pp
                        (mkEta (TLambda nAnon
                                        (TConstruct i r (etaArgs (S n)))) n)
                        (mkEta (TLambda nAnon
                                        (TConstruct i r (etaArgs (S n)))) n)).
            simpl. rewrite mkEta_under_Lambda. constructor. }
      * discriminate.
    + discriminate.
  - rewrite (strip_Ind_invrt H). rewrite (strip_Ind_invrt H0). constructor.
  - unfold strip in H. unfold strip in H0. myInjection H. myInjection H0.
    constructor.
  -





Qed.

***)


(***  scratch below  *****
Section FlatApp.
Variable flatApp: L2_5Term -> Term.
Fixpoint flatApps (ts:L2_5Terms) : Terms :=
  match ts with
    | L2_5.term.tnil => tnil
    | L2_5.term.tcons s ss => tcons (flatApp s) (flatApps ss)
  end.
Fixpoint flatAppDs (ts:L2_5Defs) : Defs :=
  match ts with
    | L2_5.term.dnil => dnil
    | L2_5.term.dcons nm bod n ds => dcons nm (flatApp bod) n (flatAppDs ds)
  end.
Fixpoint mkApp (fn:Term) (l:L2_5Terms) : Term :=
    match l with
      | L2_5.term.tnil => fn
      | L2_5.term.tcons b t => mkApp (TApp fn (flatApp b)) t
    end.
End FlatApp.

Function flatApp (t:L2_5Term) : Term :=
  match t with
    | L2_5.term.TRel n => TRel n
    | L2_5.term.TSort s => TSort s
    | L2_5.term.TProd nm bod => TProd nm (flatApp bod)
    | L2_5.term.TLambda nm bod => TLambda nm (flatApp bod)
    | L2_5.term.TLetIn nm dfn bod => TLetIn nm (flatApp dfn) (flatApp bod)
    | L2_5.term.TApp fn arg args =>
      match fn with 
        | L2_5.term.TConstruct i n =>
             TConstruct i n (tcons (flatApp arg) (flatApps args))
        | x => mkApp flatApp (flatApp x)
                     (tcons (flatApp arg) (flatApps flatApp args))
      end
    | L2_5.term.TConst nm => TConst nm
    | L2_5.term.TInd i => TInd i
    | L2_5.term.TConstruct i n => TConstruct i n tnil
    | L2_5.term.TCase n mch brs => TCase n (flatApp mch) (flatApps brs)
    | L2_5.term.TFix ds n => TFix (flatAppDs ds) n
  end.
***)
