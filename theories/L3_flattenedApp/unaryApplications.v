
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
  forall t, isConstruct (strip t) -> L2_5.term.isConstruct t.
Proof.
  destruct t; intros h;
    try (cbn; destruct h as [x0 [x1 [x2 h]]]; discriminate). 
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

Lemma TApp_hom:
  forall fn arg args,
    strip (L2_5.compile.TApp fn arg args) =
    mkApp (strip fn) (strips (L2_5.compile.tcons arg args)).
  destruct fn; intros arg args; try reflexivity.
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

Lemma TCase_hom:
  forall i de brs ,
    strip (L2_5.compile.TCase i de brs) = TCase i (strip de) (stripBs brs).
Proof.
  intros. reflexivity. 
Qed.

Lemma TConstruct_hom:
  forall i ix ts ,
    strip (L2_5.compile.TConstruct i ix ts) = TConstruct i ix (strips ts).
Proof.
  intros. reflexivity. 
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

Lemma dlength_hom:
  forall dts, dlength (stripDs dts) = L2_5.compile.dlength dts.
Proof.
  induction dts; cbn. reflexivity. rewrite IHdts. reflexivity.
Qed.

Lemma dnthBody_hom:
  forall dts m,
    dnthBody m (stripDs dts) =
    option_map (fun x => strip (fst x)) (L2_5.term.dnthBody m dts).
Proof.
  induction dts; intros.
  - reflexivity.
  - case_eq m; intros.
    + unfold dnthBody, L2_5.term.dnthBody. rewrite dcons_hom. unfold dnth.
      reflexivity.
    + rewrite dcons_hom.
      change
        (dnthBody n1 (stripDs dts) =
         option_map (fun x : compile.L2_5Term * nat => strip (fst x))
                    (L2_5.term.dnthBody n1 dts)).
      rewrite <- IHdts. reflexivity.
Qed.

Lemma fold_left_hom:
forall (F:L2_5Term -> nat -> L2_5Term) 
       (stripF:Term -> nat -> Term) (ns:list nat) (t:L2_5Term),
  (forall (s:L2_5Term) (n:nat), strip (F s n) = stripF (strip s) n) ->
  strip (fold_left F ns t) = fold_left stripF ns (strip t).
Proof.
  induction ns; intros t h.
  - intuition.
  - simpl. rewrite IHns.
    + rewrite h. reflexivity.
    + assumption.
Qed.

Lemma L25dnthBody_dnthBody:
  forall m dts L25bod q,
    L2_5.term.dnthBody m dts = Some (L25bod, q) ->
    forall t, dnthBody m (stripDs dts) = Some t -> strip L25bod = t.
Proof.
  induction m; induction dts; intros.
  - cbn in H0. discriminate.
  - specialize (IHdts L25bod). cbn in H.
    change (Some (strip t) = Some t0) in H0.
    myInjection H. myInjection H0. reflexivity.
  - cbn in H. discriminate.
  - cbn in H.
    change (dnthBody m (stripDs dts) = Some t0) in H0.
    specialize (IHm _ _ _ H _ H0). assumption.
Qed.

Lemma pre_whFixStep_hom:
  forall x dts arg args,
    mkApp (pre_whFixStep (strip x) (stripDs dts) (strip arg)) (strips args) =
    strip (L2_5.term.pre_whFixStep x dts (L2_5.compile.tcons arg args)).
Proof.
  intros. unfold pre_whFixStep, L2_5.term.pre_whFixStep.
  rewrite mkApp_hom. rewrite tcons_hom. cbn. eapply f_equal2; try reflexivity.
  erewrite fold_left_hom.
  - rewrite <- dlength_hom. reflexivity.
  - intros. cbn. rewrite (proj1 instantiate_hom). rewrite TFix_hom.
    reflexivity.
Qed.

(**********
Lemma whFixStep_hom:
  forall L25bod q dts m,
    L2_5.term.dnthBody m dts = Some (L25bod, q) ->
    forall bod,
      dnthBody m (stripDs dts) = Some bod ->
      forall args,
        strip (L2_5.term.pre_whFixStep L25bod dts args) =
        mkApp (fold_left
                 (fun bod ndx => instantiate (TFix (stripDs dts) ndx) 0 bod)
                 (list_to_zero (dlength (stripDs dts))) bod)
              (strips args).
Proof.
  intros. unfold L2_5.term.pre_whFixStep. rewrite mkApp_hom.
***************)

Lemma whFixStep_hom:
  forall L25bod q dts m,
    L2_5.term.dnthBody m dts = Some (L25bod, q) ->
    forall bod,
      dnthBody m (stripDs dts) = Some bod ->
      forall args,
        strip (L2_5.term.pre_whFixStep L25bod dts args) =
        mkApp (fold_left
                 (fun bod ndx => instantiate (TFix (stripDs dts) ndx) 0 bod)
                 (list_to_zero (dlength (stripDs dts))) bod)
              (strips args).
Proof.
  intros. unfold L2_5.term.pre_whFixStep. rewrite mkApp_hom.
  apply f_equal2; try reflexivity.
  rewrite <- dlength_hom.
  rewrite (fold_left_hom
             (fun (bod:L2_5.compile.Term) (ndx:nat) =>
                L2_5.term.instantiate (L2_5.compile.TFix dts ndx) 0 bod)
             (fun (bod:Term) (ndx:nat) =>
                instantiate (TFix (stripDs dts) ndx) 0 bod)
             (list_to_zero (dlength (stripDs dts)))).
  - apply f_equal2. reflexivity.
    rewrite (@L25dnthBody_dnthBody _ _ _ _ H _ H0). reflexivity.
  - intros. rewrite (proj1 instantiate_hom).
    apply f_equal2; try reflexivity.
Qed.

Lemma whFixStep_hom':
  forall L25bod q dts args m,
    L2_5.term.dnthBody m dts = Some (L25bod, q) ->
    whFixStep (stripDs dts) m = Some (strip L25bod) ->
    strip (L2_5.term.pre_whFixStep L25bod dts args) =
    mkApp  (strip L25bod) (strips args).
Proof.
  intros. unfold L2_5.term.pre_whFixStep. unfold whFixStep in H0.
  case_eq (dnthBody m (stripDs dts)); intros.
  - rewrite H1 in H0. myInjection H0.
    rewrite mkApp_hom. apply f_equal2; try reflexivity.
    rewrite <- H2. rewrite <- dlength_hom.
    rewrite (fold_left_hom
             (fun (bod:L2_5.compile.Term) (ndx:nat) =>
                L2_5.term.instantiate (L2_5.compile.TFix dts ndx) 0 bod)
             (fun (bod:Term) (ndx:nat) =>
                instantiate (TFix (stripDs dts) ndx) 0 bod)
             (list_to_zero (dlength (stripDs dts)))).
    + apply f_equal2. reflexivity.
      rewrite (@L25dnthBody_dnthBody _ _ _ _ H _ H1). reflexivity.
    + intros. rewrite (proj1 instantiate_hom).
      apply f_equal2; try reflexivity.
  - rewrite H1 in H0. discriminate.
Qed.
      
Lemma isLambda_invrt:
  forall fn, isLambda (strip fn) -> L2_5.term.isLambda fn.
Proof.
  intros fn h. destruct h as [x0 [x1 jx]].
  destruct fn; try (cbn in jx; discriminate).
  - auto.
  - change (mkApp (TApp (strip fn1) (strip fn2)) (strips t) =
            TLambda x0 x1) in jx.
    destruct (isApp_mkApp_TApp (strips t) (strip fn1) (strip fn2))
      as [y0 [y1 jy]].
    rewrite jx in jy. discriminate.
Qed.

Lemma isFix_invrt:
  forall fn, isFix (strip fn) -> L2_5.term.isFix fn.
Proof.
  intros fn h. destruct h as [x0 [x1 jx]].
  destruct fn; try (cbn in jx; discriminate).
  - change (mkApp (TApp (strip fn1) (strip fn2)) (strips t) =
            TFix x0 x1) in jx.
    destruct (isApp_mkApp_TApp (strips t) (strip fn1) (strip fn2))
      as [y0 [y1 jy]].
    rewrite jx in jy. discriminate.
  - auto.
Qed.

Lemma isProof_invrt:
  forall fn, TProof = (strip fn) -> L2_5.term.isProof fn.
Proof.
  intros fn h.
  destruct fn; try (cbn in h; discriminate).
  - unfold L2_5.term.isProof. reflexivity.
  - change (TProof = mkApp (TApp (strip fn1) (strip fn2)) (strips t)) in h.
    destruct (isApp_mkApp_TApp (strips t) (strip fn1) (strip fn2))
      as [x0 [x1 jx]].
    rewrite jx in h. discriminate.
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

Lemma TApp_Hom:
  forall fn arg args,
    strip (L2_5.compile.TApp fn arg args) =
    mkApp (strip fn) (tcons (strip arg) (strips args)).
  induction fn; intros arg args; try reflexivity.
Qed.

Lemma treverse_terms_ind:
 forall (P : Terms -> Prop),
       P tnil ->
       (forall (a: Term) (l:Terms),
           P (treverse l) -> P (treverse (tcons a l))) ->
       forall l:Terms, P (treverse l).
Proof.
  intros. induction l.
  - cbn. assumption.
  - eapply H0. assumption.
Qed.

Lemma treverse_ind:
  forall (P: Terms -> Prop),
    P tnil ->
    (forall (x: Term) (l: Terms), P l -> P (tappend l (tunit x))) ->
    forall l: Terms, P l.
Proof.
  intros.
  assert (j: treverse (treverse l) = l). apply treverse_involutive.
  rewrite <-j.
  apply treverse_terms_ind.
  - assumption.
  - intros. cbn. apply H0. assumption.
Qed.

(************
Lemma WcbvEval_mkApp_step_args:
  forall p args args',
      WcbvEvals p args args' ->
      forall fn s, WcbvEval p (mkApp fn args') s ->
                   WcbvEval p (mkApp fn args) s.
Proof.
  induction args; intros.
  - inversion_Clear H. assumption.
  - inversion_Clear H. cbn. eapply IHargs; try eassumption. cbn in H0.
    eapply WcbvEval_mkApp_step; try eassumption.
    destruct (wappend _ _ H) as [y0 [ y1 [jya [jyb jyc]]]]. clear H.
    subst args'. rewrite mkApp_tl in H0. inversion_Clear H0.
    + constructor. eapply IHargs; eassumption.
    + eapply wAppLam; try eassumption.
      * eapply IHargs; try eassumption.
      * unfold whBetaStep in *. eapply IHargs; try eassumption.


      Check (IHargs _ _ _ _ H2). econstructor; try eassumption.

    econstructor; try eassumption.
**************)



Lemma WcbvEval_mkApp_fn:
  forall p fn fn',
   WcbvEval p fn fn' ->
   forall args s, WcbvEval p (mkApp fn args) s ->
                  WcbvEval p (mkApp fn' args) s.
Proof.
  induction args using treverse_ind; intros.
  - cbn in *. rewrite (WcbvEval_single_valued H H0).
    eapply WcbvEval_no_further. eassumption.
  - rewrite mkApp_tl. rewrite mkApp_tl in H0.
    inversion_clear H0.
    + econstructor; try eassumption. eapply  IHargs; eassumption.
    + econstructor; try eassumption. eapply IHargs; eassumption.
    + eapply wAppFix; try eassumption. eapply IHargs; try eassumption.
Qed.
  
Lemma WcbvEval_mkApp_step:
  forall p fn s,
    WcbvEval p fn s -> 
    forall args t, WcbvEval p (mkApp s args) t ->
                   WcbvEval p (mkApp fn args) t.
Proof.
  intros p fn s h0.  
  induction args using treverse_ind; intros.
  - cbn in *.
    pose proof (proj1 (WcbvEval_no_further p) _ _ h0) as k.
    rewrite <- (WcbvEval_single_valued k H). assumption.
  - rewrite mkApp_tl. rewrite mkApp_tl in H. inversion_clear H.
    + constructor. eapply IHargs. eassumption.
    + specialize (IHargs _ H0). econstructor; eassumption.
    + specialize (IHargs _ H0). econstructor; eassumption.
Qed.

(***************
Lemma WcbvEval_step:
  forall p fn fn',
    WcbvEval p fn fn' -> 
    forall arg arg',
      WcbvEval p arg arg' ->
      forall t, WcbvEval p (TApp fn' arg') t -> WcbvEval p (TApp fn arg) t.
Proof.
  induction 1; intros.
  - inversion_Clear H0; try inversion H3.
    * constructor. constructor.
    * inversion_Clear H3. elim H6. reflexivity.
  - inversion_Clear H1; try inversion H4.
    * apply waPrf. apply waPrf. assumption.
    * inversion H4. contradiction.
  - inversion_Clear H0.
    + inversion_Clear H4.
    + inversion_Clear H3. econstructor; try econstructor; try eassumption.
      pose proof (proj1 (WcbvEval_no_further _) _ _ H) as k.
      rewrite <- (WcbvEval_single_valued H4 k). assumption.
    + inversion H3.
    + inversion_Clear H3. elim H4. auto.
  - inversion_Clear H1. 
    + inversion H5.
    + inversion H4.
    + inversion H4.
    + inversion_Clear H4. apply wAppCong; try eassumption.
      * constructor. 
        pose proof (proj2 (WcbvEval_no_further _) _ _ H) as k.
        rewrite (WcbvEvals_single_valued H10 k). assumption.
      * pose proof (proj1 (WcbvEval_no_further _) _ _ H0) as k.
        rewrite (WcbvEval_single_valued H9 k). assumption.
  - inversion_Clear H0.
    + inversion H4.
    + inversion_Clear H3.
    + inversion_Clear H3. econstructor.
      *
    
    + constructor. constructor.
    + inversion H3.
    + 
      apply (@waPrf p TProof _ (wPrf p)). 

    
  intros. inversion_Clear H1.
  - constructor.
    pose proof (proj1 (WcbvEval_no_further p) _ _ H) as k.
    rewrite <- (WcbvEval_single_valued k); assumption.
  - 


    induction args using treverse_ind; intros.
  - cbn in *.
    pose proof (proj1 (WcbvEval_no_further p) _ _ h0) as k.
    rewrite <- (WcbvEval_single_valued k H). assumption.
  - rewrite mkApp_tl. rewrite mkApp_tl in H. inversion_clear H.
    + constructor. eapply IHargs. eassumption.
    + specialize (IHargs _ H0). econstructor; eassumption.
    + specialize (IHargs _ H0). econstructor; eassumption.
    + specialize (IHargs _ H0). econstructor; eassumption.
Qed.


Lemma WcbvEval_mkApp_steps:
  forall p args fn fn',
    WcbvEval p fn fn' ->
    forall args',
      WcbvEvals p args args' ->
      forall s, WcbvEval p (mkApp fn' args') s ->
                WcbvEval p (mkApp fn args) s.
Proof.
  induction args; intros.
  - inversion_Clear H0. cbn in *.
    pose proof (proj1 (WcbvEval_no_further p) _ _ H) as k.
    erewrite (WcbvEval_single_valued H1); eassumption.
  - inversion_Clear H0. cbn. cbn in H1. eapply IHargs.


    Lemma WcbvEval_mkApp_fn_args:
  forall p args fn fn',
    WcbvEval p fn fn' ->
    forall args',
      WcbvEvals p args args' ->
      forall s, WcbvEval p (mkApp fn args) s ->
                WcbvEval p (mkApp fn' args') s.
Proof.
  induction args using treverse_ind; intros.
  - inversion_clear H0. eapply WcbvEval_mkApp_fn; eassumption.
  - destruct (wappend _ _ H0) as [y0 [ y1 [jya [jyb jyc]]]]. clear H0.
    subst args'.
    change (WcbvEval p (mkApp fn' (tappend y0 (tunit y1))) s).

    cbn. rewrite mkApp_tl. econstructor.

    rewrite mkApp_tl in H1. eapply IHargs. Check (IHargs _ _ _ _ jyb).

Lemma WcbvEval_mkApp_step_args:
  forall p args args',
      WcbvEvals p args args' ->
      forall fn s, WcbvEval p (mkApp fn args') s ->
                   WcbvEval p (mkApp fn args) s.
Proof.
  induction args; intros.
  - inversion_Clear H. assumption.
  - inversion_Clear H. cbn. eapply IHargs; try eassumption. cbn in H0.
    
    eapply WcbvEval_mkApp_fn; try eassumption.
    destruct (wappend _ _ H) as [y0 [ y1 [jya [jyb jyc]]]]. clear H.
    subst args'. rewrite mkApp_tl in H0. inversion_Clear H0.



    Lemma WcbvEval_mkApp_step_args:
  forall p args args',
      WcbvEvals p args args' ->
      forall fn s, WcbvEval p (mkApp fn args') s ->
                   WcbvEval p (mkApp fn args) s.
Proof.
  induction args using treverse_ind; intros.
  - inversion_Clear H. assumption.
  - destruct (wappend _ _ H) as [y0 [ y1 [jya [jyb jyc]]]]. clear H.
    subst args'. rewrite mkApp_tl. econstructor.




    Lemma WcbvEval_mkApp_args:
  forall p args args',
      WcbvEvals p args args' ->
      forall fn s, WcbvEval p (mkApp fn args) s ->
                   WcbvEval p (mkApp fn args') s.
Proof.
  induction args using treverse_ind; intros.
  - inversion_Clear H. assumption.
  - destruct (wappend _ _ H) as [y0 [ y1 [jya [jyb jyc]]]]. clear H.
    subst args'. rewrite mkApp_tl.


  Lemma WcbvEval_mkApp_fn_args:
  forall p args fn fn',
    WcbvEval p fn fn' ->
    forall args',
      WcbvEvals p args args' ->
      forall s, WcbvEval p (mkApp fn args) s ->
                WcbvEval p (mkApp fn' args') s.
Proof.
  induction args using treverse_ind; intros.
  - inversion_clear H0. eapply WcbvEval_mkApp_fn; eassumption.
  - destruct (wappend _ _ H0) as [y0 [ y1 [jya [jyb jyc]]]]. clear H0.
    subst args'. rewrite mkApp_tl.

    rewrite mkApp_tl in H1. eapply IHargs. Check (IHargs _ _ _ _ jyb).

    

    eapply WcbvEval_mkApp_step.
    rewrite mkApp_tl in H1.


    eapply IHargs; try eassumption.


    inversion_Clear H1.
    Check (IHargs _ _ _ us ju). try eassumption.
    
    destruct (tappend_mk_canonical args x tnil) as [x0 [x1 jx]].
    rewrite jx in H0. rewrite jx in H1.
    inversion_Clear H0. cbn. eapply IHargs; try eassumption. cbn in *. destruct fn'.
    + inversion H.



    eapply IHargs; try eassumption.

    eapply IHargs; try eassumption.
    inversion_Clear H0. cbn in *.
    eapply IHargs; try eassumption.


  
  induction args using treverse_ind; intros.
  - inversion_clear H0. eapply WcbvEval_mkApp_fn; eassumption.
  - destruct (tappend_mk_canonical args x tnil) as [x0 [x1 jx]].
    rewrite jx in H0. rewrite jx in H1. inversion_Clear H0.
    eapply IHargs; try eassumption.


    cbn. eapply WcbvEval_mkApp_step. eapply WcbvEval_mkApp_fn.

    eapply IHargs; try eassumption.


  - inversion_Clear H0.
    + destruct (tappend_mk_canonical args x tnil) as [x0 [x1 jx]].
      rewrite jx in H3. discriminate.
    + specialize (IHargs _ _ H).

      rewrite <- H2 in H1.  (* cbn in H1. cbn. *)
      eapply IHargs; try eassumption.
      
    
                rewrite (WcbvEval_single_valued H H0).
    eapply WcbvEval_no_further. eassumption.
  - rewrite mkApp_tl. rewrite mkApp_tl in H0.
    inversion_clear H0. econstructor; try eassumption.
    + eapply IHargs; eassumption.
    + econstructor; try eassumption. eapply IHargs; eassumption.
    + eapply wAppFix; try eassumption. eapply IHargs; try eassumption.
    + eapply wAppCong; try eassumption. eapply IHargs; try eassumption.
Qed.
***************************)

Lemma waPrf_args:
  forall p args fn,
    WcbvEval p fn TProof -> WcbvEval p (mkApp fn args) TProof.
Proof.
  induction args; intros.
  - cbn. assumption.
  - cbn. eapply WcbvEval_mkApp_step.
    + apply waPrf. assumption.
    + eapply IHargs. constructor.
Qed.

(**********
Lemma wAppCong':
  forall p args args' fn fn',
    WcbvEvals p args args' ->
    WcbvEval p fn fn' ->
    ~ isLambda fn' -> ~ isFix fn' -> TProof <> fn' ->
    WcbvEval p (mkApp fn args) (mkApp fn' args').
Proof.
  induction args; intros.
  - inversion_Clear H. cbn. assumption.
  - inversion_Clear H. cbn. apply IHargs; try assumption.
    + apply wAppCong; try assumption.
    + intros h. destruct h as [x0 [x1 jx]]. discriminate.
    + intros h. destruct h as [x0 [x1 jx]]. discriminate.
    + intros h. discriminate.
Qed.
******************)

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
  - simpl. eapply WcbvEval_mkApp_step.
    + constructor. assumption.
    + eapply WcbvEval_mkApp_step.
      * econstructor.
      * apply waPrf_args. constructor.
  - cbn. econstructor; try eassumption. apply LookupDfn_hom.
    unfold LookupDfn. unfold lookupDfn in e. case_eq (lookup nm p); intros.
    + rewrite H0 in e. destruct e0.
      * myInjection e. apply lookup_Lookup. assumption.
      * discriminate.
    + rewrite H0 in e. discriminate.
  - (* beta step in L2_5 *)
    rewrite whBetaStep_hom in H1.
    destruct (WcbvEval_mkApp_WcbvEval _ _ H1) as [y jy].
    rewrite TApp_Hom. cbn. eapply WcbvEval_mkApp_step.
    + eapply wAppLam; eassumption.
    + eapply WcbvEval_mkApp_fn; eassumption. 
  - cbn. econstructor; try eassumption. rewrite <- (proj1 instantiate_hom).
    apply H0.
  - (* Fix in L2_5 *)
    rewrite <- pre_whFixStep_hom in H0.
    change (WcbvEval (stripEnv p) (strip fn) (TFix (stripDs dts) m)) in H.
    destruct (WcbvEval_mkApp_WcbvEval _ _ H0) as [y jy].
    assert (j: dnthBody m (stripDs dts) = Some (strip x)).
    { rewrite dnthBody_hom. rewrite e. cbn. reflexivity. }
    rewrite TApp_Hom. cbn. eapply WcbvEval_mkApp_step.
    + eapply wAppFix; eassumption. 
    + eapply WcbvEval_mkApp_fn; eassumption.
  - rewrite TCase_hom. rewrite TConstruct_hom in H. 
    eapply wCase; try eassumption.
    rewrite <- whCaseStep_hom. rewrite e. reflexivity.
Qed.
Print Assumptions WcbvEval_hom.
