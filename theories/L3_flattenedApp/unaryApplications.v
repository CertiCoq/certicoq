
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
Lemma optStripDnth_hom:
  forall y n, optStripDnth (Some (y, n)) = Some (strip y, n).
induction y; simpl; reflexivity.
Qed.
Lemma optStripCanP_hom:
  forall y n, optStripCanP (Some (n, y)) = Some (n, strips y).
induction y; simpl; reflexivity.
Qed.


Lemma tlength_hom:
  forall ts, tlength (strips ts) = L2_5.term.tlength ts.
Proof.
  induction ts.
  - reflexivity.
  - cbn. rewrite IHts. reflexivity.
Qed.

(***********
Lemma mkApp_hom:
  forall ts t,
    isL2_5Cnstr t = None -> ~ L2_5.term.isApp t ->
    strip (L2_5.compile.mkApp t ts) = mkApp (strip t) (strips ts).
Proof.
  induction ts; intros; cbn.
  - rewrite L2_5.term.mkApp_tnil_ident. reflexivity.
  - rewrite L2_5.term.mkApp_goodFn.
    cbn. rewrite H. reflexivity. assumption.
Qed.
***************)

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

(********
Lemma mkApp_hom:
  forall fn t ts u us,
    isL2_5Cnstr fn = None ->
    mkApp (strip (L2_5.compile.TApp fn u us)) (strip t) (strips ts) =
    strip (L2_5.term.mkApp (L2_5.compile.TApp fn u us) (L2_5.compile.tcons t ts)).
Proof.
  cbn; intros. rewrite H. destruct fn. cbn. unfold mkApp. rewrite mkApp_idempotent.

  destruct fn; intros; cbn; try reflexivity.
  -
    +  unfold etaExp_cnstr. destruct p. destruct p. cbn.
    + cbn in H. rewrite H0 in H. elim H. unfold etaExp_cnstr.


         destruct p as [[x0 x1] x2]. unfold etaExp_cnstr. cbn.
 *****)


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

(******************************
Lemma instantiate_hom:
  (forall bod, L2_5.term.WFapp bod -> forall arg n, WFTrm (strip arg) 0 ->
     strip (L2_5.term.instantiate arg n bod) =
     instantiate (strip arg) n (strip bod)) /\
  (forall bods, L2_5.term.WFapps bods -> forall arg n, WFTrm (strip arg) 0 -> 
     strips (L2_5.term.instantiates arg n bods) =
     instantiates (strip arg) n (strips bods)) /\
  (forall ds, L2_5.term.WFappDs ds -> forall arg n, WFTrm (strip arg) 0 ->
          stripDs (L2_5.term.instantiateDefs arg n ds) =
     instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L2_5.term.WFappTrmsDefs_ind; intros; try (cbn; reflexivity);
  try (cbn; rewrite H0; try reflexivity; assumption).
  - cbn. destruct (lt_eq_lt_dec m n); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n m)); try omega. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
    + rewrite (proj1 (nat_compare_lt n m)); trivial.
  - cbn. rewrite H0; try assumption. apply f_equal.
    rewrite H2. reflexivity. assumption.
  - rewrite TApp_hom. destruct (isL2_5Cnstr fn).
    + destruct p. destruct p.
      
    rewrite L2_5.term.instantiate_TApp_commute. Check mkApp_hom.
    rewrite TApp_hom. 
    
HERE


    
  - cbn. erewrite <- instantiate_etaExp; try eassumption. reflexivity.
  - rewrite TCase_hom. rewrite instantiate_TCase.
    change
     (TCase m (strip (L2_5.term.instantiate arg n mch))
            (stripDs (L2_5.term.instantiateDefs arg n brs)) =
      TCase m (instantiate (strip arg) n (strip mch))
            (instantiateDefs (strip arg) n (stripDs brs))).
    apply f_equal2.
    + rewrite H0; try reflexivity; try assumption.
    + rewrite H2; try reflexivity; try assumption.
  - change
      (TFix
         (stripDs (L2_5.term.instantiateDefs
                     arg (n + (L2_5.compile.dlength defs)) defs)) m =
       TFix (instantiateDefs
               (strip arg) (n + (dlength (stripDs defs))) (stripDs defs)) m).
    apply f_equal2; try reflexivity.
    rewrite H0; try assumption.
    apply f_equal2; try reflexivity. rewrite stripDs_pres_dlength.
    reflexivity. 
  - rewrite L2_5.stripEvalCommute.instantiates_tcons_commute.
    rewrite tcons_hom. rewrite H0; try assumption.
    rewrite tcons_hom. rewrite instantiates_tcons.
    rewrite H2. reflexivity. assumption.
  - rewrite L2_5.stripEvalCommute.instantiates_dcons_commute.
    rewrite dcons_hom. rewrite H0; try assumption.
    rewrite dcons_hom. rewrite instantiates_dcons.
    rewrite H2. reflexivity. assumption.

    
Admitted.
 **************)


(*********************
Lemma instantiate_hom:
  (forall bod arg n, WFTrm (strip arg) 0 ->
     L2_5.term.WFapp bod ->
     strip (L2_5.term.instantiate arg n bod) =
     instantiate (strip arg) n (strip bod)) /\
  (forall bods arg n, WFTrm (strip arg) 0 ->
     L2_5.term.WFapps bods ->
     strips (L2_5.term.instantiates arg n bods) =
     instantiates (strip arg) n (strips bods)) /\
  (forall ds arg n, WFTrm (strip arg) 0 ->
     L2_5.term.WFappDs ds ->
     stripDs (L2_5.term.instantiateDefs arg n ds) =
     instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L2_5.compile.TrmTrmsDefs_ind; intros; try (simpl; reflexivity).
  - simpl. destruct (lt_eq_lt_dec n n0); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n0 n)); try omega. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
        rewrite L2_5.compile.mkApp_tnil_ident. reflexivity.
    + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
  - inversion_Clear H1.
    change (strip (L2_5.term.instantiate arg n t) =
            (instantiate (strip arg) n (strip t))).
    rewrite H; try reflexivity; assumption.
  - inversion_Clear H1.
    change (TProd n (strip (L2_5.term.instantiate arg (S n0) t)) =
            (TProd n (instantiate (strip arg) (S n0) (strip t)))).
    rewrite H; try reflexivity; assumption.
  - inversion_Clear H1.
    change (TLambda n (strip (L2_5.term.instantiate arg (S n0) t)) =
            (TLambda n (instantiate (strip arg) (S n0) (strip t)))).
    rewrite H; try reflexivity; assumption.
  - inversion_Clear H2.
    change (TLetIn n (strip (L2_5.term.instantiate arg n0 t))
                   (strip (L2_5.term.instantiate arg (S n0) t0)) =
            (TLetIn n (instantiate (strip arg) n0 (strip t))
                    (instantiate (strip arg) (S n0) (strip t0)))).
    rewrite H, H0; try reflexivity; try assumption.
    (*********************)
  - inversion_Clear H3. rewrite TApp_hom. rewrite instantiate_TApp_mkApp.
    case_eq (isL2_5Cnstr t).
    + intros p h. destruct p as [[p0 p1] p2]. rewrite tlength_hom.
      destruct (etaExp_cnstr_Lam_or_Cnstr'
                  p0 p1 (p2 - S (L2_5.term.tlength t1))
                  (tcons (strip t0) (strips t1))).
      * {destruct H3 as [ytra [k1 k2]]. rewrite k2.
         rewrite instantiate_TLambda.
         rewrite L2_5.stripEvalCommute.instantiates_tcons_commute.
         rewrite L2_5.compile.mkApp_goodFn.
         rewrite TApp_hom.
         destruct (isL2_5Cnstr_spec _ h).
         - rewrite H3. unfold L2_5.term.instantiate at 1.
           unfold isL2_5Cnstr. unfold L2_5.term.isL2_5Cnstr.
           rewrite H0, H1; try assumption.
           rewrite instantiates_pres_tlength. rewrite tlength_hom.
            destruct
             (etaExp_cnstr_Lam_or_Cnstr'
                p0 p1
                (p2 - S (L2_5.term.tlength t1))
                (tcons (instantiate (strip arg) n (strip t0))
                       (instantiates (strip arg) n (strips t1)))).
            + destruct H4 as [ztra [j1 j2]].
              rewrite j2. apply f_equal.
              assert (tra: ytra = ztra). omega. rewrite tra.
              rewrite instantiate_mkEtaLams.
              rewrite <- instantiates_mkEtaArgs; try assumption.
              rewrite instantiates_tcons. unfold instantiate at 2.
              rewrite (proj2 (Nat.compare_gt_iff _ _)); try omega.
              rewrite <- instantiates_tcons.
              rewrite <- instantiates_pres_treverse.
              rewrite (proj1 (proj2 (instantiate_lift _)));
                try omega; try assumption.
              reflexivity.
            + destruct H4 as [ztra [j1 j2]]. rewrite j1 in k1. discriminate.
         - destruct H3 as [u [j1 j2]]. subst. cbn in h. cbn.
           rewrite tlength_hom. rewrite L2_5.term.instantiates_pres_tlength. 

              
         rewrite L2_5.stripEvalCommute.instantiates_tcons_commute.
          rewrite mkApp_hom.
          rewrite tcons_hom. rewrite H, H0, H1.
          erewrite (isL2_5Cnstr_Some t h).
          rewrite (etaExp_cnstr_tnil).
          rewrite instantiate_mkEtaLams. rewrite instantiate_TLambda.       
              rewrite TApp_hom.
          rewrite mkApp_hom.
          rewrite H.
          rewrite L2_5.stripEvalCommute.instantiates_tcons_commute.
          rewrite tcons_hom. rewrite H0, H1.
          rewrite TApp_hom. rewrite h. rewrite H3. unfold strip at 2.
          unfold etaExp_cnstr.
          rewrite instantiate_TApp_mkApp.
                destruct (L2_5.term.isL2_5Cnstr_spec _ h).
      rewrite mkApp_goodFn.
      - rewrite TApp_hom. rewrite <- H3. rewrite h. unfold etaExp_cnstr.
      rewrite H0, H1; try assumption.
      cbn. rewrite h. rewrite <- instantiates_tcons.
      unfold etaExp_cnstr. rewrite instantiates_pres_tlength.
      destruct (tlength (tcons (strip t0) (strips t1)) ?= p2).
      * reflexivity.
      * rewrite instantiate_mkEtaLams. rewrite instantiate_TConstruct.
        rewrite <- tcons_hom. rewrite strips_pres_tlength.
        set (q:= L2_5.term.tlength (L2_5.compile.tcons t0 t1)).
        eapply f_equal. eapply f_equal.
        rewrite <- instantiates_pres_treverse.
        rewrite instantiates_mkEtaArgs. reflexivity.
        assumption.
      * rewrite instantiate_TConstruct. apply f_equal.
        rewrite instantiates_ttake. reflexivity.
      * intros j. destruct j as [x0 [x1 [x2 k]]]. discriminate.
(************  ????
    + intros h. rewrite TApp_hom. rewrite h.
      case_eq (L2_5.term.isApp_dec t); intros.
      destruct i as [x0 [x1 [x2 j]]].
      * admit.
      * rewrite L2_5.term.instantiate_TApp_mkApp.
      unfold L2_5.term.instantiate. rewrite j.
******************)      
    + intros h. rewrite (TApp_mkApp_hom _ _ _ h).
      rewrite instantiate_mkApp_commute.
      rewrite <- H; try assumption.
      rewrite instantiates_tcons.
      rewrite <- H0; try assumption. rewrite <- H1; try assumption.
      rewrite L2_5.term.instantiate_TApp_mkApp.
      apply mkApp_instantiate_hom; try assumption.
      admit. admit.
  - cbn. apply instantiate_etaExp. assumption.
  - inversion_Clear H2.
    rewrite TCase_hom. rewrite instantiate_TCase.
    change
     (TCase p (strip (L2_5.term.instantiate arg n t))
            (strips(L2_5.term.instantiates arg n t0)) =
      TCase p (instantiate (strip arg) n (strip t))
            (instantiates (strip arg) n (strips t0))).
    apply f_equal2.
    + rewrite H; try reflexivity; try assumption.
    + rewrite H0; try reflexivity; try assumption.
  - inversion_Clear H1.
    change
      (TFix
         (stripDs (L2_5.term.instantiateDefs
                     arg (n0 + (L2_5.term.dlength d)) d)) n =
       TFix (instantiateDefs
               (strip arg) (n0 + (dlength (stripDs d))) (stripDs d)) n).
    rewrite H; try assumption.
    apply f_equal2; try reflexivity. rewrite stripDs_pres_dlength.
    reflexivity.
  - inversion_Clear H2. rewrite tcons_hom. rewrite instantiates_tcons.
    rewrite L2_5.stripEvalCommute.instantiates_tcons_commute.
    rewrite tcons_hom.
    rewrite H; try assumption. rewrite H0; try assumption. reflexivity.
  - inversion_Clear H2. rewrite dcons_hom. rewrite instantiates_dcons.
    rewrite L2_5.stripEvalCommute.instantiates_dcons_commute.
    rewrite dcons_hom.
    rewrite H; try assumption. rewrite H0; try assumption. reflexivity.
Admitted.
*************************)

Lemma tnth_hom:
 forall ts n, optStrip (L2_5.term.tnth n ts) = tnth n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed. 

Lemma tskipn_hom:
  forall ts n, optStrips (L2_5.term.tskipn n ts) = tskipn n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.

    
Lemma whCaseStep_hom:
  forall n brs ts,
    optStrip (L2_5.term.whCaseStep n ts brs) =
    whCaseStep n (strips ts) (stripBs brs).
(*****
Proof.
  destruct n, brs; intros; simpl; try reflexivity.
  - unfold whCaseStep. cbn. apply f_equal. rewrite mkApp_hom.
    reflexivity.
    
    admit. (* rewrite mkApp_hom. reflexivity. *)
  - unfold whCaseStep. unfold L2_5.term.whCaseStep. simpl. 
    rewrite <- tnth_hom. destruct (L2_5.term.tnth n brs); simpl.
    + admit. (* rewrite mkApp_hom. reflexivity. *)
    + reflexivity.
****)
Admitted.

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
Admitted.
(*******
Proof.
  induction args; cbn; intros.
  - unfold L2_5.term.whBetaStep, whBetaStep.
    rewrite L2_5.compile.mkApp_tnil_ident. apply (proj1 instantiate_hom).
  - unfold L2_5.term.whBetaStep, whBetaStep.
    unfold L2_5.term.whBetaStep, whBetaStep in IHargs.
    rewrite <- (proj1 instantiate_hom) in IHargs.
    

 rewrite <- (proj1 instantiate_hom). 
   unfold mkApp.
    destruct (L2_5.term.instantiate arg 0 bod); cbn.
******)

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

  
(******
Lemma WcbvEval_hom:
  forall p,
    (forall t t', L2_5.wcbvEval.WcbvEval p t t' -> L2_5.term.WFTrm t 0 ->
              (**    L2_5.program.Crct p 0 t ->  **)
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L2_5.wcbvEval.WcbvEvals p ts ts' -> L2_5.term.WFTrms ts 0 ->
              (**      L2_5.program.Crcts p 0 ts ->  **)
                    WcbvEvals (stripEnv p) (strips ts) (strips ts')).
Proof.
  intros p.
  apply L2_5.wcbvEval.WcbvEvalEvals_ind; intros; try reflexivity;
  try (solve[constructor; trivial]); try assumption.
  - cbn. inversion_Clear H0; intuition.
  - cbn. rewrite etaExp_cnstr_tnil. induction arty.
    + cbn. constructor. constructor.
    + cbn. constructor.
  - eapply wConst; try eassumption.
    + unfold LookupDfn in *.
      assert (j:= Lookup_hom l). cbn in j. eassumption.
    +  apply H. Check (L2_5.wcbvEval.WcbvEval_pres_WFTrm). intuition.
   (**    apply H. inversion H0. intuition. subst. inversion_Clear H0.**)
  - (* beta step in L2_5 *)
    rewrite TApp_hom. cbn in H.
    case_eq (isL2_5Cnstr fn); intros.
    + (* fn is a Constructor or Cast: L2_5 beta is impossible *)
      destruct p0, p0.
      discriminate (isL2_5Cnstr_WcbvEval_TCnstr H3 w).
    + (* L2_5 beta step *)
      cbn. induction args.
      * { eapply wAppLam; try eassumption.
          - apply H. constructor.
        rewrite whBetaStep_tnil_hom in H1. assumption.

      rewrite TApp_hom. cbn in H.
      assert (k: isL2_5Cnstr fn = None).
      { unfold isL2_5Cnstr. destruct fn; try reflexivity.
        - elim H2. auto. }
      rewrite TApp_hom. rewrite k. cbn. cbn in H.
      induction args.
      * cbn. refine (wAppLam _ _ _); try eassumption.
        cbn in H1. Check whBetaStep_hom. rewrite <- whBetaStep_hom.


      
      rewrite (TApp_hom fn a1 args). rewrite j.
      rewrite whBetaStep_hom in H1. cbn.
      Check whBetaStep_hom.
      Check (wAppLam H H0).
      assert (k:= (L2_5.compile.TLambda nm bod)).
cbn.
      
      cbn in *. rewrite j. destruct fn; inversion_Clear H; cbn.
      * rewrite <- H4.
        
      destruct bod; cbn; rewrite j; destruct fn; cbn.
      eapply wAppLam.
      rewrite TApp_hom. unfold etaExp_cnstr. destruct fn. rewrite tunit_treverse. cbn.
      
    + destruct p0. destruct p0. unfold etaExp_cnstr.
      destruct (n - tlength (tcons (strip a1) (strips args))).
      * cbn. rewrite tappend_tnil.
      change (WcbvEval (stripEnv p) (TLam).
  - eapply wLetIn; try eassumption.
    rewrite <- (proj1 (instantiate_hom)). assumption.
  - admit.
  - admit.
  - eapply wCase; try eassumption. rewrite whCaseStep_hom in e1.
*************)

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
