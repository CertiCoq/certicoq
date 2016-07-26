(******)
Add LoadPath "../common" as Common.
Add LoadPath "../L1_5_box" as L1_5.
Add LoadPath "../L2_typeStripped" as L2.
(******)

Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import L1_5.L1_5.
Require Import L2.term.
Require Import L2.program.
Require Import L2.wndEval.
Require Import L2.wcbvEval.
Require Import L2.wNorm.
Require Import L2.compile.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1_5Term := L1_5.compile.Term.
Definition L1_5Terms := L1_5.compile.Terms.
Definition L1_5Defs := L1_5.compile.Defs.
Definition ecTrm := AstCommon.ecTrm.
Definition ecTyp := AstCommon.ecTyp Term.
Definition ecAx := AstCommon.ecAx Term.

Definition optStrip (t:option L1_5Term) : option Term :=
  match t with
    | None => None
    | Some t => Some (strip t)
  end.
Definition optStrips (ts:option L1_5Terms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (strips ts)
  end.
Definition optStripDnth (b: option (L1_5Term * nat)) : option (Term * nat) :=
                           match b with
                             | None => None
                             | Some (t, n) => Some (strip t, n)
                           end.
Definition optStripCanP (b: option (nat * L1_5Terms)) : option (nat * Terms) :=
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
                              

Lemma stripEnv_hom:
  forall str (ec:L1_5.compile.envClass) p,
    stripEnv ((str, ec) :: p) = (str, (stripEC ec))::(stripEnv p).
induction p; destruct ec; try reflexivity.
Qed.

Lemma Lookup_hom:
 forall p s ec, L1_5.program.Lookup s p ec -> 
               Lookup s (stripEnv p) (stripEC ec).
induction 1; destruct t.
- change (Lookup s ((s, ecTrm (strip l)) :: (stripEnv p))
                    (ecTrm (strip l))).
  apply LHit.
- change (Lookup s ((s, ecTyp n i) :: (stripEnv p)) (ecTyp n i)).
  apply LHit.
- change (Lookup s2 ((s1, ecTrm (strip l)) :: (stripEnv p))
                     (stripEC ec)).
  apply LMiss; assumption.
- change (Lookup s2 ((s1, ecTyp n i) :: (stripEnv p)) (stripEC ec)).
  apply LMiss; assumption.
Qed.

Lemma LookupDfn_hom:
 forall p s t, L1_5.program.LookupDfn s p t -> 
               LookupDfn s (stripEnv p) (strip t).
unfold L1_5.program.LookupDfn, L2.program.LookupDfn. intros.
assert (j:= Lookup_hom H). exact j.
Qed.

Lemma dlength_hom:
  forall ds, L1_5.compile.dlength ds = dlength (stripDs ds).
induction ds. intuition. simpl. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, strips (L1_5.compile.tcons t ts) = tcons (strip t) (strips ts).
reflexivity.
Qed.

Lemma tnil_hom: strips L1_5.compile.tnil = tnil.
reflexivity.
Qed.

Lemma dcons_hom:
  forall nm ty bod rarg ds,
    stripDs (L1_5.compile.dcons nm ty bod rarg ds) =
    dcons nm (strip bod) rarg (stripDs ds).
reflexivity.
Qed.

Lemma dnil_hom: stripDs L1_5.compile.dnil = dnil.
reflexivity.
Qed.

Lemma dnthBody_hom: 
  forall m ds, optStripDnth (L1_5.term.dnthBody m ds) =
               dnthBody m (stripDs ds).
induction m; induction ds; try intuition.
- simpl. intuition.
Qed.

Lemma canonicalP_hom:
  forall t, optStripCanP (L1_5.term.canonicalP t) = canonicalP (strip t).
Proof.
  destruct t; cbn; try reflexivity.
  destruct t1; cbn; try reflexivity.
Qed.
  
Lemma tnth_hom:
 forall ts n, optStrip (L1_5.term.tnth n ts) = tnth n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed. 

Lemma tskipn_hom:
  forall ts n, optStrips (L1_5.term.tskipn n ts) = tskipn n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.

Lemma tappend_hom:
  forall ts us,
    strips (L1_5.compile.tappend ts us) = tappend (strips ts) (strips us).
induction ts; intros us; simpl. reflexivity.
rewrite IHts. reflexivity.
Qed.

Lemma TApp_hom:
  forall fn arg args,
    strip (L1_5.compile.TApp fn arg args) =
    TApp (strip fn) (strip arg) (strips args).
induction fn; intros arg args; try reflexivity.
Qed.

Lemma isApp_hom:
  forall t, isApp (strip t) -> L1_5.term.isApp t.
destruct t; simpl; intros h; destruct h as [x0 [x1 [x2 h]]]; try discriminate. 
- exists t1, t2, t3. reflexivity.
Qed.

Lemma isLambda_hom:
  forall t, isLambda (strip t) -> L1_5.term.isLambda t.
destruct t; simpl; intros h; destruct h as [x0 [x1 h]]; try discriminate. 
- exists n, t1, t2. reflexivity.
Qed.

Lemma isFix_hom:
  forall t, isFix (strip t) -> L1_5.term.isFix t.
destruct t; simpl; intros h; destruct h as [x0 [x1 h]]; try discriminate. 
- exists d, n. reflexivity.
Qed.

Lemma L1WFapp_L2WFapp:
  (forall t, L1_5.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L1_5.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ds, L1_5.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
  apply L1_5.term.WFappTrmsDefs_ind; simpl; constructor; auto.
  - intros h. elim H. apply isApp_hom. assumption.
Qed.

Lemma L1WFaEnv_L2WFaEnv:
  forall p:L1_5.compile.environ, L1_5.program.WFaEnv p -> WFaEnv (stripEnv p).
Proof.
  induction 1; simpl; constructor.
  - inversion H; destruct ec; simpl; try discriminate; constructor.
    + apply (proj1 (L1WFapp_L2WFapp)). assumption.
  - assumption.
Qed.


Lemma WFapp_hom:
  (forall t, L1_5.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L1_5.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ds, L1_5.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
   apply L1_5.term.WFappTrmsDefs_ind; cbn; intros;
  try (solve [constructor]);
  try (solve [constructor; intuition]).
  - constructor; try assumption.
    + intros h. assert (j:= isApp_hom _ h). contradiction.
Qed.

Lemma mkApp_tcons_lem1:
  forall fn arg args,
    mkApp (mkApp fn (tcons arg args)) tnil = mkApp fn (tcons arg args).
Proof.
  destruct fn; intros arg args; simpl;
  try rewrite tappend_tnil; try reflexivity.
Qed.

Lemma mkApp_tcons_lem2:
 forall fn ts u s args,
   mkApp fn (tcons u (tappend ts (tcons s args))) =
   mkApp (mkApp fn (tcons u ts)) (tcons s args).
Proof.
  destruct fn; destruct ts; intros; try reflexivity.
  - rewrite mkApp_idempotent. simpl. reflexivity.
  - rewrite mkApp_idempotent. simpl. reflexivity.
Qed.

Lemma mkApp_hom:
forall fn args,
  strip (L1_5.compile.mkApp fn args) = mkApp (strip fn) (strips args).
Proof.
  induction fn; induction args; simpl; try reflexivity.
  - rewrite tappend_tnil. rewrite L1_5.term.tappend_tnil. reflexivity.
  - rewrite <- tcons_hom. rewrite <- tappend_hom. reflexivity.
Qed.

Lemma TCast_hom:
  forall tm ck ty, strip (L1_5.compile.TCast tm ck ty) = TCast (strip tm).
reflexivity.
Qed.

Lemma instantiate_tappend_commute:
  forall ts us tin n,
    instantiates tin n (tappend ts us) =
    tappend (instantiates tin n ts) (instantiates tin n us).
induction ts; intros.
- reflexivity.
- change (tcons (instantiate tin n t) (instantiates tin n (tappend ts us)) =
          tcons (instantiate tin n t) (tappend (instantiates tin n ts)
                                               (instantiates tin n us))).
 rewrite IHts. reflexivity.
Qed.

Lemma instantiates_tcons_commute:
  forall tin n t ts,
         (instantiates tin n (tcons t ts)) = 
         (tcons (instantiate tin n t) (instantiates tin n ts)).
intros tin n t ts. reflexivity.
Qed.

Lemma instantiate_mkApp_commute:
forall tin n bod arg args,
  instantiate tin n (mkApp bod (tcons arg args)) =
  mkApp (instantiate tin n bod) (tcons (instantiate tin n arg)
                                       (instantiates tin n args)).
induction bod; simpl; intros; try reflexivity.
- change
    (mkApp (instantiate tin n bod1) 
           (tcons (instantiate tin n bod2)
                     (instantiates tin n (tappend t (tcons arg args)))) =
     mkApp (mkApp (instantiate tin n bod1)
                  (tcons (instantiate tin n bod2)
                         (instantiates tin n t)))
           (tcons (instantiate tin n arg) (instantiates tin n args))).
  rewrite mkApp_idempotent. simpl. 
  rewrite instantiate_tappend_commute. rewrite instantiates_tcons_commute.
  reflexivity.
Qed.

Lemma instantiate_mkApp_nil_commute:
forall tin n bod,
  instantiate tin n (mkApp bod tnil) = mkApp (instantiate tin n bod) tnil.
induction bod; simpl; intros; try reflexivity.
- destruct (lt_eq_lt_dec n n0) as [[h1 | h2 ] | h3].
  + unfold instantiate. rewrite (proj1 (nat_compare_lt _ _) h1). 
    simpl. reflexivity.
  + subst. unfold instantiate. rewrite (proj2 (nat_compare_eq_iff n0 n0)).
    * rewrite mkApp_idempotent. simpl. reflexivity.
    * reflexivity.
  + unfold instantiate. rewrite (proj1 (nat_compare_gt _ _) h3).
    simpl. reflexivity.
- rewrite tappend_tnil.
  change (instantiate tin n (TApp bod1 bod2 t) =
         mkApp (mkApp (instantiate tin n bod1)
                      (tcons (instantiate tin n bod2)
                             (instantiates tin n t)))
                      tnil).
  rewrite mkApp_idempotent. simpl. rewrite tappend_tnil. reflexivity. 
Qed.

Lemma instantiate_hom:
    (forall bod arg n, strip (L1_5.term.instantiate arg n bod) =
                   instantiate (strip arg) n (strip bod)) /\
    (forall bods arg n, strips (L1_5.term.instantiates arg n bods) =
                    instantiates (strip arg) n (strips bods)) /\
    (forall ds arg n, stripDs (L1_5.term.instantiateDefs arg n ds) =
                    instantiateDefs (strip arg) n (stripDs ds)).
apply L1_5.compile.TrmTrmsDefs_ind; intros; try (simpl; reflexivity).
- simpl. destruct (lt_eq_lt_dec n n0); cbn.
  + destruct s.
    * rewrite (proj1 (nat_compare_gt n0 n)); try omega. cbn. reflexivity.
    * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
      rewrite mkApp_tnil_ident. reflexivity.
  + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
- change (TCast (strip (L1_5.term.instantiate arg n t)) =
         (TCast (instantiate (strip arg) n (strip t)))).
  rewrite H. reflexivity.
- change (TProd n (strip (L1_5.term.instantiate arg (S n0) t0)) =
         (TProd n (instantiate (strip arg) (S n0) (strip t0)))).
  rewrite H0. reflexivity.
- change (TLambda n (strip (L1_5.term.instantiate arg (S n0) t0)) =
         (TLambda n (instantiate (strip arg) (S n0) (strip t0)))).
  rewrite H0. reflexivity.
- change (TLetIn n (strip (L1_5.term.instantiate arg n0 t))
                   (strip (L1_5.term.instantiate arg (S n0) t1)) =
         (TLetIn n (instantiate (strip arg) n0 (strip t))
                   (instantiate (strip arg) (S n0) (strip t1)))).
  rewrite H. rewrite H1. reflexivity.
- change (strip (L1_5.compile.mkApp
                   (L1_5.term.instantiate arg n t)
                   (L1_5.compile.tcons (L1_5.term.instantiate arg n t0)
                                       (L1_5.term.instantiates arg n t1))) =
          instantiate (strip arg) n (strip (L1_5.compile.TApp t t0 t1))). 
  rewrite TApp_hom. 
  change
    (strip (L1_5.compile.mkApp (L1_5.term.instantiate arg n t)
                          (L1_5.compile.tcons (L1_5.term.instantiate arg n t0)
                                         (L1_5.term.instantiates arg n t1))) =
     (mkApp (instantiate (strip arg) n (strip t))
            (tcons (instantiate (strip arg) n (strip t0))
                   (instantiates (strip arg) n (strips t1))))).
  rewrite <- H. rewrite <- H0. rewrite <- H1. 
  rewrite mkApp_hom. rewrite tcons_hom. reflexivity.
- change (TCase p (strip (L1_5.term.instantiate arg n t0))
                (strips (L1_5.term.instantiates arg n t1)) =
         (TCase p (instantiate (strip arg) n (strip t0))
                (instantiates (strip arg) n (strips t1)))).
  rewrite H0. rewrite H1. reflexivity.
- change (TFix (stripDs (L1_5.term.instantiateDefs
                           arg (n0 + L1_5.compile.dlength d) d)) n =
         (TFix (instantiateDefs (strip arg)
                                (n0 + dlength (stripDs d)) (stripDs d)) n)).
  rewrite H. rewrite dlength_hom. reflexivity.
- change (tcons (strip (L1_5.term.instantiate arg n t))
                (strips (L1_5.term.instantiates arg n t0)) =
          tcons (instantiate (strip arg) n (strip t))
                (instantiates (strip arg) n (strips t0))).
  rewrite H. rewrite H0. reflexivity.
- change (dcons n (strip (L1_5.term.instantiate arg n1 t0)) n0
                  (stripDs (L1_5.term.instantiateDefs arg n1 d)) =
          dcons n (instantiate (strip arg) n1 (strip t0)) n0
                (instantiateDefs (strip arg) n1 (stripDs d))).
  rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma whBetaStep_hom:
  forall bod arg args,
    strip (L1_5.term.whBetaStep bod arg args) =
    whBetaStep (strip bod) (strip arg) (strips args).
intros bod arg args.
unfold L1_5.term.whBetaStep, whBetaStep.
rewrite mkApp_hom. rewrite <- (proj1 instantiate_hom). reflexivity.
Qed.

Lemma TConstruct_hom:
  forall i n , strip (L1_5.compile.TConstruct i n) = TConstruct i n.
intros. simpl.  destruct i. reflexivity.
Qed.


Lemma optStrip_match:
  forall x (f:L1_5Term -> L1_5Term) (g:Term -> Term), 
    (forall z, strip (f z) = g (strip z)) ->
    optStrip (match x with Some y => Some (f y) | None => None end) =
    match (optStrip x) with Some y => Some (g y) | None => None end.
induction x; intros f g h; simpl.
- rewrite h; reflexivity.
- reflexivity.
Qed.

Lemma whCaseStep_hom:
  forall n brs ts,
    optStrip (L1_5.term.whCaseStep n ts brs) =
    whCaseStep n (strips ts) (strips brs).
destruct n, brs; intros; simpl; try reflexivity.
- unfold whCaseStep. simpl. rewrite mkApp_hom. reflexivity.
- unfold whCaseStep. unfold L1_5.term.whCaseStep. simpl. 
  rewrite <- tnth_hom. destruct (L1_5.term.tnth n brs); simpl.
  + rewrite mkApp_hom. reflexivity.
  + reflexivity.
Qed.

Lemma TFix_hom:
  forall defs n, strip (L1_5.compile.TFix defs n) = TFix (stripDs defs) n.
reflexivity.
Qed.

Lemma TProd_hom:
  forall nm ty bod, strip (L1_5.compile.TProd nm ty bod) = TProd nm (strip bod).
reflexivity.
Qed.

Lemma TLambda_hom:
  forall nm ty bod, strip (L1_5.compile.TLambda nm ty bod) = TLambda nm (strip bod).
reflexivity.
Qed.

Lemma TLetIn_hom:
  forall nm dfn ty bod,
    strip (L1_5.compile.TLetIn nm dfn ty bod) = TLetIn nm (strip dfn) (strip bod).
reflexivity.
Qed.

Lemma TCase_hom:
  forall n ty mch brs,
    strip (L1_5.compile.TCase n ty mch brs) = TCase n (strip mch) (strips brs).
reflexivity.
Qed.

Lemma fold_left_hom:
forall (F:L1_5Term -> nat -> L1_5Term) 
       (stripF:Term -> nat -> Term) (ns:list nat) (t:L1_5Term),
  (forall (s:L1_5Term) (n:nat), strip (F s n) = stripF (strip s) n) ->
  strip (fold_left F ns t) = fold_left stripF ns (strip t).
induction ns; intros t h.
- intuition.
- simpl. rewrite IHns.
  + rewrite h. reflexivity.
  + assumption.
Qed.

Lemma pre_whFixStep_hom:
  forall body dts args,
    pre_whFixStep (strip body) (stripDs dts) (strips args) =
    strip (L1_5.term.pre_whFixStep body dts args).
Proof.
  intros body dts args.
  destruct dts, args; unfold pre_whFixStep, L1_5.term.pre_whFixStep;
  simpl; rewrite mkApp_hom; try reflexivity.
  - rewrite (fold_left_hom _
          (fun (bod : Term) (ndx : nat) =>
                instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx)
                  0 bod)).
    + rewrite <- (dcons_hom _ L1_5.compile.prop).
      rewrite (proj1 instantiate_hom).
      rewrite <- dlength_hom. reflexivity. 
    + intros. rewrite (proj1 instantiate_hom). simpl. reflexivity.
  - rewrite (fold_left_hom _
            (fun (bod : Term) (ndx : nat) =>
         instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx) 0 bod)).
    + rewrite dlength_hom. rewrite (proj1 instantiate_hom).
      rewrite tcons_hom. reflexivity.
    + intros. rewrite (proj1 instantiate_hom).
      rewrite <- (dcons_hom _ L1_5.compile.prop). simpl. reflexivity.
Qed.


Lemma appliedAxiomP_hom:
  forall Mch, L1_5.term.appliedAxiomP Mch = appliedAxiomP (strip Mch).
Proof.
  destruct Mch; cbn; try reflexivity.
  destruct Mch1; cbn; try reflexivity.
Qed.

Lemma WcbvEval_hom:
  forall p,
    (forall t t', L1_5.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L1_5.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (strips ts) (strips ts')) /\  
    (forall dts dts', L1_5.wcbvEval.WcbvDEvals p dts dts' ->
                      WcbvDEvals (stripEnv p) (stripDs dts) (stripDs dts')).
Proof.
  intros p.
  apply L1_5.wcbvEval.WcbvEvalEvals_ind; intros; simpl; try reflexivity;
  try (solve[constructor; trivial]).
  - constructor. unfold LookupAx. unfold L1_5.program.LookupAx in *.
    change (Lookup nm (stripEnv p)
                   (stripEC (AstCommon.ecAx (L1_5.compile.Term)))).
    apply Lookup_hom. assumption.
  - refine (wConst _ _); try eassumption.
    unfold LookupDfn. unfold L1_5.program.LookupDfn in *.
    change (Lookup nm (stripEnv p) (stripEC (AstCommon.ecTrm t))).
    apply Lookup_hom. assumption.
  - refine (wAppLam _ _ _).
    + rewrite TLambda_hom in H. eassumption.
    + eassumption.
    + rewrite whBetaStep_hom in H1. eassumption.
  - refine (wLetIn _ _ _ _). eassumption.
    rewrite <- (proj1 instantiate_hom). assumption.
  - refine (wAppFix _ _ _ _).
    + rewrite TFix_hom in H. eassumption.
    + rewrite <- dnthBody_hom. destruct (L1_5.term.dnthBody m dts).
      * rewrite e. cbn. reflexivity.
      * discriminate.
    + rewrite <- tcons_hom. cbn.
      destruct (WcbvEvals_tcons_tcons' H0) as [j0 j1].
      constructor; eassumption.
    + rewrite <- tcons_hom. rewrite pre_whFixStep_hom.
      assumption.
  - refine (wCase _ _ _ _ _ _ _); try eassumption.
    * rewrite <- canonicalP_hom. rewrite e. reflexivity.
    * rewrite <- tskipn_hom. rewrite e0. reflexivity.
    * rewrite <- whCaseStep_hom. rewrite e1. reflexivity.
  - refine (wCaseAx _ _ _ _); try eassumption.
    + rewrite <- appliedAxiomP_hom. assumption.
Qed.
Print Assumptions WcbvEval_hom.


Lemma Prf_strip_inv:
  forall s, TProof = strip s -> s = L1_5.compile.TProof.
Proof.
  destruct s; simpl; intros h; try discriminate. reflexivity.
Qed.
  
Lemma Lam_strip_inv:
  forall nm bod s, TLambda nm bod = strip s ->
   exists sty sbod, 
     (L1_5.compile.TLambda nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Prod_strip_inv:
  forall nm bod s, TProd nm bod = strip s ->
   exists sty sbod, 
     (L1_5.compile.TProd nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Cast_strip_inv:
  forall tm s, TCast tm = strip s ->
   exists stm ck sty, 
     (L1_5.compile.TCast stm ck sty) = s /\ tm = strip stm.
Proof.
  intros tm; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, c, s2. intuition. 
Qed.

Lemma Construct_strip_inv:
  forall i n s, TConstruct i n = strip s -> L1_5.compile.TConstruct i n = s.
Proof.
  intros i n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Sort_strip_inv:
  forall srt s, TSort srt = strip s -> L1_5.compile.TSort srt = s.
Proof.
  intros srt. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Ind_strip_inv:
  forall i s, TInd i = strip s -> L1_5.compile.TInd i = s.
Proof.
  intros i. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Const_strip_inv:
  forall nm s, TConst nm = strip s -> L1_5.compile.TConst nm = s.
Proof.
  intros nm. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Fix_strip_inv:
  forall ds n s, TFix ds n = strip s ->
    exists sds, (L1_5.compile.TFix sds n) = s /\ ds = stripDs sds.
Proof.
  intros ds n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists d. intuition.
Qed.

Lemma App_strip_inv:
  forall fn arg args s, TApp fn arg args = strip s ->
    exists sfn sarg sargs,
      (L1_5.compile.TApp sfn sarg sargs) = s /\
      fn = strip sfn /\ arg = strip sarg /\ args = strips sargs.
Proof.
  intros fn arg args. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma LetIn_strip_inv:
  forall nm dfn bod s, TLetIn nm dfn bod = strip s ->
    exists sdfn sty sbod,
      (L1_5.compile.TLetIn nm sdfn sty sbod = s) /\
      dfn = strip sdfn /\ bod = strip sbod.
Proof.
  intros nm dfn bod s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, s3. intuition.
Qed.

Lemma Case_strip_inv:
  forall m mch brs s, TCase m mch brs = strip s ->
    exists sty smch sbrs, (L1_5.compile.TCase m sty smch sbrs = s) /\
              mch = strip smch /\ brs = strips sbrs.
Proof.
  intros m mch brs s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma tnil_strip_inv:
  forall ts, tnil = strips ts -> ts = L1_5.compile.tnil.
Proof.
  induction ts; intros; try reflexivity.
  - simpl in H. discriminate.
Qed.

Lemma tcons_strip_inv:
  forall t ts us, tcons t ts = strips us ->
    exists st sts, (L1_5.compile.tcons st sts = us) /\ 
                   t = strip st /\ ts = strips sts.
Proof.
  intros t ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, us. intuition.
Qed.

Lemma dcons_strip_inv:
  forall nm t m ts us, dcons nm t m ts = stripDs us ->
    exists ty st sts, (L1_5.compile.dcons nm ty st m sts = us) /\ 
                   t = strip st /\ ts = stripDs sts.
Proof.
  intros nm t m ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, t1, us. intuition.
Qed.

Lemma whCaseStep_Hom:
  forall n ts bs t,
    L1_5.term.whCaseStep n ts bs = Some t -> 
    whCaseStep n (strips ts) (strips bs) = Some (strip t).
Proof.
  intros n ts bs t h. rewrite <- whCaseStep_hom. rewrite <- optStrip_hom.
  apply f_equal. assumption.
Qed.

Theorem L2WcbvEval_L1_5WcbvEval:
  forall L2p p, L2p = stripEnv p -> L1_5.program.WFaEnv p ->
  forall L2t t, L2t = strip t -> L1_5.term.WFapp t ->
  forall L2s, WcbvEval L2p L2t L2s ->
  forall s, L1_5.wcbvEval.WcbvEval p t s -> L2s = strip s.
Proof.
  intros.
  refine (WcbvEval_single_valued _ _). eassumption.
  subst. apply WcbvEval_hom. assumption.
Qed.
Print Assumptions L2WcbvEval_L1_5WcbvEval.

Theorem L2WcbvEval_sound_for_L1_5wndEval:
  forall L2p L2t L2s, WcbvEval L2p L2t L2s ->
  forall p, L2p = stripEnv p -> L1_5.program.WFaEnv p -> 
  forall t, L2t = strip t -> L1_5.term.WFapp t ->       
  forall s, L1_5.wcbvEval.WcbvEval p t s ->      
            L2s = strip s /\ L1_5.wndEval.wndEvalRTC p t s.
Proof.
  intros. repeat split.
  - refine (WcbvEval_single_valued _ _). eassumption.
    subst. apply WcbvEval_hom. assumption.
  - refine (proj1 (L1_5.wcbvEval.WcbvEval_wndEvalRTC _) _ _ _ _); assumption.
Qed.
Print Assumptions L2WcbvEval_sound_for_L1_5wndEval.


(*** unstrip: replace every missing type field with [prop]  ***)
Function unstrip (t:Term) : L1_5Term :=
  match t with
    | TProof => L1_5.compile.TProof
    | TRel n => L1_5.compile.TRel n
    | TSort s => L1_5.compile.TSort s
    | TCast t => L1_5.compile.TCast (unstrip t) Cast L1_5.compile.prop
    | TProd nm bod => L1_5.compile.TProd nm L1_5.compile.prop (unstrip bod)
    | TLambda nm bod => L1_5.compile.TLambda nm L1_5.compile.prop (unstrip bod)
    | TLetIn nm dfn bod =>
           L1_5.compile.TLetIn nm (unstrip dfn) L1_5.compile.prop (unstrip bod)
    | TApp fn arg args =>
           L1_5.compile.TApp (unstrip fn) (unstrip arg) (unstrips args)
    | TConst nm => L1_5.compile.TConst nm
    | TInd i => L1_5.compile.TInd i
    | TConstruct i m => L1_5.compile.TConstruct i m
    | TCase n mch brs =>
           L1_5.compile.TCase n L1_5.compile.prop (unstrip mch) (unstrips brs)
    | TFix ds n => L1_5.compile.TFix (unstripDs ds) n
  end
with unstrips (ts:Terms) : L1_5Terms := 
  match ts with
    | tnil => L1_5.compile.tnil
    | tcons t ts => L1_5.compile.tcons (unstrip t) (unstrips ts)
  end
with unstripDs (ts:Defs) : L1_5Defs := 
  match ts with
    | dnil => L1_5.compile.dnil
    | dcons nm t m ds =>
           L1_5.compile.dcons nm L1_5.compile.prop (unstrip t) m (unstripDs ds)
  end.

Lemma strip_leftInv_unstrip:
  (forall (t:Term), strip (unstrip t) = t) /\
  (forall ts:Terms, strips (unstrips ts) = ts) /\
  (forall ds:Defs, stripDs (unstripDs ds) = ds).
Proof.
  apply TrmTrmsDefs_ind; simpl; intros;
  try reflexivity; try (rewrite H; reflexivity);
  try (rewrite H; rewrite H0; reflexivity);
  try (rewrite H; rewrite H0; rewrite H1; reflexivity).
Qed.

Function unstripCnstrs (cs:list Cnstr) : list AstCommon.Cnstr :=
  match cs with
    | nil => nil
    | cons (mkCnstr str arity) cs =>
        cons (AstCommon.mkCnstr str arity) (unstripCnstrs cs)
  end.
Function unstripItyPack (its:itypPack) : AstCommon.itypPack :=
  match its with
    | nil => nil
    | (mkItyp str itps) :: itpacks =>
         (AstCommon.mkItyp str (unstripCnstrs itps)) ::
                           unstripItyPack itpacks
  end.
Function unstripEC (ec:envClass) : AstCommon.envClass L1_5.compile.Term :=
  match ec with
    | AstCommon.ecTrm t => ecTrm (unstrip t)
    | AstCommon.ecTyp _ npars itp =>
       AstCommon.ecTyp _ npars (unstripItyPack itp)
  end.
Fixpoint unstripEnv (p:environ) : AstCommon.environ L1_5.compile.Term :=
  match p with
    | nil => nil
    | cons (nm, ec) q => cons (nm, (unstripEC ec)) (unstripEnv q)
  end.
