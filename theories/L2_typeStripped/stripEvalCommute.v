
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import L1g.L1g.
Require Import L2.compile.
Require Import L2.term.
Require Import L2.program.
Require Import L2.wndEval.
Require Import L2.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1gTerm := L1g.compile.Term.
Definition L1gTerms := L1g.compile.Terms.
Definition L1gBrs := L1g.compile.Brs.
Definition L1gDefs := L1g.compile.Defs.


Definition optStrip (t:option L1gTerm) : option Term :=
  match t with
    | None => None
    | Some t => Some (strip t)
  end.
Definition optStrips (ts:option L1gTerms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (strips ts)
  end.
Definition optStripDnth (b: option (L1gTerm * nat)) : option (Term * nat) :=
                           match b with
                             | None => None
                             | Some (t, n) => Some (strip t, n)
                           end.
Definition optStripBnth := optStripDnth.
Definition optStripCanP
           (b: option (nat * L1gTerms)): option (nat * Terms) :=
                           match b with
                             | None => None
                             | Some (n, t) => Some (n, strips t)
                           end.
Definition optStrip_split
           (b: option L1g.term.split): option split :=
  match b with
    | None => None
    | Some (L1g.term.mkSplit fsts t lsts) =>
      Some (mkSplit (strips fsts) (strip t) (strips lsts))
  end.


Lemma optStrip_hom: forall y, optStrip (Some y) = Some (strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optStrip_hom_None: optStrip (@None L1g.compile.Term) = @None (Term).
  reflexivity.
Qed.

Lemma optStrips_hom: forall y, optStrips (Some y) = Some (strips y).
induction y; simpl; reflexivity.
Qed.
Lemma optStripDnth_hom:
  forall y n, optStripDnth (Some (y, n)) = Some (strip y, n).
induction y; simpl; reflexivity.
Qed.
Definition optStripBnth_hom := optStripDnth_hom.
Lemma optStripCanP_hom:
  forall y n, optStripCanP (Some (n, y)) = Some (n, strips y).
induction y; simpl; reflexivity.
Qed.
Lemma optStrip_split_hom:
  forall fsts t lsts,
    optStrip_split (Some (L1g.term.mkSplit fsts t lsts)) =
    Some (mkSplit (strips fsts) (strip t) (strips lsts)).
Proof.
  induction fsts; cbn; intros; try reflexivity.
Qed.
                              
Lemma tlength_hom:
  forall ts, tlength (strips ts) = L1g.term.tlength ts.
Proof.
  induction ts; intros; try reflexivity.
  - cbn. apply f_equal. assumption.
Qed.
  
Lemma Lookup_hom:
  forall p s ec, Lookup s p ec -> Lookup s (stripEnv p) (stripEC ec).
Proof.
  induction 1; destruct t.
  - change (Lookup s ((s, ecTrm (strip l)) :: (stripEnv p))
                   (ecTrm (strip l))).
    apply LHit.
  - cbn. apply LHit.
  - change (Lookup s2 ((s1, ecTrm (strip l)) :: (stripEnv p))
                   (stripEC ec)).
    apply LMiss; assumption.
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

Lemma dlength_hom:
  forall ds, L1g.compile.dlength ds = dlength (stripDs ds).
induction ds. intuition. simpl. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, strips (L1g.compile.tcons t ts) = tcons (strip t) (strips ts).
reflexivity.
Qed.

Lemma tnil_hom: strips L1g.compile.tnil = tnil.
reflexivity.
Qed.

Lemma dcons_hom:
  forall nm ty bod rarg ds,
    stripDs (L1g.compile.dcons nm ty bod rarg ds) =
    dcons nm (strip bod) rarg (stripDs ds).
reflexivity.
Qed.

Lemma dnil_hom: stripDs L1g.compile.dnil = dnil.
reflexivity.
Qed.

Lemma dnthBody_hom: 
  forall m ds, optStripDnth (L1g.compile.dnthBody m ds) =
               dnthBody m (stripDs ds).
induction m; induction ds; try intuition.
- simpl. intuition.
Qed.

Lemma bnth_hom:
  forall m ds, optStripBnth (L1g.compile.bnth m ds) =
               bnth m (stripBs ds).
induction m; induction ds; try intuition.
- simpl. intuition.
Qed.

Lemma canonicalP_hom:
  forall t, optStripCanP (L1g.term.canonicalP t) = canonicalP (strip t).
Proof.
  induction t; intros; cbn; try reflexivity; try assumption.
  - destruct t1; cbn; try reflexivity.
Qed.

Lemma tnth_hom:
 forall ts n, optStrip (L1g.term.tnth n ts) = tnth n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed. 

Lemma tskipn_hom:
  forall ts n, optStrips (L1g.term.tskipn n ts) = tskipn n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.

Lemma tappend_hom:
  forall ts us,
    strips (L1g.compile.tappend ts us) = tappend (strips ts) (strips us).
induction ts; intros us; simpl. reflexivity.
rewrite IHts. reflexivity.
Qed.

Lemma TApp_hom:
  forall fn arg args,
    strip (L1g.compile.TApp fn arg args) =
    TApp (strip fn) (strip arg) (strips args).
induction fn; intros arg args; try reflexivity.
Qed.

Lemma isApp_hom:
  forall t, isApp (strip t) -> L1g.term.isApp t.
Proof.
  destruct t; simpl; intros h;
  destruct h as [x0 [x1 [x2 h]]]; try discriminate. 
  exists t1, t2, t3. reflexivity.
Qed.

Lemma isLambda_hom:
  forall t, isLambda (strip t) -> L1g.term.isLambda t.
Proof.
  destruct t; simpl; intros h; destruct h as [x0 [x1 h]]; try discriminate. 
  exists n, t1, t2. reflexivity.
Qed.

Lemma isFix_hom:
  forall t, isFix (strip t) -> L1g.term.isFix t.
Proof.
  destruct t; cbn; intros h; destruct h as [x0 [x1 h]]; try discriminate.
  exists d, n. reflexivity. 
Qed.

Lemma L1WFapp_L2WFapp:
  (forall t, L1g.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L1g.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ts, L1g.term.WFappBs ts -> WFappBs (stripBs ts)) /\
  (forall ds, L1g.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
  apply L1g.term.WFappTrmsBrsDefs_ind; simpl; constructor; auto.
  intros h. elim H. apply isApp_hom. assumption.
Qed.

Lemma L1WFaEnv_L2WFaEnv:
  forall p:environ L1gTerm, L1g.program.WFaEnv p -> WFaEnv (stripEnv p).
Proof.
  induction 1; simpl; constructor.
  - inversion H; destruct ec; simpl; try discriminate; constructor.
    + apply (proj1 (L1WFapp_L2WFapp)). assumption.
  - assumption.
  - apply stripEnv_pres_fresh. assumption.
Qed.

(***
Lemma WFapp_hom:
  (forall t, L1g.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L1g.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ds, L1g.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
   apply L1g.term.WFappTrmsDefs_ind; cbn; intros;
  try (solve [constructor]);
  try (solve [constructor; intuition]).
  - constructor; try assumption.
    + intros h. assert (j:= isApp_hom _ h). contradiction.
Qed.
 ****)

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
  strip (L1g.term.mkApp fn args) = mkApp (strip fn) (strips args).
Proof.
  destruct args; try (reflexivity).
  - rewrite L1g.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident.
    reflexivity.
  - destruct fn; try reflexivity.
    cbn. rewrite <- tcons_hom. rewrite <- tappend_hom. reflexivity.
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

Lemma instantiates_dcons_commute:
  forall tin n nm t m ds,
         (instantiateDefs tin n (dcons nm t m ds)) = 
         (dcons nm (instantiate tin n t) m (instantiateDefs tin n ds)).
reflexivity.
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

Lemma instantiate_hom:
  (forall bod arg n, strip (L1g.term.instantiate arg n bod) =
                     instantiate (strip arg) n (strip bod)) /\
    (forall bods arg n, strips (L1g.term.instantiates arg n bods) =
                    instantiates (strip arg) n (strips bods)) /\
    (forall brs arg n, stripBs (L1g.term.instantiateBrs arg n brs) =
                    instantiateBrs (strip arg) n (stripBs brs)) /\
    (forall ds arg n, stripDs (L1g.term.instantiateDefs arg n ds) =
                      instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L1g.compile.TrmTrmsBrsDefs_ind; intros; try (simpl; reflexivity).
  - simpl. destruct (lt_eq_lt_dec n n0); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n0 n)); try omega. cbn. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
    + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
  - cbn. rewrite H. reflexivity.
  - change (TProd n (strip (L1g.term.instantiate arg (S n0) t0)) =
            (TProd n (instantiate (strip arg) (S n0) (strip t0)))).
    rewrite H0. reflexivity.
  - change (TLambda n (strip (L1g.term.instantiate arg (S n0) t0)) =
            (TLambda n (instantiate (strip arg) (S n0) (strip t0)))).
    rewrite H0. reflexivity.
  - change (TLetIn n (strip (L1g.term.instantiate arg n0 t))
                   (strip (L1g.term.instantiate arg (S n0) t1)) =
            (TLetIn n (instantiate (strip arg) n0 (strip t))
                    (instantiate (strip arg) (S n0) (strip t1)))).
    rewrite H. rewrite H1. reflexivity.
  - change (strip (L1g.term.mkApp
                     (L1g.term.instantiate arg n t)
                     (L1g.compile.tcons (L1g.term.instantiate arg n t0)
                                         (L1g.term.instantiates arg n t1))) =
            instantiate (strip arg) n (strip (L1g.compile.TApp t t0 t1))). 
    rewrite TApp_hom. 
    change
      (strip (L1g.term.mkApp
                (L1g.term.instantiate arg n t)
                (L1g.compile.tcons (L1g.term.instantiate arg n t0)
                                   (L1g.term.instantiates arg n t1))) =
       (mkApp (instantiate (strip arg) n (strip t))
              (tcons (instantiate (strip arg) n (strip t0))
                     (instantiates (strip arg) n (strips t1))))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. 
    rewrite mkApp_hom. rewrite tcons_hom. reflexivity.
  - change (TCase p (strip (L1g.term.instantiate arg n t0))
                  (stripBs (L1g.term.instantiateBrs arg n b)) =
            (TCase p (instantiate (strip arg) n (strip t0))
                   (instantiateBrs (strip arg) n (stripBs b)))).
    rewrite H0. rewrite H1. reflexivity.
  - change (TFix (stripDs (L1g.term.instantiateDefs
                             arg (n0 + L1g.compile.dlength d) d)) n =
            (TFix (instantiateDefs
                     (strip arg) (n0 + dlength (stripDs d)) (stripDs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (strip (L1g.term.instantiate arg n t))
                  (strips (L1g.term.instantiates arg n t0)) =
            tcons (instantiate (strip arg) n (strip t))
                  (instantiates (strip arg) n (strips t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (bcons n (strip (L1g.term.instantiate arg n0 t))
                  (stripBs (L1g.term.instantiateBrs arg n0 b)) =
            bcons n (instantiate (strip arg) n0 (strip t))
                  (instantiateBrs (strip arg) n0 (stripBs b))).
    rewrite H0. rewrite H. reflexivity.
  - change (dcons n (strip (L1g.term.instantiate arg n1 t0)) n0
                  (stripDs (L1g.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (strip arg) n1 (strip t0)) n0
                  (instantiateDefs (strip arg) n1 (stripDs d))).
    rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma whBetaStep_hom:
  forall bod arg args,
    strip (L1g.term.whBetaStep bod arg args) =
    whBetaStep (strip bod) (strip arg) (strips args).
Proof.
  intros bod arg args.
  unfold L1g.term.whBetaStep, whBetaStep.
  rewrite mkApp_hom. rewrite <- (proj1 instantiate_hom). reflexivity.
Qed.

Lemma TConstruct_hom:
  forall i n np na,
    strip (L1g.compile.TConstruct i n np na) = TConstruct i n np na.
intros. simpl.  destruct i. reflexivity.
Qed.


Lemma optStrip_match:
  forall x (f:L1gTerm -> L1gTerm) (g:Term -> Term), 
    (forall z, strip (f z) = g (strip z)) ->
    optStrip (match x with Some y => Some (f y) | None => None end) =
    match (optStrip x) with Some y => Some (g y) | None => None end.
induction x; intros f g h; simpl.
- rewrite h; reflexivity.
- reflexivity.
Qed.

Lemma whCaseStep_hom:
  forall n brs ts,
    optStrip (L1g.term.whCaseStep n ts brs) =
    whCaseStep n (strips ts) (stripBs brs).
destruct n, brs; intros; simpl; try reflexivity.
- unfold whCaseStep. simpl. rewrite mkApp_hom. reflexivity.
- unfold whCaseStep. unfold L1g.term.whCaseStep. cbn. 
  rewrite <- bnth_hom. destruct (compile.bnth n brs); simpl.
  + destruct p as [x0 x1]. cbn. rewrite mkApp_hom. reflexivity.
  + reflexivity.
Qed.

Lemma TFix_hom:
  forall defs n, strip (L1g.compile.TFix defs n) = TFix (stripDs defs) n.
reflexivity.
Qed.

Lemma TProd_hom:
  forall nm ty bod,
    strip (L1g.compile.TProd nm ty bod) = TProd nm (strip bod).
reflexivity.
Qed.

Lemma TLambda_hom:
  forall nm ty bod,
    strip (L1g.compile.TLambda nm ty bod) = TLambda nm (strip bod).
reflexivity.
Qed.

Lemma TLetIn_hom:
  forall nm dfn ty bod,
    strip (L1g.compile.TLetIn nm dfn ty bod) =
    TLetIn nm (strip dfn) (strip bod).
reflexivity.
Qed.

Lemma TCase_hom:
  forall n ty mch brs,
    strip (L1g.compile.TCase n ty mch brs) =
    TCase n (strip mch) (stripBs brs).
reflexivity.
Qed.

Lemma fold_left_hom:
forall (F:L1gTerm -> nat -> L1gTerm) 
       (stripF:Term -> nat -> Term) (ns:list nat) (t:L1gTerm),
  (forall (s:L1gTerm) (n:nat), strip (F s n) = stripF (strip s) n) ->
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
    strip (L1g.term.pre_whFixStep body dts args).
Proof.
  intros body dts args.
  destruct dts, args; unfold pre_whFixStep, L1g.term.pre_whFixStep;
  simpl; rewrite mkApp_hom; try reflexivity.
  - rewrite (fold_left_hom _
          (fun (bod : Term) (ndx : nat) =>
                instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx)
                  0 bod)).
    + rewrite <- (dcons_hom _ L1g.compile.prop).
      rewrite (proj1 instantiate_hom).
      rewrite <- dlength_hom. reflexivity. 
    + intros. rewrite (proj1 instantiate_hom). simpl. reflexivity.
  - rewrite (fold_left_hom _
            (fun (bod : Term) (ndx : nat) =>
         instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx) 0 bod)).
    + rewrite dlength_hom. rewrite (proj1 instantiate_hom).
      rewrite tcons_hom. reflexivity.
    + intros. rewrite (proj1 instantiate_hom).
      rewrite <- (dcons_hom _ L1g.compile.prop). simpl. reflexivity.
Qed.

Lemma tsplit_hom:
  forall ix arg args,
    optStrip_split (L1g.term.tsplit ix arg args) =
    tsplit ix (strip arg) (strips args).
Proof.
  intros ix arg args.
  functional induction (L1g.term.tsplit ix arg args); simpl; intros.
  - reflexivity.
  - destruct n. elim y. reflexivity.
  - destruct ls; cbn; reflexivity.
  - case_eq (tsplit m (strip t) (strips ts)); intros.
    + destruct s.
      assert (j0:= L1g.term.tsplit_sanity m t ts). rewrite e1 in j0.
      assert (j1:= tsplit_sanity m (strip t) (strips ts)).
      rewrite H in j1. destruct j1.
      assert (j2: tlength (strips ts) = tlength fsts + tlength lsts).
      { apply (f_equal tlength) in H0. rewrite tlength_tappend in H0.
        cbn in H0. omega. }
      rewrite tlength_hom in j2. rewrite j2 in j0. rewrite H1 in j0. omega.
    + reflexivity.
  - destruct (tsplit m (strip t) (strips ts)).
    + destruct s0. rewrite e1 in IHo. rewrite optStrip_split_hom in IHo.
      myInjection IHo. reflexivity.
    + rewrite e1 in IHo.  rewrite optStrip_split_hom in IHo.
      discriminate.
Qed.

Lemma optStripCanP_hom':
  forall z, optStripCanP (Some z) =
            Some (fst z, strips (snd z)).
intros. destruct z as [z0 z1]. cbn. reflexivity.
Qed.

(***** Can this weaker version of WcbvEval_hom be proven?
****  Seems need stronger IH   **************
Lemma compile_pres_wcbvEval:
  forall p,
    (forall t t', L1g.wcbvEval.WcbvEval p t t' ->
                  exists u, WcbvEval (stripEnv p) (strip t) u) /\
    (forall ts ts', L1g.wcbvEval.WcbvEvals p ts ts' ->
                  exists us, WcbvEvals (stripEnv p) (strips ts) us).
Proof.
  intros p.
  apply L1g.wcbvEval.WcbvEvalEvals_ind; intros; cbn.
  - destruct H as [x jx]. exists x. econstructor. assumption.
  - destruct H as [x jx]. exists (TLambda nm (strip bod)). econstructor.
  - destruct H as [x jx]. exists (TProd nm (strip bod)). econstructor.
  - destruct H as [x jx]. exists x. constructor. assumption.
  - exists (TConstruct i r arty). constructor.
  - exists (TInd i). constructor.
  - exists (TSort srt). constructor.
  - exists (TFix (stripDs dts) m). constructor.
  - exists TAx. constructor.
  - destruct H as [x jx]. exists x. econstructor; try eassumption.
    eapply (lookupDfn_hom _ _ e).
  - destruct H as [x jx]. destruct H0 as [y jy]. destruct H1 as [z jz].
    rewrite whBetaStep_hom in jz. exists z.
    eapply (@wAppLam
             (stripEnv p) (strip fn)
             (strip bod) (strip a1) (strip a1') z (strips args) _ _ _ jz).
  - destruct H as [x jx]. destruct H0 as [y jy].
    rewrite (proj1 instantiate_hom) in jy. exists y.
    eapply (@wLetIn (stripEnv p) nm (strip dfn) (strip bod) _ _ _ jy). 
  - destruct H as [u ju]. destruct H0 as [y jy]. destruct H1 as [z jz].
    rewrite <- pre_whFixStep_hom in jz. cbn in jy. cbn in jz. exists z.
    eapply (@wAppFix
             (stripEnv p) (stripDs dts) m
             (strip fn) (strip arg) (strip arg') z (strip x)
          (strips args) (strips args') ix _ _ _ _ jz).
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
    Grab Existential Variables.
    rewrite tlength_hom. assumption.
    rewrite <- dnthBody_hom. rewrite e. cbn. reflexivity.
    admit.
    admit.
****)

    
Lemma WcbvEval_hom:
  forall p,
    (forall t t', L1g.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L1g.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (strips ts) (strips ts')).
Proof.
  intros p.
  apply L1g.wcbvEval.WcbvEvalEvals_ind; intros; try reflexivity;
  try (solve[constructor; trivial]).
  - cbn. econstructor; try eassumption. apply lookupDfn_hom. assumption.
  - cbn. eapply wAppLam.
    + apply H. 
    + apply H0. 
    + rewrite whBetaStep_hom in H1. assumption.
  - cbn. eapply wLetIn.
    + apply H. 
    + rewrite <- (proj1 instantiate_hom). assumption.
  - cbn. eapply wAppFix.
    + eapply H.
    + rewrite <- dnthBody_hom. rewrite e. reflexivity.
    + rewrite <- pre_whFixStep_hom in H0. eapply H0.
  - destruct (WcbvEvals_tcons_tcons H0) as [a' [args' j]]. rewrite j in H0.
    cbn. rewrite mkApp_hom. eapply wAppCong. try eassumption.
    + intros h. elim n. apply isLambda_hom. assumption.
    + intros h. elim n0. apply isFix_hom. assumption.
    + rewrite j. cbn in H0. assumption.
  - refine (wCase _ _ _ _ _ _ _); try eassumption.
    * rewrite <- canonicalP_hom. rewrite e. reflexivity.
    * rewrite <- tskipn_hom. rewrite e0. reflexivity.
    * rewrite <- whCaseStep_hom. rewrite e1. reflexivity.
  - refine (wCaseCong _ _ _ _); try eassumption.
    + rewrite <- canonicalP_hom. rewrite e. reflexivity.
Qed.
Print Assumptions WcbvEval_hom.

(** WcbvEval_hom is nice, but it is stronger than necessary to prove 
*** certiL1g_to_L2Correct (in instances.v).
**)
Corollary strip_pres_eval:
  forall (p:environ L1g.compile.Term) (t tv:L1g.compile.Term),
    L1g.wcbvEval.WcbvEval p t tv ->
    exists stv, WcbvEval (stripEnv p) (strip t) stv.
Proof.
  intros. exists (strip tv). apply (proj1 (WcbvEval_hom _)).
  assumption.
Qed.

Corollary wcbvEval_hom:
  forall p n t t',
    L1g.wcbvEval.wcbvEval p n t = Ret t' ->
    exists m, wcbvEval (stripEnv p) m (strip t) = Ret (strip t').
Proof.
  intros. 
  assert (j1:= proj1 (L1g.wcbvEval.wcbvEval_WcbvEval p n) _ _ H).
  assert (k0:= proj1 (WcbvEval_hom p) _ _ j1).
  assert (j2:= @WcbvEval_wcbvEval (stripEnv p) (strip t) (strip t') k0).
  destruct j2 as [ny jny].
  exists ny. eapply jny. omega.
Qed.


Lemma Prf_strip_inv:
  forall s st, TProof st = strip s ->
              exists t, s = L1g.compile.TProof t /\ st = strip t.
Proof.
  destruct s; simpl; intros h; try discriminate.
  intros. myInjection H. exists s. intuition.
Qed.
  
Lemma Lam_strip_inv:
  forall nm bod s, TLambda nm bod = strip s ->
   exists sty sbod, 
     (L1g.compile.TLambda nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Prod_strip_inv:
  forall nm bod s, TProd nm bod = strip s ->
   exists sty sbod, 
     (L1g.compile.TProd nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Construct_strip_inv:
  forall i n np na s,
    TConstruct i n np na = strip s -> L1g.compile.TConstruct i n np na = s.
Proof.
  intros i n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Sort_strip_inv:
  forall srt s, TSort srt = strip s -> L1g.compile.TSort srt = s.
Proof.
  intros srt. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Ind_strip_inv:
  forall i s, TInd i = strip s -> L1g.compile.TInd i = s.
Proof.
  intros i. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Const_strip_inv:
  forall nm s, TConst nm = strip s -> L1g.compile.TConst nm = s.
Proof.
  intros nm. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Fix_strip_inv:
  forall ds n s, TFix ds n = strip s ->
    exists sds, (L1g.compile.TFix sds n) = s /\ ds = stripDs sds.
Proof.
  intros ds n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists d. intuition.
Qed.

Lemma App_strip_inv:
  forall fn arg args s, TApp fn arg args = strip s ->
    exists sfn sarg sargs,
      (L1g.compile.TApp sfn sarg sargs) = s /\
      fn = strip sfn /\ arg = strip sarg /\ args = strips sargs.
Proof.
  intros fn arg args. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma LetIn_strip_inv:
  forall nm dfn bod s, TLetIn nm dfn bod = strip s ->
    exists sdfn sty sbod,
      (L1g.compile.TLetIn nm sdfn sty sbod = s) /\
      dfn = strip sdfn /\ bod = strip sbod.
Proof.
  intros nm dfn bod s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, s3. intuition.
Qed.

Lemma Case_strip_inv:
  forall m mch brs s, TCase m mch brs = strip s ->
    exists sty smch sbrs, (L1g.compile.TCase m sty smch sbrs = s) /\
              mch = strip smch /\ brs = stripBs sbrs.
Proof.
  intros m mch brs s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, b. intuition.
Qed.

Lemma tnil_strip_inv:
  forall ts, tnil = strips ts -> ts = L1g.compile.tnil.
Proof.
  induction ts; intros; try reflexivity.
  - simpl in H. discriminate.
Qed.

Lemma tcons_strip_inv:
  forall t ts us, tcons t ts = strips us ->
    exists st sts, (L1g.compile.tcons st sts = us) /\ 
                   t = strip st /\ ts = strips sts.
Proof.
  intros t ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, us. intuition.
Qed.

Lemma dcons_strip_inv:
  forall nm t m ts us, dcons nm t m ts = stripDs us ->
    exists ty st sts, (L1g.compile.dcons nm ty st m sts = us) /\ 
                   t = strip st /\ ts = stripDs sts.
Proof.
  intros nm t m ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, t1, us. intuition.
Qed.

Lemma whCaseStep_Hom:
  forall n ts bs t,
    L1g.term.whCaseStep n ts bs = Some t -> 
    whCaseStep n (strips ts) (stripBs bs) = Some (strip t).
Proof.
  intros n ts bs t h. rewrite <- whCaseStep_hom. rewrite <- optStrip_hom.
  apply f_equal. assumption.
Qed.

Definition excStrip (t:exception L1gTerm) : exception Term :=
  match t with
    | Exc str => Exc str
    | Ret t => Ret (strip t)
  end.


Theorem L2WcbvEval_sound_for_L1gWcbvEval:
  forall (p:environ L1g.compile.Term) (t:L1g.compile.Term) (L2s:Term),
    WcbvEval (stripEnv p) (strip t) L2s ->
  forall s, L1g.wcbvEval.WcbvEval p t s -> L2s = strip s.
Proof.
  intros. refine (WcbvEval_single_valued _ _).
  - eassumption.
  - apply WcbvEval_hom. assumption.
Qed.
Print Assumptions L2WcbvEval_sound_for_L1gWcbvEval.

(******
Theorem L2WcbvEval_sound_for_L1gwndEval:
  forall p t s, WcbvEval (stripEnv p) (strip t) (strip s) ->
           L1g.program.WFaEnv p -> L1g.term.WFapp t ->        
        L1g.wndEval.wndEvalRTC p t s.
Proof.
  intros.
  refine (proj1 (L1g.wcbvEval.WcbvEval_wndEvalRTC _) _ _ _ _);
    try assumption.
  
Qed.
Print Assumptions L2WcbvEval_sound_for_L1gwndEval.
 *****************)

Theorem L2WcbvEval_sound_for_L1gwndEval:
  forall (p:environ L1g.compile.Term) (t:L1g.compile.Term) (L2s:Term),
    WcbvEval (stripEnv p) (strip t) L2s ->
    forall s, L1g.wcbvEval.WcbvEval p t s ->
              L1g.program.WFaEnv p -> L1g.term.WFapp t ->        
              L1g.wndEval.wndEvalRTC p t s.
Proof.
  intros.
  refine (proj1 (L1g.wcbvEval.WcbvEval_wndEvalRTC _) _ _ _ _); assumption.
Qed.
Print Assumptions L2WcbvEval_sound_for_L1gwndEval.

(*****
Parameter ObsCrct: Term -> L1g.compile.Term -> Prop.
Goal
  forall (sp:environ L1g.compile.Term) (st:L1g.compile.Term),
   (exists ou:Term, WcbvEval (stripEnv sp) (strip st) ou ->
       exists su, L1g.wcbvEval.WcbvEval sp st su /\ ObsCrct ou su) /\
(forall (su:L1g.compile.Term),
  L1g.wcbvEval.WcbvEval sp st su ->
    exists ou:Term, WcbvEval (stripEnv sp) (strip st) ou).
Proof.
  split; intros. Focus 2.
*******************)
  


    
Lemma sound_and_complete:
  forall (p:environ L1g.compile.Term) (t s:L1g.compile.Term),
    L1g.wcbvEval.WcbvEval p t s ->
    WcbvEval (stripEnv p) (strip t) (strip s).
Proof.
  intros p t s h. apply (proj1 (WcbvEval_hom p)). assumption.
Qed.

Lemma sac_complete:
  forall p t s, L1g.wcbvEval.WcbvEval p t s ->
                WcbvEval (stripEnv p) (strip t) (strip s).
Proof.
  intros. apply sound_and_complete. assumption.
Qed.

Lemma sac_sound:
  forall p t s, L1g.wcbvEval.WcbvEval p t s ->
  forall L2s, WcbvEval (stripEnv p) (strip t) L2s -> L2s = strip s.
Proof.
  intros p t s h1 L2s h2.
  apply (WcbvEval_single_valued h2). apply (sound_and_complete h1).
Qed. 
Print Assumptions sac_sound.
