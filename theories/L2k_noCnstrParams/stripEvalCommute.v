
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import L2.L2.
Require Import L2k.compile.
Require Import L2k.term.
Require Import L2k.program.
Require Import L2k.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1gTerm := L2.compile.Term.
Definition L1gTerms := L2.compile.Terms.
Definition L1gDefs := L2.compile.Defs.


Definition optStrip (t:option L2Term) : option Term :=
  match t with
    | None => None
    | Some t => Some (strip t)
  end.
Definition optStrips (ts:option L2Terms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (strips ts)
  end.
Definition optStripDnth (b: option (L2Term * nat)) : option (Term * nat) :=
                           match b with
                             | None => None
                             | Some (t, n) => Some (strip t, n)
                           end.
Definition optStripCanP
           (b: option (nat * L2Terms * nat)): option (nat * Terms * nat) :=
                           match b with
                             | None => None
                             | Some (n, t, m) => Some (n, strips t, m)
                           end.
Definition optStrip_split
           (b: option L2.term.split): option split :=
  match b with
    | None => None
    | Some (L2.term.mkSplit fsts t lsts) =>
      Some (mkSplit (strips fsts) (strip t) (strips lsts))
  end.


Lemma optStrip_hom: forall y, optStrip (Some y) = Some (strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optStrip_hom_None: optStrip (@None L2.compile.Term) = @None (Term).
  reflexivity.
Qed.

Lemma optStrips_hom: forall y, optStrips (Some y) = Some (strips y).
induction y; simpl; reflexivity.
Qed.
Lemma optStripDnth_hom:
  forall y n, optStripDnth (Some (y, n)) = Some (strip y, n).
induction y; simpl; reflexivity.
Qed.
Lemma optStripCanP_hom:
  forall y n m, optStripCanP (Some (n, y, m)) = Some (n, strips y, m).
induction y; simpl; reflexivity.
Qed.
Lemma optStrip_split_hom:
  forall fsts t lsts,
    optStrip_split (Some (L2.term.mkSplit fsts t lsts)) =
    Some (mkSplit (strips fsts) (strip t) (strips lsts)).
Proof.
  induction fsts; cbn; intros; try reflexivity.
Qed.
                              
Lemma tlength_hom:
  forall ts, tlength (strips ts) = L2.term.tlength ts.
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
  forall ds, L2.term.dlength ds = dlength (stripDs ds).
induction ds. intuition. simpl. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, strips (L2.compile.tcons t ts) = tcons (strip t) (strips ts).
reflexivity.
Qed.

Lemma tnil_hom: strips L2.compile.tnil = tnil.
reflexivity.
Qed.

Lemma dcons_hom:
  forall nm bod rarg ds,
    stripDs (L2.compile.dcons nm bod rarg ds) =
    dcons nm (strip bod) rarg (stripDs ds).
reflexivity.
Qed.

Lemma dnil_hom: stripDs L2.compile.dnil = dnil.
reflexivity.
Qed.

Lemma dnthBody_hom: 
  forall m ds, optStripDnth (L2.term.dnthBody m ds) =
               dnthBody m (stripDs ds).
induction m; induction ds; try intuition.
- simpl. intuition.
Qed.


Lemma TCast_hom:
  forall tm, strip (L2.compile.TCast tm) = TCast (strip tm).
Proof.
  reflexivity.
Qed.

(****
Lemma canonicalP_hom:
  forall t, optStripCanP (L2.term.canonicalP t) = canonicalP (strip t).
Proof.
  destruct t; intros; cbn; try reflexivity.
  destruct t1; cbn; try reflexivity.
Qed.
 ****)

Lemma tnth_hom:
 forall ts n, optStrip (L2.term.tnth n ts) = tnth n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed. 

Lemma tskipn_hom:
  forall ts n, optStrips (L2.term.tskipn n ts) = tskipn n (strips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.

Lemma tappend_hom:
  forall ts us,
    strips (L2.term.tappend ts us) = tappend (strips ts) (strips us).
Proof.
  induction ts; intros us; simpl. reflexivity.
  rewrite IHts. reflexivity.
Qed.

Lemma TApp_hom:
  forall fn arg args, ~ L2.term.isConstruct fn ->
    strip (L2.compile.TApp fn arg args) =
    TApp (strip fn) (strip arg) (strips args).
Proof.
  destruct fn; intros arg args h; try reflexivity.
  elim h. auto.
Qed.

Lemma isApp_hom:
  forall t,
    isApp (strip t) -> L2.term.isApp t.
Proof.
  destruct t; cbn; intros h;
  destruct h as [x0 [x1 [x2 h]]]; try discriminate; auto.     
  - destruct (etaExp_cnstr_Sanity' i n n0 n1 tnil).
    + rewrite h in H. destruct H as [y0 [y1 [y2 jy]]]. discriminate.
    + rewrite h in H. destruct H as [y0 [y1 jy]]. discriminate.
  - destruct p. discriminate.
Qed.

Lemma isLambda_hom:
  forall t,
    isLambda (strip t) ->
    L2.term.isLambda t \/ L2.term.isConstruct t \/  L2.term.isApp t.
Proof.
  intros t. functional induction (strip t); intros h;
  destruct h as [x0 [x1 jx]]; try discriminate.
  - left. auto.
  - right. right. auto.
  - right. left. auto.
Qed.

Lemma isFix_hom:
  forall t, isFix (strip t) -> L2.term.isFix t.
Proof.
  induction t; intros; simpl in *;
  try (destruct H as [x0 [x1 jx]]; discriminate); auto.
  - destruct t1; try (destruct H as [x0 [x1 jx]]; discriminate).
    assert (j:= etaExp_cnstr_sanity i n n0 n1 (tcons (strip t2) (strips t3))).
    destruct (n0 + n1 - tlength (tcons (strip t2) (strips t3))).
    + destruct j as [x0 [x1 [x2 jx]]]. rewrite jx in H.
      destruct H as [y0 [y1 jy]]. discriminate.
    + destruct j as [x0 [x1 jx]]. rewrite jx in H.
      destruct H as [y0 [y1 jy]]. discriminate.
  - assert (j:= etaExp_cnstr_sanity i n n0 n1 tnil).
    destruct (n0 + n1); cbn in j.
    + destruct j as [x0 [x1 [x2 jx]]]. rewrite jx in H.
      destruct H as [y0 [y1 jy]]. discriminate.
    + destruct j as [x0 [x1 jx]]. rewrite jx in H.
      destruct H as [y0 [y1 jy]]. discriminate.
  - destruct p. destruct H as [y0 [y1 jy]]. discriminate.
Qed.


Lemma L2WFapp_L2kWFapp:
  (forall t, L2.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L2.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ts, L2.term.WFappBs ts -> WFappBs (stripBs ts)) /\
  (forall ds, L2.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
  apply L2.term.WFappTrmsBrsDefs_ind; cbn; try constructor; auto; intros.
  - destruct fn; cbn; auto; try (constructor; try assumption; not_isApp).
    + apply etaExp_cnstr_pres_WFapp. constructor; assumption.
    + destruct p. constructor; try assumption. not_isApp.
  - apply etaExp_cnstr_pres_WFapp. constructor.
  - destruct m. constructor; try assumption.
Qed.

Lemma L2WFaEnv_L2kWFaEnv:
  forall p:environ L2Term, L2.program.WFaEnv p -> WFaEnv (stripEnv p).
Proof.
  induction 1; simpl; constructor.
  - inversion H; destruct ec; simpl; try discriminate; constructor.
    + apply (proj1 (L2WFapp_L2kWFapp)). assumption.
  - assumption.
  - apply stripEnv_pres_fresh. assumption.
Qed.

(***
Lemma WFapp_hom:
  (forall t, L2.term.WFapp t -> WFapp (strip t)) /\
  (forall ts, L2.term.WFapps ts -> WFapps (strips ts)) /\
  (forall ds, L2.term.WFappDs ds -> WFappDs (stripDs ds)).
Proof.
   apply L2.term.WFappTrmsDefs_ind; cbn; intros;
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

(***
Lemma mkApp_hom:
forall fn args, ~ L2.term.isApp fn ->
  strip (L2.term.mkApp fn args) = mkApp (strip fn) (strips args).
Proof.
  intros. destruct args.
  - rewrite L2.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident. reflexivity.
  - rewrite L2.term.mkApp_goodFn; try assumption. rewrite tcons_hom.
    assert (j: ~ isApp (strip fn)).
    { intros h. elim H. apply isApp_hom. assumption. }
    rewrite mkApp_goodFn; try assumption. destruct fn; cbn; try reflexivity.
    unfold strip in j.
    
  destruct args; try (reflexivity).
  - rewrite L2.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident.
    reflexivity.
  - destruct (L2.term.isApp_dec fn).
    + admit.
    + rewrite L2.term.mkApp_goodFn; try assumption.
      destruct (L2.term.isConstruct_dec fn).
      * { destruct H as [x0 [x1 [x2 [x3 jx]]]]. subst. cbn.
          destruct (etaExp_cnstr_Sanity'
                      x0 x1 x2 x3 (tcons (strip t) (strips args))).
          - destruct H as [y0 [y1 [y2 jy]]]. rewrite jy.
            destruct (etaExp_cnstr_Sanity' x0 x1 x2 x3 tnil).
            + destruct H as [z0 [z1 [z2 jz]]]. rewrite jz. cbn. rewrite <- jy.



              destruct (etaExp_cnstr_Sanity' x0 x1 x2 x3 tnil).
          
          assert (j:= etaExp_cnstr_Sanity
                        x0 x1 x2 x3 (tcons (strip t) (strips args))).
          rewrite TApp_hom. admit. ; try assumption.

    case_eq fn; intros; try reflexivity.
    cbn. rewrite <- tcons_hom. rewrite <- tappend_hom. reflexivity.
Qed.
***)

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

(*****************  broken from here  ************
Lemma instantiate_hom:
  (forall bod arg n, strip (L2.term.instantiate arg n bod) =
                     instantiate (strip arg) n (strip bod)) /\
  (forall bods arg n, strips (L2.term.instantiates arg n bods) =
                    instantiates (strip arg) n (strips bods)) /\
  (forall ds arg n, stripDs (L2.term.instantiateDefs arg n ds) =
                    instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L2.compile.TrmTrmsDefs_ind; intros; try (simpl; reflexivity).
  - simpl. destruct (lt_eq_lt_dec n n0); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n0 n)); try omega. cbn. reflexivity.
      * subst. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
    + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
  - cbn. rewrite H. reflexivity.
  - cbn. rewrite H. reflexivity.
  - cbn. rewrite H. reflexivity.
  - cbn. rewrite H. rewrite H0. reflexivity.
  - change (strip (L2.term.mkApp
                     (L2.term.instantiate arg n t)
                     (L2.compile.tcons (L2.term.instantiate arg n t0)
                                         (L2.term.instantiates arg n t1))) =
            instantiate (strip arg) n (strip (L2.compile.TApp t t0 t1))). 
    rewrite TApp_hom. 
    change
      (strip (L2.term.mkApp
                (L2.term.instantiate arg n t)
                (L2.compile.tcons (L2.term.instantiate arg n t0)
                                   (L2.term.instantiates arg n t1))) =
       (mkApp (instantiate (strip arg) n (strip t))
              (tcons (instantiate (strip arg) n (strip t0))
                     (instantiates (strip arg) n (strips t1))))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. 
    rewrite mkApp_hom. rewrite tcons_hom. reflexivity.
  - change (TCase p (strip (L2.term.instantiate arg n t0))
                  (stripDs (L2.term.instantiateDefs arg n d)) =
            (TCase p (instantiate (strip arg) n (strip t0))
                   (instantiateDefs (strip arg) n (stripDs d)))).
    rewrite H0. rewrite H1. reflexivity.
  - change (TFix (stripDs (L2.term.instantiateDefs
                             arg (n0 + L2.compile.dlength d) d)) n =
            (TFix (instantiateDefs
                     (strip arg) (n0 + dlength (stripDs d)) (stripDs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (strip (L2.term.instantiate arg n t))
                  (strips (L2.term.instantiates arg n t0)) =
            tcons (instantiate (strip arg) n (strip t))
                  (instantiates (strip arg) n (strips t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (dcons n (strip (L2.term.instantiate arg n1 t0)) n0
                  (stripDs (L2.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (strip arg) n1 (strip t0)) n0
                  (instantiateDefs (strip arg) n1 (stripDs d))).
    rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma whBetaStep_hom:
  forall bod arg args,
    strip (L2.term.whBetaStep bod arg args) =
    whBetaStep (strip bod) (strip arg) (strips args).
Proof.
  intros bod arg args.
  unfold L2.term.whBetaStep, whBetaStep.
  rewrite mkApp_hom. rewrite <- (proj1 instantiate_hom). reflexivity.
Qed.

(***
Lemma TConstruct_hom:
  forall i n args,
    strip (L2.compile.TConstruct i n args) = TConstruct i n args.
intros. simpl.  destruct i. reflexivity.
Qed.
***)

Lemma optStrip_match:
  forall x (f:L2Term -> L2Term) (g:Term -> Term), 
    (forall z, strip (f z) = g (strip z)) ->
    optStrip (match x with Some y => Some (f y) | None => None end) =
    match (optStrip x) with Some y => Some (g y) | None => None end.
induction x; intros f g h; simpl.
- rewrite h; reflexivity.
- reflexivity.
Qed.

Lemma whCaseStep_hom:
  forall n brs ts,
    optStrip (L2.term.whCaseStep n ts brs) =
    whCaseStep n (strips ts) (stripDs brs).
destruct n, brs; intros; simpl; try reflexivity.
- unfold whCaseStep. simpl. rewrite mkApp_hom. reflexivity.
- unfold whCaseStep. unfold L2.term.whCaseStep. cbn. 
  rewrite <- dnthBody_hom. destruct (compile.dnthBody n brs); simpl.
  + destruct p as [x0 x1]. cbn. rewrite mkApp_hom. reflexivity.
  + reflexivity.
Qed.

Lemma TFix_hom:
  forall defs n, strip (L2.compile.TFix defs n) = TFix (stripDs defs) n.
reflexivity.
Qed.

Lemma TProd_hom:
  forall nm ty bod,
    strip (L2.compile.TProd nm ty bod) = TProd nm (strip bod).
reflexivity.
Qed.

Lemma TLambda_hom:
  forall nm ty bod,
    strip (L2.compile.TLambda nm ty bod) = TLambda nm (strip bod).
reflexivity.
Qed.

Lemma TLetIn_hom:
  forall nm dfn ty bod,
    strip (L2.compile.TLetIn nm dfn ty bod) =
    TLetIn nm (strip dfn) (strip bod).
reflexivity.
Qed.

Lemma TCase_hom:
  forall n ty mch brs,
    strip (L2.compile.TCase n ty mch brs) =
    TCase n (strip mch) (stripDs brs).
reflexivity.
Qed.

Lemma fold_left_hom:
forall (F:L2Term -> nat -> L2Term) 
       (stripF:Term -> nat -> Term) (ns:list nat) (t:L2Term),
  (forall (s:L2Term) (n:nat), strip (F s n) = stripF (strip s) n) ->
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
    strip (L2.term.pre_whFixStep body dts args).
Proof.
  intros body dts args.
  destruct dts, args; unfold pre_whFixStep, L2.term.pre_whFixStep;
  simpl; rewrite mkApp_hom; try reflexivity.
  - rewrite (fold_left_hom _
          (fun (bod : Term) (ndx : nat) =>
                instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx)
                  0 bod)).
    + rewrite <- (dcons_hom _ L2.compile.prop).
      rewrite (proj1 instantiate_hom).
      rewrite <- dlength_hom. reflexivity. 
    + intros. rewrite (proj1 instantiate_hom). simpl. reflexivity.
  - rewrite (fold_left_hom _
            (fun (bod : Term) (ndx : nat) =>
         instantiate (TFix (dcons n (strip t0) n0 (stripDs dts)) ndx) 0 bod)).
    + rewrite dlength_hom. rewrite (proj1 instantiate_hom).
      rewrite tcons_hom. reflexivity.
    + intros. rewrite (proj1 instantiate_hom).
      rewrite <- (dcons_hom _ L2.compile.prop). simpl. reflexivity.
Qed.

Lemma tsplit_hom:
  forall ix arg args,
    optStrip_split (L2.term.tsplit ix arg args) =
    tsplit ix (strip arg) (strips args).
Proof.
  intros ix arg args.
  functional induction (L2.term.tsplit ix arg args); cbn; intros.
  - reflexivity.
  - destruct n. elim y. reflexivity.
  - destruct ls; cbn; reflexivity.
  - case_eq (tsplit m (strip t) (strips ts)); intros.
    + destruct s.
      assert (j0:= L2.term.tsplit_sanity m t ts). rewrite e1 in j0.
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
            Some (fst (fst z), strips (snd (fst z)), snd z).
intros. destruct z as [[z0 z1] z2]. cbn. reflexivity.
Qed.

Lemma WcbvEval_hom:
  forall p,
    (forall t t', L2.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L2.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (strips ts) (strips ts')).
Proof.
  intros p.
  apply L2.wcbvEval.WcbvEvalEvals_ind; intros; try reflexivity;
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
    + apply H0.
    + rewrite <- dnthBody_hom. rewrite e. reflexivity.
    + rewrite tlength_hom. assumption.
    + rewrite <- pre_whFixStep_hom in H1. eapply H1.
  - destruct (WcbvEvals_tcons_tcons H0) as [a' [args' j]]. rewrite j in H0.
    cbn. rewrite mkApp_hom. eapply wAppCong. try eassumption.
    + intros h. elim n. apply isLambda_hom. assumption.
    + intros h. elim n0. apply isFix_hom. assumption.
    + rewrite j. cbn in H0. assumption.
  - cbn. eapply wAppFixCong1; try eassumption.
    + rewrite <- dnthBody_hom. rewrite e. reflexivity.
    + rewrite tlength_hom. assumption. 
  - refine (wCase _ _ _ _ _ _ _); try eassumption.
    +

      
    * rewrite <- canonicalP_hom. rewrite e. reflexivity.
    * rewrite <- tskipn_hom. rewrite e0. reflexivity.
    * rewrite <- whCaseStep_hom. rewrite e1. reflexivity.
  - refine (wCaseCong _ _ _ _); try eassumption.
    + rewrite <- canonicalP_hom. rewrite e. reflexivity.
Qed.
Print Assumptions WcbvEval_hom.

(** WcbvEval_hom is nice, but it is stronger than necessary to prove 
*** certiL2_to_L2Correct (in instances.v).
**)
Corollary strip_pres_eval:
  forall (p:environ L2.compile.Term) (t tv:L2.compile.Term),
    L2.wcbvEval.WcbvEval p t tv ->
    exists stv, WcbvEval (stripEnv p) (strip t) stv.
Proof.
  intros. exists (strip tv). apply (proj1 (WcbvEval_hom _)).
  assumption.
Qed.

Corollary wcbvEval_hom:
  forall p n t t',
    L2.wcbvEval.wcbvEval p n t = Ret t' ->
    exists m, wcbvEval (stripEnv p) m (strip t) = Ret (strip t').
Proof.
  intros. 
  assert (j1:= proj1 (L2.wcbvEval.wcbvEval_WcbvEval p n) _ _ H).
  assert (k0:= proj1 (WcbvEval_hom p) _ _ j1).
  assert (j2:= @WcbvEval_wcbvEval (stripEnv p) (strip t) (strip t') k0).
  destruct j2 as [ny jny].
  exists ny. eapply jny. omega.
Qed.


Lemma Prf_strip_inv:
  forall s st, TProof st = strip s ->
              exists t, s = L2.compile.TProof t /\ st = strip t.
Proof.
  destruct s; simpl; intros h; try discriminate.
  intros. myInjection H. exists s. intuition.
Qed.
  
Lemma Lam_strip_inv:
  forall nm bod s, TLambda nm bod = strip s ->
   exists sty sbod, 
     (L2.compile.TLambda nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Prod_strip_inv:
  forall nm bod s, TProd nm bod = strip s ->
   exists sty sbod, 
     (L2.compile.TProd nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Cast_strip_inv:
  forall tm s, TCast tm = strip s ->
   exists stm sty, 
     (L2.compile.TCast stm sty) = s /\ tm = strip stm.
Proof.
  intros tm; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Construct_strip_inv:
  forall i n arty s,
    TConstruct i n arty = strip s -> L2.compile.TConstruct i n arty = s.
Proof.
  intros i n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Sort_strip_inv:
  forall srt s, TSort srt = strip s -> L2.compile.TSort srt = s.
Proof.
  intros srt. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Ind_strip_inv:
  forall i s, TInd i = strip s -> L2.compile.TInd i = s.
Proof.
  intros i. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Const_strip_inv:
  forall nm s, TConst nm = strip s -> L2.compile.TConst nm = s.
Proof.
  intros nm. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Fix_strip_inv:
  forall ds n s, TFix ds n = strip s ->
    exists sds, (L2.compile.TFix sds n) = s /\ ds = stripDs sds.
Proof.
  intros ds n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists d. intuition.
Qed.

Lemma App_strip_inv:
  forall fn arg args s, TApp fn arg args = strip s ->
    exists sfn sarg sargs,
      (L2.compile.TApp sfn sarg sargs) = s /\
      fn = strip sfn /\ arg = strip sarg /\ args = strips sargs.
Proof.
  intros fn arg args. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma LetIn_strip_inv:
  forall nm dfn bod s, TLetIn nm dfn bod = strip s ->
    exists sdfn sty sbod,
      (L2.compile.TLetIn nm sdfn sty sbod = s) /\
      dfn = strip sdfn /\ bod = strip sbod.
Proof.
  intros nm dfn bod s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, s3. intuition.
Qed.

Lemma Case_strip_inv:
  forall m mch brs s, TCase m mch brs = strip s ->
    exists sty smch sbrs, (L2.compile.TCase m sty smch sbrs = s) /\
              mch = strip smch /\ brs = stripDs sbrs.
Proof.
  intros m mch brs s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, d. intuition.
Qed.

Lemma tnil_strip_inv:
  forall ts, tnil = strips ts -> ts = L2.compile.tnil.
Proof.
  induction ts; intros; try reflexivity.
  - simpl in H. discriminate.
Qed.

Lemma tcons_strip_inv:
  forall t ts us, tcons t ts = strips us ->
    exists st sts, (L2.compile.tcons st sts = us) /\ 
                   t = strip st /\ ts = strips sts.
Proof.
  intros t ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, us. intuition.
Qed.

Lemma dcons_strip_inv:
  forall nm t m ts us, dcons nm t m ts = stripDs us ->
    exists ty st sts, (L2.compile.dcons nm ty st m sts = us) /\ 
                   t = strip st /\ ts = stripDs sts.
Proof.
  intros nm t m ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, t1, us. intuition.
Qed.

Lemma whCaseStep_Hom:
  forall n ts bs t,
    L2.term.whCaseStep n ts bs = Some t -> 
    whCaseStep n (strips ts) (stripDs bs) = Some (strip t).
Proof.
  intros n ts bs t h. rewrite <- whCaseStep_hom. rewrite <- optStrip_hom.
  apply f_equal. assumption.
Qed.

Definition excStrip (t:exception L2Term) : exception Term :=
  match t with
    | Exc str => Exc str
    | Ret t => Ret (strip t)
  end.


Theorem L2WcbvEval_sound_for_L2WcbvEval:
  forall (p:environ L2.compile.Term) (t:L2.compile.Term) (L2s:Term),
    WcbvEval (stripEnv p) (strip t) L2s ->
  forall s, L2.wcbvEval.WcbvEval p t s -> L2s = strip s.
Proof.
  intros. refine (WcbvEval_single_valued _ _).
  - eassumption.
  - apply WcbvEval_hom. assumption.
Qed.
Print Assumptions L2WcbvEval_sound_for_L2WcbvEval.


Lemma sound_and_complete:
  forall (p:environ L2.compile.Term) (t s:L2.compile.Term),
    L2.wcbvEval.WcbvEval p t s ->
    WcbvEval (stripEnv p) (strip t) (strip s).
Proof.
  intros p t s h. apply (proj1 (WcbvEval_hom p)). assumption.
Qed.

Lemma sac_complete:
  forall p t s, L2.wcbvEval.WcbvEval p t s ->
                WcbvEval (stripEnv p) (strip t) (strip s).
Proof.
  intros. apply sound_and_complete. assumption.
Qed.

Lemma sac_sound:
  forall p t s, L2.wcbvEval.WcbvEval p t s ->
  forall L2s, WcbvEval (stripEnv p) (strip t) L2s -> L2s = strip s.
Proof.
  intros p t s h1 L2s h2.
  apply (WcbvEval_single_valued h2). apply (sound_and_complete h1).
Qed. 
Print Assumptions sac_sound.

*******************************)