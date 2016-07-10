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

Require L1_5.L1_5.
Require Import L2.compile.
Require Import L2.term.
Require Import L2.program.
Require Import L2.wndEval.
Require Import L2.wcbvEval.
Require Import L2.wNorm.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L1_5Term := L1_5.compile.Term.
Definition L1_5Terms := L1_5.compile.Terms.
Definition L1_5Defs := L1_5.compile.Defs.

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
    stripEnv ((str, ec) :: p) = (str, (stripEc ec))::(stripEnv p).
induction p; destruct ec; try reflexivity.
Qed.

Lemma Lookup_hom:
 forall p s ec, L1_5.program.Lookup s p ec -> 
               Lookup s (stripEnv p) (stripEc ec).
induction 1; destruct t.
- change (Lookup s ((s, L2.compile.ecTrm (strip t)) :: (stripEnv p))
                    (L2.compile.ecTrm (strip t))).
  apply LHit.
- change (Lookup s ((s, L2.compile.ecTyp n (stripItyPack i)) :: (stripEnv p))                    (L2.compile.ecTyp n (stripItyPack i))).
  apply LHit.
- change (Lookup s ((s, L2.compile.ecAx) :: (stripEnv p)) ecAx).
  apply LHit.
- change (Lookup s2 ((s1, L2.compile.ecTrm (strip t)) :: (stripEnv p))
                     (stripEc ec)).
  apply LMiss; assumption.
- change (Lookup s2 ((s1, L2.compile.ecTyp n (stripItyPack i)) :: (stripEnv p))
                     (stripEc ec)).
  apply LMiss; assumption.
- change (Lookup s2 ((s1, L2.compile.ecAx) :: (stripEnv p))
                     (stripEc ec)).
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
  apply L1_5.term.WFappTrmsDefs_ind; simpl; intros; try (solve [constructor]);
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


(** The goal is to prove that if [wndEval.wndEval p t s] (unstripped),
*** then [wndEval (stripEnv p) (strip t) (strip s)] (stripped).
*** However the unstripped language has steps in type fields where the 
*** stripped language can make no step.  Thus we need "reflexive closure",
*** allowing null steps for the stripped language.
**)
Inductive wndEvalRC: environ -> Term -> Term -> Prop :=
| wERCrfl: forall p t, wndEvalRC p t t
| wERCstep: forall p t s, wndEval p t s -> wndEvalRC p t s.

Inductive wndEvalsRC: environ -> Terms -> Terms -> Prop :=
| wEsRCrfl: forall p ts, wndEvalsRC p ts ts
| wEsRCstep: forall p ts ss, wndEvals p ts ss -> wndEvalsRC p ts ss.

Inductive WcbvEvalRC: environ -> Term -> Term -> Prop :=
| WcERCrfl: forall p t, WcbvEvalRC p t t
| WcERCstep: forall p t s, WcbvEval p t s -> WcbvEvalRC p t s.

Inductive WcbvEvalsRC: environ -> Terms -> Terms -> Prop :=
| WcEsRCrfl: forall p ts, WcbvEvalsRC p ts ts
| WcEsRCstep: forall p ts ss, WcbvEvals p ts ss -> WcbvEvalsRC p ts ss.
Hint Constructors WcbvEvalRC WcbvEvalsRC.

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
    change (Lookup nm (stripEnv p) (stripEc L1_5.compile.ecAx)).
    apply Lookup_hom. assumption.
  - refine (wConst _ _); try eassumption.
    unfold LookupDfn. unfold L1_5.program.LookupDfn in *.
    change (Lookup nm (stripEnv p) (stripEc (L1_5.compile.ecTrm t))).
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

 
Theorem L1wcbvEval_strip_L2WcbvEval:
  forall p, L1_5.program.WFaEnv p ->
    (forall t s, L1_5.wcbvEval.WcbvEval p t s -> L1_5.term.WFapp t ->
          WcbvEval (stripEnv p) (strip t) (strip s)) /\
    (forall ts ss, L1_5.wcbvEval.WcbvEvals p ts ss -> L1_5.term.WFapps ts ->
                   WcbvEvals (stripEnv p) (strips ts) (strips ss)) /\
    (forall ds es, L1_5.wcbvEval.WcbvDEvals p ds es -> L1_5.term.WFappDs ds ->
                   WcbvDEvals (stripEnv p) (stripDs ds) (stripDs es)).
intros p hp.
apply L1_5.wcbvEval.WcbvEvalEvals_ind; intros; try (solve [constructor]).
- simpl. eapply wCast. inversion H0. intuition.
- simpl. eapply wFix. inversion H0. intuition.
- simpl. eapply wAx. unfold L1_5.program.LookupAx in l. unfold LookupAx.
  apply (Lookup_hom l).
- simpl. eapply wConst.
  + apply LookupDfn_hom. eassumption.
  + apply H. assert (j:= L1_5.program.Lookup_pres_WFapp hp l). inversion_Clear j.
    assumption.
- rewrite TApp_hom. inversion H2. subst. eapply wAppLam.
  + rewrite TLambda_hom in H. apply H. assumption.
  + apply H0. constructor; assumption.
  + rewrite whBetaStep_hom in H1. apply H1.
    destruct (L1_5.wcbvEval.WcbvEvals_tcons_tcons' w0).
    apply L1_5.term.whBetaStep_pres_WFapp. 
    * assert (j:= proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp) _ _ w H7).
      inversion j. assumption.
    * eapply (proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp)); eassumption.
    * eapply (proj1 (proj2 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp)));
      eassumption.
- simpl. inversion H1. subst. eapply wLetIn.
  + apply H. assumption.
  + rewrite (proj1 instantiate_hom) in H0. apply H0.
    apply L1_5.term.instantiate_pres_WFapp; try assumption.
    * apply (proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp) _ _ w). assumption.
- inversion_Clear H2.
  assert (j:= proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp) _ _ w H7). 
  inversion_Clear j.
  rewrite TApp_hom. eapply wAppFix.
  + rewrite TFix_hom in H. apply H. assumption.
  + rewrite <- dnthBody_hom. rewrite e. cbn. reflexivity. 
  + rewrite <- tcons_hom. rewrite <- tcons_hom. apply H0.
    constructor; assumption.
  + rewrite <- tcons_hom. rewrite pre_whFixStep_hom. apply H1.
    assert (j: L1_5.term.WFapps (L1_5.compile.tcons arg' args')).
    { refine (proj1 (proj2 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp)) _ _ w0 _).
      constructor; assumption. }
    inversion_Clear j.
    refine (L1_5.term.pre_whFixStep_pres_WFapp _ _ _); try eassumption.
    * refine (L1_5.term.dnthBody_pres_WFapp _ _ _); eassumption.
    * constructor; assumption.
- inversion_Clear H1. rewrite TApp_hom. rewrite TApp_hom.
  apply wAppAx; intuition.
- inversion_Clear H1. rewrite TApp_hom. rewrite TApp_hom.
  apply wAppCnstr; intuition.
- inversion_Clear H1. rewrite TApp_hom. rewrite TApp_hom.
  apply wAppInd; intuition.  
- inversion_Clear H1. rewrite TCase_hom. eapply wCase.
  + simpl in H. apply H. assumption.  HERE
  + rewrite <- tnil_hom. rewrite <- whCaseStep_hom. rewrite <- optStrip_hom.
    apply f_equal. eassumption.
  + apply H0. refine (L1_5.term.whCaseStep_pres_WFapp H7 _ _ e). constructor.
- inversion_Clear H1. rewrite TCase_hom. simpl in H. eapply wCasen.
  + apply H. assumption.
  + rewrite <- tcons_hom. rewrite <- tskipn_hom. rewrite e. 
    rewrite optStrips_hom. reflexivity.
  + rewrite <- whCaseStep_hom. rewrite e0. rewrite optStrip_hom. reflexivity.
  + apply H0. refine (L1_5.term.whCaseStep_pres_WFapp H7 _ _ e0). 
    refine (L1_5.term.tskipn_pres_WFapp _ _ e).
    assert (j: L1_5.term.WFapp (L1_5.term.TApp (L1_5.term.TConstruct i n) arg args)).
    { refine (proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp) _ _ _ _).
      try apply mch. eassumption. eassumption. }
    inversion_clear j. constructor; assumption.
- inversion_Clear H2. simpl.  apply wCaseAx; simpl in H; intuition.   
- inversion_Clear H1. rewrite tcons_hom. rewrite tcons_hom.
  constructor; intuition.
- inversion_Clear H2. rewrite dcons_hom. rewrite dcons_hom.
  constructor; intuition.
Qed.

Print Assumptions L1wcbvEval_strip_L2WcbvEval.

Lemma Prf_strip_inv:
  forall s, TProof = strip s -> s = L1_5.term.TProof.
Proof.
  destruct s; simpl; intros h; try discriminate. reflexivity.
Qed.
  
Lemma Lam_strip_inv:
  forall nm bod s, TLambda nm bod = strip s ->
   exists sty sbod, 
     (L1_5.term.TLambda nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Prod_strip_inv:
  forall nm bod s, TProd nm bod = strip s ->
   exists sty sbod, 
     (L1_5.term.TProd nm sty sbod) = s /\ bod = strip sbod.
Proof.
  intros nm bod; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2. intuition. 
Qed.

Lemma Cast_strip_inv:
  forall tm s, TCast tm = strip s ->
   exists stm ck sty, 
     (L1_5.term.TCast stm ck sty) = s /\ tm = strip stm.
Proof.
  intros tm; destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, c, s2. intuition. 
Qed.

Lemma Construct_strip_inv:
  forall i n s, TConstruct i n = strip s -> L1_5.term.TConstruct i n = s.
Proof.
  intros i n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Sort_strip_inv:
  forall srt s, TSort srt = strip s -> L1_5.term.TSort srt = s.
Proof.
  intros srt. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Ind_strip_inv:
  forall i s, TInd i = strip s -> L1_5.term.TInd i = s.
Proof.
  intros i. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Const_strip_inv:
  forall nm s, TConst nm = strip s -> L1_5.term.TConst nm = s.
Proof.
  intros nm. destruct s; simpl; intros h; try discriminate.
  - myInjection h. reflexivity.
Qed.

Lemma Fix_strip_inv:
  forall ds n s, TFix ds n = strip s ->
    exists sds, (L1_5.term.TFix sds n) = s /\ ds = stripDs sds.
Proof.
  intros ds n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists d. intuition.
Qed.

Lemma App_strip_inv:
  forall fn arg args s, TApp fn arg args = strip s ->
    exists sfn sarg sargs,
      (L1_5.term.TApp sfn sarg sargs) = s /\
      fn = strip sfn /\ arg = strip sarg /\ args = strips sargs.
Proof.
  intros fn arg args. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma LetIn_strip_inv:
  forall nm dfn bod s, TLetIn nm dfn bod = strip s ->
    exists sdfn sty sbod,
      (L1_5.term.TLetIn nm sdfn sty sbod = s) /\
      dfn = strip sdfn /\ bod = strip sbod.
Proof.
  intros nm dfn bod s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, s3. intuition.
Qed.

Lemma Case_strip_inv:
  forall m mch brs s, TCase m mch brs = strip s ->
    exists sty smch sbrs, (L1_5.term.TCase m sty smch sbrs = s) /\
              mch = strip smch /\ brs = strips sbrs.
Proof.
  intros m mch brs s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma tnil_strip_inv:
  forall ts, tnil = strips ts -> ts = L1_5.term.tnil.
Proof.
  induction ts; intros; try reflexivity.
  - simpl in H. discriminate.
Qed.

Lemma tcons_strip_inv:
  forall t ts us, tcons t ts = strips us ->
    exists st sts, (L1_5.term.tcons st sts = us) /\ 
                   t = strip st /\ ts = strips sts.
Proof.
  intros t ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, us. intuition.
Qed.

Lemma dcons_strip_inv:
  forall nm t m ts us, dcons nm t m ts = stripDs us ->
    exists ty st sts, (L1_5.term.dcons nm ty st m sts = us) /\ 
                   t = strip st /\ ts = stripDs sts.
Proof.
  intros nm t m ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, t1, us. intuition.
Qed.

(***
Lemma WcbvDEvals_pres_Defs:
  forall p dts edts,
    wcbvEval.WcbvDEvals p dts edts -> stripDs dts = stripDs edts.
Proof.
  induction dts; intros edts h; inversion h.
  - reflexivity.
  - simpl. apply f_equal4; try reflexivity.
    apply IHdts. assumption.
Qed.
 ***)

Lemma whCaseStep_Hom:
  forall n ts bs t,
    L1_5.term.whCaseStep n ts bs = Some t -> 
    whCaseStep n (strips ts) (strips bs) = Some (strip t).
Proof.
  intros n ts bs t h. rewrite <- whCaseStep_hom. rewrite <- optStrip_hom.
  apply f_equal. assumption.
Qed.

(** Proof suggested by Zoe. **)
Theorem L2WcbvEval_L1WcbvEval:
  forall L2p p, L2p = stripEnv p -> L1_5.program.WFaEnv p ->
    (forall L2t L2s, WcbvEval L2p L2t L2s ->
     forall t, L2t = strip t -> L1_5.term.WFapp t ->
           forall s, L1_5.wcbvEval.WcbvEval p t s -> L2s = strip s).
Proof.
  intros L2p p hp1 hp2 L2t L2s h1 t h2 ht s hs.
  apply (WcbvEval_single_valued h1).
  rewrite hp1. rewrite h2.
  apply (proj1 (L1wcbvEval_strip_L2WcbvEval hp2)). apply hs. apply ht.
Qed.
    
Theorem L2WcbvEval_L1WcbvEval':  (** old proof **)
  forall L2p p, L2p = stripEnv p -> L1_5.program.WFaEnv p ->
    (forall L2t L2s, WcbvEval L2p L2t L2s ->
     forall t, L2t = strip t -> L1_5.term.WFapp t ->
           forall s, L1_5.wcbvEval.WcbvEval p t s -> L2s = strip s) /\
    (forall L2ts L2ss, WcbvEvals L2p L2ts L2ss ->
     forall ts, L2ts = strips ts -> L1_5.term.WFapps ts ->
           forall ss, L1_5.wcbvEval.WcbvEvals p ts ss -> L2ss = strips ss) /\
    (forall L2ts L2ss, WcbvDEvals L2p L2ts L2ss ->
     forall ts, L2ts = stripDs ts -> L1_5.term.WFappDs ts ->
           forall ss, L1_5.wcbvEval.WcbvDEvals p ts ss -> L2ss = stripDs ss).
Proof.
  intros L2p p hp1 hp2. apply WcbvEvalEvals_ind; simpl; intros.
  - rewrite (Prf_strip_inv _ H) in H1. inversion H1. reflexivity.
  - destruct (Lam_strip_inv _ H) as [t0 [t1 [jtl jtr]]]. subst.
    inversion H1. simpl. reflexivity.
  - destruct (Prod_strip_inv _ H) as [t0 [t1 [jtl jtr]]]. subst.
    inversion H1. simpl. reflexivity.
  - destruct (Cast_strip_inv _ H0) as [y0 [y1 [y2 [jt0 jt1]]]].
    eapply H. 
    + eassumption.
    + rewrite <- jt0 in H1. inversion_Clear H1. assumption.
    + rewrite <- jt0 in H2. inversion H2. assumption.
  - destruct (Construct_strip_inv _ H). inversion H1. reflexivity.
  - destruct (Ind_strip_inv _ H). inversion_Clear H1. reflexivity.
  - destruct (Sort_strip_inv _ H). inversion H1. reflexivity.
  - destruct (Fix_strip_inv _ H0) as [x [j1 j2]]. subst. 
    inversion_Clear H2. simpl. apply f_equal2; try reflexivity.
    inversion_Clear H1. refine (H _ _ _ _ _ ); trivial.
  - rewrite <- (Const_strip_inv _ H) in H1. inversion_Clear H1.
    + reflexivity.
    + unfold LookupAx in l. unfold L1_5.program.LookupDfn in H3.
      assert (j:= Lookup_hom H3). simpl in j.
      assert (j1:= Lookup_single_valued l j). discriminate.
  - unfold LookupDfn in l.
    rewrite <- (Const_strip_inv _ H0) in H2. inversion_Clear H2.
    + unfold L1_5.program.LookupAx in H4.
      assert (j:= Lookup_hom H4). simpl in j.
      assert (j1:= Lookup_single_valued l j). discriminate.
    + unfold L1_5.program.LookupDfn in H4.
      assert (j:= Lookup_hom H4). simpl in j.
      assert (j1:= Lookup_single_valued l j). injection j1. intros.
      apply (H _ H2); try assumption.
      assert (j3:= L1_5.program.Lookup_pres_WFapp hp2 H4).
      inversion j3. assumption.
  - destruct (App_strip_inv _ H2) as [x1 [x2 [x3 [x4 [x5 [x6 x7]]]]]].
    clear H2. subst. inversion_Clear H3. inversion_Clear H4.
    + refine (H1 (L1_5.term.whBetaStep bod0 a1'0 x3) _ _ _ _); try assumption.
      * rewrite whBetaStep_hom. apply f_equal3; try reflexivity.
        { assert (j0:= H _ eq_refl H8 (L1_5.term.TLambda nm0 ty bod0) H6).
          simpl in j0. myInjection j0. reflexivity. }
        { assert (j1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H12 H9).
          apply (WcbvEval_single_valued w0 j1). }
      * { refine (L1_5.term.whBetaStep_pres_WFapp _ _ _); try assumption.
          - assert
              (j:= proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp2) _ _ H6 H8).
            inversion j; assumption. 
          - apply (proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp2) _ _ H12 H9). }
    + assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H6 H8).
      simpl in j. assert (k:= WcbvEval_single_valued w j). discriminate.
    + assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H6 H8).
      assert (k:= WcbvEval_single_valued w j).
      destruct (Lam_strip_inv _ k) as [y1 [y2 [l1 j2]]]. discriminate.
    + assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H6 H8).
      simpl in j. assert (k:= WcbvEval_single_valued w j). discriminate.
    + assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H6 H8).
      simpl in j. assert (k:= WcbvEval_single_valued w j). discriminate.
  - destruct (LetIn_strip_inv _ H1) as [x0 [x1 [x2 [j1 [j2 j3]]]]].
    clear H1. rewrite <- j1 in H2. inversion_Clear H2.
    inversion_clear H3.
    eapply H0.
    + erewrite H.
      * rewrite <- (proj1 (instantiate_hom)). apply f_equal. reflexivity.
      * reflexivity.
      * assumption.
      * eassumption.
    + assert (j0: L1_5.term.WFapp dfn'0).
      { eapply (proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp2)); eassumption. }
      assert (j1: WcbvEval (stripEnv p)
                           (strip (L1_5.term.instantiate dfn'0 0 x2))
                           (strip s0)).
      { apply (proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H2).
        apply (L1_5.term.instantiate_pres_WFapp); assumption. }
      rewrite (proj1 instantiate_hom) in j1.
      apply (L1_5.term.instantiate_pres_WFapp). assumption.
      eapply (proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp2)); eassumption.
    + assumption.
  - destruct (App_strip_inv _ H1) as [x1 [x2 [x3 [x4 [x5 [x6 x7]]]]]].
    clear H1. subst. inversion H2. inversion H3; subst; clear H2 H3.
    + assert (j1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H13 H7).
      simpl in j1. assert (k:= WcbvEval_single_valued w j1). discriminate.
    + refine (H0 (L1_5.term.whFixStep dts0 m0 (L1_5.term.tcons x2 x3)) _ _ _ _);
      try assumption.
      rewrite whFixStep_hom. erewrite (f_equal2 whFixStep). reflexivity.
      * assert (j0:= H _ eq_refl H7 (L1_5.term.TFix dts0 m0) H13).
        simpl in j0. myInjection j0. reflexivity.
      * assert (j1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H13 H7).
        simpl in j1. injection (WcbvEval_single_valued w j1). intros.
        assumption.
      * { refine (L1_5.term.whFixStep_pres_WFapp _ _ _); try assumption.
          - assert (j:=proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp2) _ _ H13 H7).
            inversion j; assumption.
          - constructor; assumption. }
    + assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H13 H7).
      assert (k:= WcbvEval_single_valued w j). simpl in k. discriminate.
    + assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H13 H7).
      assert (k:= WcbvEval_single_valued w j). simpl in k. discriminate.
    + assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H13 H7).
      assert (k:= WcbvEval_single_valued w j). simpl in k. discriminate.
  - destruct (App_strip_inv _ H2) as [x1 [x2 [x3 [x4 [x5 [x6 x7]]]]]].
    clear H2. subst. inversion H3. inversion H4; subst; clear H3 H4.
    + assert (j1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
       simpl in j1. assert (k:= WcbvEval_single_valued w j1). discriminate.
    + assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
      simpl in j. assert (k:= WcbvEval_single_valued w j). discriminate.
    + simpl. apply (f_equal3 TApp).
      * assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
        simpl in j. apply (WcbvEval_single_valued w). assumption.
      * refine (H0 _ _ _ _ _); try reflexivity; try assumption.
      * refine (H1 _ _ _ _ _); try reflexivity; try assumption.
    + simpl. apply (f_equal3 TApp).
      * assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
        simpl in j. apply (WcbvEval_single_valued w). assumption.
      * refine (H0 _ _ _ _ _); try reflexivity; try assumption.
      * refine (H1 _ _ _ _ _); try reflexivity; try assumption.
    + simpl. apply (f_equal3 TApp).
      * assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
        simpl in j. apply (WcbvEval_single_valued w). assumption.
      * refine (H0 _ _ _ _ _); try reflexivity; try assumption.
      * refine (H1 _ _ _ _ _); try reflexivity; try assumption.
  - destruct (App_strip_inv _ H2) as [x1 [x2 [x3 [x4 [x5 [x6 x7]]]]]].
    clear H2. subst. inversion H3. inversion H4; subst; clear H3 H4.
    + assert (j1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
       simpl in j1. assert (k:= WcbvEval_single_valued w j1). discriminate.
    + assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
      simpl in j. assert (k:= WcbvEval_single_valued w j). discriminate.
    + simpl. apply (f_equal3 TApp).
      * assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
        simpl in j. apply (WcbvEval_single_valued w). assumption.
      * refine (H0 _ _ _ _ _); try reflexivity; try assumption.
      * refine (H1 _ _ _ _ _); try reflexivity; try assumption.
    + simpl. apply (f_equal3 TApp).
      * assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
        simpl in j. apply (WcbvEval_single_valued w). assumption.
      * refine (H0 _ _ _ _ _); try reflexivity; try assumption.
      * refine (H1 _ _ _ _ _); try reflexivity; try assumption.
    + simpl. apply (f_equal3 TApp).
      * assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
        simpl in j. apply (WcbvEval_single_valued w). assumption.
      * refine (H0 _ _ _ _ _); try reflexivity; try assumption.
      * refine (H1 _ _ _ _ _); try reflexivity; try assumption.
  - destruct (App_strip_inv _ H2) as [x1 [x2 [x3 [x4 [x5 [x6 x7]]]]]].
    clear H2. subst. inversion H3. inversion H4; subst; clear H3 H4.
    + assert (j1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
       simpl in j1. assert (k:= WcbvEval_single_valued w j1). discriminate.
    + assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
      simpl in j. assert (k:= WcbvEval_single_valued w j). discriminate.
    + simpl. apply (f_equal3 TApp).
      * assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
        simpl in j. apply (WcbvEval_single_valued w). assumption.
      * refine (H0 _ _ _ _ _); try reflexivity; try assumption.
      * refine (H1 _ _ _ _ _); try reflexivity; try assumption.
    + simpl. apply (f_equal3 TApp).
      * assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
        simpl in j. apply (WcbvEval_single_valued w). assumption.
      * refine (H0 _ _ _ _ _); try reflexivity; try assumption.
      * refine (H1 _ _ _ _ _); try reflexivity; try assumption.
    + simpl. apply (f_equal3 TApp).
      * assert (j:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H14 H8).
        simpl in j. apply (WcbvEval_single_valued w). assumption.
      * refine (H0 _ _ _ _ _); try reflexivity; try assumption.
      * refine (H1 _ _ _ _ _); try reflexivity; try assumption.
  - destruct (Case_strip_inv _ H1) as [x0 [x1 [x2 [j0 [j1 j2]]]]].
    clear H1. subst. inversion_Clear H2. inversion_Clear H3.
    + assert (k0: n = n0).
      { assert (j0:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H10 H6).
        simpl in j0. assert (j1:= WcbvEval_single_valued w j0). myInjection j1.
        reflexivity. }
      subst.
      assert (k1:= whCaseStep_Hom  _ _ _ H11). simpl in k1.
      rewrite e in k1. myInjection k1. clear k1.
      refine (H0 _ _ _ _ _); try reflexivity; try assumption.
      refine (L1_5.term.whCaseStep_pres_WFapp _ _ _ H11); try assumption.
      auto.
    + assert (j0:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H7 H6).
      simpl in j0.
      assert (j1:= WcbvEval_single_valued w j0). discriminate.
    + assert (j0:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H10 H6).
      assert (j1:= WcbvEval_single_valued w j0). discriminate.
 - destruct (Case_strip_inv _ H1) as [x0 [x1 [x2 [j0 [j1 j2]]]]].
    clear H1. subst. inversion_Clear H2. inversion_Clear H3.
    + simpl in e. myInjection e. clear e.
      assert (k1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H10 H6).
      simpl in k1.
      assert (k2:= WcbvEval_single_valued w k1). discriminate.
    + assert (k1:= proj1 (L1_5.wcbvEval.wcbvEval_pres_WFapp hp2) _ _ H7 H6).
      inversion_Clear k1. clear H4 H5.
      assert (j0:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H7 H6).
      simpl in j0.
      assert (k3:= WcbvEval_single_valued w j0). myInjection k3. clear k3.
      assert (k0: L1_5.term.WFapp cs0).
      { refine (L1_5.term.whCaseStep_pres_WFapp _ _ _ H12); try assumption.
        refine (L1_5.term.tskipn_pres_WFapp _ _ H11).
        constructor; try assumption. }
      refine (H0 _ _ _ _ H13); try assumption.
      assert (k1: ts = strips ts0).
      { rewrite <- tcons_hom in e.  rewrite <- tskipn_hom in e.
        rewrite H11 in e. rewrite optStrips_hom in e. myInjection e.
        reflexivity. }
      subst. rewrite <- whCaseStep_hom in e0. rewrite H12 in e0.
      rewrite optStrip_hom in e0. myInjection e0.  reflexivity.
    + assert (k1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H10 H6).
      simpl in k1. assert (k:= WcbvEval_single_valued w k1). discriminate.
  - destruct (Case_strip_inv _ H1) as [x0 [x1 [x2 [j0 [j1 j2]]]]].
    clear H1. subst. inversion_Clear H2. inversion_Clear H3.
    + assert (k1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H10 H6).
      simpl in k1. assert (k:= WcbvEval_single_valued w k1). discriminate.
    + assert (k1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H7 H6).
      simpl in k1. assert (k:= WcbvEval_single_valued w k1). discriminate.
    + assert (k1:= proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ H10 H6).
      assert (k2:= proj1 (proj2 (L1wcbvEval_strip_L2WcbvEval hp2)) _ _ H12 H8).
      simpl in k1.
      assert (k:= WcbvEval_single_valued w k1). myInjection k. clear k w.
      assert (k:= WcbvEvals_single_valued w0 k2). 
      rewrite TCase_hom. simpl. apply f_equal3; try reflexivity. assumption.
  - rewrite (tnil_strip_inv _ H) in H1. inversion H1. reflexivity. 
  - destruct (tcons_strip_inv _ H1) as [x0 [x1 [j1 [j2 j3]]]]. subst.
    clear H1. inversion_Clear H2; inversion_Clear H3. simpl.
    eapply f_equal2.
    + refine (WcbvEval_single_valued w _).
      refine (proj1 (L1wcbvEval_strip_L2WcbvEval hp2) _ _ _ _); assumption.
    + refine (H0 _ _ _ _ H8). reflexivity. assumption.
  - assert (j:= proj2 (proj2 (WcbvEval_hom p)) _ _ H1).
    rewrite <- H in j. inversion_Clear j. reflexivity.
  - destruct (dcons_strip_inv _ H1) as [x0 [x1 [x2 [j1 [j2 j3]]]]]. subst.
    inversion_Clear H2. inversion_Clear H3. simpl.
    eapply f_equal4; try reflexivity.
    + refine (H _ _ _ _ _); try reflexivity; try assumption.
    + refine (H0 _ _ _ _ _); try reflexivity; try assumption.
Qed.

Print Assumptions L2WcbvEval_L1WcbvEval.

(** add w.r.t. L1 wndEval **)
Lemma L2WcbvEval_sound_for_L1wndEval:
  forall L2p p, L2p = stripEnv p -> L1_5.program.WFaEnv p ->
    (forall L2t L2s, WcbvEval L2p L2t L2s ->
     forall t, L2t = strip t -> L1_5.term.WFapp t ->
           forall s, L1_5.wcbvEval.WcbvEval p t s ->
                     L2s = strip s /\ L1_5.wndEval.wndEvalRTC p t s).
Proof.
  intros L2p p hp1 hp2 L2t L2s h0 t h1 h2 s h3; split.
  - refine (L2WcbvEval_L1WcbvEval hp1 hp2 h0 h1 h2 h3).
  - apply (proj1 (L1_5.wcbvEval.WcbvEval_wndEvalRTC hp2) t s h3 h2).
Qed.
Print Assumptions L2WcbvEval_sound_for_L1wndEval.


(*** unstrip: replace every missing type field with [prop]  ***)
Function unstrip (t:Term) : L1_5Term :=
  match t with
    | TProof => L1_5.term.TProof
    | TRel n => L1_5.term.TRel n
    | TSort s => L1_5.term.TSort s
    | TCast t => L1_5.term.TCast (unstrip t) Cast L1_5.term.prop
    | TProd nm bod => L1_5.term.TProd nm L1_5.term.prop (unstrip bod)
    | TLambda nm bod => L1_5.term.TLambda nm L1_5.term.prop (unstrip bod)
    | TLetIn nm dfn bod =>
           L1_5.term.TLetIn nm (unstrip dfn) L1_5.term.prop (unstrip bod)
    | TApp fn arg args =>
           L1_5.term.TApp (unstrip fn) (unstrip arg) (unstrips args)
    | TConst nm => L1_5.term.TConst nm
    | TInd i => L1_5.term.TInd i
    | TConstruct i m => L1_5.term.TConstruct i m
    | TCase n mch brs =>
           L1_5.term.TCase n L1_5.term.prop (unstrip mch) (unstrips brs)
    | TFix ds n => L1_5.term.TFix (unstripDs ds) n
  end
with unstrips (ts:Terms) : L1_5Terms := 
  match ts with
    | tnil => L1_5.term.tnil
    | tcons t ts => L1_5.term.tcons (unstrip t) (unstrips ts)
  end
with unstripDs (ts:Defs) : L1_5Defs := 
  match ts with
    | dnil => L1_5.term.dnil
    | dcons nm t m ds =>
           L1_5.term.dcons nm L1_5.term.prop (unstrip t) m (unstripDs ds)
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

Definition optUnstrip (t:option Term) : option L1_5Term :=
  match t with
    | None => None
    | Some t => Some (unstrip t)
  end.
Definition optUnstrips (ts:option Terms) : option L1_5Terms :=
  match ts with
    | None => None
    | Some ts => Some (unstrips ts)
  end.

Lemma optUnstrip_unhom: forall y, optUnstrip (Some y) = Some (unstrip y).
induction y; simpl; reflexivity.
Qed.
Lemma optUnstrips_unhom: forall y, optUnstrips (Some y) = Some (unstrips y).
induction y; simpl; reflexivity.
Qed.

Function unstripCnstrs (cs:list Cnstr) : list L1_5.program.Cnstr :=
  match cs with
    | nil => nil
    | cons (mkCnstr str arity) cs =>
        cons (L1_5.program.mkCnstr str arity) (unstripCnstrs cs)
  end.
Function unstripItyPack (its:itypPack) : L1_5.program.itypPack :=
  match its with
    | nil => nil
    | (mkItyp str itps) :: itpacks =>
         (L1_5.program.mkItyp str (unstripCnstrs itps)) ::
                           unstripItyPack itpacks
  end.
Function unstripEc (ec:envClass) : L1_5.program.envClass :=
  match ec with
    | ecTrm t => L1_5.program.ecTrm (unstrip t)
    | ecTyp npars itp => L1_5.program.ecTyp npars (unstripItyPack itp)
    | ecAx => L1_5.program.ecAx
  end.
Fixpoint unstripEnv (p:environ) : L1_5.program.environ :=
  match p with
    | nil => nil
    | cons (nm, ec) q => cons (nm, (unstripEc ec)) (unstripEnv q)
  end.

Lemma stripItyCnstrs_leftInv_unstripCnstrs:
  forall cs, stripCnstrs (unstripCnstrs cs) = cs.
Proof.
  induction cs.
  - reflexivity.
  - destruct a. simpl. rewrite IHcs. reflexivity.
Qed.

Lemma stripItyPack_leftInv_unstripItyPack:
  forall its, stripItyPack (unstripItyPack its) = its.
Proof.
  induction its.
  - simpl. reflexivity.
  - destruct a. simpl. rewrite IHits.
    rewrite stripItyCnstrs_leftInv_unstripCnstrs.
    reflexivity.
Qed.

Lemma stripEc_leftInv_unstripEc:
  forall ec, stripEc (unstripEc ec) = ec.
Proof.
  induction ec.
  - simpl. rewrite (proj1 strip_leftInv_unstrip). reflexivity.
  - simpl. destruct i.
    + reflexivity.
    + simpl. destruct i. simpl. 
      rewrite stripItyCnstrs_leftInv_unstripCnstrs.
      rewrite stripItyPack_leftInv_unstripItyPack.
      reflexivity.
  - simpl. reflexivity.
Qed.

Lemma stripEnv_leftInv_unstripEnv:
  forall (p:environ), stripEnv (unstripEnv p) = p.
Proof.
  induction p.
  - reflexivity.
  - destruct a. simpl. rewrite IHp. destruct e.
    + simpl. rewrite (proj1 strip_leftInv_unstrip). reflexivity.
    + simpl; destruct i.
      * simpl. reflexivity.
      * rewrite stripItyPack_leftInv_unstripItyPack.
        reflexivity.
    + simpl. reflexivity.
Qed.

Lemma L2WFapp_L1WFapp:
  (forall t, WFapp t -> L1_5.term.WFapp (unstrip t)) /\
  (forall ts, WFapps ts -> L1_5.term.WFapps (unstrips ts)) /\
  (forall ds, WFappDs ds -> L1_5.term.WFappDs (unstripDs ds)).
Proof.
  apply WFappTrmsDefs_ind; simpl; intros; try (solve [constructor]);
  try (solve [constructor; try assumption; constructor]).
  - constructor; try assumption.
    + intros h. elim H. destruct h as [x0 [x1 [x2 j]]].
      assert (k:= f_equal strip j).
      rewrite (proj1 (strip_leftInv_unstrip)) in k. rewrite k. simpl.
      exists (strip x0), (strip x1), (strips x2). reflexivity.
Qed.

Lemma Lookup_unhom:
 forall nm p ec, 
   Lookup nm p ec -> L1_5.program.Lookup nm (unstripEnv p) (unstripEc ec).
Proof.
  induction 1; destruct t; simpl.
  - constructor.
  - constructor.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
  - constructor; assumption.
Qed.

Lemma tappend_unhom:
  forall ts us,
    unstrips (tappend ts us) = L1_5.term.tappend (unstrips ts) (unstrips us).
 Proof.
   induction ts; intros us; simpl; try reflexivity.
   - rewrite IHts. reflexivity.
Qed.

Lemma mkApp_unhom:
  forall fn args,
    unstrip (mkApp fn args) = L1_5.term.mkApp (unstrip fn) (unstrips args).
Proof.
  induction fn; induction args; simpl; try reflexivity.
  - rewrite tappend_tnil. rewrite L1_5.term.tappend_tnil. reflexivity.
  - rewrite tappend_unhom. simpl. reflexivity.
Qed.

Lemma dlength_unhom:
  forall ds, dlength ds = L1_5.term.dlength (unstripDs ds).
Proof.
  induction ds; simpl.
  - reflexivity.
  - rewrite IHds. reflexivity.
Qed.

Lemma tcons_unhom:
  forall t ts,
    unstrips (tcons t ts) = L1_5.term.tcons (unstrip t) (unstrips ts).
Proof.
  reflexivity.
Qed.

Lemma dcons_unhom:
  forall nm bod rarg ds,
    unstripDs (dcons nm bod rarg ds) =
    L1_5.term.dcons nm L1_5.term.prop (unstrip bod) rarg (unstripDs ds).
reflexivity.
Qed.

Lemma instantiate_unhom: 
  (forall bod tin ni,
    unstrip (instantiate tin ni bod) =
    L1_5.term.instantiate (unstrip tin) ni (unstrip bod)) /\
  (forall bods tin ni,
    unstrips (instantiates tin ni bods) =
    L1_5.term.instantiates (unstrip tin) ni (unstrips bods)) /\
  (forall ds tin ni,
    unstripDs (instantiateDefs tin ni ds) =
    L1_5.term.instantiateDefs (unstrip tin) ni (unstripDs ds)).
Proof.
  apply TrmTrmsDefs_ind; intros;
  try (solve [unfold instantiate, L1_5.term.instantiate; simpl; reflexivity]).
  - destruct (lt_eq_lt_dec n ni) as [[j1|j2]|j3];
    unfold instantiate, L1_5.term.instantiate; simpl.
    + rewrite (proj1 (nat_compare_gt _ _) j1). reflexivity.
    + subst. rewrite (proj2 (nat_compare_eq_iff ni ni)); try reflexivity.
      rewrite mkApp_unhom. simpl. reflexivity.
    + rewrite (proj1 (nat_compare_lt _ _) j3). reflexivity.
  - change (unstrip (TCast (instantiate tin ni t)) =
            L1_5.term.TCast
              (L1_5.term.instantiate (unstrip tin) ni (unstrip t))
              Cast L1_5.term.prop).
    rewrite <- H. simpl. reflexivity.
  - change (unstrip (TProd n (instantiate tin (S ni) t)) =
            L1_5.term.TProd n L1_5.term.prop
                          (L1_5.term.instantiate (unstrip tin) (S ni)
                                               (unstrip t))).
    rewrite <- H. simpl. reflexivity.
  - change (unstrip (TLambda n (instantiate tin (S ni) t)) =
            L1_5.term.TLambda n L1_5.term.prop
                            (L1_5.term.instantiate (unstrip tin) (S ni)
                                                 (unstrip t))).
    rewrite <- H. simpl. reflexivity.
  - change (unstrip (TLetIn n (instantiate tin ni t)
                            (instantiate tin (S ni) t0)) =
            L1_5.term.TLetIn n (L1_5.term.instantiate
                                (unstrip tin) ni (unstrip t))
                           L1_5.term.prop
                           (L1_5.term.instantiate
                              (unstrip tin) (S ni) (unstrip t0))).
    rewrite <- H. rewrite <- H0. simpl. reflexivity.
  - change (unstrip (mkApp (instantiate tin ni t)
                           (tcons (instantiate tin ni t0)
                                  (instantiates tin ni t1))) =
            L1_5.term.mkApp (L1_5.term.instantiate (unstrip tin) ni (unstrip t))
                          (L1_5.term.tcons 
                             (L1_5.term.instantiate 
                                (unstrip tin) ni (unstrip t0))
                             (L1_5.term.instantiates
                                (unstrip tin) ni (unstrips t1)))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. simpl.
    rewrite mkApp_unhom. reflexivity.
  - change (unstrip (TCase p (instantiate tin ni t)
                           (instantiates tin ni t0)) =
            L1_5.term.TCase p L1_5.term.prop
                          (L1_5.term.instantiate (unstrip tin) ni (unstrip t))
                          (L1_5.term.instantiates (unstrip tin) ni
                                                (unstrips t0))).
    rewrite <- H. rewrite <- H0. simpl. reflexivity.
  - change (unstrip (TFix (instantiateDefs tin (ni + dlength d) d) n) =
            L1_5.term.TFix
              (L1_5.term.instantiateDefs (unstrip tin)
                                       (ni + L1_5.term.dlength (unstripDs d))
                                       (unstripDs d)) n).
    rewrite <- H. rewrite dlength_unhom. simpl. reflexivity.
  - change (unstrips (tcons (instantiate tin ni t)
                            (instantiates tin ni t0)) =
            L1_5.term.tcons (L1_5.term.instantiate (unstrip tin) ni (unstrip t))
                          (L1_5.term.instantiates (unstrip tin) ni
                                                (unstrips t0))).
    rewrite <- H. rewrite <- H0. simpl. reflexivity.
  - change (unstripDs (dcons n (instantiate tin ni t) n0
                            (instantiateDefs tin ni d)) =
            L1_5.term.dcons n L1_5.term.prop
                          (L1_5.term.instantiate (unstrip tin) ni (unstrip t))
                          n0
                          (L1_5.term.instantiateDefs (unstrip tin) ni
                                                   (unstripDs d))).
    rewrite <- H. rewrite <- H0. simpl. reflexivity.
Qed.

Lemma whBetaStep_unhom:
  forall bod a1 args,
    unstrip (whBetaStep bod a1 args) =
    L1_5.term.whBetaStep (unstrip bod) (unstrip a1) (unstrips args).
Proof.
  intros bod a1 args. unfold whBetaStep, L1_5.term.whBetaStep.
  rewrite <- (proj1 instantiate_unhom). rewrite <- mkApp_unhom. reflexivity.
Qed.

Lemma dnthBody_unhom:
  forall m ds,
   unstrip (dnthBody m ds) = L1_5.term.dnthBody m (unstripDs ds).
Proof.
  induction m; induction ds; try intuition.
  - simpl. intuition.
Qed.

Lemma fold_left_unhom:
forall (F:Term -> nat -> Term) 
       (unstripF:L1_5Term -> nat -> L1_5Term) (ns:list nat) (t:Term),
  (forall (s:Term) (n:nat), unstrip (F s n) = unstripF (unstrip s) n) ->
  unstrip (fold_left F ns t) = fold_left unstripF ns (unstrip t).
induction ns; intros t h.
- intuition.
- simpl. rewrite IHns.
  + rewrite h. reflexivity.
  + assumption.
Qed.

Lemma pre_whFixStep_unhom:
  forall body dts args,
    unstrip (pre_whFixStep body dts args) = 
    L1_5.term.pre_whFixStep (unstrip body) (unstripDs dts) (unstrips args).
Proof. 
  intros body dts args.
  destruct dts, args; unfold pre_whFixStep, L1_5.term.pre_whFixStep;
  simpl; rewrite mkApp_unhom; try reflexivity.
  - rewrite (fold_left_unhom _ 
         (fun (bod : L1_5.term.Term) (ndx : nat) =>
            L1_5.term.instantiate
              (L1_5.term.TFix (unstripDs (dcons n t n0 dts)) ndx) 0 bod)).
    + rewrite <- dcons_unhom. rewrite (proj1 instantiate_unhom). simpl.
      rewrite dlength_unhom. reflexivity.
    + intros. simpl. rewrite (proj1 instantiate_unhom). simpl.
      reflexivity.
  - rewrite (fold_left_unhom _ 
         (fun (bod : L1_5.term.Term) (ndx : nat) =>
            L1_5.term.instantiate
              (L1_5.term.TFix (unstripDs (dcons n t n0 dts)) ndx) 0 bod)).
    + rewrite dlength_unhom. rewrite (proj1 instantiate_unhom).
      rewrite dcons_unhom. rewrite tcons_unhom. reflexivity.
    + intros. rewrite (proj1 instantiate_unhom).
      rewrite dcons_unhom. reflexivity.
Qed.

Lemma whFixStep_unhom:
  forall dts m args,
    unstrip (whFixStep dts m args) =
    L1_5.term.whFixStep (unstripDs dts) m (unstrips args).
Proof.
  intros dts m args.
  unfold L1_5.term.whFixStep, whFixStep.
  case_eq (dnthBody m dts); intros;
  try (solve [rewrite pre_whFixStep_unhom;
              rewrite <- dnthBody_unhom; rewrite H; reflexivity]).
Qed.

Lemma tnth_unhom:
 forall ts n, optUnstrip (tnth n ts) = L1_5.term.tnth n (unstrips ts).
Proof.
  induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed. 

Lemma whCaseStep_unhom:
forall n ts brs,
  optUnstrip (whCaseStep n ts brs) = 
  L1_5.term.whCaseStep n (unstrips ts) (unstrips brs).
Proof.
  destruct n, brs; intros; simpl; try reflexivity.
  - unfold whCaseStep. simpl. rewrite mkApp_unhom. reflexivity.
  - unfold whCaseStep. unfold L1_5.term.whCaseStep. simpl.
    rewrite <- tnth_unhom. destruct (tnth n brs); simpl.
    + rewrite mkApp_unhom. reflexivity.
    + reflexivity. 
Qed.

Lemma tskipn_unhom:
  forall ts n, optUnstrips (tskipn n ts) = L1_5.term.tskipn n (unstrips ts).
induction ts; simpl; intros n; case n; try reflexivity; trivial.
Qed.

Lemma isApp_unhom:
  forall t, L1_5.term.isApp (unstrip t) -> isApp t.
Proof.
  induction t; simpl; unfold L1_5.term.isApp; intros h;
  destruct h as [x0 [x1 [x2 j]]]; try discriminate.
  exists t1, t2, t3. reflexivity.
  Qed.
  
Lemma isLambda_unhom:
  forall t, L1_5.term.isLambda (unstrip t) -> isLambda t.
Proof.
  induction t; simpl; unfold L1_5.term.isLambda; intros h;
  destruct h as [x0 [x1 [x2 j]]]; try discriminate.
  exists n, t. reflexivity.
Qed.

Lemma isFix_unhom:
  forall t, L1_5.term.isFix (unstrip t) -> isFix t.
Proof.
  induction t; simpl; unfold L1_5.term.isFix; intros h;
  destruct h as [x0 [x1 j]]; try discriminate.
  exists d, n. reflexivity.
Qed.
  
(** very weak notion of soundness using unstrip **)
Theorem unstrip_L2WcbvEval_L1WcbvEval:
  forall p,
    (forall t s, WcbvEval p t s ->
     L1_5.wcbvEval.WcbvEval (unstripEnv p) (unstrip t) (unstrip s)) /\
    (forall ts ss, WcbvEvals p ts ss ->
     L1_5.wcbvEval.WcbvEvals (unstripEnv p) (unstrips ts) (unstrips ss)) /\
    (forall ts ss, WcbvDEvals p ts ss ->
     L1_5.wcbvEval.WcbvDEvals (unstripEnv p) (unstripDs ts) (unstripDs ss)).
Proof.
  intros p.
  apply WcbvEvalEvals_ind; simpl; intros; try (solve [constructor]);
  try (solve [constructor; constructor]);
  try (solve [constructor; assumption]).
  - eapply L1_5.wcbvEval.wAx.
    unfold LookupAx in l. unfold L1_5.program.LookupAx.
    apply (Lookup_unhom l).
  - eapply L1_5.wcbvEval.wConst; try eassumption.
    apply (Lookup_unhom l).
  - eapply L1_5.wcbvEval.wAppLam; try eassumption.
    rewrite <- whBetaStep_unhom. assumption.
  - eapply L1_5.wcbvEval.wLetIn; try eassumption.
    rewrite <- (proj1 instantiate_unhom). assumption.
  - eapply L1_5.wcbvEval.wAppFix; try eassumption.
    rewrite <- tcons_unhom. rewrite <- whFixStep_unhom.
    apply f_equal. assumption.
  - eapply L1_5.wcbvEval.wCase0; try eassumption.
    + change
        (L1_5.term.whCaseStep n (unstrips tnil) (unstrips brs) =
         Some (unstrip cs)).
      rewrite <- whCaseStep_unhom. rewrite <- optUnstrip_unhom.
      apply f_equal. assumption.
  - refine (L1_5.wcbvEval.wCasen _ _ _ _ _ _ H0); try eassumption.
    + rewrite <- tcons_unhom. rewrite <- tskipn_unhom.
      rewrite e. rewrite <- optUnstrips_unhom. reflexivity.
    + rewrite <- whCaseStep_unhom. rewrite <- optUnstrip_unhom.
      apply f_equal. assumption.
  - eapply (L1_5.wcbvEval.wCaseAx); try assumption.
    apply (L1_5.wcbvEval.wSort).
  - constructor. constructor. assumption. assumption.
Qed.

Lemma use_unstrip:
 forall p, exists pp, p = stripEnv pp /\
    (forall t s, WcbvEval p t s ->
         exists tt ss, L1_5.wcbvEval.WcbvEval pp tt ss /\
                    t = strip tt /\ s = strip ss) /\
    (forall ts ss, WcbvEvals p ts ss ->
         exists tts sss, L1_5.wcbvEval.WcbvEvals pp tts sss /\
                    ts = strips tts /\ ss = strips sss).
Proof.
  intros p. exists (unstripEnv p). split.
  - rewrite stripEnv_leftInv_unstripEnv. reflexivity.
  - split.
    + intros t s hpts. exists (unstrip t), (unstrip s). split.
      { apply (proj1 (unstrip_L2WcbvEval_L1WcbvEval p)). assumption. }
      { split; rewrite (proj1 strip_leftInv_unstrip); reflexivity. }
    + intros ts ss hpts. exists (unstrips ts), (unstrips ss). split.
      { apply (proj2 (unstrip_L2WcbvEval_L1WcbvEval p)). assumption. }
      { split; rewrite (proj1 (proj2 strip_leftInv_unstrip)); reflexivity. }
Qed.

Print Assumptions use_unstrip.


(**** below here scratch ****
Goal
  forall (q:environ), WFaEnv q ->
     forall p1, q = stripEnv p1 -> forall p2, q = stripEnv p2 ->
  (forall (t x:Term), WcbvEval q t x -> 
      forall t1, t = strip t1 -> forall t2, t = strip t2 -> 
     forall s1 s2, L1_5.wcbvEval.WcbvEval p1 t1 s1 ->
            L1_5.wcbvEval.WcbvEval p2 t2 s2 -> strip s1 = strip s2) /\
  (forall (ts xs:Terms), WcbvEvals q ts xs -> 
     forall t1s, ts = strips t1s -> forall t2s, ts = strips t2s -> 
     forall s1s s2s, L1_5.wcbvEval.WcbvEvals p1 t1s s1s ->
            L1_5.wcbvEval.WcbvEvals p2 t2s s2s -> strips s1s = strips s2s).
Proof.
Admitted.
(***********
  intros q hq p1 hp1 p2 hp2.
  apply WcbvEvalEvals_ind; intros.
  - destruct (Lam_strip_inv _ H) as [x1 [y1 [j1 k1]]]. clear H.
    destruct (Lam_strip_inv _ H0) as [x2 [y2 [j2 k2]]]. clear H0.
    subst.
    refine (WcbvEval_single_valued _ _).
    inversion H1. subst.
    refine (proj1 (L1wcbvEval_strip_L2WcbvEval _) _ _ _ _).


     (proj1 (L1wcbvEval_strip_L2WcbvEval _)).


    refine (proj1 (L1wcbvEval_strip_L2WcbvEval _) _ _ _ _).



Qed.

***********)



Theorem L2wcbvEval_strip_L1WcbvEval:
  forall pp, WFaEnv pp -> forall p, pp = stripEnv p ->
    (forall (tt ss:Term), WcbvEval pp tt ss -> WFapp tt ->
     forall (t:L1_5Term), tt = strip t -> 
       exists s:L1_5Term, ss = strip s /\ L1_5.wcbvEval.WcbvEval p t s)  /\
    (forall tts sss, WcbvEvals pp tts sss -> WFapps tts ->
     forall ts, tts = strips ts ->
       exists ss:L1_5Terms, sss = strips ss /\ L1_5.wcbvEval.WcbvEvals p ts ss).
Proof.


Theorem L2wcbvEval_strip_L1WcbvEval:
  forall pp, WFaEnv pp -> forall p, pp = stripEnv p ->
    (forall (tt ss:Term), WcbvEval pp tt ss -> WFapp tt ->
     forall (t:L1_5Term), tt = strip t -> 
       exists s:L1_5Term, ss = strip s /\ L1_5.wcbvEval.WcbvEval p t s)  /\
    (forall tts sss, WcbvEvals pp tts sss -> WFapps tts ->
     forall ts, tts = strips ts ->
       exists ss:L1_5Terms, sss = strips ss /\ L1_5.wcbvEval.WcbvEvals p ts ss).
Proof.
  intros pp hpp p hp. apply WcbvEvalEvals_ind; intros.
  - destruct (Lam_strip_inv H0 _) as [x0 [x1 [j0 j1]]]. subst.
    exists (L1_5.term.TLambda nm L1_5.term.prop x1). intuition.
    apply L1_5.wcbvEval.wLam.


    destruct (Lam_strip_inv _ H1) as [y0 [y1 [k0 k1]]].
    subst. simpl in *. apply L1_5.wcbvEval.wLam.

rewrite H1 in H0.


(*************
Lemma wndEval_types_irrelevant:
  forall p,
    (forall t s, L1_5.wndEval.wndEval p t s ->
          wndEvalRC (stripEnv p) (strip t) (strip s)) /\
    (forall ts ss, L1_5.wndEval.wndEvals p ts ss ->
          wndEvalsRC (stripEnv p) (strips ts) (strips ss)).
intros p. apply L1_5.wndEval.wndEvalEvals_ind; intros.
- apply wERCstep. constructor. apply LookupDfn_hom. assumption.
- apply wERCstep. simpl. rewrite whBetaStep_hom. apply sBeta.
- apply wERCstep. simpl. rewrite (proj1 (instantiate_hom )).
  apply sLetIn.
- apply wERCstep. rewrite TCase_hom. apply sCase0.
  assert (j: optStrip (L1_5.term.whCaseStep n L1_5.term.tnil brs) =
             optStrip (Some s)).
  apply f_equal. assumption.
  simpl in j. rewrite <- j. rewrite whCaseStep_hom. reflexivity.
- apply wERCstep. simpl. eapply sCasen.
  rewrite <- tcons_hom. rewrite <- tskipn_hom. rewrite e. reflexivity.
  rewrite <- whCaseStep_hom. rewrite e0. reflexivity.
- apply wERCstep. rewrite TApp_hom. rewrite TFix_hom. apply sFix.
  assert (j: optStrip (L1_5.term.whFixStep dts m (L1_5.term.tcons arg args)) = 
             optStrip (Some s)).
  apply f_equal. assumption.
  simpl in j. rewrite <- j. rewrite whFixStep_hom. reflexivity.
  intros h. simpl in h. destruct h as [x0 [x1 [x2 j]]]. discriminate.
- simpl. apply wERCrfl.
- rewrite mkApp_hom. rewrite tcons_hom. rewrite TApp_hom.

- assert (j:= L1_5.term.mkApp_isApp r arg args).
  destruct j as [x0 [x1 [x2 k]]]. rewrite k.
  simpl.
  inversion H. 
  + rewrite mkApp_goodFn. HERE

- rewrite mkApp_hom. rewrite tcons_hom. (* rewrite TApp_hom. *)
  inversion H.
  + rewrite mkApp_goodFn. simpl.
    * constructor. rewrite TApp_hom. constructor.
    * intros h. elim n. apply (proj1 (isApp_hom _)). assumption.
  + apply wERCstep. apply sAppFn; assumption. 
- rewrite TApp_hom. rewrite TApp_hom.
  inversion_clear H. constructor.
  + apply wERCstep; apply sAppArg; assumption. 
- rewrite TApp_hom. rewrite TApp_hom. inversion_clear H. constructor.
  + apply wERCstep. apply sAppArgs. assumption. 
    (* no step for TProd or TLambda in stripped language *)
- rewrite TProd_hom. rewrite TProd_hom. apply wERCrfl.
- rewrite TLambda_hom. rewrite TLambda_hom. apply wERCrfl.
- rewrite TLetIn_hom. rewrite TLetIn_hom. apply wERCrfl.
- rewrite TLetIn_hom. rewrite TLetIn_hom. inversion_clear H. constructor.
  + apply wERCstep. apply sLetInDef. assumption.
- rewrite TCase_hom. rewrite TCase_hom. inversion_clear H. constructor.
  + apply wERCrfl.
- rewrite TCase_hom. rewrite TCase_hom. inversion_clear H. constructor.
  + apply wERCstep. apply sCaseArg. assumption.
- rewrite TCase_hom. rewrite TCase_hom. inversion_clear H. constructor.
  + apply wERCstep. apply sCaseBrs. assumption.
- rewrite tcons_hom. rewrite tcons_hom. inversion_clear H. constructor.
  + apply wEsRCstep. apply saHd. assumption.
- rewrite tcons_hom. rewrite tcons_hom. inversion_clear H. constructor.
  + apply wEsRCstep. apply saTl. assumption.
Qed.
***********************)

***)