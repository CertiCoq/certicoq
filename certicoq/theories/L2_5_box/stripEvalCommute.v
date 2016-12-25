
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import L2.L2.
Require Import L2_5.compile.
Require Import L2_5.term.
Require Import L2_5.program.
Require Import L2_5.wndEval.
Require Import L2_5.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2Term := L2.compile.Term.
Definition L2Terms := L2.compile.Terms.
Definition L2Defs := L2.compile.Defs.
Definition strip := L2Term_Term.
Definition strips := L2Terms_Terms.
Definition stripDs := L2Defs_Defs.
Definition stripEnv := L2Env_Env.
Definition stripEc := L2EC_EC.

Definition optStrip (t:option L2Term) : option Term :=
  match t with
    | None => None
    | Some t => Some (strip t)
  end.
Definition optL2Terms_Terms (ts:option L2Terms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (L2Terms_Terms ts)
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
                             | Some (n, t, m) => Some (n, L2Terms_Terms t, m)
                           end.

Lemma optStrip_hom: forall y, optStrip (Some y) = Some (strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optL2Terms_Terms_hom: forall y, optL2Terms_Terms (Some y) = Some (L2Terms_Terms y).
induction y; simpl; reflexivity.
Qed.
Lemma optStripDnth_hom:
  forall y n, optStripDnth (Some (y, n)) = Some (strip y, n).
induction y; simpl; reflexivity.
Qed.
Lemma optStripCanP_hom:
  forall y n m, optStripCanP (Some (n, y, m)) = Some (n, L2Terms_Terms y, m).
induction y; simpl; reflexivity.
Qed.
                              
Lemma Lookup_hom:
  forall (p:environ L2.compile.Term) s ec, Lookup s p ec -> Lookup s (L2Env_Env p) (L2EC_EC ec).
Proof.
  induction 1; destruct t.
  - change (Lookup s ((s, ecTrm (strip t)) :: (L2Env_Env p))
                   (ecTrm (strip t))).
    apply LHit.
  - cbn. apply LHit.
  - change (Lookup s2 ((s1, ecTrm (strip t)) :: (L2Env_Env p))
                   (L2EC_EC ec)).
    apply LMiss; assumption.
  - cbn. apply LMiss; assumption.
Qed.

Lemma lookup_hom:
  forall p nm ec,
    lookup nm p = Some ec -> lookup nm (stripEnv p) = Some (L2EC_EC ec).
Proof.
  intros p nm ec h. apply Lookup_lookup.
  apply Lookup_hom. apply (lookup_Lookup _ _ h).
Qed.
  
Lemma lookup_hom_None:
  forall p nm,
    lookup nm p = None -> lookup nm (L2Env_Env p) = None.
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
  forall t ts, L2Terms_Terms (L2.compile.tcons t ts) =
               tcons (strip t) (L2Terms_Terms ts).
reflexivity.
Qed.

Lemma tnil_hom: L2Terms_Terms L2.compile.tnil = tnil.
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

Lemma tappend_hom:
  forall ts us,
    L2Terms_Terms (L2.term.tappend ts us) =
    tappend (L2Terms_Terms ts) (L2Terms_Terms us).
induction ts; intros us; simpl. reflexivity.
rewrite IHts. reflexivity.
Qed.

Lemma TApp_hom:
  forall fn arg args,
    strip (L2.compile.TApp fn arg args) =
    TApp (strip fn) (strip arg) (strips args).
induction fn; intros arg args; try reflexivity.
Qed.


(*******************
Lemma isApp_hom:
  forall t, isApp (strip t) -> L2.term.isApp t.
Proof.
  destruct t; cbn; intros h;
  destruct h as [x0 [x1 [x2 h]]]; try discriminate. 
  - exists t1, t2, t3. reflexivity.
  - destruct p as [[y0 y1] y2]. destruct y2.
    + discriminate.
    + 
    destruct t.
Qed.

Lemma mkApp_hom:
forall fn args,
  strip (L2.term.mkApp fn args) = mkApp (strip fn) (L2Terms_Terms args).
Proof.
  destruct args; try (reflexivity).
  - rewrite L2.term.mkApp_tnil_ident. rewrite mkApp_tnil_ident.
    reflexivity.
  - destruct fn; try reflexivity.
    + change (TApp (strip fn1) (strip fn2)
                   (strips (L2.term.tappend t0 (L2.compile.tcons t args))) =
              TApp (strip fn1) (strip fn2)
                   (tappend (strips t0) (tcons (strip t) (strips args)))).
      rewrite <- tcons_hom. rewrite <- tappend_hom. reflexivity.
    + rewrite L2.term.mkApp_goodFn. rewrite tcons_hom.
      rewrite mkApp_goodFn. rewrite TApp_hom. reflexivity.
      * { induction fn; unfold strip;  
          intros h; destruct h as [x0 [x1 [x2 jx]]]; cbn in jx;
          destruct p as [[y0 y1] y2]; try discriminate.
          - induction t0; cbn in jx.
            + discriminate.
            + cbn in jx. 
            
      * { intros h. destruct h as [x0 [x1 [x2 jx]]]. cbn in jx.
          destruct p as [[i k] ks]. destruct fn; cbn in jx; try discriminate.
          - admit.
          -
  -
      
      cbn. rewrite tappend_hom. L2Terms_Terms. cbn. rewrite <- tcons_hom. rewrite <- tappend_hom. reflexivity.


    destruct fn; cbn.
    rewrite L1g.term.tappend_tnil. reflexivity.
  - destruct fn; cbn; try reflexivity.
  - destruct fn; cbn; try reflexivity.
  - rewrite tappend_tnil. rewrite L2.term.tappend_tnil. reflexivity.
  -
  
  - rewrite <- tcons_hom. rewrite <- tappend_hom. reflexivity.
Qed.

  intros fn args. functional induction (L2.term.mkApp fn args).
  -  cbn.
  

Lemma instantiate_hom:
  (forall bod arg n, strip (L2.term.instantiate arg n bod) =
                     instantiate (strip arg) n (strip bod)) /\
    (forall bods arg n, L2Terms_Terms (L2.term.instantiates arg n bods) =
                    instantiates (strip arg) n (L2Terms_Terms bods)) /\
    (forall ds arg n, stripDs (L2.term.instantiateDefs arg n ds) =
                      instantiateDefs (strip arg) n (stripDs ds)).
Proof.
  apply L2.compile.TrmTrmsDefs_ind; intros; try (simpl; reflexivity).
  - simpl. destruct (lt_eq_lt_dec n n0); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n0 n)); try omega. cbn. reflexivity.
      * subst n. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
        rewrite L2.term.mkApp_tnil_ident. reflexivity.
    + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
  - admit.
  - cbn. rewrite H. reflexivity.
  - cbn. rewrite H. reflexivity.
  - cbn. rewrite H. rewrite H0. reflexivity.
   - change (strip (L2.term.mkApp
                     (L2.term.instantiate arg n t)
                     (L2.compile.tcons (L2.term.instantiate arg n t0)
                                         (L2.term.instantiates arg n t1))) =
            instantiate (strip arg) n (strip (L2.compile.TApp t t0 t1))). 
Check TApp_hom. 
    change
      (strip (L2.term.mkApp
                (L2.term.instantiate arg n t)
                (L2.compile.tcons (L2.term.instantiate arg n t0)
                                   (L2.term.instantiates arg n t1))) =
       (mkApp (instantiate (strip arg) n (strip t))
              (tcons (instantiate (strip arg) n (strip t0))
                     (instantiates (strip arg) n (L2Terms_Terms t1))))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. 
    Check mkApp_hom. rewrite tcons_hom. reflexivity.
  - change (TCase p (strip (L2.term.instantiate arg n t0))
                  (L2Terms_Terms (L2.term.instantiates arg n t1)) =
            (TCase p (instantiate (strip arg) n (strip t0))
                   (instantiates (strip arg) n (L2Terms_Terms t1)))).
    rewrite H0. rewrite H1. reflexivity.
  - change (TFix (stripDs (L2.term.instantiateDefs
                             arg (n0 + L2.compile.dlength d) d)) n =
            (TFix (instantiateDefs
                     (strip arg) (n0 + dlength (stripDs d)) (stripDs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (strip (L2.term.instantiate arg n t))
                  (L2Terms_Terms (L2.term.instantiates arg n t0)) =
            tcons (instantiate (strip arg) n (strip t))
                  (instantiates (strip arg) n (L2Terms_Terms t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (dcons n (strip (L2.term.instantiate arg n1 t0)) n0
                  (stripDs (L2.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (strip arg) n1 (strip t0)) n0
                  (instantiateDefs (strip arg) n1 (stripDs d))).
    rewrite H0. rewrite H1. reflexivity.
Qed.



Lemma WcbvEval_hom:
  forall p,
    (forall t t', L2.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L2.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (L2Terms_Terms ts) (strips ts')).
Proof.
  intros p.
  apply L2.wcbvEval.WcbvEvalEvals_ind; intros; try reflexivity;
  try (solve[ constructor; intuition]).  
  - cbn. destruct t; cbn; try (try constructor; assumption).
  - cbn. econstructor; try eassumption.
    eapply (lookupDfn_hom). assumption.
(*************
  - destruct (L2.term.isApp_dec t).
    + destruct i as [x0 [x1 [x2 jx]]]. subst t. 
      cbn. econstructor. eapply H. intros h. discriminate.
    + cbn. destruct t; cbn; try (solve[eapply H; intros k; discriminate]).
      
    + unfold isProof in H1. rewrite H1 in H0. cbn in H0.
    
    destruct H0 as [u ju]. subst t. cbn. inversion_Clear w.
**********)
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
    * rewrite <- canonicalP_hom. rewrite e. reflexivity.
    * rewrite <- tskipn_hom. rewrite e0. reflexivity.
    * rewrite <- whCaseStep_hom. rewrite e1. reflexivity.
  - refine (wCaseCong _ _ _ _); try eassumption.
    + rewrite <- canonicalP_hom. rewrite e. reflexivity.
Qed.
Print Assumptions WcbvEval_hom.

****************************)