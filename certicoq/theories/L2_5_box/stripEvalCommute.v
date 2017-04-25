
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Setoids.Setoid.
Require Import Omega.

Require Import L2k.L2k.
Require Import L2_5.compile.
Require Import L2_5.term.
Require Import L2_5.program.
Require Import L2_5.wcbvEval.

Local Open Scope string_scope.
Local Open Scope bool.
Local Open Scope list.
Set Implicit Arguments.

Definition L2kTerm := L2k.compile.Term.
Definition L2kTerms := L2k.compile.Terms.
Definition L2kDefs := L2k.compile.Defs.
Definition strip := L2kTerm_Term.
Definition strips := L2kTerms_Terms.
Definition stripDs := L2kDefs_Defs.
Definition stripEnv := L2kEnv_Env.
Definition stripEc := L2kEC_EC.

Lemma isApp_strip_TApp:
  forall s1 s2 s3, isApp (strip (L2k.compile.TApp s1 s2 s3)).
Proof.
  intros s1 s2 s3.
  change (isApp (mkApp (strip s1) (tcons (strip s2) (strips s3)))).
  apply (mkApp_isApp (strip s1) (strip s2) (strips s3)).
Qed.                          

Definition optStrip (t:option L2kTerm) : option Term :=
  match t with
    | None => None
    | Some t => Some (strip t)
  end.
Definition optL2kTerms_Terms (ts:option L2kTerms) : option Terms :=
  match ts with
    | None => None
    | Some ts => Some (L2kTerms_Terms ts)
  end.
Definition optStripDnth (b: option (L2kTerm * nat)) : option (Term * nat) :=
                           match b with
                             | None => None
                             | Some (t, n) => Some (strip t, n)
                           end.
Definition optStripCanP
           (b: option (nat * L2kTerms * nat)): option (nat * Terms * nat) :=
                           match b with
                             | None => None
                             | Some (n, t, m) => Some (n, L2kTerms_Terms t, m)
                           end.

Lemma optStrip_hom: forall y, optStrip (Some y) = Some (strip y).
induction y; simpl; reflexivity.
Qed.
Lemma optL2kTerms_Terms_hom: forall y, optL2kTerms_Terms (Some y) = Some (L2kTerms_Terms y).
induction y; simpl; reflexivity.
Qed.
Lemma optStripDnth_hom:
  forall y n, optStripDnth (Some (y, n)) = Some (strip y, n).
induction y; simpl; reflexivity.
Qed.
Lemma optStripCanP_hom:
  forall y n m, optStripCanP (Some (n, y, m)) = Some (n, L2kTerms_Terms y, m).
induction y; simpl; reflexivity.
Qed.
                              
Lemma Lookup_hom:
  forall (p:environ L2k.compile.Term) s ec, Lookup s p ec -> Lookup s (L2kEnv_Env p) (L2kEC_EC ec).
Proof.
  induction 1; destruct t.
  - change (Lookup s ((s, ecTrm (strip t)) :: (L2kEnv_Env p))
                   (ecTrm (strip t))).
    apply LHit.
  - cbn. apply LHit.
  - change (Lookup s2 ((s1, ecTrm (strip t)) :: (L2kEnv_Env p))
                   (L2kEC_EC ec)).
    apply LMiss; assumption.
  - cbn. apply LMiss; assumption.
Qed.

Lemma lookup_hom:
  forall p nm ec,
    lookup nm p = Some ec -> lookup nm (stripEnv p) = Some (L2kEC_EC ec).
Proof.
  intros p nm ec h. apply Lookup_lookup.
  apply Lookup_hom. apply (lookup_Lookup _ _ h).
Qed.
  
Lemma lookup_hom_None:
  forall p nm,
    lookup nm p = None -> lookup nm (L2kEnv_Env p) = None.
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
  forall ds, L2k.compile.dlength ds = dlength (stripDs ds).
induction ds. intuition. simpl. rewrite IHds. reflexivity.
Qed.

Lemma tcons_hom:
  forall t ts, L2kTerms_Terms (L2k.compile.tcons t ts) =
               tcons (strip t) (L2kTerms_Terms ts).
reflexivity.
Qed.

Lemma tnil_hom: L2kTerms_Terms L2k.compile.tnil = tnil.
reflexivity.
Qed.

Lemma dcons_hom:
  forall nm bod rarg ds,
    stripDs (L2k.compile.dcons nm bod rarg ds) =
    dcons nm (strip bod) rarg (stripDs ds).
reflexivity.
Qed.

Lemma dnil_hom: stripDs L2k.compile.dnil = dnil.
reflexivity.
Qed.

Lemma dnthBody_hom: 
  forall m ds, optStripDnth (L2k.term.dnthBody m ds) =
               dnthBody m (stripDs ds).
induction m; induction ds; try intuition.
- simpl. intuition.
Qed.

Lemma tappend_hom:
  forall ts us,
    L2kTerms_Terms (L2k.term.tappend ts us) =
    tappend (L2kTerms_Terms ts) (L2kTerms_Terms us).
induction ts; intros us; simpl. reflexivity.
rewrite IHts. reflexivity.
Qed.

Lemma TCase_hom:
  forall m mch brs,
    strip (L2k.compile.TCase m mch brs) =
      match L2k.term.isProof_dec mch with
        | left _ =>
          match brs with
            | L2k.compile.dunit _ br n =>
              applyBranchToProof n (L2kTerm_Term br)
            | _ => TCase m (L2kTerm_Term mch) (L2kDefs_Defs brs)
          end
        | right _ => TCase m (L2kTerm_Term mch) (L2kDefs_Defs brs)
      end.
Proof.
  reflexivity.
Qed.


Lemma TApp_hom:
  forall fn arg args,
    strip (L2k.compile.TApp fn arg args) =
    mkApp (strip fn) (strips (L2k.compile.tcons arg args)).
  induction fn; intros arg args; try reflexivity.
Qed.

(**
Lemma hom_isApp:
  forall t, L2k.term.isApp t -> isApp (strip t).
Proof.
  induction t; cbn; intros; destruct H as [x0 [x1 [x2 jx]]]; try discriminate.
  - myInjection jx. auto.
Qed.
 **)

Lemma isApp_hom:
  forall t,
    isApp (strip t) ->
    L2k.term.isApp t \/
    exists x n u br nm,
      t = L2k.compile.TCase x (L2k.compile.TProof u) (L2k.compile.dunit nm br n).
Proof.
  destruct t; cbn; intros h;
  destruct h as [x0 [x1 [x2 h]]]; try discriminate. 
  - left. exists t1, t2, t3. reflexivity.
  - destruct t; try discriminate. destruct d.
    + discriminate.
    + right. exists i, n0, t, t0, n. destruct d.
      * reflexivity.
      * discriminate.
Qed.

Lemma mkApp_hom:
  forall fn args,
    strip (L2k.term.mkApp fn args) = mkApp (strip fn) (L2kTerms_Terms args).
Proof.
  intros fn args. functional induction (L2k.term.mkApp fn args).
  - rewrite TApp_hom. rewrite TApp_hom. rewrite mkApp_idempotent.
    rewrite tcons_hom. rewrite tcons_hom. rewrite tappend_hom.
    reflexivity.
  - destruct t; try (elim y); try reflexivity.
    + destruct (L2k.term.isProof_dec t).
      destruct i0 as [x jx]. subst t.
      * { destruct (L2k.term.is_dunit_dec d).
          - destruct H as [x0 [x1 [x2 jx]]]. subst d. cbn.
            rewrite mkApp_tnil_ident. reflexivity.
          - unfold L2kTerms_Terms. rewrite mkApp_tnil_ident.
            reflexivity. }
      * unfold L2kTerms_Terms. rewrite mkApp_tnil_ident.
        reflexivity.
  - destruct t; try (elim y); try reflexivity.
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
      

Lemma TCast_hom:
  forall tm, strip (L2k.compile.TCast tm) = TCast (strip tm).
Proof.
  reflexivity.
Qed.


Lemma instantiate_hom:
  (forall bod arg n, strip (L2k.term.instantiate arg n bod) =
                     instantiate (strip arg) n (strip bod)) /\
  (forall bods arg n, L2kTerms_Terms (L2k.term.instantiates arg n bods) =
                      instantiates (strip arg) n (L2kTerms_Terms bods)) /\
  (forall ds arg n, stripDs (L2k.term.instantiateDefs arg n ds) =
                    instantiateDefs (strip arg) n (stripDs ds)).
Proof.
Admitted.
     (**************************
  apply L2k.compile.TrmTrmsDefs_ind; intros; try (simpl; reflexivity).
  - simpl. destruct (lt_eq_lt_dec n n0); cbn.
    + destruct s.
      * rewrite (proj1 (nat_compare_gt n0 n)); try omega. cbn. reflexivity.
      * subst n. rewrite (proj2 (nat_compare_eq_iff _ _)); trivial.
        rewrite L2k.term.mkApp_tnil_ident. reflexivity.
    + rewrite (proj1 (nat_compare_lt n0 n)); trivial.
  - admit.
  - cbn. rewrite H. reflexivity.
  - cbn. rewrite H. reflexivity.
  - cbn. rewrite H. rewrite H0. reflexivity.
   - change (strip (L2k.term.mkApp
                     (L2k.term.instantiate arg n t)
                     (L2k.compile.tcons (L2k.term.instantiate arg n t0)
                                         (L2k.term.instantiates arg n t1))) =
            instantiate (strip arg) n (strip (L2k.compile.TApp t t0 t1))). 
Check TApp_hom. 
    change
      (strip (L2k.term.mkApp
                (L2k.term.instantiate arg n t)
                (L2k.compile.tcons (L2k.term.instantiate arg n t0)
                                   (L2k.term.instantiates arg n t1))) =
       (mkApp (instantiate (strip arg) n (strip t))
              (tcons (instantiate (strip arg) n (strip t0))
                     (instantiates (strip arg) n (L2kTerms_Terms t1))))).
    rewrite <- H. rewrite <- H0. rewrite <- H1. 
    Check mkApp_hom. rewrite tcons_hom. reflexivity.
  - change (TCase p (strip (L2k.term.instantiate arg n t0))
                  (L2kTerms_Terms (L2k.term.instantiates arg n t1)) =
            (TCase p (instantiate (strip arg) n (strip t0))
                   (instantiates (strip arg) n (L2kTerms_Terms t1)))).
    rewrite H0. rewrite H1. reflexivity.
  - change (TFix (stripDs (L2k.term.instantiateDefs
                             arg (n0 + L2k.compile.dlength d) d)) n =
            (TFix (instantiateDefs
                     (strip arg) (n0 + dlength (stripDs d)) (stripDs d)) n)).
    rewrite H. rewrite dlength_hom. reflexivity.
  - change (tcons (strip (L2k.term.instantiate arg n t))
                  (L2kTerms_Terms (L2k.term.instantiates arg n t0)) =
            tcons (instantiate (strip arg) n (strip t))
                  (instantiates (strip arg) n (L2kTerms_Terms t0))).
    rewrite H. rewrite H0. reflexivity.
  - change (dcons n (strip (L2k.term.instantiate arg n1 t0)) n0
                  (stripDs (L2k.term.instantiateDefs arg n1 d)) =
            dcons n (instantiate (strip arg) n1 (strip t0)) n0
                  (instantiateDefs (strip arg) n1 (stripDs d))).
    rewrite H0. rewrite H1. reflexivity.
Qed.
********************)


Lemma TProof_strip_inv:
  forall t, TProof = strip t -> (L2k.term.isProof t) \/ (L2k.term.isCase t).
Proof.
  intros t ht. destruct t; try discriminate.
  - left. exists t. reflexivity.
  - unfold strip in ht.
    destruct t1; simpl in ht; try discriminate.
    + pose proof
           (mkApp_isApp
              (mkApp (L2kTerm_Term t1_1)
                     (tcons (L2kTerm_Term t1_2) (L2kTerms_Terms t)))
              (L2kTerm_Term t2) (L2kTerms_Terms t3)).
      destruct H as [x0 [x1 [x2 j]]]. rewrite j in ht. discriminate.
    + destruct (L2k.term.isProof_dec t1).
      * destruct
          (mkApp_isApp
             (match d with
                | L2k.compile.dnil => TCase i (L2kTerm_Term t1) (L2kDefs_Defs d)
                | L2k.compile.dunit _ br n =>
                  applyBranchToProof n (L2kTerm_Term br)
                | L2k.compile.dcons _ br n (L2k.compile.dcons _ _ _ _) =>
                  TCase i (L2kTerm_Term t1) (L2kDefs_Defs d)
              end) (L2kTerm_Term t2) (L2kTerms_Terms t3)) as [x0 [x1 [x2 jx]]].
        rewrite jx in ht. discriminate.
      * destruct (mkApp_isApp (TCase i (L2kTerm_Term t1) (L2kDefs_Defs d))
                              (L2kTerm_Term t2) (L2kTerms_Terms t3))
          as [x0 [x1 [x2 jx]]].
        rewrite jx in ht. discriminate.
  - right. exists i, t, d. reflexivity.
Qed.

Lemma Const_strip_inv:
  forall nm s, TConst nm = strip s ->
               (L2k.compile.TConst nm = s) \/ (L2k.term.isCase s).
Proof.
  intros nm. destruct s; intros h; try discriminate.
  - left.
    change (TConst nm = mkApp (L2kTerm_Term s1)
                        (tcons (L2kTerm_Term s2) (L2kTerms_Terms t))) in h.
    pose proof (mkApp_isApp (L2kTerm_Term s1)
                            (L2kTerm_Term s2) (L2kTerms_Terms t)) as k.
    destruct k as [x0 [x1 [x2 jx]]]. rewrite jx in h. discriminate.
  - left. cbn in h. myInjection h. reflexivity.
  - right. exists i, s, d. reflexivity.    
Qed.

(*************
Lemma Cast_strip_inv:
  forall tm s, TCast tm = strip s ->
   exists stm, (L2k.compile.TCast stm) = s /\ tm = strip stm.
Proof.
  intros tm; destruct s; intros h; try discriminate.
  - myInjection h. exists s. intuition.
  - destruct (mkApp_isApp (strip s1) (strip s2) (strips t))
      as [x0 [x1 [x2 jx]]].
    change (TCast tm = mkApp (strip s1) (tcons (strip s2) (strips t))) in h.
    rewrite jx in h. discriminate.
  - change ()  HERE
Qed.


(*****  HERE
Lemma Fix_strip_inv:
  forall ds n s, TFix ds n = strip s ->
    exists sds, (L2k.compile.TFix sds n) = s /\ ds = stripDs sds.
Proof.
  intros ds n. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists d. intuition.
Qed.

Lemma App_strip_inv:
  forall fn arg args s, TApp fn arg args = strip s ->
    exists sfn sarg sargs,
      (L2k.compile.TApp sfn sarg sargs) = s /\
      fn = strip sfn /\ arg = strip sarg /\ args = strips sargs.
Proof.
  intros fn arg args. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, t. intuition.
Qed.

Lemma LetIn_strip_inv:
  forall nm dfn bod s, TLetIn nm dfn bod = strip s ->
    exists sdfn sty sbod,
      (L2k.compile.TLetIn nm sdfn sty sbod = s) /\
      dfn = strip sdfn /\ bod = strip sbod.
Proof.
  intros nm dfn bod s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, s3. intuition.
Qed.

Lemma Case_strip_inv:
  forall m mch brs s, TCase m mch brs = strip s ->
    exists sty smch sbrs, (L2k.compile.TCase m sty smch sbrs = s) /\
              mch = strip smch /\ brs = stripDs sbrs.
Proof.
  intros m mch brs s. destruct s; simpl; intros h; try discriminate.
  - myInjection h. exists s1, s2, d. intuition.
Qed.

Lemma tnil_strip_inv:
  forall ts, tnil = strips ts -> ts = L2k.compile.tnil.
Proof.
  induction ts; intros; try reflexivity.
  - simpl in H. discriminate.
Qed.

Lemma tcons_strip_inv:
  forall t ts us, tcons t ts = strips us ->
    exists st sts, (L2k.compile.tcons st sts = us) /\ 
                   t = strip st /\ ts = strips sts.
Proof.
  intros t ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, us. intuition.
Qed.

Lemma dcons_strip_inv:
  forall nm t m ts us, dcons nm t m ts = stripDs us ->
    exists ty st sts, (L2k.compile.dcons nm ty st m sts = us) /\ 
                   t = strip st /\ ts = stripDs sts.
Proof.
  intros nm t m ts us. destruct us; simpl; intros h; try discriminate.
  - myInjection h. exists t0, t1, us. intuition.
Qed.
 *****************)


Lemma WcbvEval_hom:
  forall p,
    (forall t t', L2k.wcbvEval.WcbvEval p t t' ->
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L2k.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (L2kTerms_Terms ts) (strips ts')).
Proof.
  intros p.
  apply L2k.wcbvEval.WcbvEvalEvals_ind; intros;
  try (solve[constructor; intuition]); try (solve[right; cbn; constructor]).
  - cbn. destruct (strip s); inversion_Clear H.





(***********************)
Lemma WcbvEval_hom:
  forall p,
    (forall t t', L2k.wcbvEval.WcbvEval p t t' ->
                  strip t' = TProof \/
                  WcbvEval (stripEnv p) (strip t) (strip t')) /\
    (forall ts ts', L2k.wcbvEval.WcbvEvals p ts ts' ->
                    WcbvEvals (stripEnv p) (L2kTerms_Terms ts) (strips ts')).
Proof.
  intros p.
  apply L2k.wcbvEval.WcbvEvalEvals_ind; intros;
  try (solve[constructor; intuition]); try (solve[right; cbn; constructor]).
  - intuition. right. cbn. constructor. assumption.
  - destruct H; intuition. cbn.
    destruct (L2k.term.isProof_dec t). cbn.
    + destruct i. subst t. cbn in H. intuition.
    + destruct t; cbn in H. inversion_Clear w.  inversion_Clear w.
cbn in H


    + destruct H0. subst t. cbn in H. right. assumption.
    + 

      
    intuition. right. cbn. 
  -
  - cbn. destruct t; cbn; try (try constructor; assumption).
  - cbn. econstructor; try eassumption.
    eapply (lookupDfn_hom). assumption.
(*************
  - destruct (L2k.term.isApp_dec t).
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
