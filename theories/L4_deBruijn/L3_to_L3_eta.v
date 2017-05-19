(** Intermediate L3_eta language.

  Enforce eta-expanded branches in match, so that the following L3-L4 phase
  can strip them correctly. *)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String Coq.Lists.List
        Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.
Require Export Common.Common.  (* shared namespace *)
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.
Require Import L3.compile.
Module L3t := L3.compile.
Require Import L4.expression.

(** Tactics *)
Ltac forward H :=
  match type of H with
  | ?T -> _ => let H' := fresh in cut T;[intros H'; specialize (H H') | ]
  end.

Import L3t.

Section TermTranslation.
    

  Fixpoint is_n_lambda n t :=
    match n with
    | 0%nat => true
    | S n => match t with
            | TLambda _ t => is_n_lambda n t
            | _ => false
            end
    end.

  (* Move Γ |- body : τ1 -> .. -> τn -> τ to 
     Γ, x1 : τ1, .., xn : τn |- body x1 .. xn : τ
   *)

  Fixpoint eta_expand_aux (n : nat) (t : Term) : Term :=
    match n with
    | 0%nat => t
    | S n' =>
      TLambda nAnon (eta_expand_aux n' (TApp (lift 0 t) (TRel 0)))
    end.

  Definition eta_expand n t :=
    if is_n_lambda n t then t
    else eta_expand_aux n t.
      
  Eval compute in is_n_lambda 1 (TLambda (nNamed "x") (TRel 0)).
  Eval compute in eta_expand 1 (TLambda (nNamed "x") (TRel 0)).
  
  Eval compute in eta_expand 2 (TLambda (nNamed "x") (TRel 0)).
  Eval compute in eta_expand 2 (TLambda (nNamed "x") (TRel 1)).
    
  Eval compute in eta_expand 3 (TRel 0).
  Eval compute in eta_expand 1 (TLambda (nNamed "x") (TRel 0)).
  Eval compute in eta_expand 2 (TLambda (nNamed "x") (TRel 1)).
  
  Fixpoint trans (k : nat) (t : Term) : Term :=
    match t with
    | TWrong => TWrong
    | TProof => TProof
    | TRel n => TRel n
    | TLambda n t => TLambda n (trans (1+k) t)
    | TLetIn n t u => TLetIn n (trans k t) (trans (1+k) u)
    | TApp t u => TApp (trans k t) (trans k u)
    | TConst s => TConst s
    | TConstruct ind c args =>      
      TConstruct ind c (trans_terms k args)
    | TCase ind t brs =>
      TCase ind (trans k t) (trans_brs ind k brs)
    | TFix d n =>
      let len := L3t.dlength d in
      let defs' := trans_fixes (len + k) d in
      TFix defs' n
    end

  with trans_terms (k : nat) (ts : Terms) : Terms :=
    match ts with
    | tnil => tnil
    | tcons t ts => tcons (trans k t) (trans_terms k ts)
    end
  with trans_brs (i : inductive) (k : nat) (brs : Brs) : Brs :=
    match brs with
    | bnil => bnil
    | bcons n t brs =>
      let transt := trans k t in
      let etat := eta_expand n transt in
      bcons n etat (trans_brs i k brs)
    end
  with trans_fixes (k : nat) (d : Defs) : Defs :=
    match d with
    | dnil => dnil
    | dcons na t n ds => dcons na (trans k t) n (trans_fixes k ds)
    end.

  
End TermTranslation.

Require Import L3.term L3.program L3.compile L3.wcbvEval.

Fixpoint transEC (ec:envClass Term) : envClass Term :=
  match ec with
    | ecTrm t => ecTrm (trans 0 t)
    | ecTyp _ n itp => ecTyp _ n itp
  end.

Fixpoint transEnv (p:environ Term) : environ Term :=
  match p with
    | nil => nil
    | cons (nm, ec) q => cons (nm, transEC ec) (transEnv q)
  end.

Lemma Lookup_trans_env e nm t : LookupDfn nm e t -> LookupDfn nm (transEnv e) (trans 0 t).
Proof.
  red. intros H. red in H.
  dependent induction H. simpl. constructor.
  constructor; auto.
Qed.

Lemma wcbvEval_pres_Crct e t t' :
  crctTerm e 0 t -> WcbvEval e t t' -> crctTerm e 0 t'.
Admitted.

Inductive match_annot : list Cnstr -> Brs -> Prop :=
| match_annot_nil : match_annot [] bnil
| match_annot_cons t args c cnstrs ds :
    c.(CnstrArity) = args ->
    match_annot cnstrs ds ->
    match_annot (c :: cnstrs) (bcons args t ds).
         
Definition crctAnn (e : environ Term) ann brs :=
  let 'mkInd nm tndx := ann in
  exists pack ityp,
    LookupTyp nm e 0 pack /\
    getInd pack tndx = Ret ityp /\
    match_annot ityp.(itypCnstrs) brs.

Lemma Crct_invrt_Case e n ann mch brs :
  crctTerm e n (TCase ann mch brs) ->
  crctTerm e n mch /\ crctBs e n brs /\
  crctAnn e ann brs /\
  (forall i t, bnth i brs = Some t -> crctTerm e n (fst t)).
Admitted.

Lemma Crct_construct {e : environ Term} {i n args} : crctEnv e ->
  crctTerm e 0 (TConstruct i n args) ->
  cnstrArity e i n = Ret (0%nat, tlength args).
Proof. intros. inv H. Admitted.

Lemma dnthBody_trans n t i brs :
  bnth n brs = Some t -> exists t',
    bnth n (trans_brs i 0 brs) = Some t' /\
    fst t' = eta_expand (snd t) (trans 0 (fst t)).
Proof.
  revert n t i; induction brs; intros *.
  simpl; intros. discriminate.
  
  simpl. destruct n0. simpl.
  intros [= <-].
  eexists; split; eauto.
  simpl.
  
  intros. now eapply IHbrs.
Qed.
      
Arguments raise : simpl never.
Arguments String.append : simpl never.

Lemma match_annot_n {cnstrs brs n c t} :
  match_annot cnstrs brs ->
  exnNth cnstrs n = Ret c ->
  bnth n brs = Some t -> CnstrArity c = snd t.
Proof.
  intros H; revert n c t; induction H; intros; simpl; auto.
  - discriminate.
  - destruct n. injection H1; intros ->. injection H2; intros <-.
    simpl; auto.

    simpl in H1, H2.
    now specialize (IHmatch_annot _ _ _ H1 H2).
Qed.

Lemma WcbvEval_mkApp_einv {e f a s} : WcbvEval e (mkApp f a) s ->
                                      exists s', WcbvEval e f s'.
Proof.
  revert f; induction a; simpl; intros.
  - exists s. intuition. 
  - specialize (IHa (TApp f t) H).
    destruct IHa. inv H0.
    * now exists TProof. 
    * now exists (TLambda nm bod). 
    * now exists (TFix dts m). 
    * now exists efn.  
Qed.

Lemma WcbvEval_is_n_lam e n t t' : is_n_lambda n t = true -> WcbvEval e t t' -> is_n_lambda n t' = true.
Proof.
  induction n; simpl; intros Hlam; auto.
  
  destruct t; try discriminate.
  intros. inv H.
  auto.
Qed.

Lemma wcbvEval_no_step e s t : WcbvEval e s t -> WcbvEval e t t.
Admitted.
Hint Resolve wcbvEval_no_step.

Lemma WcbvEval_mkApp_inner e f s' a s :
  (WcbvEval e f s' ->
   WcbvEval e (mkApp s' a) s -> WcbvEval e (mkApp f a) s) /\
  (WcbvEval e f s' ->
   WcbvEval e (mkApp f a) s -> WcbvEval e (mkApp s' a) s).
  
Proof.
  revert f s' s; induction a; intros *; split; intros evf evapp; simpl in *.
  - pose (wcbvEval_no_step _ _ _ evf). rewrite <- (WcbvEval_single_valued w evapp). eauto.
  - rewrite <- (WcbvEval_single_valued evf evapp). eauto.
    
  - simpl in *.
    destruct (WcbvEval_mkApp_einv evapp) as [s'' evs''].
    assert(WcbvEval e (TApp f t) s'').
    { pose (wcbvEval_no_step _ _ _ evf). inv evs''. 
      pose proof (WcbvEval_single_valued w H2). subst s'. repeat  constructor.  auto.
      pose proof (WcbvEval_single_valued w H1). subst s'. 
      econstructor; eauto.
      pose proof (WcbvEval_single_valued w H1). subst s'.
      eapply wAppFix; eauto.
      pose proof (WcbvEval_single_valued w H1). subst efn.
      eapply wAppCong; eauto. }
    eapply (proj1 (IHa (TApp f t) s'' s)); eauto.
    eapply (proj2 (IHa (TApp s' t) s'' s)); eauto.

  - simpl in *.
    destruct (WcbvEval_mkApp_einv evapp) as [s'' evs''].
    assert(WcbvEval e (TApp s' t) s'').
    { inv evs''. 
      pose proof (WcbvEval_single_valued evf H2). subst s'. repeat  constructor.  auto.
      pose proof (WcbvEval_single_valued evf H1). subst s'. 
      econstructor; eauto.
      pose proof (WcbvEval_single_valued evf H1). subst s'.
      eapply wAppFix; eauto.
      pose proof (WcbvEval_single_valued evf H1). subst efn.
      eapply wAppCong; eauto. }
    eapply (proj1 (IHa _ _ s)). eauto.
    eapply (proj2 (IHa _ _ s)). eapply evs''. apply evapp.
Qed.

Lemma instantiate_eta t k n u : WFTrm t 0 -> instantiate t k (eta_expand_aux n u) =
                                            eta_expand_aux n (instantiate t k u).
Proof.
  revert k u; induction n; intros. simpl. auto.
  simpl. rewrite instantiate_TLambda.
  f_equal. rewrite IHn; auto.
  f_equal. rewrite instantiate_TApp_commute.
  f_equal. rewrite <- (proj1 (instantiate_lift _)); auto. 
  lia.
Qed.
  
Lemma wcbvEval_eta e t s n : WcbvEval e t s -> exists s', WcbvEval e (eta_expand_aux n t) s'.
Proof.
  induction n; intros.
  simpl.
  - now exists s.
  - simpl. eexists. constructor.
Qed.

Lemma is_n_lambda_eta n t : is_n_lambda n (eta_expand_aux n t) = true.
Proof.
  revert t; induction n; intros; trivial.
  simpl. now rewrite IHn.
Qed.

Lemma eval_app_terms e f args s :
  WFTrms args 0 -> WcbvEvals e args args ->
  WcbvEval e (mkApp f args) s ->
  WcbvEval e (mkApp (eta_expand (tlength args) f) args) s.
Proof.
  intros wfargs nosteps.
  unfold eta_expand. case_eq (is_n_lambda (tlength args) f). trivial.
  intros _.
  revert e f s wfargs nosteps; induction args; intros.
  { simpl; trivial. }
  simpl in *; pose proof (WcbvEval_mkApp_einv H).
  destruct H0 as [s' evft].
  destruct (wcbvEval_eta _ _ _ (tlength args) evft).

  eapply WcbvEval_mkApp_inner with (s':=x). 
  - eapply wAppLam with (a1':=t). constructor.
    now inv nosteps.
    unfold whBetaStep.
    rewrite instantiate_eta.
    rewrite instantiate_TApp_commute.
    cbn. rewrite (proj1 (instantiate_noLift t)).
    exact H0. now inv wfargs.
  - eapply (proj2 (WcbvEval_mkApp_inner _ _ _ _ _)). eauto.
    eapply IHargs. now inv wfargs. now inv nosteps. eauto.
Qed.    

Lemma trans_terms_pres_tlength n a : tlength a = tlength (trans_terms n a).
Proof. induction a; trivial. simpl. now rewrite IHa. Qed.

Lemma trans_mkApp n t u : trans n (mkApp t u) = mkApp (trans n t) (trans_terms n u).
Proof.
  revert t; induction u; trivial.
  simpl. intros. now rewrite IHu. 
Qed.

Lemma whCase_step e i n args brs cs s :
  crctEnv e -> crctBs e 0 brs -> crctAnn e i brs -> crctTerms e 0 args ->
  cnstrArity e i n = Ret (0%nat, tlength args) ->
  whCaseStep n args brs = Some cs -> WcbvEval e cs s ->
  WcbvEval (transEnv e) (trans 0 cs) (trans 0 s) ->
  exists cs',
    whCaseStep n (trans_terms 0 args) (trans_brs i 0 brs) =
    Some cs' /\ WcbvEval (transEnv e) cs' (trans 0 s).
Proof.
  intros crcte crctds crctann crctargs crctar Hcase Hev IHev.
  unfold whCaseStep in Hcase.
  revert Hcase; case_eq (bnth n brs). intros [t arg] Hdn [= <-].
  unfold whCaseStep.
  
  unfold dnthBody in Hdn. case_eq (bnth n brs). intros. rewrite H in Hdn.
  destruct (dnthBody_trans _ _ i _ H) as [cs' [Hnth Heq]].
  unfold dnthBody. rewrite Hnth. destruct cs'. simpl in *.
  eexists; split; eauto.
  
  destruct p. simpl in *.
  injection Hdn. intros -> ->.
  assert(tlength args = arg).
  { unfold crctAnn in *. destruct i as [nm ndx].
    destruct crctann as [pack [ityp [Hlook [Hind Hann]]]].
    unfold cnstrArity in crctar. red in Hlook. destruct Hlook as [Hlook none].
    apply Lookup_lookup in Hlook. unfold lookupTyp in *. rewrite Hlook in crctar.
    destruct pack; try discriminate. rewrite Hind in crctar.
    unfold getCnstr in crctar. case_eq (exnNth (itypCnstrs ityp) n).
    intros. rewrite H0 in crctar. discriminate.
    intros; rewrite H0 in crctar.
    injection crctar. intros.
    assert (me:=match_annot_n Hann H0 H). simpl in me. congruence. }
  clear Hnth H .

  clear crctar Hdn.
  subst t0. simpl in *. rewrite <- H0.
  rewrite (trans_terms_pres_tlength 0 args).
  eapply eval_app_terms.
  eapply (proj1 (proj2 Crct_WFTrm)).
  admit. admit.
  now rewrite trans_mkApp in IHev.

  intros. rewrite H in Hdn. discriminate.

  intros. discriminate.
Admitted.

Theorem translate_correct_subst (e : environ Term) (t t' : Term) :
  crctEnv e -> crctTerm e 0 t ->
  WcbvEval e t t' -> 
  WcbvEval (transEnv e) (trans 0 t) (trans 0 t').
Proof.
  assert ((forall t t' : Term,
  WcbvEval e t t' -> 
  crctEnv e -> crctTerm e 0 t ->
  WcbvEval (transEnv e) (trans 0 t) (trans 0 t')) /\
          (forall t t' : Terms,
   WcbvEvals e t t' ->
   crctEnv e -> crctTerms e 0 t ->
   WcbvEvals (transEnv e) (trans_terms 0 t) (trans_terms 0 t'))).
  clear; apply WcbvEvalEvals_ind; simpl; auto.

  - intros fn arg evprf IHev crcte crctt.
    apply Crct_invrt_App in crctt.
    constructor. intuition eauto.

  - intros i r args args' evargs evtras crcte crctc.
    destruct i as [ipkg inum]. 
    apply Crct_invrt_Construct in crctc.
    intuition.

  - intros nm t s Ht evalt IHt crcte crctt.
    econstructor; [ | eapply IHt]; eauto.
    apply Lookup_trans_env; auto.
    eapply Crct_LookupDfn_Crct; eauto.

  - intros * evfn IHfn evat IHa1 eva1' IHa1' crcte crctc.
    apply Crct_invrt_App in crctc as [crctfn crcta1].
    econstructor; eauto.

    assert(trans 0 (whBetaStep bod a1') = whBetaStep (trans 1 bod) (trans 0 a1')).
    admit.
    rewrite <- H. apply IHa1'; auto.
    eapply whBetaStep_pres_Crct.
    apply wcbvEval_pres_Crct in evfn; auto.
    now apply Crct_invrt_Lam in evfn.
    apply wcbvEval_pres_Crct in evat; auto.

  - intros * evdfn IHdfn evbod IHbod crcte crctt.
    apply Crct_invrt_LetIn in crctt as [crctdn crctbod].
    econstructor; eauto.
    forward IHbod; auto. forward IHbod.
    admit.
    admit.

  - intros * evfix IHfix Hfix evapp IHapp crcte crcta.
    apply Crct_invrt_App in crcta as [crctfn crctarg].
    eapply wAppFix with (fs := trans 0 fs). forward IHfix; auto.
    admit.
    apply IHapp; auto.
    admit.

  - intros * wfn IHfn notlam notfix nproof evarg IHarg crcte crcta.
    apply Crct_invrt_App in crcta as [crctfn crctarg].
    constructor; auto.
    admit. admit. admit.

  - intros * evmch IHmch Hcase evcs IHcs crcte crctc.
    apply Crct_invrt_Case in crctc as [crctmch [crctbrs [crctann H']]].
    pose (whCase_step e i n args brs cs s crcte crctbrs crctann).
    forward e0. forward e0. specialize (e0 Hcase evcs).
    forward e0. destruct e0 as [cs' [whtrans evtrans]].
    econstructor; eauto.
    eapply IHcs; eauto.
    admit. (* Well-formedness *)
    admit. (* Well-formedness *)
    admit.
    
  - intros * evmch IHmch. admit.

  - intros. inv H2. constructor; auto.
  - intros. apply H; auto.
Admitted.
    
(** start-to-L4 translations **)
Definition myprogram_Program : program -> Program Term :=
  L3t.program_Program.

Definition translate_program (e : environ L3.compile.Term) (t : L3t.Term) : L3t.Term :=
  trans 0 t.

Definition Program_Program (pgm : Program L3t.Term) : Program L3t.Term :=
  let 'mkPgm main env := pgm in
  {| main := trans 0 main; env := transEnv env |}.

Definition program_L3_eta (pgm:program) : Program L3t.Term :=
  Program_Program (myprogram_Program pgm).