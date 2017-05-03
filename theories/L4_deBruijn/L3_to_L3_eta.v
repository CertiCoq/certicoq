(** Naive conversion to a deBruijn-only expression language for a core calculus including
    mutually recursive functions, data constructors, and pattern matching.
 *)

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
    
  Fixpoint strip_lam (k : nat) (e : exp) : list name * exp :=
    match k, e with
    | 0%nat, _ => ([], e)
    | S n, Lam_e na e => let '(names, e) := strip_lam n e in
                       (na :: names, e)
    | S n, _ => ([],e)
    end.

  (* Section fixes. *)
  (*   Variable trans : N -> L3t.Term -> exp. *)
  (*   Definition trans_args (k : N) (t : L3t.Terms) : exps := *)
  (*     map_terms (trans k) t. *)
  (*   Fixpoint trans_brs ind k n l := *)
  (*     match l with *)
  (*     | L3t.dnil => brnil_e *)
  (*     | L3t.dcons na t nargs ts => *)
  (*       let '(names, t') := strip_lam nargs (trans k t) in *)
  (*       brcons_e (ind,n) (N.of_nat nargs, names) t' *)
  (*                (trans_brs ind k (n + 1)%N ts) *)
  (*     end. *)
  (*   Fixpoint trans_fixes k l := *)
  (*     match l with *)
  (*     | L3t.dnil => eflnil *)
  (*     | L3t.dcons na t _ l' => *)
  (*       eflcons na (trans k t) (trans_fixes k l') *)
  (*     end. *)

  (* End fixes. *)

  (* Move Γ |- body : τ1 -> .. -> τn -> τ to 
     Γ, x1 : τ1, .., xn : τn |- body x1 .. xn : τ
   *)
  

  Fixpoint is_n_lambda n t :=
    match n with
    | 0%nat => true
    | S n => match t with
            | TLambda _ t => is_n_lambda n t
            | _ => false
            end
    end.

  Fixpoint eta_expand_aux (n : nat) (t : Term) (k : Terms) : Term :=
    match n with
    | 0%nat => mkApp t (treverse k)
    (* | S n, TLambda na t => *)
    (*   (* Γ |- λ t : τ1 -> τ2 .. τn -> τ to  *)
    (*      Γ, τ1 |- t : τ2 .. τn -> τ *)
    (*    *)  *)
    (*   TLambda na (eta_expand_aux n t k) *)
    | S n' =>
      TLambda nAnon (eta_expand_aux n' (lift 0 t) (tcons (TRel n') k))
    end.

  Definition eta_expand n t :=
    if is_n_lambda n t then t
    else eta_expand_aux n t tnil.
      
  Eval compute in is_n_lambda 1 (TLambda (nNamed "x") (TRel 0)).
  Eval compute in eta_expand 1 (TLambda (nNamed "x") (TRel 0)).
  
  Eval compute in eta_expand 2 (TLambda (nNamed "x") (TRel 0)).
  Eval compute in eta_expand 2 (TLambda (nNamed "x") (TRel 1)).
    
  Eval compute in eta_expand 3 (TRel 0).
  Eval compute in eta_expand 1 (TLambda (nNamed "x") (TRel 0)).
  Eval compute in eta_expand 2 (TLambda (nNamed "x") (TRel 1)).
  
  Fixpoint trans (k : nat) (t : Term) : Term :=
    match t with
    | TAx => TAx
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
  with trans_brs (i : inductive) (k : nat) (brs : Defs) : Defs :=
    match brs with
    | dnil => dnil
    | dcons na t n brs =>
      let transt := trans k t in
      let etat := eta_expand n transt in
      dcons na etat n (trans_brs i k brs)
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

Inductive match_annot : list Cnstr -> Defs -> Prop :=
| match_annot_nil : match_annot [] dnil
| match_annot_cons na t args c cnstrs ds :
    c.(CnstrArity) = args ->
    match_annot cnstrs ds ->
    match_annot (c :: cnstrs) (dcons na t args ds).
         
Definition crctAnn (e : environ Term) ann brs :=
  let 'mkInd nm tndx := ann in
  exists pack ityp,
    LookupTyp nm e 0 pack /\
    getInd pack tndx = Ret ityp /\
    match_annot ityp.(itypCnstrs) brs.

Lemma Crct_invrt_Case e n ann mch brs :
  crctTerm e n (TCase ann mch brs) ->
  crctTerm e n mch /\ crctDs e n brs /\
  crctAnn e ann brs /\
  (forall i t, dnth i brs = Some t -> crctTerm e n (dbody _ t)).
Admitted.

Lemma Crct_construct {e : environ Term} {i n args} : crctEnv e ->
  crctTerm e 0 (TConstruct i n args) ->
  cnstrArity e i n = Ret (0%nat, tlength args).
Proof. intros. inv H. Admitted.

Lemma dnthBody_trans n t i brs :
  dnth n brs = Some t -> exists t',
    dnth n (trans_brs i 0 brs) = Some t' /\
    t'.(dbody _) = eta_expand (t.(rarg _)) (trans 0 t.(dbody _)).
Proof.
  revert n t i; induction brs; intros *.
  simpl; intros. discriminate.
  
  simpl. unfold dnthBody. destruct n1. simpl.
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
  dnth n brs = Some t -> CnstrArity c = t.(rarg _).
Proof.
  intros H; revert n c t; induction H; intros; simpl; auto.
  - discriminate.
  - destruct n. injection H1; intros ->. injection H2; intros <-.
    simpl; auto.

    simpl in H1, H2.
    now specialize (IHmatch_annot _ _ _ H1 H2).
Qed.

Lemma WcbvEval_mkApp_einv {e f a s} : WcbvEval e (mkApp f a) s -> exists s', WcbvEval e f s'.
Proof.
  revert f; induction a; simpl; intros.
  - now exists s.
  - specialize (IHa (TApp f t) H).
    destruct IHa.
    inv H0.
    * now exists TProof.
    * now exists (TLambda nm bod).
    * exists (TFix dts m). auto.
    * now exists efn. 
Qed.

Lemma WcbvEval_is_n_lam e n t t' : is_n_lambda n t = true -> WcbvEval e t t' -> is_n_lambda n t' = true.
Proof.
  induction n; simpl; intros Hlam; auto.
  
  destruct t; try discriminate.
  intros. inv H.
  auto.
Qed.

Lemma WcbvEval_mkApp_inner e f f' s' a s :
  let n := tlength a in
  is_n_lambda n s' = true ->
  WcbvEval e f s' ->
  WcbvEval e f' s' ->
  WcbvEval e (mkApp f a) s -> WcbvEval e (mkApp f' a) s.
Proof.
  revert f f' s' s; induction a; intros *; intros Hlam evf evf' evapp; simpl in *.
  - now rewrite <- (WcbvEval_single_valued evf evapp).
  - subst n; simpl in *.
    destruct s'; try discriminate.
    destruct (WcbvEval_mkApp_einv evapp) as [s'' evs''].
    
    assert(WcbvEval e (TApp f' t) s'').
    { inv evs''.
      pose proof (WcbvEval_single_valued evf H2). discriminate.
      injection (WcbvEval_single_valued evf H1). intros -> ->.
      econstructor; eauto.
      pose proof (WcbvEval_single_valued evf H1). discriminate.
      pose proof (WcbvEval_single_valued evf H1). subst efn. elim H2. red.
      do 2 eexists ; reflexivity. }
    eapply (IHa (TApp f t) (TApp f' t) s'' s ); auto.
    
    inv evs''.
    pose proof (WcbvEval_single_valued evf H3). discriminate.
    injection (WcbvEval_single_valued evf H2). intros -> ->.
    eapply WcbvEval_is_n_lam. 2:apply H5. admit.
    pose proof (WcbvEval_single_valued evf H2). discriminate.
    pose proof (WcbvEval_single_valued evf H2). subst efn. elim H3.
    do 2 eexists; reflexivity.
Admitted.

Lemma eval_app_terms e f args s :
  WcbvEval e (mkApp f args) s ->
  WcbvEval e (mkApp (eta_expand (tlength args) f) args) s.
Proof.
  revert e f s; induction args; intros.
  simpl; trivial.

  simpl.
  unfold eta_expand.
  destruct is_n_lambda. auto.

  simpl.
  Lemma WcbvEval_mkApp e f f' a s :
    WcbvEval e f f' -> WcbvEval e (mkApp f' a) s ->
    WcbvEval e (mkApp f a) s.
  Proof.
    intros evff' evf'a.
    dependent induction evf'a.
  Admitted.

  eapply WcbvEval_mkApp.
  eapply wAppLam. constructor. admit.
  simpl in H. unfold whBetaStep.
Admitted.
    
  
  

(* Lemma eval_app_terms e f args s : *)
(*   WcbvEval e (mkApp f args) s -> *)
(*   WcbvEval e (mkApp (eta_expand (tlength args) f) args) s. *)
(* Proof. *)
(*   revert e f s; induction args; intros. *)
(*   simpl; trivial. *)
  
(*   simpl in *. specialize (IHargs _ _ _ H). unfold eta_expand. *)
(*   case_eq (is_n_lambda (S (tlength args)) f). auto. *)
(*   intros. *)

  
  
(*   eapply WcbvEval_mkApp_inner. 2:apply IHargs. *)
  
(*   simpl. *)
(* Admitted. *)

Lemma whCase_step e i n args brs cs s :
  crctEnv e -> crctDs e 0 brs -> crctAnn e i brs ->
  cnstrArity e i n = Ret (0%nat, tlength args) ->
  whCaseStep n args brs = Some cs -> WcbvEval e cs s ->
  WcbvEval (transEnv e) (trans 0 cs) (trans 0 s) ->
  exists cs',
    whCaseStep n (trans_terms 0 args) (trans_brs i 0 brs) =
    Some cs' /\ WcbvEval (transEnv e) cs' (trans 0 s).
Proof.
  intros crcte crctds crctann crctar Hcase Hev IHev.
  unfold whCaseStep in Hcase.
  revert Hcase; case_eq (dnthBody n brs). intros t Hdn [= <-].
  unfold whCaseStep.
  
  unfold dnthBody in Hdn. case_eq (dnth n brs). intros. rewrite H in Hdn.
  destruct (dnthBody_trans _ _ i _ H) as [cs' [Hnth Heq]].
  unfold dnthBody. rewrite Hnth. destruct cs'. simpl in *.
  eexists; split; eauto.
  
  subst dbody.
  destruct d. simpl in *.
  assert(tlength args = rarg0).
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
  subst rarg0. injection Hdn ; intros <-.
  clear Hnth H .

  clear crctar Hdn.
  revert dbody s Hev IHev.
  induction args. simpl.
  unfold eta_expand. simpl. trivial.

  simpl; intros dbody s Hev IHev.
  specialize (IHargs _ _ Hev IHev).
  simpl in IHargs.
    
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
   crctTerms e 0 t ->
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
    apply Crct_invrt_Case in crctc as [crctmch crctbrs].
    econstructor. eauto.
    
Admitted.    
    
(** start-to-L4 translations **)
Definition myprogram_Program : program -> Program Term :=
  L3t.program_Program.
(*************
  do pgm0 <- malecha_L1.program_Program pgm (Ret nil);
    let e' := stripEvalCommute.stripEnv (program.env pgm0) in
    match L3U.stripEnv e' with
    | Ret senv => 
      match L3U.strip e' (stripEvalCommute.strip (program.main pgm0)) with
      | Ret smain => Ret {| main := smain; L3.program.env := senv |}
      | Exc s => Exc ("Error in stripping: " ++ s)
      end
    | Exc s => Exc ("Error while stripping environ L3.compile.Termment: " ++ s)
    end.
 *************)

Definition translate_program (e : environ L3.compile.Term) (t : L3t.Term) : L3t.Term :=
  trans 0 t.

Definition Program_Program (pgm : Program L3t.Term) : Program L3t.Term :=
  let 'mkPgm main env := pgm in
  {| main := trans 0 main; env := transEnv env |}.

Definition program_L3_eta (pgm:program) : Program L3t.Term :=
  Program_Program (myprogram_Program pgm).