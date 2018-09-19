Require Import L6.cps L6.cps_util L6.eval L6.logical_relations L6.set_util L6.identifiers L6.ctx
        L6.hoare L6.Ensembles_util L6.List_util L6.uncurry.
Require Import closure_conversion_corresp. (* for [fresh] *)
Require Import Coq.ZArith.Znumtheory Coq.Relations.Relations Coq.Arith.Wf_nat.
Require Import Coq.Lists.List Coq.MSets.MSets Coq.MSets.MSetRBT Coq.Numbers.BinNums
        Coq.NArith.BinNat Coq.PArith.BinPos Coq.Sets.Ensembles Omega.
Require Import ExtLib.Structures.Monads ExtLib.Data.Monads.StateMonad.

Import ListNotations MonadNotation.


Section Uncurry_correct.

  (* Parameters of the big step evaluation relation *)
  Variable (pr : prims).
  Variable (cenv : cEnv).
    
  Transparent bind ret.

  Print st_eq.

  (* This identity is useful for the Ecase case -- see below *)
  Lemma st_eq_Ecase {S} (m1 : state S (list (cTag * exp))) (x : var) y :
    st_eq
      (bind (bind m1 (fun ys => ret (y :: ys))) (fun ys' => ret (Ecase x ys')))
      (e <- (ys <- m1 ;;
             ret (Ecase x ys)) ;;
       match e with
         | Ecase x ys =>
           ret (Ecase x (y :: ys))
         | _ => ret e
       end).
  Proof.
    unfold pbind, ret.
    intros s. simpl. destruct (runState m1 s). reflexivity.
  Qed.

  Global Opaque bind ret.

  Lemma uncurry_exp_Ecase x l :
    {{ fun _ => True }}
      uncurry_exp (Ecase x l)
    {{ fun _ e' _ => exists l', e' = Ecase x l' }}.
  Proof.
    eapply bind_triple. now apply post_trivial.
    intros l' s'. apply return_triple. eauto.
  Qed.


  (* Un-nesting the Efun case from the main proof *) 
  Lemma uncurry_fundefs_correct k B1 B1' B2  e S :
    (* The induction hypothesis for expressions *)
    (forall m : nat,
       m < k ->
       forall (e : exp) S,
         Disjoint var S (Union var (bound_var e) (occurs_free e)) ->
         {{fun s : stateType => fresh S (fst ((fst (fst (fst (fst (fst s)))))))}} 
           uncurry_exp e
         {{fun (_ : stateType) (e' : exp) (s' : stateType) =>
             (forall rho rho',
                preord_env_P pr cenv (occurs_free e) m rho rho' ->
                preord_exp pr cenv m (e, rho) (e', rho')) /\ fresh S (fst (fst (fst (fst (fst (fst s')))))) }}) ->
    (* Assumption about the set [S]  *)
    Disjoint _ S (Union _ (bound_var_fundefs B2) (occurs_free_fundefs B2)) ->
    {{ fun s =>  fresh S (fst (fst (fst (fst (fst (fst s)))))) }}
      uncurry_fundefs B2
    {{ fun s B2' s' =>
         (forall rho rho',
            preord_env_P pr cenv (occurs_free (Efun B1 e)) k rho rho' ->
            (* We need to generalize the first argument of [def_funs] for the
               proof to work, although in practice it will always be the same
               with the second one. To be able to instantiate the IH we need to
               have some hypotheses for B1 B1'. However, I do not have a way to
               do this directly for the stateful program. When the proof is done
               using a relational definition for the transformation (say R) we
               can assume that B1 R B1' and the proof goes through.*)
            preord_env_P pr cenv (Union _ (occurs_free (Efun B1 e)) (name_in_fundefs B2)) k
                         (def_funs B1 B2 rho rho) (def_funs B1' B2' rho' rho')) /\
         fresh S (fst (fst (fst (fst (fst (fst s'))))))
    }}.
  Proof.
    revert B2 B1 B1' e S. induction k as [k IHk] using lt_wf_rec1.
    induction B2; intros B1 B1' e' S IHe HD; simpl.
    Opaque uncurry_exp uncurry_fundefs.
    - eapply bind_triple.
      + apply IHB2; [ eassumption |  ].
        eapply Disjoint_Included_r; [| eassumption ].
        now eapply bound_var_occurs_free_fundefs_Fcons_Included.
      + intros B2' s1. eapply pre_curry_l. intros HB2.
        destruct k as [| k].
        * (* should be straightforward for index 0 -- holds vacuously *) 
          admit.
        * destruct l.
          (* empty argument list *)
          { admit. }
          (* non-empty argument list *)  
          { destruct e. 
            - admit.
            - admit.
            - admit.
            - destruct f0 as [ g gt gvs ge B |].
              + destruct B.
                { admit. }
                { destruct e.
                  - admit.
                  - admit.
                  - admit.
                  - admit.
                  - destruct l0. 
                    + admit.
                    + destruct l0. 
                      (* This is the interesting case *)
                     *  eapply bind_triple.
                        eapply IHe with (m := k). omega.
                        eapply Disjoint_Included_r; [| eassumption ].
                        admit.
                        intros ge' s2. apply pre_curry_l. intros He'.
                        destruct (eq_var v0 v1 && eq_var g v2 &&
                                         negb (occurs_in_exp v0 ge) &&
                                         negb (occurs_in_exp g ge)) eqn:Heq.
                        apply andb_prop in Heq. destruct Heq as [Heq Heq1].
                        apply andb_prop in Heq. destruct Heq as [Heq Heq2].
                        apply andb_prop in Heq. destruct Heq as [Heq3 Heq4].
                        apply Peqb_true_eq in Heq3. apply Peqb_true_eq in Heq4. subst.
                        admit.
                        
                        admit.
                     * admit.
                  - admit.
                  - admit. } 
              + admit. 
            - admit.
            - admit.
            - admit. }
    - apply return_triple. intros s1 Hf.
      split; [| eassumption ]. intros rho rho' Henv.
      rewrite Union_Empty_set_neut_r. eassumption.
  Abort.
  
  Transparent uncurry_exp uncurry_fundefs.

  Print triple.
  Print fresh.
  Print Ensemble.
  Print preord_env_P. (* two environments agree up to k-betareductions *)
  Print preord_var_env.
  Print preord_exp. (* contextual equivalent *)
  Check lt_wf_rec1.
  Check exp_ind'.
  Check assoc.
  Check bind_triple.
  Check st_eq_Ecase.
  Search preord_exp.

  Lemma uncurry_exp_correct (k : nat) (e : exp) (S : Ensemble var) :
    (* S is the set that contains all the fresh variables we can generate. This
       is denoted by the precondition [fresh S (fst s)]. S is disjoint from all
       the free or bound identifiers in the term *)
    Disjoint _ S (Union _ (bound_var e) (occurs_free e)) ->
    {{ fun s => fresh S (fst (fst (fst (fst (fst (fst s)))))) }}
      uncurry_exp e
    {{ fun s e' s' =>
         (forall rho rho',
            (* if rho and rho' agree on the free variables of e, *)
            preord_env_P pr cenv (occurs_free e) k rho rho' ->
            (* then e and e' are contextually equivalent *) 
            preord_exp pr cenv k (e, rho) (e', rho')) /\
         (* Q: can't s' have increased due to uncurrying? *)
         (* A: sure, but S still contains all the free variables we can generate.
               just some extras too that we can't.
               we want to make sure that the fresh variable counter has not decreased
               *)
         fresh S (fst (fst (fst (fst (fst  (fst s'))))))
    }}.
  Proof with now eauto with Ensembles_DB.
    revert e; induction k as [k IHk] using lt_wf_rec1. (* strong induction on step index *)
    induction e using exp_ind'; intros HD; simpl.
    Opaque uncurry_exp uncurry_fundefs.
    - (* Case Econstr -- directly from compatibility lemma *)
      eapply bind_triple. apply IHe.
      eapply Disjoint_Included_r; [| eassumption ].
      eapply bound_var_occurs_free_Econstr_Included.
      intros e' s1. apply return_triple. intros. destruct H. split; [| assumption].
      intros rho rho' H1.
      apply preord_exp_const_compat.
      + induction l; try constructor. apply H1. constructor. now constructor.
        apply IHl. apply Disjoint_Included_r
          with (bound_var (Econstr v t (a :: l) e) :|: occurs_free (Econstr v t (a :: l) e)).
        unfold Included. intros. destruct H2.
        apply Union_introl. inversion H2; subst. constructor. now constructor.
        apply Union_intror. inversion H2; subst. constructor. now apply in_cons.
        apply Free_Econstr2; eauto.
        assumption.
        unfold preord_env_P. intros.
        apply H1. inversion H2; subst.
        * constructor. now apply in_cons.
        * now apply Free_Econstr2.
      + intros. apply H. unfold preord_env_P. intros.
        unfold preord_env_P in H1.
        destruct (Positive_as_OT.eq_dec x v).
        * subst x. apply preord_var_env_extend_eq. rewrite preord_val_eq.
          unfold preord_val'. split; try trivial.
          now apply Forall2_Forall2_asym_included.
        * apply preord_var_env_extend. auto. rewrite preord_val_eq.
          unfold preord_val'. split; try trivial.
          now apply Forall2_Forall2_asym_included.
    - (* Case Ecase x [] -- directly from compatibility lemma *)
      setoid_rewrite left_id. apply return_triple. intros s H. split; [|assumption].
      intros rho rho' Henv.
      apply preord_exp_case_nil_compat.
    - (* Case Ecase x ((c, e) :: l) *)
      (* This one is trickier because the computation of IHl is not
         a subcomputation of the goal. We can make it a subcomputation
         of the goal by rewriting with some monad identities *)
      setoid_rewrite assoc. eapply bind_triple.
      + eapply IHe; eauto.
        eapply Disjoint_Included_r; [| eassumption ].
        eapply bound_var_occurs_free_Ecase_Included.
        now constructor.
      + intros e' s1. rewrite st_eq_Ecase.
        eapply pre_curry_l. intros He.
        eapply bind_triple. eapply post_conj.
        * eapply IHe0.
          eapply Disjoint_Included_r; [| eassumption ].
          eapply bound_var_occurs_free_Ecase_cons_Included.
        * eapply pre_strenghtening; [| now apply uncurry_exp_Ecase ].
          now intros; simpl; eauto.
        * intros e'' s2. simpl. apply pre_curry_r. intros [l' Heq].
          subst. apply pre_curry_l. intros Hl. apply return_triple.
          intros s3 Hf. split; [| eassumption ]. intros rho rho' Henv. 
          (* now we can apply the compatibility lemma *)
          eapply preord_exp_case_cons_compat.
          admit. (* the two lists have the same tags -- should be easy *)
          eapply Henv. apply occurs_free_Ecase_cons...
          apply He. eapply preord_env_P_antimon. eassumption.
          rewrite occurs_free_Ecase_cons...
          simpl; eapply Hl. eapply preord_env_P_antimon. eassumption.
          rewrite occurs_free_Ecase_cons...
    - (* Case Eproj -- directly from compatibility lemma *)
      eapply bind_triple. apply IHe.
      eapply Disjoint_Included_r; [| eassumption ].
      eapply bound_var_occurs_free_Eproj_Included. intros e' s1. apply pre_curry_l.
      intros. apply return_triple. intros s2 Hs. split; [| assumption].
      intros rho rho' Henv.
      apply preord_exp_proj_compat; [auto|].
      intros v1 v2 Hval. apply H. intros x Hocc.
      destruct (Positive_as_OT.eq_dec x v).
      + subst x. now apply preord_var_env_extend_eq.
      + apply preord_var_env_extend; [| assumption].
        apply Henv. apply Free_Eproj2; auto.
    - (* Using [uncurry_fundefs_correct] *)
      admit.
    - (* Case Eapp -- directly from compatibility lemma *)
      apply return_triple. intros s Hs. split; [| assumption].
      intros rho rho' Henv.
      apply preord_exp_app_compat. auto.
      induction l; constructor. apply Henv. apply Free_Eapp2. simpl. auto. apply IHl.
      + eapply Disjoint_Included_r; [| eassumption ].
        intros x Hin. inversion Hin; subst.
        * apply Union_introl. inversion H.
        * apply Union_intror. destruct (Positive_as_OT.eq_dec x v).
          ** subst x. auto.
          ** inversion H; subst; try contradiction. apply Free_Eapp2. simpl. auto.
      + intros x Hocc. apply Henv.
        destruct (Positive_as_OT.eq_dec x v).
        * subst x. constructor.
        * apply Free_Eapp2. inversion Hocc; subst; try contradiction.
          simpl. auto.
    - (* Case Eprim -- directly from compatibility lemma *)
      eapply bind_triple. apply IHe.
      eapply Disjoint_Included_r; [| eassumption].
      apply bound_var_occurs_free_Eprim_Included. intros e' s1. apply pre_curry_l.
      intros. apply return_triple. intros s2 Hs. split; [| assumption].
      intros rho rho' Henv.
      apply preord_exp_prim_compat.
      + induction l; constructor. apply Henv. apply Free_Eprim1. simpl. auto. apply IHl.
        * eapply Disjoint_Included_r; [| eassumption].
          intros x Hin. inversion Hin; subst.
          ** apply Union_introl. inversion H0; subst; constructor; auto.
          ** apply Union_intror. inversion H0; subst.
             *** apply Free_Eprim1. simpl. auto.
             *** apply Free_Eprim2; assumption.
        * intros x Hocc. apply Henv. inversion Hocc; subst.
          ** apply Free_Eprim1. simpl. auto.
          ** apply Free_Eprim2; assumption.
      + intros. apply H. intros x Hocc.
        destruct (Positive_as_OT.eq_dec x v).
        * subst x. now apply preord_var_env_extend_eq.
        * apply preord_var_env_extend; [| assumption].
          apply Henv. apply Free_Eprim2; auto.
    - (* Case Ehalt -- directly from compatibility lemma *)
      apply return_triple. intros s H. split; [| assumption].
      intros rho rho' Henv. apply preord_exp_halt_compat. auto.
  Admitted.

  
  (* Note : The proof could also work with mutual induction on exp / fundefs but
     we would need a more general induction principle since the recursive call
     in uncurry_fundefs is not on an immediate subterm of the term. The trick with
     first inducting on the step-index can work but maybe the proof will be more
     cumbersome. *)

End Uncurry_correct.
