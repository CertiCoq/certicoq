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
  Lemma uncurry_fundefs_correct k B1 B1' B2 e S :
    (* The induction hypothesis for expressions *)
    (forall m : nat,
       m < k ->
       forall (e : exp) S,
         Disjoint var S (Union var (bound_var e) (occurs_free e)) ->
         {{fun s : var * bool => fresh S (fst s)}} 
           uncurry_exp e
         {{fun (_ : var * bool) (e' : exp) (s' : var * bool) =>
             (forall rho rho',
                preord_env_P pr cenv (occurs_free e) m rho rho' ->
                preord_exp pr cenv m (e, rho) (e', rho')) /\ fresh S (fst s') }}) ->
    (* Assumption about the set [S] we  *)
    Disjoint _ S (Union _ (bound_var_fundefs B2) (occurs_free_fundefs B2)) ->
    (* We need to generalize the first argument of [def_funs] for the proof
       to work, although in practice it will always be the same with the
       second one. This may or may not be a sufficient and convenient
       assumption for B1 and B1' *)
    {{ fun _ => True }} uncurry_fundefs B1 {{ fun _ B1'' _ => B1' = B1'' }} ->
    {{ fun s =>  fresh S (fst s) }}
      uncurry_fundefs B2
    {{ fun s B2' s' =>
         (forall rho rho',
            preord_env_P pr cenv (occurs_free (Efun B1 e)) k rho rho' ->
            preord_env_P pr cenv (Union _ (occurs_free (Efun B1 e)) (name_in_fundefs B2)) k
                      (def_funs B1 B2 rho rho) (def_funs B1' B2' rho' rho')) /\
         fresh S (fst s')
    }}.
  Proof.
    revert B2 B1 B1' e S. induction k as [k IHk] using lt_wf_rec1.
    induction B2; intros B1 B1' e' S IHe HD Hunc; simpl.
    Opaque uncurry_exp uncurry_fundefs.
    - eapply bind_triple.
      + apply IHB2; [ eassumption | | eassumption ].
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

  Lemma uncurry_exp_correct (k : nat) (e : exp) (S : Ensemble var) :
    (* S is the set that contains all the fresh variables we can generate. This
       is denoted by the precondition [fresh S (fst s)]. S is disjoint from all
       the free or bound identifiers in the term *)
    Disjoint _ S (Union _ (bound_var e) (occurs_free e)) ->
    {{ fun s => fresh S (fst s) }}
      uncurry_exp e
    {{ fun s e' s' =>
         (forall rho rho',
            preord_env_P pr cenv (occurs_free e) k rho rho' ->
            preord_exp pr cenv k (e, rho) (e', rho')) /\
         fresh S (fst s')
    }}.
  Proof with now eauto with Ensembles_DB.
    revert e; induction k as [k IHk] using lt_wf_rec1.
    induction e using exp_ind'; intros HD; simpl.
    Opaque uncurry_exp uncurry_fundefs.
    - (* Case Econstr -- directly from compatibility lemma *)
      admit.
    - (* Case Ecase x [] -- directly from compatibility lemma *)
      admit.
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
      admit.
    - (* Using [uncurry_fundefs_correct] *)
      admit.
    - (* Case Eproj -- directly from compatibility lemma *)
      admit.
    - (* Case Eproj -- directly from compatibility lemma *)
      admit.
    - (* Case Ehalt -- directly from compatibility lemma *)
      admit. 
  Admitted.

  
  (* Note : The proof could also work with mutual induction on exp / fundefs but
     we would need a more general induction principle since the recursive call
     in uncurry_fundefs is not on an immediate subterm of the term. The trick with
     first inducting on the step-index can work but maybe the proof will be more
     cumbersome. *)

End Uncurry_correct.