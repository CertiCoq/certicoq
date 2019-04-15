From CertiCoq.L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics map_util.

From CertiCoq.L6.Heap Require Import heap heap_defs heap_equiv space_sem
     cc_log_rel dead_param_elim_rel GC log_rel_defs log_rel_post_cc.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega Permutation.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module DeadParamCorrect (H : Heap).

  Module LR := LogRelPostCC H.
  
  Import H LR LR.LRDefs LR.LRDefs.Sem.GC LR.LRDefs.Sem.GC.Equiv
         LR.LRDefs.Sem.GC.Equiv.Defs LR.LRDefs.Sem.

  
  Definition Pre : IInv :=
    fun c1 c2 => 
      let '(H1, rho1, e1) := c1 in
      let '(H2, rho2, e2) := c2 in
      size_heap H2 <= size_heap H1. 

  Definition Post : Inv :=
    fun c p1 p2 =>
      let '(c1, m1) := p1 in
      let '(c2, m2) := p1 in
      c2 <= c1 /\ m2 <= m1. 

  Definition PreG : GIInv :=
    fun _ _ _ _ c1 c2 => 
      let '(H1, rho1, e1) := c1 in
      let '(H2, rho2, e2) := c2 in
      size_heap H2 <= size_heap H1. 

  Definition PostG : GInv :=
    fun _ _ c p1 p2 =>
      let '(c1, m1) := p1 in
      let '(c2, m2) := p1 in
      c2 <= c1 /\ m2 <= m1. 

  Definition drop_invariant (drop : var -> option (list bool)) rho1 rho2 :=
    forall f bs, drop f = Some bs ->
            exists B1 f1 B2 f2 ft1 xs1 e1 ft2 xs2 e2 S,
              M.get f rho1 = Some (FunPtr B1 f1) /\
              M.get f rho2 = Some (FunPtr B1 f2) /\
              find_def f1 B1 = Some (ft1, xs1, e1) /\
              find_def f2 B2 = Some (ft2, xs2, e2) /\
              Drop_params xs1 bs xs2 S /\
              Drop_body drop S e1 e2.

  Lemma drop_invariant_extend drop rho1 rho2 x v1 v2 :
    ~ x \in domain drop ->
    drop_invariant drop rho1 rho2 ->
    drop_invariant drop (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros Hnin Hinv f bs Hf.
    setoid_rewrite M.gso. eapply Hinv. eassumption.

    intros Hc; subst.
    eapply Hnin. exists bs. eassumption.
    intros Hc; subst.
    eapply Hnin. exists bs. eassumption.
  Qed. 
    
  Lemma dead_param_elim_correct
        k j (* step and heap indices *)
        H1 rho1 e1 H2 rho2 e2 (* source and target conf *)
        b (* location renaming *)
        drop (* dropper function *)
        S (* dropped variables *) :

    (forall j, (H1, rho1) ⋞ ^ (occurs_free e1 \\ S \\ dropped_funs drop ; k ; j; PreG ; PostG ; b) (H2, rho2)) ->

    (* invariant about dropped function names *)
    drop_invariant drop rho1 rho2 -> 
    
    (* Assumptions about variable names *)
    unique_bindings e1 ->
    Disjoint _ (domain drop) (bound_var e1) ->
    Disjoint _ (occurs_free e1) (bound_var e1) -> 
    
    (* e2 is the dropping of e1 *)
    Drop_body drop S e1 e2 ->
    (* The source and target are related *)
    (H1, rho1, e1) ⪯ ^ ( k ; j ; Pre ; PreG ; Post ; PostG ) (H2, rho2, e2).
  Proof with now eauto with Ensembles_DB.
    revert j H1 rho1 e1 H2 rho2 e2 b drop S;
      induction k as [k IHk] using lt_wf_rec1;
      intros j H1 rho1 e1 H2 rho2 e2 b drop S Hrel Hdinv Hun Hdis1 Hdis2 Hdrop.
    inv Hdrop. 
    - (* ----------- Econstr ----------- (3) *)
      eapply exp_rel_constr_compat. 
      + admit. 
      + admit. 
      + admit. 
      + intros l Hloc. admit.      
      + admit. 
      + intros j'. setoid_rewrite Setminus_Union in Hrel. 
        eapply var_log_rel_Forall2.   
        * admit. 
        * admit. 
      + intros vs1 vs2 l1 l2 H1' H2' Hleq Hloc1 Hloc2 Halloc1 Halloc2 HForall2 j'. 
        eapply IHk with (S := S) (drop := drop). 
        * simpl in *. omega. 
        * intros j''. 
          eapply env_log_rel_P_set. 

          eapply env_log_rel_i_monotonic with (i := k); tci. 

          eapply env_log_rel_P_antimon with (S1 := (occurs_free (Econstr x ct ys e) \\ S \\ dropped_funs drop)). 
          admit. 
          
          normalize_occurs_free. 
          rewrite !Setminus_Union. 
          rewrite !Union_assoc. rewrite (Union_commut _ ([set x])). 
          rewrite <- Setminus_Union... 
          omega.
          
          admit. 
        * eapply drop_invariant_extend; [|eassumption]. 
          intros Hcontra. eapply Hdis1. 
          normalize_bound_var. split. eassumption. eauto with Ensembles_DB. 
        * inv Hun. eassumption. 
        * eapply Disjoint_Included_r; [|eassumption]. 
          normalize_bound_var... 
        * eapply Disjoint_Included_l. 
          eapply occurs_free_Econstr_Included. 
          eapply Union_Disjoint_l. 
          eapply Disjoint_Included_r; [|eassumption]. 
          normalize_bound_var... 
          inv Hun. eapply Disjoint_Singleton_l. eassumption. 
        * eassumption. 
    - (* ----------- Eprim ----------- *)
      admit. 
    - (* ----------- Eproj ----------- (1) *)
      eapply exp_rel_proj_compat.
      + admit. (* precondition preservation *) 
      + admit. (* postcondition preservation *)
      + admit. (* base case for post *)
      + intros j'. setoid_rewrite Setminus_Union in Hrel.
        eapply Hrel. 
        split; [| eassumption ].
        normalize_occurs_free...
      + intros v1 v2 Hleq Hv1 Hv2 Hrelv j'. 
        eapply IHk with (S := S) (drop := drop).
        * simpl in *. omega. 
        * intros j''. 
          eapply env_log_rel_P_set. 

          eapply env_log_rel_i_monotonic with (i := k); tci.
          (* Note: These generates a bunch of goals of the form [Proper ... ]. Should be solvable
             with the tactic [tci] (shorthand for [eauto with typeclass_instances]. *)
          eapply env_log_rel_P_antimon. eapply Hrel. 
          
          normalize_occurs_free. 
          rewrite !Setminus_Union.
          rewrite !Union_assoc. rewrite (Union_commut _ ([set x])).
          rewrite <- Setminus_Union...
          omega. 

          eapply Hrelv. 
        * eapply drop_invariant_extend; [| eassumption ].
          intros Hcontra.
          eapply Hdis1. 
          normalize_bound_var. split. eassumption. eauto with Ensembles_DB. 
        * inv Hun. eassumption.
        * eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var...
        * eapply Disjoint_Included_l.
          eapply occurs_free_Eproj_Included.
          eapply Union_Disjoint_l.

          eapply Disjoint_Included_r; [| eassumption ].
          normalize_bound_var...

          inv Hun. eapply Disjoint_Singleton_l. eassumption.
        * eassumption. 
    - (* ----------- Ecase ----------- *)
      admit. 
    - (* ----------- Ehalt ----------- (2) *)
      eapply exp_rel_halt_compat.
      + admit. 
      + admit. (* base case for post *)
      + setoid_rewrite Setminus_Union in Hrel.
        eapply Hrel. 
        split; [| eassumption ]. 
        rewrite occurs_free_Ehalt... 
    - (* ----------- Eapp (unknown) ----------- *)
      eapply exp_rel_app_compat. 
      + admit. 
      + admit. 
      + intros j'. setoid_rewrite Setminus_Union in Hrel. 
        eapply Hrel.
        split; [|eassumption]. 
        normalize_occurs_free... 
      + eapply Forall2_same. intros x Hin j'. 
        setoid_rewrite Setminus_Union in Hrel. eapply Hrel. 
        admit. 
    - (* ----------- Eapp (known) ----------- *)
      admit. 
  Abort. 

End DeadParamCorrect.