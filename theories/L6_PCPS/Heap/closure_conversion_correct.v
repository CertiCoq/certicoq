From CertiCoq.L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics map_util.

From CertiCoq.L6.Heap Require Import heap heap_defs heap_equiv space_sem
     cc_log_rel closure_conversion closure_conversion_util bounds
     invariants GC.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega Permutation.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module ClosureConversionCorrect (H : Heap).

  Module Inv := Invariants H.
  
  Import H Inv.Size.Util.C.LR.Sem.GC.Equiv Inv.Size.Util.C.LR.Sem.GC.Equiv.Defs
         Inv.Size.Util.C.LR.Sem.GC Inv.Size.Util.C.LR.Sem Inv.Size.Util.C.LR
         Inv.Size.Util.C Inv.Size.Util Inv.Size Inv.

  Definition ct := Inv.Size.Util.clo_tag. 
    
  (* TODO move *)
  Instance ToMSet_Union_list_map {A} (f : A -> Ensemble var)
           l {_ : forall x, ToMSet (f x)} : ToMSet (Union_list (map f l)).
  Admitted.

  (** * Lemmas about [project_var] and [project_vars] *)

  (** Correctness of [project_var] *)
  Lemma project_var_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b
        Scope {_ : ToMSet Scope} Scope' Funs Funs' c Γ fenv FVs x C m :
    (* well-formedness *)
    
    project_var ct Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b) (H2, rho2)) ->
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    (forall j, FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
   
    Disjoint _ (Γ |: image fenv (Funs \\ Scope)) (FV Scope Funs FVs) ->
    
    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->

    binding_in_map Scope rho1 ->

    exists b', 
      (forall j, (H1, rho1) ⋞ ^ (Scope'; k; j; GII; GI; b') (H2', rho2'))  /\
      (forall j, Fun_inv k j GII GI b' rho1 H1 rho2' H2' Scope' Funs' fenv FVs) /\
      (forall j, FV_inv k j GII GI b' rho1 H1 rho2' H2' c Scope' Funs' Γ FVs).
  Proof with (now eauto with Ensembles_DB).
    intros Hproj Hcc Hfun Hfv Hdis Hctx Hbin.
    inv Hproj. 
    - inv Hctx. eexists. repeat (split; [ eassumption | ]). eassumption.
    - inv Hctx. simpl in H13. 
      destruct (M.get x rho2) as [v1|] eqn:Hgetx; try congruence.
      destruct (M.get (fenv x) rho2) as [v2|] eqn:Hgetg; try congruence. inv H13. 
      inv H14. inv H15.
      edestruct (Hfun 0)
        as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis'
               & Hget2 & Hget3 & Hget4 & Henv & Heq);
        try eassumption.
      repeat subst_exp. 
      edestruct (alloc (Constr Inv.Size.Util.clo_tag
                               [FunPtr B2 g2; Loc lenv]) H2) as [l' H2''] eqn:Ha. inv H4.
      assert (Hseq : FV (x |: Scope) Funs FVs <--> FV Scope Funs FVs).
      { unfold FV. rewrite <- (Union_assoc [set x] Scope Funs) at 1.
        rewrite !(Union_commut [set x]) at 2.
        rewrite !(Union_commut [set x] (Scope :|: Funs)) at 1.
        do 2 rewrite <- Setminus_Union.
        rewrite Union_Setminus_Included; try eauto with Ensembles_DB typeclass_instances.
        rewrite (Union_Setminus_Included _ (Funs \\ Scope));
          try eauto with Ensembles_DB typeclass_instances.
        rewrite  <- !Union_assoc.
        rewrite Union_Same_set. reflexivity. eapply Singleton_Included.
        right. left. constructor; eauto. }
      assert (Hseq' : FV (x |: Scope) (Funs \\ [set x]) FVs <--> FV Scope Funs FVs).
      { unfold FV.
        rewrite (Union_Setminus_Included (x |: Scope) Funs); tci; [| now eauto with Ensembles_DB ].
        rewrite Setminus_Union. rewrite (Union_Same_set [set x] (x |: Scope)); [| now eauto with Ensembles_DB ].
        rewrite (Union_Setminus_Included (x |: Scope) Funs); tci; [| now eauto with Ensembles_DB ].
        
        rewrite <- (Union_assoc [set x] Scope Funs) at 2.
        rewrite !(Union_commut [set x] (Scope :|: Funs)) at 1.
        do 2 rewrite <- Setminus_Union.
        rewrite Union_Setminus_Included; try eauto with Ensembles_DB typeclass_instances.
        rewrite (Union_Setminus_Included Scope Funs); tci; [| now eauto with Ensembles_DB ].
        rewrite !Setminus_Union.
        rewrite  <- !Union_assoc.
        rewrite Union_Same_set. reflexivity. eapply Singleton_Included.
        right. left. eassumption. }
      exists (b {l1 ~> l}). split; [| split ].
      + intros j.
        edestruct (Hfun j)
          as (l1' & lenv' & B1' & g1' & rhoc' & B2' & g2' & Hget1' & Hdis'' & (* Hsub' & *)
              Hget2' & Hget3' & Hget4' & Henv' & Heq');
          try eassumption. unfold ct in *.
        repeat subst_exp. rewrite H5 in Heq'. eapply cc_approx_env_P_union.
        * intros y Hin. inv Hin. intros v1 Hget. repeat subst_exp. 
          eexists. rewrite M.gss. split. reflexivity.
          eassumption. 
        * eapply cc_approx_env_P_set_not_in_P_r; [| eassumption ].
          eapply cc_approx_env_heap_monotonic.
          eapply HL.subheap_refl.
          eapply HL.alloc_subheap. eassumption.

          intros j'. 
          eapply cc_approx_env_rename_ext with (β := b).
          now eapply Hcc.
          eapply f_eq_subdomain_extend_not_In_S_r.
          intros Hc. eapply Fun_inv_locs_Disjoint1. eapply (Hfun 0).
          now constructor; eauto.
          constructor; try eassumption.
          eapply get_In_env_locs. now constructor; eauto. eassumption. reflexivity. 
          eapply reach'_set_monotonic; [| eassumption ].
          eapply env_locs_monotonic... reflexivity.
           
      + intros j.   
        eapply Fun_inv_set_r; [ eapply Fun_inv_rename_ext | | ]. 
        * eapply Fun_inv_subheap; try rewrite Hseq; try eassumption.
          
          eapply well_formed_antimon; [| eapply FV_reach1; try eassumption; now tci ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          eapply Included_trans. eapply FV_Union1.
          eapply Included_trans. eapply Included_Union_compat. reflexivity.
          eapply FV_Setminus2. tci. rewrite Union_Same_set; [| now eauto with Ensembles_DB ]. 
          eapply Union_Included; [| reflexivity ]. 
          unfold FV. eapply Singleton_Included.
          left; right. now constructor; eauto.

          eapply Included_trans; [| eapply FV_dom1; try eassumption; now tci ].
          eapply env_locs_monotonic.
          eapply Included_trans. eapply FV_Union1.
          eapply Included_trans. eapply Included_Union_compat. reflexivity.
          eapply FV_Setminus2. tci. rewrite Union_Same_set; [| now eauto with Ensembles_DB ]. 
          eapply Union_Included; [| reflexivity ]. 
          unfold FV. eapply Singleton_Included.
          left; right. now constructor; eauto.
          
          eapply Included_trans; [| eapply reachable_in_dom ].
          eapply Included_trans; [| eapply FV_image_reach; eassumption ].

          eapply image_monotonic.
          eapply Included_Setminus. eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eapply Fun_inv_locs_Disjoint2; eauto ]. 
          eapply reach'_set_monotonic. eapply post_set_monotonic. eapply env_locs_monotonic...
          rewrite (reach_unfold H1 (env_locs _ _ )). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. eapply post_set_monotonic. eapply env_locs_monotonic...
          
          eapply well_formed_antimon; [| eapply FV_reach2; try eassumption; now tci ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic. unfold FV_cc...

          eapply Included_trans; [| eapply FV_dom2; try eassumption; now tci ]. 
          eapply env_locs_monotonic. unfold FV_cc...

          intros j'. 
          eapply Fun_inv_Scope_monotonic'; now tci.
          
          now eapply HL.subheap_refl.

          eapply HL.alloc_subheap. eassumption.

        * eapply f_eq_subdomain_extend_not_In_S_r.
          intros Hc. eapply Fun_inv_locs_Disjoint1. now eapply (Hfun 0). now constructor; eauto.
          constructor; eauto.
          eapply get_In_env_locs. reflexivity. eassumption. reflexivity.
          eapply reach'_set_monotonic; [| eassumption ]. eapply env_locs_monotonic.
          unfold FV. rewrite !Setminus_Union_distr. eapply Included_Union_preserv_l...
          reflexivity.
        * intros Hc. inv Hc. eauto.
        * intros Hc. eapply Hdis. constructor. right.
          eapply image_monotonic; [| eassumption ]...
          left; right. now constructor; eauto.  
      +  intros j'.
        eapply FV_inv_set_not_in_FVs_r.
        eapply FV_inv_FV_eq.
        now eapply X. now tci. 
        eapply FV_inv_heap_mon; [ | | ].
        * eapply HL.subheap_refl.
        * eapply HL.alloc_subheap. eassumption.
        * intros j1. eapply FV_inv_rename_ext. now eapply Hfv.

          eapply f_eq_subdomain_extend_not_In_S_l.
          intros Hc. eapply Fun_inv_locs_Disjoint1. now eapply (Hfun 0). now constructor; eauto.
          constructor; eauto.
          eapply get_In_env_locs. constructor; eauto. eassumption. reflexivity.
          eapply reach'_set_monotonic; [| eassumption ].
          eapply env_locs_monotonic. unfold FV. 
          rewrite !Setminus_Union_distr. 
          eapply Included_Union_preserv_r. rewrite Setminus_Union.
          rewrite (Union_commut _ [set x]).
          rewrite (Union_Same_set [set x])...
          reflexivity.  
        * rewrite Union_Setminus_Included.
          rewrite <- Union_assoc. rewrite (Union_Same_set [set x]). reflexivity.  
          eapply Singleton_Included. now right. tci.
          eapply Singleton_Included. now left.
        * intros Hc. subst.
          eapply Hdis. constructor. now left.
          left. right; constructor; eauto.  
    - inv Hctx. inv H18.
      assert (Hseq : FV (x |: Scope) Funs' FVs <--> FV Scope Funs' FVs).
      { unfold FV. rewrite <- (Union_assoc [set x] Scope Funs') at 1.
        rewrite !(Union_commut [set x]) at 2.
        rewrite !(Union_commut [set x] (Scope :|: Funs')) at 1.
        do 2 rewrite <- Setminus_Union.
        rewrite Union_Setminus_Included; try eauto with Ensembles_DB typeclass_instances.
        rewrite (Union_Setminus_Included _ (Funs' \\ Scope));
          try eauto with Ensembles_DB typeclass_instances.
        rewrite  <- !Union_assoc.
        rewrite (Union_Same_set [set x]). reflexivity. eapply Singleton_Included.
        right. right. constructor; eauto. eapply nthN_In. eassumption.
        intros Hc. inv Hc; eauto. }
      eexists. split; [| split ]. 
      + intros j.
        edestruct (Hfv j) as (Hwf & Hkey & vs1 & loc_env & Hget1 & Hget2 & Hall).
        repeat subst_exp. eapply cc_approx_env_P_union.
        * edestruct (Forall2_P_nthN _ _ _ _ FVs _ N _ Hall H3) as (v2 & Hnth' & vs4 & Hget4 & Hrel).
          intros Hc. now inv Hc.  
          intros y Hin v' Hget. inv Hin. rewrite M.gss.
          repeat subst_exp. eexists. split. reflexivity.
          eassumption.
        * eapply cc_approx_env_P_set_not_in_P_r; try eassumption.
          now eauto.
      + intros j. eapply Fun_inv_set_r.
        now eapply Fun_inv_Scope_monotonic; tci.
        now intros Hc; inv Hc; eauto.
        intros Hin. eapply Hdis. constructor. right.
        eapply image_monotonic; [| eassumption ]...
        right. constructor; eauto. eapply nthN_In. eassumption.
        intros Hc. inv Hc; eauto.
      + intros j.
        edestruct (Hfv j) as (Hwf & Hkey & vs1 & loc_env & Hget1 & Hget2 & Hall).
        split. rewrite env_locs_set_not_In. eassumption.

        intros Hc. inv Hc.
        eapply Hdis. constructor. now left.
        right. constructor. eapply nthN_In. eassumption.
        intros Hc; inv Hc; eauto.  split. 
        rewrite Hseq. eassumption. 
        repeat eexists; eauto. 
        rewrite M.gso; eauto.
        intros Hc. subst.
        eapply Hdis. constructor. now left.
        right. constructor. eapply nthN_In. eassumption.
        intros Hc; inv Hc; eauto. 

        eapply Forall2_P_monotonic; [ eassumption | ]...

        Grab Existential Variables. exact 0.

  Qed. 
 
  (** Correctness of [project_vars] *)
  Lemma project_vars_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b
        Scope {Hs : ToMSet Scope} Scope' Funs Funs' fenv c Γ FVs xs C m :
    
    project_vars ct Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b) (H2, rho2)) ->
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    (forall j, FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->


    Disjoint _ (Γ |: image fenv (Funs \\ Scope)) (FV Scope Funs FVs) ->

    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->

    binding_in_map (FV Scope Funs FVs) rho1 ->

    exists b', 
      (forall j, (H1, rho1) ⋞ ^ (Scope'; k; j; GII; GI; b') (H2', rho2'))  /\
      (forall j, Fun_inv k j GII GI b' rho1 H1 rho2' H2' Scope' Funs' fenv FVs) /\
      (forall j, FV_inv k j GII GI b' rho1 H1 rho2' H2' c Scope' Funs' Γ FVs).
  Proof with (now eauto with Ensembles_DB).
    intros Hvars.
    revert b m H1 rho1 H2 rho2 H2' rho2'.
    induction Hvars;
      intros b m H1 rho1 H2 rho2 H2' rho2' Hcc Hfun Hfv
             Hdis Hctx Hbin.
    - inv Hctx. eexists. split; [| split ]; eauto.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      edestruct project_var_correct as (b' & Hcc' & Hfun' & Hfv');
        try eassumption.

      eapply binding_in_map_antimon; [| eassumption ]...
      
      eapply IHHvars; try eassumption.
      + eapply project_var_ToMSet; eassumption.
      + erewrite <- project_var_FV_eq; try eassumption.
        eapply Disjoint_Included_l; [ | eapply Hdis ].
        eapply Included_Union_compat; [reflexivity | ].
        eapply image_monotonic. eapply Included_Setminus_compat.
        eapply project_var_Funs_l. eassumption.
        eapply project_var_Scope_l. eassumption.
      + erewrite <- project_var_FV_eq; try eassumption.
  Qed.
    

  Opaque Pre.

  Lemma Closure_conversion_fundefs_correct
    (k : nat)
    (* The IH *)
    (IHexp :
       forall m : nat,
         m < k ->
         forall (H1 H2 : heap block) (rho1 rho2 : env) 
           (e1 e2 : exp) (C : exp_ctx) (Scope : Ensemble var)
           {Hs : ToMSet Scope}
           (Funs : Ensemble var) (Hf : ToMSet Funs) 
           (FVs : list var) (fenv : positive -> positive) 
           (β : Inj) (c : cTag) (Γ : var) A δ,
           (forall j : nat,
              (H1, rho1) ⋞ ^ (Scope; m; j; PreG; PostG; β) (H2, rho2)) ->
           (forall j : nat,
              FV_inv m j PreG PostG β rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
           (forall j : nat,
              Fun_inv m j PreG PostG β rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
           
           Disjoint var (Γ |: image fenv (Funs \\ Scope))
                    (bound_var e1 :|: FV Scope Funs FVs) ->
           binding_in_map (FV Scope Funs FVs) rho1 ->
           unique_bindings e1 ->
           Disjoint var (bound_var e1) (FV Scope Funs FVs) ->
           Closure_conversion ct Scope Funs fenv c Γ FVs e1 e2 C ->
           forall j : nat,
             (e1, rho1, H1) ⪯ ^ (m; j; Pre (Funs :&: occurs_free e1 \\ Scope) A δ; PreG; Post 0 A δ; PostG) (C |[ e2 ]|, rho2, H2)) :
    (* ************************************************ *)
    forall B1 B2
      (H1 H1' H2 : heap block) lenv (rho1 rho1c rho1' rho2 : env) b
      (Scope Funs : Ensemble var) fenv  (Hs : ToMSet Scope)
      (Hf : ToMSet Funs) (FVs FVs': list var)
      (c : cTag) (Γ' : var),
      
      (* Environment invariants *)
      closed (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) H1 ->
      closed (reach' H2 (env_locs rho2 (FV_cc Scope Funs fenv Γ'))) H2 -> 

      (forall j, Fun_inv k j PreG PostG b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
      (* Free variables invariant for new fundefs *)
      (forall j, FV_inv k j PreG PostG b rho1c H1 rho2 H2 c (Empty_set _) (Empty_set _) Γ' FVs') -> (* no scope, no funs yet *)     
      

      FromList FVs' <--> occurs_free_fundefs B1 ->
      NoDup FVs' ->
      unique_bindings_fundefs B1 ->

      (* Freshness *)
      Disjoint var (bound_var_fundefs B1) (FV Scope Funs FVs :|: FromList FVs') ->
      Disjoint _ (Γ' |: image fenv (Funs \\ Scope)) (name_in_fundefs B1) ->

      (* Properties of the new environment *)
      get lenv H1 = Some (Env rho1c) ->
      M.get Γ' rho2 = Some (Loc (b lenv)) -> 
      env_locs rho1c (Full_set _) \subset env_locs rho1 (FV Scope Funs FVs \\ (Funs \\ Scope)) ->
      
      true_mut B1 ->
      
      Closure_conversion_fundefs ct B1 c FVs' B1 B2 ->
      
      def_closures B1 B1 rho1 H1 (Loc lenv)  = (H1', rho1') -> 
      
      (forall j, Fun_inv k j PreG PostG b
                    rho1' H1' (def_funs B2 B2 rho2) H2
                    (Scope \\ name_in_fundefs B1) (name_in_fundefs B1 :|: Funs) (extend_fundefs' fenv B1 Γ') FVs).
  Proof with (now eauto with Ensembles_DB).
    Opaque cc_approx_exp.
    induction k as [k IHk] using lt_wf_rec1.  
    intros B1 B2 H1 H1' H2 lenv rho1 rho1c rho1' rho2 b
           Scope Funs fenv Hs Hf FVs FVs' c Γ' Hc1 Hc2
           Hfun Hfvs'
           Hfveq Hnd Hun1 Hfresh Hdis
           Hgetenv1 Hgetenv2 Hincl Htm Hccf1 Hclo j.

    destruct (Hfvs' j) as  (Hwf & Hkey & vs & lenv'' & Hgetlenv & Hget' & HallP).
    simpl in Hclo.
    unfold FV in Hkey.
    rewrite !Union_Empty_set_neut_l, !Setminus_Empty_set_neut_r, !Union_Empty_set_neut_l in Hkey.
    
    intros f1 Hin Hnin. repeat subst_exp. 
    edestruct (@Dec _ (name_in_fundefs B1) _ f1) as [ Hfin | Hfnin ].
    - edestruct def_closures_exists as [lf [Hgetf [Hgetlf Hfresh']]]; try eassumption.
      exists lf, lenv, (b lenv), B1, f1, B2, f1.
      split; [ | split; [ | split; [ | split; [ | split; [ | split ] ] ] ]].
      * eassumption.
      * intros Hc.
        
        assert (Hseq : (FV (Scope \\ name_in_fundefs B1)
                           (name_in_fundefs B1 :|: Funs) FVs \\ [set f1]) \subset
                        FV Scope Funs FVs \\ name_in_fundefs B1 :|: (name_in_fundefs B1 \\ [set f1])). 
        { eapply Setminus_Included_Included_Union.
          eapply Included_trans.
          eapply FV_Setminus1. now tci.
          eapply Included_trans. eapply Included_Union_compat. reflexivity. 
          eapply FV_Union2.
          rewrite <- !Union_assoc. rewrite <- Union_Setminus.
          rewrite !Union_assoc. rewrite  <- Union_Setminus. 
          now eauto with Ensembles_DB. now tci. now tci. }
        
        rewrite reach'_Union in Hc.
        rewrite post_Singleton in Hc; [| eassumption ]. simpl in Hc.
        rewrite Union_Empty_set_neut_l in Hc.
         
 
        { inv Hc.  
          - eapply reach'_set_monotonic in H; [| eapply env_locs_monotonic; eassumption ]. 
            rewrite env_locs_Union, reach'_Union in H. inv H.  
            
            + eapply reach'_set_monotonic in H0; [| eapply env_locs_def_funs; [ reflexivity | now eauto ] ].
            
              rewrite <- well_formed_reach_subheap_same in H0.
              
              eapply reachable_in_dom in H0. eapply Hfresh'. eassumption.
              
              eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
              eapply reach'_set_monotonic. eapply env_locs_monotonic...
              
              eapply Included_trans; [| eapply env_locs_closed; eassumption ].
              eapply Included_trans; [| eapply reach'_extensive ].
              eapply env_locs_monotonic...

              eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
              eapply reach'_set_monotonic. eapply env_locs_monotonic...
              
              eapply Included_trans; [| eapply env_locs_closed; eassumption ].
              eapply Included_trans; [| eapply reach'_extensive ].
              eapply env_locs_monotonic...
              
              eapply def_funs_subheap. now eauto.
              
            + rewrite reach_unfold in H0. inv H0.
              
              eapply def_closures_env_locs_fresh. eassumption.
              eapply unique_bindings_fundefs_unique_functions.
              eassumption. eassumption.
              constructor; [| eassumption ]. rewrite env_locs_Singleton; eauto. reflexivity.

              eapply reach'_set_monotonic in H;
                [| eapply Included_trans; [eapply post_set_monotonic; eapply env_locs_monotonic
                                          | eapply def_closures_post; eassumption ] ];
                try now eauto with Ensembles_DB.
              
              rewrite reach_unfold in H. inv H.
               
              * inv H0. eapply Hfresh'. eexists; eauto.
              * simpl in H0. rewrite post_Singleton in H0; [| eapply def_funs_subheap; now eauto ].
                simpl in H0.
                rewrite <- reach'_subheap in H0; [| | | eapply def_funs_subheap; now eauto ].
                rewrite env_locs_key_set, Hkey in H0.  
                eapply reachable_in_dom in H0. contradiction.
                
                eapply well_formed_antimon; [| eapply FV_inv_reach1; now apply Hfvs' ].
                eapply reach'_set_monotonic. rewrite Union_Empty_set_neut_l, Setminus_Empty_set_neut_r.
                eapply env_locs_monotonic. now eauto with Ensembles_DB.
                
                eapply Included_trans; [| eapply FV_inv_dom1; now apply Hfvs' ].
                eapply env_locs_monotonic. unfold FV.
                rewrite !Union_Empty_set_neut_l, !Setminus_Empty_set_neut_r at 1...
                
                eapply well_formed_antimon; [| eapply FV_inv_reach1; now apply Hfvs' ].
                eapply reach'_set_monotonic. rewrite Union_Empty_set_neut_l, Setminus_Empty_set_neut_r.
                rewrite env_locs_key_set, Hkey. 
                eapply env_locs_monotonic...
                
                eapply Included_trans; [| eapply FV_inv_dom1; now apply Hfvs' ].
                rewrite env_locs_key_set, Hkey. 
                eapply env_locs_monotonic. 
                rewrite !Union_Empty_set_neut_l, !Setminus_Empty_set_neut_r at 1...
                
          - rewrite reach_unfold in H. inv H.
            * inv H0. eapply Hfresh'. eexists; eauto.
            * simpl in H0. rewrite post_Singleton in H0; [| eapply def_funs_subheap; now eauto ].
              simpl in H0.
              rewrite <- reach'_subheap in H0; [| | | eapply def_funs_subheap; now eauto ].
              rewrite env_locs_key_set, Hkey in H0.  
              eapply reachable_in_dom in H0. contradiction.
              
              eapply well_formed_antimon; [| eapply FV_inv_reach1; now apply Hfvs' ].
              eapply reach'_set_monotonic. rewrite Union_Empty_set_neut_l, Setminus_Empty_set_neut_r.
              eapply env_locs_monotonic. now eauto with Ensembles_DB.
              
              eapply Included_trans; [| eapply FV_inv_dom1; now apply Hfvs' ].
              eapply env_locs_monotonic. unfold FV.
              rewrite !Union_Empty_set_neut_l, !Setminus_Empty_set_neut_r at 1...
              
              eapply well_formed_antimon; [| eapply FV_inv_reach1; now apply Hfvs' ].
              eapply reach'_set_monotonic. rewrite Union_Empty_set_neut_l, Setminus_Empty_set_neut_r.
              rewrite env_locs_key_set, Hkey. 
              eapply env_locs_monotonic...
              
              eapply Included_trans; [| eapply FV_inv_dom1; now apply Hfvs' ].
              rewrite env_locs_key_set, Hkey. 
              eapply env_locs_monotonic. 
              rewrite !Union_Empty_set_neut_l, !Setminus_Empty_set_neut_r at 1... }
      * erewrite def_funs_eq. reflexivity. reflexivity.
        rewrite <- closure_conversion_fundefs_Same_set. eassumption. eassumption.
      * eassumption.
      * rewrite extend_fundefs'_get_s.
        erewrite def_funs_neq. eassumption. reflexivity.
        intros Hc. eapply Hdis.
        rewrite closure_conversion_fundefs_Same_set.
        constructor. now left. eassumption.
        eassumption. eassumption.
      * eapply FV_inv_cc_approx_clos; [ | | | | | ].
        
        eapply FV_inv_heap_mon. eapply def_funs_subheap. now eauto.
        now eapply HL.subheap_refl. 
        eassumption.
        unfold FV in Hkey.
        rewrite <- Hkey. eapply binding_in_map_key_set.
        eassumption. 

        eapply def_funs_subheap; try eassumption. now eauto. 
        eassumption. reflexivity.
      * destruct (alloc (Constr _ [FunPtr B2 f1; Loc (b lenv)]) H2)
          as [lenv2 H2'] eqn:Ha'.

        simpl cc_approx_val'. erewrite !(gas _ _ _ _ _ Ha'); eauto.
        split; [ rewrite extend_gss; reflexivity |].
        rewrite Hgetlf. 
         
        { split.
          (* Closure environment relation *)
          - intros i Hlt.
            eapply FV_inv_cc_approx_clos; [ | | eassumption | | eassumption | ].
            eapply FV_inv_heap_mon. eapply def_funs_subheap. now eauto.
            eapply HL.alloc_subheap. eassumption. intros j'.
 
            eapply FV_inv_rename_ext; [ now eauto | ].
 
            eapply f_eq_subdomain_extend_not_In_S_l.
            intros Hc. eapply reachable_in_dom in Hc. contradiction.
            eapply FV_inv_reach1. eassumption.
            eapply FV_inv_dom1. eassumption.
            reflexivity.
            rewrite <- Hkey. now eapply binding_in_map_key_set. 
            eapply def_funs_subheap; try eassumption. now eauto.
            rewrite extend_gso. reflexivity.
            intros Hc; subst. 
            eapply def_funs_subheap in Hgetenv1; try now eauto.
            congruence.
          - intros b1 b2 lenv1 rhoc' rhoc1 rhoc2 H3 H3' H4 lr xs1 ft ef vs1 vs2. 
            intros Heq1 Hinj1 Heq2 Hinj2 Hf' Hget Hdef Hset Hlen.
            edestruct Closure_conversion_fundefs_find_def as
                (Γ'' & e2 & C' & Hfind & Hdisg & Hclo').
            eassumption. eassumption.


            assert (Hf1 :  ~ In var (FromList xs1) Γ'' ).
            { intros Hc. eapply Hdisg... }
            assert (Hf2 :  ~ In var (name_in_fundefs B1) Γ'' ).
            { intros Hc. eapply Hdisg... }

            assert (Ha : key_set rhoc' <--> key_set rho1c).
            { rewrite res_equiv_eq in Heq1. destruct Heq1 as [Hbeq1 Hres]. 

              unfold id in *; subst.
              eapply def_funs_subheap in Hgetenv1; eauto.
              rewrite Hgetenv1, Hget in Hres. simpl in Hres.
              eapply heap_env_equiv_key_set. symmetry. eassumption. }


            edestruct (setlist_length rhoc1 (def_funs B2 B2 (M.empty value))
                                      rhoc2 xs1 vs1 vs2) 
              as [rho2' Hset2]; [ eassumption (* add length vs1 = lngth v2 *)
                                | now apply Hset | ].
            { do 3 eexists. split; [| split ]. 
              - eassumption.
              - simpl. rewrite Hset2. reflexivity.
              - intros i Hlt b' Hall Hfeq.

                assert (Hwf1' : closed (reach' H3 (Union_list (map val_loc vs1))) H3). 
                { (* eapply reach'_closed. *)
                  revert Hall. clear. revert vs2.
                  induction vs1; intros vs2 Hall.
                  - simpl. rewrite reach'_Empty_set.
                    intros x Hin. inv Hin.
                  - simpl. rewrite reach'_Union.
                    destruct vs2 as [| b vs2].
                    specialize (Hall 0). now inv Hall.
                    eapply closed_Union.

                    eapply reach'_closed.
                    eapply cc_approx_val_well_formed_reach1. 
                    intros j. specialize (Hall j). inv Hall. rewrite cc_approx_val_eq in H2.
                    eassumption. 
                    specialize (Hall 0). inv Hall. 
                    eapply cc_approx_val_dom1. rewrite cc_approx_val_eq in H2.
                    eassumption. 

                    eapply IHvs1. intros j. specialize (Hall j). inv Hall.
                    rewrite cc_approx_val_eq in H2. eassumption. }

                  assert (Hfvs'' : forall j2, FV_inv i j2 PreG PostG b' rhoc' H3 (M.set Γ'' (Loc lr) (M.empty value)) H4
                                                 c (Empty_set var) (Empty_set var) Γ'' FVs'). 
                  { intros j2'. 
                    eapply FV_inv_heap_f_eq_subdomain; [| eapply f_eq_subdomain_antimon; try eassumption ].
                    eapply FV_inv_heap_env_equiv with (H1 := H1') (H2 := H2').
                    eapply FV_inv_rho_swap with (rho2' := M.set Γ'' (Loc (b lenv)) (M.empty value)). tci.
                    
                    eapply FV_inv_monotonic.
                    eapply FV_inv_heap_mon. eapply def_funs_subheap. now eauto. 
                    eapply HL.alloc_subheap. eassumption.  
                    intros j3. eapply FV_inv_rename_ext.  eapply Hfvs'.
                    
                    eapply f_eq_subdomain_extend_not_In_S_l. intros Hc. eapply reachable_in_dom in Hc.
                    contradiction. 
                    
                    eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
                    eapply reach'_set_monotonic. rewrite Union_Empty_set_neut_r, Setminus_Empty_set_neut_r.
                    eapply Included_trans. eapply Included_trans. eapply env_locs_monotonic with (S2 := Full_set _)...
                    eassumption. eapply env_locs_monotonic...
                    
                    eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                    rewrite Union_Empty_set_neut_r, Setminus_Empty_set_neut_r.
                    eapply Included_trans. eapply Included_trans. eapply env_locs_monotonic with (S2 := Full_set _)...
                    eassumption. eapply Included_trans; [| eapply reach'_extensive ]. eapply env_locs_monotonic...
                    reflexivity.
                    
                    omega.
                    rewrite M.gss. eassumption.
                    
                    rewrite res_equiv_eq in Heq1. simpl in Heq1. destruct Heq1 as [Hbeq Hres]. 
                    unfold id in *; subst.
                    eapply def_funs_subheap in Hgetenv1; eauto. rewrite Hgetenv1, Hget in Hres. 
                    eassumption.
                    
                    eapply injective_subdomain_antimon. eassumption.
                     
                    rewrite (reach'_idempotent H3 [set lenv1]). eapply reach'_set_monotonic.
                    eapply Included_trans; [| eapply Included_post_reach' ]. rewrite post_Singleton; eauto.
                    reflexivity.
                    
                    eapply heap_env_equiv_set. rewrite Setminus_Same_set_Empty_set.
                    split; intros x v Hin'; now inv Hin'.
                    eassumption.
                    
                    eapply injective_subdomain_antimon. eassumption.
                    
                    eapply reach'_set_monotonic. eapply Included_trans. eapply env_locs_set_Inlcuded'.
                    rewrite <- env_locs_Empty...


                    rewrite (reach_unfold H3 [set lenv1]), post_Singleton; eauto.
                    eapply Included_Union_preserv_r. 
                    eapply reach'_set_monotonic. simpl.
                    rewrite env_locs_key_set, Ha, Hkey... }
                  edestruct (Hfvs'' j) as (Hwf'' & Hkey'' & vs1'' & loc_env'' & Hget1'' & Hget2'' & Hall'').
                  repeat subst_exp. 
                  split.
                + intros Hgc2 g2 Hl2. 
                  eapply PreSubsetCompat 
                  with (Funs := name_in_fundefs B1 :&: occurs_free ef).
                  { eapply GC_pre with (Scope := reach' H3 (env_locs rhoc2 (occurs_free ef :&: FromList xs1) :|:
                                                                     (env_locs rhoc' (FromList FVs'))))
                                         (xs2' := Γ'' :: xs1) (β := b').
                    - eauto 20 with typeclass_instances.
                    - eassumption.
                    - eassumption.
                    - eassumption.
                    - eassumption.
                    - simpl. rewrite Hset2. reflexivity.
                    - eassumption.
                    - eassumption.
                    - rewrite M.gss in Hget1''. inv Hget1''. eassumption. 
                    - eapply Forall2_P_Forall2 in Hall''.
                      erewrite <- Forall2_length; [| eassumption ].
                      rewrite !PS.cardinal_spec. erewrite Same_set_FromList_length'. reflexivity. 
                      eassumption. eapply NoDupA_NoDup. eapply PS.elements_spec2w.
                      rewrite <- !FromSet_elements.
                      rewrite Hfveq. now eapply fundefs_fv_correct. 
                      now eauto with Ensembles_DB.
                    - intros j1.
                      rewrite reach'_Union. eapply cc_approx_heap_union.
                      + eapply cc_approx_env_cc_approx_heap. eassumption. eassumption.
                        intros j2. eapply cc_approx_env_P_setlist_l; try eassumption.
                        rewrite Setminus_Included_Empty_set. eapply cc_approx_env_Empty_set.
                        now eapply Included_Intersection_r.
                        eapply Forall2_monotonic; [| eapply Hall ].
                        intros. rewrite <- cc_approx_val_eq. now eapply H.
                      + eapply cc_approx_heap_antimon; [| eapply FV_inv_heap_equiv; eassumption ].
                        eapply reach'_set_monotonic. eapply env_locs_monotonic...
                    - eapply Disjoint_Included_l.
                      eapply Included_Intersection_l.
                      eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                      eapply find_def_correct. eassumption. eassumption.
                    - eapply unique_bindings_fundefs_unique_functions. eassumption.
                    - rewrite Closure_conversion_fv_cor at 3; [| eassumption ].
                      rewrite !env_locs_Union, !reach'_Union. eapply Union_Included. eapply Union_Included. 
                      + do 2 eapply Included_Union_preserv_l.
                        eapply reach'_heap_monotonic. eapply def_funs_subheap; eauto.
                      + eapply find_def_correct in Hf'. assert (Hf'' := Hf'). eapply Htm in Hf'. inv Hf'.
                        * eapply Included_Union_preserv_r.
                          rewrite <- env_locs_setlist_Disjoint with (rho' := rhoc2); try eassumption. 
                          rewrite def_closures_env_locs' with (rho1' := rhoc1); try eassumption.
                          rewrite Setminus_Disjoint.
                          eapply Included_trans; [| eapply reach'_heap_monotonic; eapply def_funs_subheap; now eauto ].
                          eapply reach'_set_monotonic.
                          eapply env_locs_monotonic. eapply Included_Intersection. rewrite <- H.
                          eapply Hfveq. reflexivity.
                          eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hfresh ].
                          now eauto with Ensembles_DB.
                          eapply Union_Included. 
                          eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs; eassumption ]... 
                          now eapply name_in_fundefs_bound_var_fundefs.
                          eapply Disjoint_Included_l.
                          eapply Included_Intersection_r. now eauto with Ensembles_DB.
                          eapply Disjoint_Included_l.
                          eapply Included_Intersection_r. now eauto with Ensembles_DB.
                        * eapply Included_Union_preserv_l.
                          eapply Included_Union_preserv_r. destruct H as [ff Hinff].
                          rewrite <- env_locs_setlist_Disjoint with (rho' := rhoc2); try eassumption. 
                          edestruct def_closures_exists as [lff [Hegtf [Hgetlff _]]]. eassumption.
                          inv Hinff. eassumption.
                          rewrite (reach_unfold H3'). eapply Included_Union_preserv_r. 
                          rewrite (reach_unfold H3'). eapply Included_Union_preserv_r. 
                          eapply Included_trans; [| eapply reach'_heap_monotonic; eapply def_funs_subheap; now eauto ].
                          eapply reach'_set_monotonic.
                          intros ll Hinll. eapply post_set_monotonic. eapply post_set_monotonic.
                          eapply get_In_env_locs.
                          rewrite Setminus_Disjoint. rewrite Intersection_commut. eassumption.
                          eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                          eassumption. eassumption. eassumption. 
                          simpl. erewrite post_Singleton; eauto. simpl. rewrite Union_Empty_set_neut_l. 
                          erewrite post_Singleton; [| eapply def_funs_subheap; eauto ]. simpl.
                          rewrite env_locs_key_set, Hkey''. eapply env_locs_monotonic; [| eassumption ]...
                          eapply Disjoint_Included_l.
                          eapply Included_Intersection_r. now eauto with Ensembles_DB.
                      + eapply Included_Union_preserv_l. eapply Included_Union_preserv_r.
                        rewrite Setminus_Disjoint, Intersection_commut. eapply reach'_extensive.
                        eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                        eapply find_def_correct. eassumption. eassumption.
                    - eapply Included_trans. eapply reach'_set_monotonic.
                      eapply env_locs_monotonic. eapply Closure_conversion_cc_fv_cor.
                      eassumption. intros Hc; inv Hc; now eauto.
                      eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                      eapply find_def_correct. eassumption. eassumption.
                      (* rewrite <- env_locs_setlist_Disjoint with (rho' := rhoc2) (S := (occurs_free ef :&: FromList xs1)); *)
                      (*   try eassumption. *)
                      (* rewrite def_closures_env_locs' with (rho1' := rhoc1); try eassumption. *)
                      (* rewrite env_locs_key_set. rewrite Ha, Hkey.  *)
                      rewrite Setminus_Disjoint.
                      
                      eapply Included_trans. eapply reach'_set_monotonic.
                      eapply env_locs_set_Inlcuded'. rewrite !Setminus_Union_distr.
                      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
                      rewrite !Setminus_Disjoint. rewrite env_locs_Union.
                      rewrite <- env_locs_setlist_Disjoint with (rho' := rho2') (S := (occurs_free ef :&: name_in_fundefs B1));
                        try eassumption. 
                      assert (Hlem : env_locs (def_funs B2 B2 (M.empty value)) (occurs_free ef :&: name_in_fundefs B1) <-->
                                     Empty_set _).
                      { rewrite env_locs_def_funs'; [ | | reflexivity ]; tci. rewrite <- env_locs_Empty. reflexivity. }
                      rewrite Hlem. rewrite Union_Empty_set_neut_r.
                      rewrite !reach'_Union. eapply Union_Included.
                      + eapply FV_inv_image_reach_eq in Hfvs''.
                        rewrite image_Union. rewrite Hfvs''. rewrite env_locs_set_In.
                        rewrite Setminus_Same_set_Empty_set. rewrite <- !env_locs_Empty, Union_Empty_set_neut_r.
                        rewrite reach_unfold... reflexivity.
                      + rewrite image_Union. eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
                        rewrite cc_approx_env_image_reach. reflexivity.
                        intros j1. eapply cc_approx_env_P_setlist_l; try eassumption.
                        rewrite Setminus_Included_Empty_set. eapply cc_approx_env_Empty_set.
                        now eapply Included_Intersection_r.
                        eapply Forall2_monotonic; [| eapply Hall ].
                        intros. rewrite <- cc_approx_val_eq. now eapply H.
                        eapply binding_in_map_antimon; [| eapply binding_in_map_setlist with (S := Empty_set _);
                                                          try eassumption ].
                        eapply Included_trans; [ eapply Included_Intersection_r | ]...
                        intros x Hinx. inv Hinx.
                      + eapply Disjoint_Included_l.
                        eapply Included_Intersection_r.
                        eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                        eapply find_def_correct. eassumption. eassumption.
                      + eapply Disjoint_Singleton_r. intros Hc; inv Hc; eauto.
                      + eapply Disjoint_Singleton_r. intros Hc; inv Hc; eauto.
                      + eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                        eapply find_def_correct. eassumption. eassumption. } 
                  now eauto with Ensembles_DB.
                + intros j0. eapply cc_approx_exp_rel_mon_post.
                  eapply cc_approx_exp_rel_mon_pre.
                  eapply IHexp with (Scope := (FromList xs1)) (Funs := name_in_fundefs B1)
                                                              (fenv := extend_fundefs' id B1 Γ'')
                                                              (β := b');
                    [ | | | | | | | | eassumption ].
                  * eassumption.
                  * intros j1.
                    eapply cc_approx_env_P_set_not_in_P_r.
                    eapply cc_approx_env_heap_monotonic; [| | ].
                    eapply def_funs_subheap. now eauto.
                    now eapply HL.subheap_refl. 
                    intros j2. eapply cc_approx_env_P_setlist_l.
                    rewrite Setminus_Same_set_Empty_set.
                    eapply cc_approx_env_Empty_set.
                    eapply Forall2_monotonic; [| now apply Hall ].
                    intros x1 x2 HR.
                    rewrite cc_approx_val_eq in *.
                    eapply HR. eassumption.
                    eassumption.
                    eassumption.
                  * intros j1.
                    eapply Proper_FV_inv_Scope;
                      [ rewrite <- (Union_Empty_set_neut_r (FromList xs1)); reflexivity | | | | ];
                      try reflexivity.
                    eapply setlist_FV_inv; [| | eassumption ]. tci.
                    
                    eapply Proper_FV_inv_Funs; 
                      [ rewrite <- (Union_Empty_set_neut_r (name_in_fundefs B1)); reflexivity | | | ];
                      try reflexivity.                  
                    eapply def_closures_FV_inv; [| | eassumption ]. tci.
                    
                    intros j2.                  

                    eapply FV_inv_rho_swap. tci. eapply Hfvs''. rewrite !M.gss. reflexivity.
                    
                  * intros j1.

                    eapply Proper_Fun_inv_Scope;
                      [ rewrite <- (Union_Empty_set_neut_r (FromList xs1)); reflexivity | | | | ];
                      try reflexivity.

                    eapply Fun_inv_Scope_Disjoint.
                    
                    edestruct (setlist_length (def_funs B2 B2 (M.empty value))
                                              (M.set Γ'' (Loc lr)
                                                     (def_funs B2 B2 (M.empty value))))
                      as [rho2'' Hset''].
                    reflexivity. eassumption.
                    
                    eapply Fun_inv_suffle_setlist_l; try eassumption.
                    
                    eapply Fun_inv_setlist_r; try eassumption.
                    eapply Fun_inv_suffle_def_funs_l.  
                    eapply Fun_inv_setlist_l; try eassumption.
                    
                    eapply Proper_Fun_inv_Scope;
                      [ rewrite <- (Setminus_Disjoint (Empty_set var) (name_in_fundefs B1))
                      | | | | ];
                      try reflexivity; eauto with Ensembles_DB.
                    eapply Proper_Fun_inv_Funs;
                      [ rewrite <- (Union_Empty_set_neut_r (name_in_fundefs B1)); reflexivity | | | ];
                      try reflexivity; eauto with Ensembles_DB.

                    assert (Hwf1 : closed (reach' H3 (env_locs rhoc' (FromList FVs'))) H3).
                    {  eapply reach'_closed.

                       eapply well_formed_antimon; [| eapply FV_inv_reach1; eassumption ].
                       eapply reach'_set_monotonic. eapply env_locs_monotonic.
                       unfold FV...

                       eapply Included_trans; [| eapply FV_inv_dom1; eassumption ]. 
                       eapply env_locs_monotonic... }

                    assert (Hwf3 : closed (reach' H4 [set lr]) H4).
                    {  eapply reach'_closed.

                       eapply well_formed_antimon; [| eapply FV_inv_reach2; eapply Hfvs'' ].
                       rewrite env_locs_set_In. eapply reach'_set_monotonic...
                       reflexivity. 
                       
                       eapply Included_trans; [| eapply FV_inv_dom2; eassumption ]. 
                       rewrite env_locs_set_In... }

                    
                    (* IH fundefs *)  
                    
                    { eapply IHk with (Scope := Empty_set _); try eassumption; tci.
                      - intros; eauto.
                        eapply IHexp with (Scope := Scope0) (Funs := Funs0); eauto. omega.
                      - unfold FV. rewrite !Union_Empty_set_neut_r, !Setminus_Empty_set_neut_r,
                                   !Union_Empty_set_neut_l at 1.
                        eassumption. 
                      - unfold FV_cc.
                        rewrite !image_id, !Union_Empty_set_neut_l, !Setminus_Empty_set_neut_r,
                        !Union_Empty_set_neut_l at 1.
                        rewrite env_locs_set_In, <- env_locs_Empty, Union_Empty_set_neut_r.
                        eassumption. reflexivity. 
                      - intros j2 x Hnin1 Hin2. inv Hin2.
                      - unfold FV.
                        rewrite !Union_Empty_set_neut_r, !Setminus_Empty_set_neut_r, 
                      !Union_Empty_set_neut_l at 1.
                        eapply Disjoint_Included_r; [| eassumption ]...
                      - rewrite image_id. rewrite Setminus_Empty_set_neut_r, Union_Empty_set_neut_r. 
                        eapply Disjoint_Singleton_l. eassumption.
                      - rewrite M.gss. 
                        eapply res_equiv_locs_eq in Heq1.
                        eapply res_equiv_locs_eq in Heq2.
                        rewrite <- Hfeq.
                        unfold compose, id in *. rewrite <- Heq1.
                        rewrite extend_gso. rewrite <- Heq2. reflexivity.
                        intros Hc; subst. eapply Hfresh'. eexists. eassumption. 
                        eapply reach'_extensive. reflexivity.
                        eassumption. eassumption. (* XXX remove extra params *)
                      - unfold FV.
                        rewrite !Union_Empty_set_neut_r, !Setminus_Empty_set_neut_r, 
                        !Union_Empty_set_neut_l at 1.
                        
                        rewrite env_locs_key_set, Ha, Hkey. reflexivity.  }
                    
                    rewrite Setminus_Empty_set_neut_r. eapply unique_bindings_fun_in_fundefs. 
                    eapply find_def_correct. eassumption. eassumption.
                    
                    
                    rewrite Setminus_Empty_set_neut_r. 
                    eapply Disjoint_Included_l; [| eapply Disjoint_sym;
                                                   eapply def_closures_env_locs_Disjoint;
                                                   eassumption ].
                    rewrite <- well_formed_reach_subheap_same; [| |
                                                               | eapply def_funs_subheap; now eauto ]. 
                    
                    eapply reachable_in_dom; [ | ].
                    eapply well_formed'_closed. eassumption.
                    eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                    eapply reach'_extensive.

                    eapply well_formed'_closed. eassumption.
                    eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                    eapply reach'_extensive.
                    rewrite <- closure_conversion_fundefs_Same_set; eassumption.
                    
                   rewrite Setminus_Empty_set_neut_r. eapply unique_bindings_fun_in_fundefs.
                   eapply find_def_correct. eassumption. eassumption.
                   
                   rewrite Setminus_Empty_set_neut_r.
                   eapply Disjoint_Included_r. eapply extend_fundefs'_image.
                   eapply Disjoint_Singleton_r. eassumption.
                   rewrite <- env_locs_setlist_Disjoint; [| eassumption | ].

                   eapply Disjoint_Included_r;
                     [|  eapply def_closures_env_locs_Disjoint; eassumption ].
                   rewrite <- well_formed_reach_subheap_same;
                   [ | | | now eapply def_funs_subheap; eauto ]. 

                   eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                   eapply reach'_set_monotonic. eapply env_locs_setlist_In. eassumption.

                   eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
                   eapply reach'_set_monotonic. eapply env_locs_setlist_In. eassumption.

                   eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                   eapply Included_trans. eapply env_locs_setlist_In. eassumption.
                   eapply reach'_extensive. 
                   
                   eapply Disjoint_sym. eapply unique_bindings_fun_in_fundefs.
                   eapply find_def_correct. eassumption. eassumption. 
                  * rewrite (Union_commut [set Γ'']), (Union_Same_set _ [set Γ'']).
                    
                    eapply Disjoint_Singleton_l. intros Hc.
                    inv Hc. eapply Hdisg...
                    eapply Hdisg. eapply Included_trans; [| | eassumption ]. reflexivity.
                    unfold FV...

                    eapply Included_trans. eapply image_monotonic.  eapply Setminus_Included.
                    eapply Included_trans. eapply extend_fundefs'_image. reflexivity.
                  * unfold FV. rewrite <- !Union_assoc.
                    eapply binding_in_map_setlist; [| eassumption ].
                    eapply binding_in_map_antimon. eapply Included_Union_compat.
                    eapply Setminus_Included. eapply Setminus_Included.
                    eapply binding_in_map_def_closures; [| eassumption ]. 
                    eapply binding_in_map_antimon.
                    rewrite <- Hkey. reflexivity. rewrite <- Ha. 
                    eapply binding_in_map_key_set.
                  * eapply unique_bindings_fun_in_fundefs.
                    eapply find_def_correct. eassumption. eassumption.
                  * unfold FV. eapply Union_Disjoint_r.
                    eapply Union_Disjoint_r.
                    
                    eapply unique_bindings_fun_in_fundefs. 
                    eapply find_def_correct. eassumption. eassumption.
                    
                    eapply Disjoint_Included_r. eapply Setminus_Included. 
                    eapply unique_bindings_fun_in_fundefs. 
                    eapply find_def_correct. eassumption. eassumption.
                    
                    eapply Disjoint_Included_r. eapply Setminus_Included. 
                    eapply Disjoint_Included; [| | eapply Hfresh ].
                    now eauto with Ensembles_DB.
                    eapply Included_trans; [| eapply fun_in_fundefs_bound_var_fundefs;
                                              eapply find_def_correct; eassumption ]...
                  * intros [[H0 rho0] e0] [[H00 rho00] e00]. unfold PreG.
                    intros Hyp. eapply Hyp.
                  * intros [[[[H0 rho0] e0] c0] m0] [[[[H00 rho00] e00] c00] m00]. unfold PreG.
                    intros Hyp. eapply Hyp.
        } }
        
    - inv Hnin. contradiction. 
      edestruct (Hfun j) as
          (l1 & lenv'' & B1' & g1 & rhoc & B2' & g2 & Hgetf1 & Hnin' & Hgetf1'
              & Hgetl1 & Hext & Henvc & Hrel).
      intros Hc. eapply Hin. constructor; eauto. eassumption.

      eexists l1, lenv'', B1', g1, rhoc, B2', g2.
      split; [| split; [| split; [| split; [| split; [| split ]]]]]. 
      + erewrite def_closures_get_neq; eassumption.
      + intros Hc. eapply Hnin'. rewrite reach'_Union in Hc.
        rewrite reach'_Union. 
        eapply Included_Union_compat in Hc;
          [
          | eapply reach'_set_monotonic ;
            eapply Defs.def_closures_env_locs; try eapply Hclo 
          | reflexivity ].
        simpl in Hc.
        rewrite !reach'_Union in Hc. 
        rewrite post_Singleton in Hc; [| eapply def_funs_subheap; now eauto ].
        simpl in Hc. rewrite Union_Empty_set_neut_l, <- Union_assoc in Hc. 
        
        inv Hc.  
        * rewrite <- well_formed_reach_subheap_same in H0.
          left. 
          eapply reach'_set_monotonic; [| eassumption ].
          eapply env_locs_monotonic.
          do 2 eapply Setminus_Included_Included_Union.
          eapply Included_trans.
          eapply FV_Setminus1. now tci.
          eapply Included_trans. eapply Included_Union_compat. reflexivity.
          eapply FV_Union2.
          rewrite <- !Union_assoc.
          rewrite (Union_commut (name_in_fundefs B1) [set f1]).
          rewrite !Union_assoc. rewrite <- Union_Setminus.
          now eauto with Ensembles_DB.
          tci.
           
          eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          do 2 eapply Setminus_Included_Included_Union. eapply Included_trans. 
          eapply FV_Setminus1. now tci. 
          eapply Included_trans. eapply Included_Union_compat. reflexivity.
          eapply FV_Union2. now eauto with Ensembles_DB. tci.
          
          eapply Included_trans; [| eapply env_locs_closed; eassumption ].
          eapply Included_trans; [| eapply reach'_extensive ]. eapply env_locs_monotonic. 
          do 2 eapply Setminus_Included_Included_Union. eapply Included_trans.
          eapply FV_Setminus1. now tci.
          eapply Included_trans. eapply Included_Union_compat. reflexivity.
          eapply FV_Union2. now eauto with Ensembles_DB.
          
          eapply def_funs_subheap. now eauto.

        * rewrite reach_unfold, <- Union_assoc in H0. 
          { inv H0.
            - exfalso. eapply def_closures_env_locs_Disjoint. eassumption.
              constructor; eauto. eexists; eauto.
            - rewrite post_Singleton; [| eauto ]. simpl. rewrite Union_Empty_set_neut_l.
              inv H3.  
              + eapply reach'_set_monotonic in H0; [| now eapply def_closures_post; eauto ].
                rewrite reach_unfold in H0. inv H0. inv H3. congruence.
                simpl in H3. rewrite post_Singleton in H3; [| eapply def_funs_subheap; now eauto ].
                simpl in H3. rewrite env_locs_key_set in H3. rewrite Hkey in H3.

                repeat subst_exp. 
                rewrite <- Hkey, <- env_locs_key_set in H3.
                eapply reach'_set_monotonic in H3; [| eassumption ].
                                
                rewrite <- reach'_subheap in H3; [| | | eapply def_funs_subheap; now eauto ].
                left. eapply reach'_set_monotonic; [| eassumption ].
                eapply env_locs_monotonic. eapply Included_Setminus_compat. reflexivity.
                eapply Singleton_Included. constructor; eauto.
                intros Hc3. eapply Hin. now constructor; eauto. 
                eapply well_formed_antimon; [| eapply well_formed'_closed; try eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic...
                
                eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                eapply Included_trans; [| eapply reach'_extensive ]. eapply env_locs_monotonic...
              + right.
                rewrite <- well_formed_reach_subheap_same in H0.
                now apply H0.
                
                eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
                rewrite (reach'_idempotent H1 (env_locs _ _ )). 
                eapply reach'_set_monotonic. eapply Singleton_Included. eapply Included_post_reach'. 
                eapply post_set_monotonic with (S1 := [set l1]). eapply Singleton_Included.
                eapply get_In_env_locs; try eassumption. left. right. constructor. eassumption.
                intros Hc. eapply Hin. constructor; eauto. reflexivity.
                rewrite post_Singleton; eauto. right. reflexivity. tci.
                eapply Singleton_Included. tci. eapply cc_approx_clos_dom1. eassumption.
                
                eapply def_funs_subheap. now eauto. }
        * eapply unique_bindings_fundefs_unique_functions. eassumption.
      + erewrite def_funs_neq. eassumption. reflexivity.
        intros Hc. eapply Hfnin. eapply closure_conversion_fundefs_Same_set.
        eassumption. eassumption.
      + eapply def_funs_subheap. now eauto. eassumption.
      + rewrite extend_fundefs'_get_o.
        edestruct (@Dec _ Scope _ f1). exfalso. eapply Hin.
        now constructor; eauto.

        erewrite def_funs_neq. eassumption. reflexivity.
        intros Hc. eapply Hdis.

        constructor. right. eexists.
        split; eauto. constructor; eauto.
        eapply closure_conversion_fundefs_Same_set; eassumption.
        eassumption.
      + eapply cc_approx_clos_heap_monotonic.
        eapply def_funs_subheap. now eauto.
        now eapply HL.subheap_refl. intros j'.
        edestruct (Hfun j') as
            (l1' & lenv''' & B1'' & g1' & rhoc' & B2'' & g2' & Hgetf2 & Hnin''
             & Hgetf2' & Hgetl1' & Hext' & Henvc' & Hrel').
        intros Hin'. eapply Hin. now constructor; eauto. 
        eassumption. 
        repeat subst_exp. eassumption.
        
      + destruct (alloc (Constr _ [FunPtr B2' g2; Loc B1']) H2) as [l2' H2''] eqn:Ha.
        eapply cc_approx_val_heap_monotonic.
        eapply def_funs_subheap. now eauto.
        now eapply HL.subheap_refl. intros j'.
        edestruct (Hfun j') as
            (l1' & lenv2 & B1'' & g1' & rhoc' & B2'' & g2' & Hgetf2 & Hnin''
            & Hgetf2' & Hgetl1' & Hext' & Henvc' & Hrel').
        intros Hin'. eapply Hin. now constructor; eauto. 
        eassumption. repeat subst_exp. rewrite Ha in Hrel'.
        eassumption.
        Grab Existential Variables. exact 0. 
  Qed.


  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct (k : nat) (H1 H2 : heap block)
        (rho1 rho2 : env) (e1 e2 : exp) (C : exp_ctx)
        (Scope Funs : Ensemble var) {Hs : ToMSet Scope} {Hf : ToMSet Funs} (FVs : list var)
        fenv (β : Inj) (c : cTag) (Γ : var) A δ:
    (* [Scope] invariant *)
    (forall j, (H1, rho1) ⋞ ^ (Scope ; k ; j ; PreG; PostG; β) (H2, rho2)) ->
    (* Free variable invariant *)
    (forall j, FV_inv k j PreG PostG β rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    (* Functions in scope invariant *)
    (forall j, Fun_inv k j PreG PostG β rho1 H1 rho2 H2  Scope Funs fenv FVs) ->

    Disjoint _ (Γ |: image fenv (Funs \\ Scope)) (bound_var e1 :|: FV Scope Funs FVs) ->
    
    (* The free variables of e are defined in the environment *)
    binding_in_map (FV Scope Funs FVs) rho1 ->

    (* Freshness requirements *)
    unique_bindings e1 ->
    Disjoint _ (bound_var e1) (FV Scope Funs FVs) ->
    
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion ct Scope Funs fenv c Γ FVs e1 e2 C ->
    
    (forall j, (e1, rho1, H1) ⪯ ^ (k ; j ;
                              Pre (Funs :&: occurs_free e1 \\ Scope) A δ; PreG;
                              Post 0 A δ; PostG)
          (C |[ e2 ]|, rho2, H2)).
  Proof with now eauto with Ensembles_DB.
    revert A δ H1 H2 rho1 rho2 e1 e2 C Scope Hs Funs Hf FVs fenv β c Γ.
    induction k as [k IHk] using lt_wf_rec1.  
    intros A δ H1 H2 rho1 rho2 e1 e2 C Scope Hs Funs Hf FVs fenv β c Γ
           Henv HFVs Hfun Hdis Hbind Hunb Hfresh Hcc. 
    assert (Hfv := Closure_conversion_pre_occurs_free_Included _ _ _ _ _ _ _ _ _ Hcc).
    assert (Hfv' := Closure_conversion_occurs_free_Included _ _ _ _ _ _ _ _ _ Hcc).
 
    (* Well formedness *)
    assert (Hwf1 : closed (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) H1). 
    { eapply reach'_closed.
      eapply well_formed_antimon; [| eapply FV_reach1; try eassumption; now tci ].
      eapply reach'_set_monotonic. eapply env_locs_monotonic. reflexivity.
      eapply Included_trans; [| eapply FV_dom1 with (Scope := Scope); try eassumption ].
      eapply env_locs_monotonic. reflexivity. }

    assert (Hwf2 : closed (reach' H2 (env_locs rho2 (FV_cc Scope Funs fenv Γ))) H2). 
    { eapply reach'_closed.
      eapply well_formed_antimon; [| eapply FV_reach2;
                                     [| eassumption | eassumption | eassumption | ]; tci ].
      eapply reach'_set_monotonic. eapply env_locs_monotonic. reflexivity.
      eapply binding_in_map_antimon; [| eassumption ]...

      eapply Included_trans; [| eapply FV_dom2 with (Scope := Scope); try eassumption ].
      eapply env_locs_monotonic. reflexivity.
      eapply binding_in_map_antimon; [| eassumption ]... }

    destruct e1.
    (* revert e2 Hcc Hfv'.  *)
    (* induction e1 using exp_ind'; intros e2 Hcc Hfv'; try clear IHe1. *)
    - (****************************** case Econstr ******************************) 
      inv Hcc.
      assert (Hf' : ToMSet Funs').
      eapply project_vars_ToMSet_Funs. eassumption. now eapply H13.
      assert (Hs' : ToMSet Scope').
      eapply (project_vars_ToMSet Scope Scope' Funs). eassumption.
        
      edestruct (binding_in_map_getlist _ rho1 l Hbind) as [vl Hgetl].
      eapply project_vars_In_Union. eassumption.
      
      edestruct project_vars_ctx_to_heap_env with (Scope := Scope) as [H2' [rho2' [m Hct]]];
        try eassumption.
      intros Hc. eapply Hdis. constructor. now left. right. eassumption.
      eapply Disjoint_Included; [ | | now eapply Hdis ]...
      specialize (Hfun 0); eapply Fun_inv_weak_in_Fun_inv; eassumption.
      specialize (HFVs 0); eapply FV_inv_weak_in_FV_inv; eassumption.
      
      assert (Hwf2' : closed (reach' H2' (env_locs rho2' (FV_cc Scope' Funs' fenv Γ))) H2'). 
      { eapply reach'_closed.
        eapply project_vars_well_formed'. eassumption. eassumption.
        eapply well_formed'_closed. eassumption.
        eapply Included_trans. eapply reach'_extensive. eapply env_locs_closed.
        eassumption.

        eapply project_vars_env_locs'. eassumption. eassumption.
        eapply well_formed'_closed. eassumption.
        eapply Included_trans. eapply reach'_extensive. eapply env_locs_closed.
        eassumption. }
        
      intros j.

      (* process right ctx *)
      eapply cc_approx_exp_right_ctx_compat
      with (IL2 := (Post (cost_ctx_full_cc C) A δ)); [ | | | | now eapply Hct | ].
      
      + eapply PostCtxCompat_vars_r; [| | | | eassumption |  ]; try eassumption.
        simpl. omega. 
      + eapply (PreCtxCompat_vars_r Scope Scope' Funs _ Funs'). normalize_occurs_free.
        now eapply Included_Union_preserv_l. 
        eassumption.
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        
      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ]. 
        eapply env_locs_monotonic. eassumption.

      + edestruct project_vars_correct with (Scope := Scope) as
            (b' & Henv' & Hfun' & HFVs');
        try eassumption.
        eapply Disjoint_Included; [ | | now apply Hdis ]...
        
        (* process Econstr one the right and left *) 
        eapply cc_approx_exp_constr_compat
        with (IIL2 := Pre (Funs' :&: occurs_free e1 \\ (v |: Scope')) A (δ + (1 + length l))) (IL2 := Post 0 A (δ + (1 + length l)));
          [ | | | | | | |  | ].
        * eapply PostConstrCompat.
          unfold cost_env_app_exp_out. 
          eapply project_vars_cost_eq'. eassumption.
          eapply Forall2_refl_strong. intros x Hin.
          eapply Henv'. eapply project_vars_In. eassumption. eassumption.
        * eapply PreConstrCompat.
          eapply Forall2_refl_strong. intros x Hin.
          eapply Henv'. eapply project_vars_In. eassumption. eassumption.
          normalize_occurs_free.
          rewrite <- Setminus_Union. eapply Included_Setminus_compat; [| reflexivity ]. 
          eapply Included_trans. eapply Setminus_Included. 
          rewrite (Intersection_commut (_ :|: _)), Intersection_Union_distr.
          eapply Included_Union_preserv_r. 
          rewrite Intersection_Setmius_Disjoint.
          rewrite Intersection_commut. reflexivity.
          eapply Disjoint_Included; [| | eapply Hfresh ].
          rewrite project_vars_FV_eq; [| eassumption ].
          unfold FV. rewrite (Union_Setminus_Included Scope').
          now eauto with Ensembles_DB. 
          tci. reflexivity. 
          eapply Singleton_Included...
        * eapply PostBase.  (* XXX Base *)
          unfold cost_env_app_exp_out.
          eapply project_vars_cost_eq'. eassumption.
          omega.
        * eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
          
        * eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic. normalize_occurs_free.
          eapply Union_Included. do 3 eapply Included_Union_preserv_l.
          eapply project_vars_In. eassumption.
          eapply Setminus_Included_Included_Union. 
          eapply Included_trans.
          eapply Closure_conversion_occurs_free_Included; eassumption.
          eapply Included_trans; [ eapply FV_cc_Union1 |]...

        * eapply Included_trans; [| eapply env_locs_closed; eassumption ].
          eapply Included_trans; [| eapply reach'_extensive ]. 
          eapply env_locs_monotonic. eassumption.

        * eapply Included_trans; [| eapply env_locs_closed; eassumption ].
          eapply Included_trans; [| eapply reach'_extensive ]. 
          eapply env_locs_monotonic.

          normalize_occurs_free.
          eapply Union_Included. do 3 eapply Included_Union_preserv_l.
          eapply project_vars_In. eassumption.
          eapply Setminus_Included_Included_Union. 
          eapply Included_trans.
          eapply Closure_conversion_occurs_free_Included; eassumption.
          eapply Included_trans; [ eapply FV_cc_Union1 |]...

        * intros j'.
          eapply Forall2_refl_strong. intros x Hin.
          eapply Henv'. eapply project_vars_In. eassumption. eassumption.
        * (* Inductive case *)  
          { intros vs1 vs2 l1 l2 H1'' H2'' Hleq Hr1 Hr2 Ha1' Ha2 Hall j1.
            repeat subst_exp.

            assert (Hfeq :
                      f_eq_subdomain (reach' H1 (env_locs rho1 (FV Scope Funs FVs)))
                                     b' (b' {l1 ~> l2})).
            { eapply f_eq_subdomain_extend_not_In_S_r.
              
              intros Hc. eapply reachable_in_dom in Hc.
              destruct Hc as [v' Hgetv]. erewrite alloc_fresh in Hgetv; eauto. 
              congruence.
              eapply well_formed'_closed; eassumption.
              eapply Included_trans; [ eapply reach'_extensive | ].
              eapply env_locs_closed; eassumption.
              reflexivity. }
            
            (* Induction hypothesis *)
            { eapply IHk with (Scope := v |: Scope');
              [ | | | | | | | | eassumption (* CC *) ].
              * simpl in *. omega.
              * { intros j2.  
                  eapply cc_approx_env_set_alloc_Constr with (b := b' {l1 ~> l2});
                    try eassumption.
                  - rewrite project_vars_FV_eq in Hwf1; [| eassumption ].
                    
                    intros j0.
                    eapply cc_approx_env_rename_ext.
                    eapply cc_approx_env_P_antimon.
                    eapply cc_approx_env_P_monotonic. now eauto.
                    simpl in *; omega.
                    now eauto with Ensembles_DB.

                    eapply f_eq_subdomain_antimon; [| eassumption ].
                    eapply reach'_set_monotonic. eapply env_locs_monotonic.
                    rewrite project_vars_FV_eq; [| eassumption ]... 

                  - rewrite extend_gss. reflexivity.
                  - intros j0. eapply Forall2_monotonic_strong; [| now eapply Hall ].
                    intros x1 x2 Hin1 Hin2 Hcc.
                    
                    eapply cc_approx_val_rename_ext. now eapply Hcc.

                    symmetry. eapply f_eq_subdomain_antimon; [| eassumption ]. 
                    eapply Included_trans.
                    eapply reach'_set_monotonic with (S2 := Union_list (map val_loc vs1)).
                    eapply In_Union_list. eapply in_map. eassumption.
                    rewrite project_vars_FV_eq; [ | eassumption ]. 
                    eapply reach'_set_monotonic. eapply Included_trans. eassumption.
                    eapply env_locs_monotonic. do 2 eapply Included_Union_preserv_l.
                    eapply project_vars_In. eassumption. }

              * (* FV_inv preservation *)
                intros j0. eapply FV_inv_heap_mon.
                eapply HL.alloc_subheap. eassumption. eapply HL.alloc_subheap. eassumption. 
                intros j'.
                eapply FV_inv_rename_ext.
                eapply FV_inv_set_not_in_FVs.
                eapply FV_inv_monotonic.
                eapply HFVs'. omega.
                intros Hc. eapply Hdis. now subst; eauto.
                symmetry. eapply f_eq_subdomain_antimon; [| eassumption ].
                rewrite project_vars_FV_eq; [| eassumption ]. 
                eapply reach'_set_monotonic. rewrite env_locs_set_not_In.
                eapply env_locs_monotonic...

                intros Hc. inv Hc. eauto.
              * (* Fun_inv preservation *)
                intros j0.
                eapply Fun_inv_alloc; [| eassumption | eassumption | | | ].

                rewrite <- project_vars_FV_eq; [| eassumption ]. eassumption.

                eapply Included_trans. eassumption.
                eapply Included_trans; [| eapply reach'_extensive ].
                eapply env_locs_monotonic. eapply project_vars_In. 
                eassumption.

                intros j'.
                eapply Fun_inv_rename_ext. 
                eapply Fun_inv_monotonic. eapply Hfun'. omega. 

                eapply f_eq_subdomain_antimon; [| eassumption ].
                rewrite project_vars_FV_eq; [| eassumption ]. 
                eapply reach'_set_monotonic.
                eapply env_locs_monotonic...
                
                intros Hc. eapply Hdis. constructor. right.
                eapply image_monotonic; [| eassumption ].
                eapply Included_Setminus_compat. eapply project_vars_Funs_l. eassumption.
                eapply project_vars_Scope_l. eassumption.
                normalize_bound_var. left. right. reflexivity.
              * eapply Disjoint_Included; [| | now eapply Hdis ]. 
                normalize_bound_var. rewrite <- Union_assoc. eapply Included_Union_compat.
                reflexivity. eapply Included_trans.
                eapply FV_Union1. erewrite <- project_vars_FV_eq. reflexivity. 
                eassumption.
                eapply Included_Union_compat. reflexivity.
                eapply image_monotonic. eapply Included_Setminus_compat.
                eapply project_vars_Funs_l. eassumption.
                eapply Included_trans; [ eapply project_vars_Scope_l; eassumption |]...
              * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
                eapply Included_trans. eapply FV_Union1.
                erewrite <- project_vars_FV_eq; [| eassumption ]...
              * inv Hunb. eassumption.
              * inv Hunb.
                eapply Disjoint_Included_r.
                eapply FV_Union1.
                eapply Union_Disjoint_r.
                eapply Disjoint_Singleton_r. eassumption.
                rewrite <- project_vars_FV_eq; [| eassumption ].
                eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var...                
            } }

    - (****************************** case Ecase ******************************) 
      inv Hcc.
      assert (Hf' : ToMSet Funs').
      eapply project_var_ToMSet_Funs; [| | eassumption ]; tci.
      assert (Hs' : ToMSet Scope').
      eapply (project_var_ToMSet Scope Scope' Funs). eassumption.
      
      edestruct (Hbind v) as [lv Hgetvl].
      rewrite project_var_FV_eq; [| eassumption ]. left. left. 
      eapply project_var_In. eassumption.
      
      edestruct project_var_ctx_to_heap_env with (Scope := Scope) as [H2' [rho2' [m Hct]]];
        try eassumption.
      specialize (Hfun 0); eapply Fun_inv_weak_in_Fun_inv; eassumption.
      specialize (HFVs 0); eapply FV_inv_weak_in_FV_inv; eassumption.
      
      assert (Hwf2' : closed (reach' H2' (env_locs rho2' (FV_cc Scope' Funs' fenv Γ))) H2'). 
      { eapply reach'_closed. 
        eapply project_var_well_formed'. eassumption. eassumption.
        eapply Included_trans. eapply reach'_extensive. 
        eapply env_locs_closed. eassumption. 
        eapply well_formed'_closed. eassumption.
        eapply project_var_env_locs'. eassumption. eassumption.
        eapply well_formed'_closed. eassumption.
        eapply Included_trans. eapply reach'_extensive. eapply env_locs_closed.
        eassumption. }
        
      intros j.
      (* process right ctx *)
      eapply cc_approx_exp_right_ctx_compat
      with (IL2 := (Post (cost_ctx_full_cc C) A δ)); [ | | | | now eapply Hct | ].
      
      + eapply PostCtxCompat_ctx_r. omega.
      + eapply (PreCtxCompat_var_r _ _ _ _ _ Scope Scope' Funs Funs'). eassumption.
        now constructor.
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        
      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ]. 
        eapply env_locs_monotonic. eassumption.

      + edestruct project_var_correct with (Scope := Scope) as
            (b' & Henv' & Hfun' & HFVs');
        try eassumption.
        eapply Disjoint_Included; [ | | now apply Hdis ]...
        eapply binding_in_map_antimon; [| eassumption ]... 
        (* process Econstr one the right and left *) 
        eapply cc_approx_exp_case_compat
        with (IILe := fun e1 e2 => Pre (Funs' :&: occurs_free e1 \\ Scope') A δ)
               (ILe := fun e1 e2 => Post 0 A δ);
          [ | | | | ].
        * eapply PostBase.  (* XXX Base *)
          unfold cost_env_app_exp_out.
          eapply project_var_cost_eq'. eassumption.
          omega. 
        * eapply PreCaseCompat. intros e1 e2 HIn.  
          eapply Included_Setminus_compat. eapply Included_Intersection_compat. reflexivity.
          eapply occurs_free_Ecase_Included. eassumption. reflexivity.
        * eapply PostCaseCompat.
          unfold cost_env_app_exp_out.
          eapply project_var_cost_eq'. eassumption.
        
        * intros j'.
          eapply Henv'. eapply project_var_In. eassumption.
        * (* Inductive case *)  
          eapply Forall2_monotonic_strong; [| eassumption ]. 
          { intros [c1 e1] [c2 e2] Hin1 Hin2 [Heq [C2' [e2cc [Heq2 Hcc]]]]. simpl in Heq, Heq2; subst.
            split. reflexivity. intros Hleq. 
            eapply IHk with (Scope := Scope');
              [ | | | | | | | | eassumption (* CC *) ].
            * simpl in *. omega. 
            * intros j1. eapply cc_approx_env_P_monotonic.
              eapply Henv'. omega. 
            * (* FV_inv preservation *)
              intros j1.
              eapply FV_inv_monotonic.
              eapply HFVs'. omega.
            * (* Fun_inv preservation *)
              intros j1.
              eapply Fun_inv_monotonic. eapply Hfun'. omega. 
            * eapply Disjoint_Included; [| | now eapply Hdis ]. 
              erewrite <- project_var_FV_eq; [| eassumption ].  eapply Included_Union_compat; [| reflexivity ].
              intros z Hin. eapply Bound_Ecase; eassumption.

              eapply Included_Union_compat. reflexivity.
              eapply image_monotonic. eapply Included_Setminus_compat.
              eapply project_var_Funs_l. eassumption.
              eapply Included_trans; [ eapply project_var_Scope_l; eassumption |]...
            * erewrite <- project_var_FV_eq; [| eassumption ]...
            * eapply unique_bindings_Ecase_In; eassumption.
            * erewrite <- project_var_FV_eq; [| eassumption ].
              eapply Disjoint_Included_l; [| eassumption ].
              intros z Hin. eapply Bound_Ecase; eassumption. }
    - (****************************** case Eproj ******************************) 
      inv Hcc. (* TODO change compat *) 
      assert (Hf' : ToMSet Funs').
      eapply project_var_ToMSet_Funs; [| | eassumption]; tci.
      assert (Hs' : ToMSet Scope').
      eapply (project_var_ToMSet Scope Scope' Funs). eassumption.

      edestruct (Hbind v0) as [lv Hgetvl].
      rewrite project_var_FV_eq; [| eassumption ]. left. left. 
      eapply project_var_In. eassumption.

      edestruct project_var_ctx_to_heap_env with (Scope := Scope) as [H2' [rho2' [m Hct]]];
        try eassumption.
      specialize (Hfun 0); eapply Fun_inv_weak_in_Fun_inv; eassumption.
      specialize (HFVs 0); eapply FV_inv_weak_in_FV_inv; eassumption.
      
      assert (Hwf2' : closed (reach' H2' (env_locs rho2' (FV_cc Scope' Funs' fenv Γ))) H2'). 
      { eapply reach'_closed. 
        eapply project_var_well_formed'. eassumption. eassumption.
        eapply Included_trans. eapply reach'_extensive. 
        eapply env_locs_closed. eassumption. 
        eapply well_formed'_closed. eassumption.
        eapply project_var_env_locs'. eassumption. eassumption.
        eapply well_formed'_closed. eassumption.
        eapply Included_trans. eapply reach'_extensive. eapply env_locs_closed.
        eassumption. }
        
      intros j.

      (* process right ctx *)
      eapply cc_approx_exp_right_ctx_compat
      with (IL2 := (Post (cost_ctx_full_cc C) A δ)); [ | | | | now eapply Hct | ].
      
      + eapply PostCtxCompat_ctx_r. omega.
      + eapply (PreCtxCompat_var_r _ _ _ _ _ Scope Scope' Funs Funs'). eassumption.
        normalize_occurs_free...
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        
      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ]. 
        eapply env_locs_monotonic. eassumption.

      + edestruct project_var_correct with (Scope := Scope) as
            (b' & Henv' & Hfun' & HFVs');
        try eassumption.
        eapply Disjoint_Included; [ | | now apply Hdis ]...
        eapply binding_in_map_antimon; [| eassumption ]... 
        (* process Econstr one the right and left *) 
        eapply cc_approx_exp_proj_compat
        with (IIL2 := Pre (Funs' :&: occurs_free e1 \\ (v |: Scope')) A δ) (IL2 := Post 0 A δ);
          [ | | | | ].
        * eapply PostProjCompat.
          unfold cost_env_app_exp_out.
          eapply project_var_cost_eq'. eassumption.

        * eapply PreProjCompat.
          normalize_occurs_free.
          rewrite <- Setminus_Union. eapply Included_Setminus_compat; [| reflexivity ]. 
          eapply Included_trans. eapply Setminus_Included. 
          rewrite (Intersection_commut (_ :|: _)), Intersection_Union_distr.
          eapply Included_Union_preserv_r. 
          rewrite Intersection_Setmius_Disjoint.
          rewrite Intersection_commut. reflexivity.
          eapply Disjoint_Included; [| | eapply Hfresh ].
          rewrite project_var_FV_eq; [| eassumption ].
          unfold FV. rewrite (Union_Setminus_Included Scope').
          now eauto with Ensembles_DB. 
          tci. reflexivity. 
          eapply Singleton_Included...
        * eapply PostBase.  (* XXX Base *)
          unfold cost_env_app_exp_out.
          eapply project_var_cost_eq'. eassumption.
          omega.
        * intros j'.
          eapply Henv'. eapply project_var_In. eassumption.
        * (* Inductive case *)  
          { intros v1 v2 Hleqk Hr1 Hr2 Hrel. 
            intros j0. 
            eapply IHk with (Scope := v |: Scope');
              [ | | | | | | | | eassumption (* CC *) ].
            * simpl in *. omega. 
            * intros j1. eapply cc_approx_env_P_set.
              eapply cc_approx_env_P_monotonic.
              eapply cc_approx_env_P_antimon. eapply Henv'.
              now eauto with Ensembles_DB.
              omega.
              eapply Hrel.
            * (* FV_inv preservation *)
              intros j1.
              eapply FV_inv_set_not_in_FVs.
              eapply FV_inv_monotonic.
              eapply HFVs'. omega.
              intros Hc. eapply Hdis. now subst; eauto.
            *  (* Fun_inv preservation *)
              intros j1.
              eapply Fun_inv_set_r. eapply Fun_inv_set_l_alt.
              eapply Fun_inv_monotonic. eapply Hfun'. omega. 
              eapply Included_trans. eassumption.
              eapply reach'_set_monotonic. eapply env_locs_monotonic.
              eapply Singleton_Included.
              eapply project_var_In. eassumption. 
               
              intros Hc. inv Hc. now eauto.
              intros Hc.
              eapply Hdis. constructor. right.
              eapply image_monotonic; [| eassumption ].
              eapply Included_Setminus_compat. eapply project_var_Funs_l. eassumption.
              eapply Included_trans. eapply project_var_Scope_l. eassumption.
              now eauto with Ensembles_DB. normalize_bound_var. left. right. reflexivity.
            * eapply Disjoint_Included; [| | now eapply Hdis ]. 
              normalize_bound_var. rewrite <- Union_assoc. eapply Included_Union_compat.
              reflexivity. eapply Included_trans.
              eapply FV_Union1. erewrite <- project_var_FV_eq. reflexivity. 
              eassumption.
              eapply Included_Union_compat. reflexivity.
              eapply image_monotonic. eapply Included_Setminus_compat.
              eapply project_var_Funs_l. eassumption.
              eapply Included_trans; [ eapply project_var_Scope_l; eassumption |]...
            * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
              eapply Included_trans. eapply FV_Union1.
              erewrite <- project_var_FV_eq; [| eassumption ]...
            * inv Hunb. eassumption.
            * inv Hunb.
              eapply Disjoint_Included_r.
              eapply FV_Union1.
              eapply Union_Disjoint_r.
              eapply Disjoint_Singleton_r. eassumption.
              rewrite <- project_var_FV_eq; [| eassumption ].
              eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var...                
          } 

    - (****************************** case Efuns ******************************) 
      inv Hcc. 
      
      assert (Hf' : ToMSet Funs').
      eapply project_vars_ToMSet_Funs; [| eassumption]; tci.
      assert (Hs' : ToMSet Scope').     
      { eapply (project_vars_ToMSet Scope Scope' Funs). eassumption. }
      
      assert (Hfveq : occurs_free (Econstr_c Γ' c' FVs' Hole_c |[ Efun B' (Ce |[ e' ]|) ]|) \subset
                                  FV_cc Scope' Funs' fenv Γ). 
      { simpl. repeat normalize_occurs_free.
        assert (Hclof := H14). eapply Closure_conversion_occurs_free_fundefs_Included in H14.
        rewrite closure_conversion_fundefs_Same_set with (B2 := B') in H14; [| eassumption ].
        rewrite Setminus_Same_set_Empty_set in H14. eapply Included_Empty_set_l in H14.
        rewrite <- H14, Union_Empty_set_neut_l. eapply Closure_conversion_occurs_free_Included in H17. 
        rewrite <- closure_conversion_fundefs_Same_set with (B2 := B'); [| eassumption ].
        eapply Union_Included.
        eapply Included_trans. eapply project_vars_In;  eassumption...
        unfold FV_cc... rewrite Setminus_Union. eapply Included_trans. 
        eapply Included_Setminus_compat. eassumption. reflexivity. 
        eapply Setminus_Included_Included_Union. eapply Included_trans.
        eapply FV_cc_Setminus1. tci.
        eapply Union_Included. eapply Union_Included. now eauto with Ensembles_DB.
        eapply Included_trans; [ eapply extend_fundefs'_image |]...
        
        eapply Included_trans. eapply FV_cc_Union2.
        eapply Union_Included. eapply Union_Included. now eauto with Ensembles_DB.
        eapply Included_trans; [ eapply extend_fundefs'_image |]...
        
        unfold FV_cc. rewrite <- !Union_assoc.
        eapply Included_Union_compat. reflexivity.
        eapply Included_Union_compat. reflexivity.
        eapply Union_Included. eapply Included_trans; [ eapply extend_fundefs'_image_Included |]...
        now eauto with Ensembles_DB. }
      
      edestruct (binding_in_map_getlist _ rho1 (FVs') Hbind) as [vl Hgetl].
      eapply Included_trans; [| eassumption ].
      rewrite <- H3. normalize_occurs_free...
      
      edestruct (project_vars_ctx_to_heap_env Scope Scope' Funs Funs') as [H2' [rho2' [m Hct]]];
        try eassumption.
      intros Hc. eapply Hdis. constructor. now left. now right. 
      eapply Disjoint_Included; [| | eapply Hdis]...
      specialize (Hfun 0); eapply Fun_inv_weak_in_Fun_inv; eassumption.
      specialize (HFVs 0); eapply FV_inv_weak_in_FV_inv; eassumption.
      
      edestruct project_vars_correct with (Scope := Scope) as
          (b' & Henv' & Hfun' & HFVs');
        try eassumption.
      eapply Disjoint_Included_r; [| eassumption ]... 
      
      assert (Hwf2' : closed
                        (reach' H2' (env_locs rho2' (FV_cc Scope' Funs' fenv Γ))) H2'). 
      { eapply reach'_closed.
        
        eapply FV_reach2. tci. eassumption. eassumption. eassumption.
        eapply binding_in_map_antimon; [| eassumption ].
        rewrite project_vars_FV_eq; [| eassumption ]...
        
        eapply FV_dom2. tci. eassumption. eassumption. eassumption.
        eapply binding_in_map_antimon; [| eassumption ].
        rewrite project_vars_FV_eq; [| eassumption ]... }
      
      rewrite <- app_ctx_f_fuse in *. intros j.
      
      edestruct (cc_approx_env_P_getlist_l ) with (j := j) as [vl' [Hgetl' Hall]] ; [ | | eassumption | ].
      eapply Henv'. eapply project_vars_In. eassumption.
      
      edestruct (alloc (Constr c' vl') H2') as [lenv H2''] eqn:Haenv. 
      
      assert (Hlen : length FVs' = PS.cardinal (fundefs_fv f)).
      { rewrite PS.cardinal_spec. eapply Same_set_FromList_length'.
        eassumption. eapply NoDupA_NoDup. eapply PS.elements_spec2w.
        rewrite <- (fundefs_fv_correct f). symmetry. eassumption. }
      
      (* process right ctx 1 : projec-t fvs *)
      eapply cc_approx_exp_right_ctx_compat; [ | | | | eassumption | ].
      
      + eapply PostCtxCompat_ctx_r with (k := cost_ctx_full_cc C0).
        omega.
      
      + eapply (PreCtxCompat_vars_r Scope Scope' Funs _ Funs'); [| eassumption ].
        rewrite <- H3. normalize_occurs_free...
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. now eapply env_locs_monotonic; eauto.
      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans. now eapply env_locs_monotonic; eauto.
        eapply reach'_extensive.   
      + eapply cc_approx_exp_right_ctx_compat;
        [ | | | | econstructor; try eassumption; now constructor | ].
        * eapply PostCtxCompat_ctx_r with (k :=  cost_ctx_full_cc (Econstr_c Γ' c' FVs' C0)).
          (* cost_ctx_full_cc C0 1 + 4 * PS.cardinal (fundefs_fv f)). *)
          simpl. unfold cost_ctx_full. omega.  
        * eapply PreCtxCompat_ctx_to_heap_env with (δ' := δ + (1 + PS.cardinal (fundefs_fv f)))
                                                     (Funs' := (Funs' :&: occurs_free (Efun f e1) \\ Scope')).
          simpl. reflexivity. simpl. omega. 
        * eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
          eapply reach'_set_monotonic. now eapply env_locs_monotonic; eauto.
        * eapply Included_trans; [| eapply env_locs_closed; eassumption ].
          eapply Included_trans; [| eapply reach'_extensive ].
          eapply env_locs_monotonic...
        * { eapply cc_approx_exp_fun_compat.
            - eapply PostFunsCompat with (m := 0). simpl. omega.
              simpl. eapply Peano.le_n_S. eapply le_trans. eapply plus_le_compat_l.
              eapply project_vars_cost_eq'. eassumption. omega. 
              reflexivity. 
            - eapply PreFunsCompat with (A := A) (S' := occurs_free e1).
         
              normalize_occurs_free.
              eapply Included_trans; [| eapply Included_Intersection_compat;
                                        [ reflexivity | eapply Included_Union_preserv_r; reflexivity ] ].
              rewrite <- (Intersection_commut _ (_ \\ _)). 
              rewrite Intersection_Setmius_Disjoint.
              rewrite Intersection_commut...

              (* XXX make lemma Funs \subset FV *)
              eapply Disjoint_Included; [| | eapply Hfresh ].
              rewrite project_vars_FV_eq; [| eassumption ]. unfold FV.
              rewrite (Union_Setminus_Included Scope' Funs').
              now eauto with Ensembles_DB. 
              tci. reflexivity.
              eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
              normalize_bound_var...
              
              eapply Disjoint_Included; [| | eapply Hfresh ].
              rewrite project_vars_FV_eq; [| eassumption ]. unfold FV.
              rewrite (Union_Setminus_Included Scope' Funs').
              now eauto with Ensembles_DB. 
              tci. reflexivity.
              eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
              normalize_bound_var...
              inv Hunb.
              eapply unique_bindings_fundefs_unique_functions.
              eassumption.
            - eapply PostBaseFuns. simpl. split. omega.  
              eapply Peano.le_n_S. 
              eapply plus_le_compat. omega. eapply le_trans.
              eapply project_vars_cost_eq'. eassumption. omega.
              eapply plus_le_compat_l. simpl. eapply Peano.le_n_S.
              eapply le_trans; [| eapply Max.le_max_r ]. omega. 
            - eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
              eapply reach'_set_monotonic. eapply env_locs_monotonic...
            - eapply Included_trans; [| eapply env_locs_closed; eassumption ].
              eapply Included_trans; [| eapply reach'_extensive ].
              eapply env_locs_monotonic...
            - eapply binding_in_map_antimon; [| eassumption ].
              eapply Included_trans; [| eassumption ]. normalize_occurs_free...
            - intros H1' H1'' rho1' rhoc el Hlt Hr Ha Hdef.
              
              assert (Hfeq :  f_eq_subdomain (reach' H1 (env_locs rho1 (FV Scope' Funs' FVs))) b'
                                             (b' {el ~> lenv})).
              { eapply f_eq_subdomain_extend_not_In_S_r.
                rewrite <- project_vars_FV_eq; [| eassumption ].
                
                intros Hc. eapply reachable_in_dom in Hc.
                eapply HL.alloc_not_In_dom. eassumption. eassumption. 
                eapply well_formed'_closed. eassumption.
                eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                eapply reach'_extensive.
                reflexivity. }

              replace (1 + PS.cardinal mset + 3 * numOf_fundefs f + δ) with
                  (δ + (1 + PS.cardinal (fundefs_fv f)) + 3 * numOf_fundefs f).
              
              eapply IHk with (Scope := Scope' \\ name_in_fundefs f) (β :=  b' {el ~> lenv});
                [| | | | | | | | (* CC *) eassumption ].
              + simpl in *. omega. 
              + intros j1.
                rewrite <- Setminus_Disjoint with (s2 := name_in_fundefs f);
                  [| now eauto with Ensembles_DB ].
                eapply def_closures_cc_approx_env; [| eassumption ].
                intros j'. rewrite closure_conversion_fundefs_Same_set; try eassumption.
                eapply def_funs_cc_approx_env.
                eapply cc_approx_env_P_set_not_in_P_r.
                eapply cc_approx_env_heap_monotonic.
                eapply HL.alloc_subheap. eassumption.
                eapply HL.alloc_subheap. eassumption.
                intros j''. eapply cc_approx_env_P_monotonic.
                eapply cc_approx_env_rename_ext. eapply Henv'.
                eapply f_eq_subdomain_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic...
                omega.
                intros Hc'. eapply H7. left. right.
                rewrite project_vars_FV_eq; [| eassumption ]. now left; left. 
              + intros j1.
                eapply def_funs_FV_inv; [| rewrite <- closure_conversion_fundefs_Same_set;
                                           now eauto with Ensembles_DB |]. 
                eapply def_closures_FV_inv; [| | now eauto ]. now tci.

                intros j2.
                eapply Proper_FV_inv_Scope. rewrite Setminus_Disjoint. reflexivity.
                eapply Disjoint_sym. eapply Disjoint_Included; [| | now eapply Hfresh ]. 
                rewrite project_vars_FV_eq; [| eassumption ]. now left; left.
                normalize_bound_var.
                eapply Included_trans; [ eapply name_in_fundefs_bound_var_fundefs |]...
                reflexivity. reflexivity. reflexivity.
                eapply FV_inv_set_not_in_FVs_r.
                eapply FV_inv_heap_mon. 
                eapply HL.alloc_subheap. eassumption.
                eapply HL.alloc_subheap. eassumption.
                
                intros j''. eapply FV_inv_monotonic. eapply FV_inv_rename_ext. eapply HFVs'.
                symmetry. eapply f_eq_subdomain_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic...
                omega.
                intros Hc. subst. eapply H7. right. right. reflexivity.
                rewrite <- closure_conversion_fundefs_Same_set; [| eassumption ].
                intros Hc. eapply Hdis. constructor. now left.
                normalize_bound_var. left. left.
                eapply name_in_fundefs_bound_var_fundefs. eassumption.
              + (* Fun_inv : IH fundefs *)
                eapply Closure_conversion_fundefs_correct with (b :=  b' {el ~> lenv})
                                                                 (H1 := H1') (Γ' := Γ').
                * intros. eapply IHk; [| | | | | | | | eassumption ]; try eassumption.
                  omega.
                * tci.
                * tci.
                * rewrite <- project_vars_FV_eq; [| eassumption ].
                  eapply reach'_closed. rewrite <- well_formed_reach_alloc_same. 
                  eapply well_formed_alloc. eapply well_formed'_closed; eassumption. eassumption.
                  subst. simpl. eapply Included_trans. eapply restrict_env_env_locs.
                  eapply restrict_env_correct. reflexivity.
                  rewrite <- (fundefs_fv_correct f).
                  eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                  eapply Included_trans; [| eapply reach'_extensive ]. 
                  eapply env_locs_monotonic. eapply Included_trans; [| eassumption ]. 
                  normalize_occurs_free...

                  eapply well_formed'_closed; eassumption.

                  eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                  eapply Included_trans; [| eapply reach'_extensive ]. 
                  eapply env_locs_monotonic...
                  eassumption. rewrite HL.alloc_dom; [ | eassumption ].

                  eapply Included_Union_preserv_r. 
                  eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                  eapply Included_trans; [| eapply reach'_extensive ]. 
                  eapply env_locs_monotonic...

                * eapply closed_set_alloc_alt; try eassumption.

                  eapply reach'_closed.
                  eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
                  eapply reach'_set_monotonic. eapply env_locs_monotonic...
                  
                  eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                  eapply Included_trans; [| eapply reach'_extensive ]. 
                  eapply env_locs_monotonic...

                  eapply Included_trans; [| eapply reach'_extensive ].
                  unfold FV_cc. rewrite !Setminus_Union_distr, !env_locs_Union.
                  do 3 eapply Included_Union_preserv_l. eapply FromList_env_locs.
                  eassumption. eapply Included_Setminus.
                  eapply Disjoint_Singleton_r.
                  intros Hc; eapply H7...

                  eapply project_vars_In. eassumption.
                * intros j1. eapply Fun_inv_set_r.
                  eapply Fun_inv_subheap; try (eapply HL.alloc_subheap; eassumption).
                  rewrite <- project_vars_FV_eq; [| eassumption ].
                  eapply well_formed'_closed. eassumption. 
                  rewrite <- project_vars_FV_eq; [| eassumption ].
                  eapply Included_trans. eapply reach'_extensive.
                  eapply env_locs_closed. eassumption. 

                  rewrite image_f_eq_subdomain;
                    [| symmetry;  eapply f_eq_subdomain_antimon; try now eapply Hfeq ].
                  
                  eapply Included_trans. eapply Fun_inv_image_reach. eassumption.
                  eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                  eapply reach'_set_monotonic. eapply env_locs_monotonic...
                  rewrite (reach_unfold H1 (env_locs rho1 (FV Scope' Funs' FVs))). 
                  eapply Included_Union_preserv_r.
                  eapply reach'_set_monotonic.  eapply post_set_monotonic.
                  eapply env_locs_monotonic...
                  
                  intros j2. eapply Fun_inv_monotonic.
                  eapply Fun_inv_rename_ext. eapply Hfun'.
                  eapply f_eq_subdomain_antimon; [| eassumption ].
                  eapply reach'_set_monotonic. eapply env_locs_monotonic...
                  omega.
                  intros Hc. eapply H7. left. right.
                  rewrite project_vars_FV_eq; [| eassumption ]. now left; right.
                  intros Hc. eapply H7. 
                  rewrite project_vars_FV_eq; [| eassumption ]. right.
                  left. right. eapply image_monotonic; [| eassumption ].
                  eapply Included_Setminus_compat.
                  eapply project_vars_Funs_l. eassumption.
                  eapply project_vars_Scope_l. eassumption.
                * intros j1.   
                  eapply FV_inv_env_constr with (rho1 := rhoc) (FVs := FVs') (Γ := Γ'); subst.
                  
                  rewrite key_set_binding_in_map_alt; rewrite <- (fundefs_fv_correct f).
                  eassumption. eapply binding_in_map_antimon; [| eassumption ].
                  eapply Included_trans; [| eassumption ].
                  normalize_occurs_free...
                  
                  rewrite M.gss. reflexivity.
                  
                  erewrite gas. reflexivity. eassumption.

                  eapply restrict_env_getlist. eapply restrict_env_correct. 
                  reflexivity. eassumption. rewrite <- (fundefs_fv_correct f). now eapply H3.

                  intros j2.
                  eapply Forall2_monotonic.
                  intros x1 x2 HR. 
                  eapply cc_approx_val_heap_monotonic.
                  eapply HL.alloc_subheap. eassumption.
                  eapply HL.alloc_subheap. eassumption.
                  now eapply HR.
                  eapply Forall2_forall. tci. intros j3. 
                  edestruct (cc_approx_env_P_getlist_l ) with (j := j3) as [vl'' [Hgetl'' Hall']] ; [ | | now apply Hgetl | ].
                  eapply Henv'. eapply project_vars_In. eassumption.
                  repeat subst_exp.
                  eapply Forall2_monotonic_strong; [| eassumption ]. intros x1 x2 Hin1 Hin2 Hcc.
                  eapply cc_approx_val_rename_ext. eapply cc_approx_val_monotonic. eapply Hcc.
                  omega.
                  symmetry. eapply f_eq_subdomain_antimon; [| eassumption ].
                  eapply reach'_set_monotonic.
                  eapply Included_trans; [| eapply FromList_env_locs ]; try eassumption.
                  eapply Included_trans; [| eapply In_Union_list ]. reflexivity.
                  eapply in_map. eassumption. do 2 eapply Included_Union_preserv_l.
                  eapply project_vars_In. eassumption.
                * symmetry. eassumption.
                * eassumption.
                * inv Hunb. eassumption.
                * rewrite <- project_vars_FV_eq; [| eassumption ].
                  eapply Disjoint_Included; [| | eapply Hfresh ].
                  eapply Union_Included. reflexivity.
                  rewrite <- H3. eapply Included_trans; [| eapply Hfv ].
                  normalize_occurs_free...
                  normalize_bound_var...
                * eapply Union_Disjoint_l.
                  
                  eapply Disjoint_Singleton_l. intros Hc. eapply H7. left.
                  normalize_bound_var. left. left. left. 
                  eapply name_in_fundefs_bound_var_fundefs...
                  
                  eapply Disjoint_Included; [| | eapply Hdis ].
                  eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
                  normalize_bound_var...
                  eapply Included_Union_preserv_r. eapply image_monotonic.
                  eapply Included_Setminus_compat.
                  eapply project_vars_Funs_l. eassumption.
                  eapply project_vars_Scope_l. eassumption.
                * erewrite gas; eauto.
                * rewrite M.gss. rewrite extend_gss. reflexivity.
                *  subst. eapply Included_trans. eapply restrict_env_env_locs.
                   eapply restrict_env_correct. reflexivity. rewrite <- (fundefs_fv_correct f).
                   rewrite H3.  eapply env_locs_monotonic. unfold FV. rewrite !Setminus_Union_distr.
                   do 2 eapply Included_Union_preserv_l. eapply Included_Setminus.
                   eapply Disjoint_Setminus_r. eapply project_vars_In; eassumption.               
                   eapply project_vars_In. eassumption.
                * eassumption.
                * eassumption.
                * eassumption.
              + eapply Disjoint_Included with (s2 := bound_var (Efun f e1) :|: FV Scope Funs FVs).
                * normalize_bound_var. eapply Union_Included; eauto with Ensembles_DB.
                  eapply Included_trans. eapply FV_Setminus1. tci.
                  eapply Union_Included. 
                  eapply Included_trans; [ eapply name_in_fundefs_bound_var_fundefs |]...
                  eapply Included_trans. eapply FV_Union2.
                  rewrite <- (project_vars_FV_eq Scope Scope' Funs Funs'); [| eassumption ].
                  eapply Included_Union_compat.
                  eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
                  now eauto with Ensembles_DB.  reflexivity.
                * eapply Included_Union_compat. reflexivity.
                  rewrite Setminus_Union_distr. rewrite image_Union.
                  eapply Included_Union_compat.
                  
                  eapply Included_trans; [| eapply extend_fundefs'_image ].
                  eapply image_monotonic...
                  eapply Included_trans. eapply extend_fundefs'_image_Included.
                  reflexivity.
                * rewrite (Union_Same_set [set Γ']); eauto with Ensembles_DB. 
                  rewrite Union_assoc, (Union_commut [set Γ]), <- Union_assoc.
                  eapply Union_Disjoint_l.
                  
                  eapply Disjoint_Singleton_l.
                  intros Hc. eapply H7. now inv Hc; eauto.
                  eapply Disjoint_Included_l; [ | eapply Hdis ].
                  eapply Included_Union_compat. reflexivity.
                  eapply image_monotonic. eapply Included_Setminus_compat.
                  eapply project_vars_Funs_l. eassumption.
                  eapply Included_Setminus.
                  eapply Disjoint_sym. eapply Disjoint_Included; [| | eapply Hfresh ].
                  now eauto with Ensembles_DB.
                  eapply Included_trans. eapply name_in_fundefs_bound_var_fundefs.
                  normalize_bound_var...
                  eapply project_vars_Scope_l. eassumption. 
              + eapply binding_in_map_antimon; [| eapply binding_in_map_def_closures; eassumption ].
                rewrite (project_vars_FV_eq Scope Scope' Funs Funs'); [| eassumption ].
                eapply Included_trans. eapply FV_Setminus1. tci.
                eapply Union_Included. now eapply Included_Union_preserv_l.
                eapply Included_trans. eapply FV_Union2. reflexivity. 
              + inv Hunb. eassumption.
              + eapply Disjoint_Included_r.
                eapply Included_trans. eapply FV_Setminus1. tci.
                eapply Union_Included. now eapply Included_Union_preserv_l.
                eapply Included_trans. eapply FV_Union2. reflexivity.
                eapply Union_Disjoint_r. inv Hunb.
                eapply Disjoint_Included_r; [| eassumption ]. now eapply name_in_fundefs_bound_var_fundefs. 
                rewrite <- (project_vars_FV_eq Scope Scope' Funs Funs'); [| eassumption ].
                eapply Disjoint_Included_l; [ | eapply Hfresh ]. normalize_bound_var...
              + rewrite !plus_assoc.
                replace (δ + 1 + PS.cardinal (fundefs_fv f) + 3 * numOf_fundefs f) with
                    (1 + PS.cardinal (fundefs_fv f) + 3 * numOf_fundefs f + δ) by omega.
                do 3 f_equal.
                rewrite !PS.cardinal_spec. erewrite Same_set_FromList_length'. reflexivity.
                eapply NoDupA_NoDup. eapply PS.elements_spec2w.
                eapply NoDupA_NoDup. eapply PS.elements_spec2w.
                rewrite <- !FromSet_elements. rewrite <- (fundefs_fv_correct f).
                rewrite <- mset_eq. reflexivity.
        } 
    - (****************************** case Eapp ******************************)       
      inv Hcc.

      assert (Hf' : ToMSet Funs').
      eapply project_vars_ToMSet_Funs; [| eassumption]; tci.
      assert (Hs' : ToMSet Scope').     
      { eapply (project_vars_ToMSet Scope Scope' Funs). eassumption. }

      edestruct (binding_in_map_getlist _ rho1 (v :: l) Hbind) as [vl Hgetl].
      eapply Included_trans; [| eassumption ].
      rewrite FromList_cons. normalize_occurs_free...
      
      edestruct (project_vars_ctx_to_heap_env Scope Scope' Funs Funs') as [H2' [rho2' [m Hct]]]; try eassumption.
      intros Hc. eapply Hdis. constructor. now left. now right. 
      eapply Disjoint_Included; [| | eapply Hdis ]...
      specialize (Hfun 0); eapply Fun_inv_weak_in_Fun_inv; eassumption.      
      specialize (HFVs 0); eapply FV_inv_weak_in_FV_inv; eassumption.

      intros j.
      (* process right ctx *)
      eapply cc_approx_exp_right_ctx_compat;
        [ | | | | eassumption | ].
      
      + eapply (PostCtxCompat_vars_r Scope Scope' Funs Funs').
        now eapply H5. rewrite <- plus_n_O. reflexivity. 
        (* eapply project_vars_cost_eq'. eassumption. *)
      + eapply (PreCtxCompat_vars_r Scope Scope' Funs _ Funs'); try now eapply H5.
        normalize_sets. normalize_occurs_free...
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        
      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ]. 
        eapply env_locs_monotonic. eassumption.

      + edestruct project_vars_correct with (Scope := Scope) as
            (b' & Henv' & Hfun' & HFVs' & Hinj');
        try eassumption.
        eapply Disjoint_Included; [ | | now apply Hdis ]...
        
        eapply cc_approx_exp_app_compat; [ | | | | | | ].
        * eapply PostAppCompat; try eassumption.
          constructor.
          eapply Henv'.
          eapply project_vars_In. eassumption. now left.
          
          eapply Forall2_refl_strong. intros x Hin. eapply Henv'.
          eapply project_vars_In. eassumption. now right.

          eapply le_trans. eapply project_vars_cost_eq'. eassumption. 
          simpl. omega.
          
          intros Hc. eapply H4. constructor. now apply H15.
          left. left. left.
          eapply project_vars_In. eassumption. now right.

          intros Hc. eapply H4. constructor. now apply H12.
          left. left. left.
          eapply project_vars_In. eassumption. now right.
          
        * eapply PostBase.
          eapply le_trans. eapply project_vars_cost_eq'. eassumption. 
          simpl. omega.
          omega. 
        * intros Hc. eapply H4. constructor. now apply H15.
          left. left. left.
          eapply project_vars_In. eassumption.
          inv Hc; eauto. inv H. now left.
          now right.

        * intros Hc. eapply H4. constructor. now apply H12.
          left. left. left.
          eapply project_vars_In. eassumption. inv Hc.
          inv H. now left. now right.

        * eauto.
        * eapply Henv'. eapply project_vars_In. eassumption.
          now left.
        * eapply Forall2_refl_strong. intros x Hin j'. eapply Henv'.
          eapply project_vars_In. eassumption. now right.

    - (****************************** case Eprim ******************************)       
      intros j. Transparent cc_approx_exp. intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hstep Hns.
      edestruct (Hns (cost (Eprim v p l e1))) as [res [m2 Hstep']]. inv Hstep'. omega.

    - (****************************** case Ehalt ******************************)  
      inv Hcc.
      assert (Hf' : ToMSet Funs').
      eapply project_var_ToMSet_Funs; [| | eassumption ]; tci.
      assert (Hs' : ToMSet Scope').
      eapply (project_var_ToMSet Scope Scope' Funs). eassumption.

      edestruct (Hbind v) as [lv Hgetvl].
      rewrite project_var_FV_eq; [| eassumption ]. left. left. 
      eapply project_var_In. eassumption.

      edestruct project_var_ctx_to_heap_env with (Scope := Scope) as [H2' [rho2' [m Hct]]];
        try eassumption.
      specialize (Hfun 0); eapply Fun_inv_weak_in_Fun_inv; eassumption.
      specialize (HFVs 0); eapply FV_inv_weak_in_FV_inv; eassumption.
      
      assert (Hwf2' : closed (reach' H2' (env_locs rho2' (FV_cc Scope' Funs' fenv Γ))) H2'). 
      { eapply reach'_closed. 
        eapply project_var_well_formed'. eassumption. eassumption.
        eapply Included_trans. eapply reach'_extensive. 
        eapply env_locs_closed. eassumption. 
        eapply well_formed'_closed. eassumption.
        eapply project_var_env_locs'. eassumption. eassumption.
        eapply well_formed'_closed. eassumption.
        eapply Included_trans. eapply reach'_extensive. eapply env_locs_closed.
        eassumption. }
        
      intros j.

      (* process right ctx *)
      eapply cc_approx_exp_right_ctx_compat
      with (IL2 := (Post (cost_ctx_full_cc C) A δ)); [ | | | | now eapply Hct | ].
      
      + eapply PostCtxCompat_ctx_r. omega.
      + eapply (PreCtxCompat_var_r _ _ _ _ _ Scope Scope' Funs Funs'). eassumption.
        rewrite occurs_free_Ehalt. reflexivity. 
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        
      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ]. 
        eapply env_locs_monotonic. eassumption.

      + edestruct project_var_correct with (Scope := Scope) as
            (b' & Henv' & Hfun' & HFVs');
        try eassumption.
        eapply Disjoint_Included; [ | | now apply Hdis ]...
        eapply binding_in_map_antimon; [| eassumption ]...
        eapply cc_approx_exp_halt_compat.
        eapply PostBase. simpl.
        eapply project_var_cost_eq'. eassumption. omega.

        eapply Henv'. eapply project_var_In. eassumption.


        
        Grab Existential Variables.
        exact 0. exact 0. 
        exact 0. exact 0.
  Qed.

End ClosureConversionCorrect.  
