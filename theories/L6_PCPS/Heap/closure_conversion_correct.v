From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics.

From L6.Heap Require Import heap heap_defs heap_equiv space_sem
     cc_log_rel closure_conversion closure_conversion_util bounds
     invariants.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega Permutation.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module ClosureConversionCorrect (H : Heap).

  Module Inv := Invariants H.
  
  Import H Inv.Size.Util.C.LR.Sem.Equiv Inv.Size.Util.C.LR.Sem.Equiv.Defs
         Inv.Size.Util.C.LR.Sem Inv.Size.Util.C.LR Inv.Size.Util.C
         Inv.Size.Util Inv.Size Inv.

  Definition ct := Inv.Size.Util.clo_tag. 
    

  (** * Lemmas about [project_var] and [project_vars] *)

  (** Correctness of [project_var] *)
  Lemma project_var_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b d
        Scope {_ : ToMSet Scope} Scope' Funs Funs' c Γ fenv FVs x C m :
    (* well-formedness *)
    
    project_var ct Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b; d) (H2, rho2)) ->
    (forall j, Fun_inv k j GII GI b d rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    (forall j, FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->

    injective_subdomain (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)) b ->
    Disjoint _ (image b (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)))
             (env_locs rho2 (image fenv (Funs \\ Scope)) :|:
             (image' d (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)))) ->

    Disjoint _ (Γ |: image fenv (Funs \\ Scope)) (FV Scope Funs FVs) ->
    
    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->

    binding_in_map Scope rho1 ->

    exists b' d', 
      (forall j, (H1, rho1) ⋞ ^ (Scope'; k; j; GII; GI; b'; d') (H2', rho2'))  /\
      (forall j, Fun_inv k j GII GI b' d' rho1 H1 rho2' H2' Scope' Funs' fenv FVs) /\
      (forall j, FV_inv k j GII GI b' d' rho1 H1 rho2' H2' c Scope' Funs' Γ FVs) /\
      injective_subdomain (reach' H1 (env_locs rho1 (FV Scope' Funs' FVs)) \\ env_locs rho1 (Funs' \\ Scope')) b' /\
      Disjoint _ (image b' (reach' H1 (env_locs rho1 (FV Scope' Funs' FVs)) \\ env_locs rho1 (Funs' \\ Scope')))
               ((env_locs rho2' (image fenv (Funs' \\ Scope'))) :|:
                (image' d' (reach' H1 (env_locs rho1 (FV Scope' Funs' FVs)) \\ env_locs rho1 (Funs' \\ Scope')))).
  Proof with (now eauto with Ensembles_DB).
    intros Hproj Hcc Hfun Hfv Hinj Hd Hdis Hctx Hbin.
    inv Hproj. 
    - inv Hctx. do 2 eexists. split. eassumption. split. eassumption.
      split. eassumption. split. eassumption. eassumption.
    - inv Hctx. simpl in H13. 
      destruct (M.get x rho2) as [v1|] eqn:Hgetx; try congruence.
      destruct (M.get (fenv x) rho2) as [v2|] eqn:Hgetg; try congruence. inv H13. 
      inv H14. inv H15.
      edestruct (Hfun 0)
          as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis' (* & Hsub *) & Hget2 & Hget3 & Hget4 & Henv & Heq);
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
      exists (b {l1 ~> l}), (d {l1 ~> Some lenv}). split; [| split; [| split; [| split] ]].
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
          eapply cc_approx_env_rename_ext with (β := b) (δ := d).
          now eapply Hcc.
          eapply f_eq_subdomain_extend_not_In_S_r.
          intros Hc. eapply Fun_inv_locs_Disjoint1. eapply (Hfun 0).
          now constructor; eauto.
          constructor; try eassumption.
          eapply get_In_env_locs. now constructor; eauto. eassumption. reflexivity. 
          eapply reach'_set_monotonic; [| eassumption ].
          eapply env_locs_monotonic... reflexivity.
           
          eapply f_eq_subdomain_extend_not_In_S_r.
          intros Hc.  eapply Fun_inv_locs_Disjoint1. eapply (Hfun 0). now constructor; eauto.
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
          
          eapply Included_Union_compat. eapply image_monotonic.
          eapply Included_Setminus. eapply Disjoint_sym.
          eapply Disjoint_Included_r; [| eapply Fun_inv_locs_Disjoint2; eauto ]. 
          eapply reach'_set_monotonic. eapply post_set_monotonic. eapply env_locs_monotonic...
          rewrite (reach_unfold H1 (env_locs _ _ )). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. eapply post_set_monotonic. eapply env_locs_monotonic...

          eapply image'_monotonic.
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
      + intros j.
        eapply FV_inv_set_not_in_FVs_r.
        eapply FV_inv_mon. 
        eapply FV_inv_heap_mon; [ | | ].
        * eapply HL.subheap_refl.
        * eapply HL.alloc_subheap. eassumption.
        * intros j'. eapply FV_inv_rename_ext. now eapply Hfv.

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
        * rewrite Union_Setminus_Included; tci; now eauto with Ensembles_DB.
        * intros Heqg; subst.
          eapply Hdis. constructor. now left.
          left. right; constructor; eauto.  
      + assert (Hsub' : reach' H1 (env_locs rho1 (FV (x |: Scope) (Funs \\ [set x]) FVs)) \\
                               env_locs rho1 (Funs \\ [set x] \\ (x |: Scope)) \\ [set l1] \subset
                               reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\
                               env_locs rho1 (Funs \\ Scope)).
        { rewrite !Setminus_Union. 
          eapply Included_Setminus_compat. rewrite Hseq'. reflexivity.
          rewrite <- env_locs_Singleton with (v := Loc l1); eauto.
          rewrite <- env_locs_Union. eapply env_locs_monotonic.
          rewrite (Union_Same_set [set x]), (Union_commut [set x]). rewrite <- Setminus_Union.
          rewrite <- Union_Setminus. eapply Included_Union_preserv_l... tci.
          now eauto with Ensembles_DB. }
 
        eapply injective_subdomain_extend'.
        * eapply injective_subdomain_antimon; try eassumption.           
        * intros Hc.
          assert (Hcn : ~ l \in dom H2).
          { intros [v Hget]. erewrite alloc_fresh in Hget; eauto. congruence. }
          eapply Hcn.  
          eapply reachable_in_dom;  [| | eapply FV_image_reach with (Scope := Scope) ].
          
          eapply well_formed_antimon; [| eapply FV_reach2; try eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic... tci. 
          
          eapply Included_trans; [| eapply FV_dom2; try eassumption ].
          eapply env_locs_monotonic... tci. eassumption.
          eassumption. left. 
          eapply image_monotonic; eassumption. 
 
      + assert (Hsub' : reach' H1 (env_locs rho1 (FV (x |: Scope) (Funs \\ [set x]) FVs)) \\
                               env_locs rho1 (Funs \\ [set x] \\ (x |: Scope)) \\ [set l1] \subset
                               reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\
                               env_locs rho1 (Funs \\ Scope)).
        { rewrite !Setminus_Union. 
          eapply Included_Setminus_compat. rewrite Hseq'. reflexivity.
          rewrite <- env_locs_Singleton with (v := Loc l1); eauto.
          rewrite <- env_locs_Union. eapply env_locs_monotonic.
          rewrite (Union_Same_set [set x]), (Union_commut [set x]). rewrite <- Setminus_Union.
          rewrite <- Union_Setminus. eapply Included_Union_preserv_l... tci.
          now eauto with Ensembles_DB. }
        
        assert (Hcn : ~ l \in dom H2).
        { intros [v Hget]. erewrite alloc_fresh in Hget; eauto. congruence. }
        
        eapply Disjoint_Included. 
        eapply Included_Union_compat. rewrite env_locs_set_not_In. reflexivity.
        intros Hc. eapply Hdis. constructor. right. eapply image_monotonic; [| eassumption ]...
        left. right. now constructor; eauto.
        eapply image'_extend_Included_Some.

        eapply image_extend_Included'.
         
        eapply Disjoint_Included.
        eapply Included_Union_compat. reflexivity. 
        eapply Included_Union_compat. 
        eapply image'_monotonic. eassumption. reflexivity.
        eapply Included_Union_compat. eapply image_monotonic. eassumption. reflexivity.
        
        eapply Union_Disjoint_l; eapply Union_Disjoint_r.
        * eapply Disjoint_Included_r; [| eassumption ].
          eapply Included_Union_preserv_l. eapply env_locs_monotonic...
        * eapply Union_Disjoint_r.
          eapply Disjoint_Included_r; [| eassumption ]...

          eapply Disjoint_Singleton_r. intros Hc.
          eapply Hd. constructor. eassumption. left.
          eapply get_In_env_locs. eexists. constructor; eauto. constructor; eauto.
          eassumption. reflexivity.

        * eapply Disjoint_Singleton_l. intros Hc.
          eapply Hcn.
          eapply reachable_in_dom.
          eapply FV_reach2; try eassumption; now tci.
          eapply FV_dom2; try eassumption; now tci.

          eapply reach'_extensive. eapply env_locs_monotonic; [| eassumption ].
          unfold FV_cc...
          
        * eapply Union_Disjoint_r.

          eapply Disjoint_Singleton_l. intros Hc.
          
          eapply Hcn.
          eapply reachable_in_dom; [| | eapply FV_image_reach; try eassumption ].
          eapply well_formed_antimon; [| eapply FV_reach2; try eassumption; now tci ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic...
          eapply Included_trans; [| eapply FV_dom2; try eassumption; now tci ]. eapply env_locs_monotonic...
          right. eassumption.
          
          constructor. intros l2 Hc. inv Hc. inv H3; inv H4. eapply Hcn.
          eapply reachable_in_dom. eapply FV_reach2; try eassumption; now tci.
          eapply FV_dom2; try eassumption; now tci.
          eapply reach'_extensive. eapply get_In_env_locs; unfold FV_cc.
          left. right. eexists. split; eauto. now constructor; eauto. eassumption.
          reflexivity.
 
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
      do 2 eexists. split; [| split; [| split ]]. repeat split.
      + intros j.
        edestruct (Hfv j) as (Hwf & vs1 & loc_env & Hget1 & Hget2 & Hall).
        repeat subst_exp. eapply cc_approx_env_P_union.
        * edestruct (Forall2_P_nthN _ _ _ _ FVs _ N _ Hall H3) as (v2 & Hnth' & vs4 & Hget4 & Hrel).
          intros Hc. now inv Hc.  
          intros y Hin v' Hget. inv Hin. rewrite M.gss.
          repeat subst_exp. eexists. split. reflexivity.
          eassumption.
        *  eapply cc_approx_env_P_set_not_in_P_r; try eassumption.
           now eauto.
      + intros j. eapply Fun_inv_set_r.
        now eapply Fun_inv_Scope_monotonic; tci.
        now intros Hc; inv Hc; eauto.
        intros Hin. eapply Hdis. constructor. right.
        eapply image_monotonic; [| eassumption ]...
        right. constructor; eauto. eapply nthN_In. eassumption.
        intros Hc. inv Hc; eauto.
      + intros j.
        edestruct (Hfv j) as (Hwf & vs1 & loc_env & Hget1 & Hget2 & Hall).
        split. rewrite env_locs_set_not_In. eassumption.

        intros Hc. inv Hc.
        eapply Hdis. constructor. now left.
        right. constructor. eapply nthN_In. eassumption.
        intros Hc; inv Hc; eauto. 
        repeat eexists; eauto. 

        rewrite M.gso; eauto.
        intros Hc. subst.
        eapply Hdis. constructor. now left.
        right. constructor. eapply nthN_In. eassumption.
        intros Hc; inv Hc; eauto. 

        eapply Forall2_P_monotonic; [ eassumption | ]...
      + assert (Hseq' : x |: Scope :|: (FromList FVs \\ (x |: Scope :|: Funs')) <-->
                          Scope :|: (FromList FVs \\ (Scope :|: Funs'))).
        { rewrite <- (Union_assoc [set x] Scope Funs'), (Union_commut [set x] (Scope :|: Funs')) at 1.
          do 2 rewrite <- Setminus_Union.
          rewrite Union_Setminus_Included; try eauto with Ensembles_DB typeclass_instances.
          rewrite <- (Union_assoc [set x]).
          rewrite (Union_Same_set [set x]). reflexivity. eapply Singleton_Included.
          right. constructor; eauto. constructor; eauto. eapply nthN_In. eassumption. }

        rewrite <- !(Setminus_Union Funs' [set x]) at 1.
        rewrite !(Setminus_Disjoint Funs' [set x]) at 1; try (eapply Disjoint_Singleton_r; eassumption).
        rewrite !Hseq at 1. split.

        eassumption.

        rewrite env_locs_set_not_In. eassumption.
        
        intros Hc. eapply Hdis. constructor. right. eapply image_monotonic; [| eassumption ]...
        right. constructor; eauto. eapply nthN_In. eassumption. now intros Hc'; inv Hc'; eauto.

        Grab Existential Variables. exact 0. exact 0. (* TODO fix *)
  Qed.

 
  Lemma project_var_env_locs_dis (Scope Scope' Funs Funs' : Ensemble var) 
        (fenv : var -> var) (c : cTag) (Γ : var) (FVs : list var) 
        (x : var) (C1 : exp_ctx) (rho1 : env) (H1 : heap block) 
        (rho2 : env) (H2 : heap block) (m : nat) S :
    project_var ct Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    Disjoint _ S (Scope' \\ Scope) ->
    env_locs rho1 S <--> env_locs rho2 S.
  Admitted.

  Lemma project_vars_env_locs_dis (Scope Scope' Funs Funs' : Ensemble var) 
        (fenv : var -> var) (c : cTag) (Γ : var) (FVs : list var) 
        (x : list var) (C1 : exp_ctx) (rho1 : env) (H1 : heap block) 
        (rho2 : env) (H2 : heap block) (m : nat) S :
    project_vars ct Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
    ctx_to_heap_env_CC C1 H1 rho1 H2 rho2 m ->
    Disjoint _ S (Scope' \\ Scope) ->
    env_locs rho1 S <--> env_locs rho2 S.
  Admitted.  

  (** Correctness of [project_vars] *)
  Lemma project_vars_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b d
        Scope {Hs : ToMSet Scope} Scope' Funs Funs' fenv c Γ FVs xs C m :
    
    project_vars ct Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b; d) (H2, rho2)) ->
    (forall j, Fun_inv k j GII GI b d rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    (forall j, FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->

    injective_subdomain (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)) b ->
    Disjoint _ (image b (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)))
             (env_locs rho2 (image fenv (Funs \\ Scope)) :|:
              image' d (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope))) ->

    Disjoint _ (Γ |: image fenv (Funs \\ Scope)) (FV Scope Funs FVs) ->

    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->

    binding_in_map (FV Scope Funs FVs) rho1 ->

    exists b' d', 
      (forall j, (H1, rho1) ⋞ ^ (Scope'; k; j; GII; GI; b'; d') (H2', rho2'))  /\
      (forall j, Fun_inv k j GII GI b' d' rho1 H1 rho2' H2' Scope' Funs' fenv FVs) /\
      (forall j, FV_inv k j GII GI b' d' rho1 H1 rho2' H2' c Scope' Funs' Γ FVs) /\
      injective_subdomain (reach' H1 (env_locs rho1 (FV Scope' Funs' FVs)) \\ env_locs rho1 (Funs' \\ Scope')) b' /\
      Disjoint _ (image b' (reach' H1 (env_locs rho1 (FV Scope' Funs' FVs)) \\ env_locs rho1 (Funs' \\ Scope')))
               (env_locs rho2' (image fenv (Funs' \\ Scope')) :|:
                image' d' (reach' H1 (env_locs rho1 (FV Scope' Funs' FVs)) \\ env_locs rho1 (Funs' \\ Scope'))).
  Proof with (now eauto with Ensembles_DB).
    intros Hvars.
    revert b d m H1 rho1 H2 rho2 H2' rho2'.
    induction Hvars;
      intros b d m H1 rho1 H2 rho2 H2' rho2' Hcc Hfun Hfv
             Hinj Hd Hdis Hctx Hbin.
    - inv Hctx. do 2 eexists. split; [| split; [| split; [| split ]]]; eauto.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      edestruct project_var_correct as (b' & d' & Hcc' & Hfun' & Hfv' & Hinj' & Hd');
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
  
  Lemma Closure_conversion_fundefs_correct
    (k : nat) :
    (* The IH *)
    (* ... *)
    forall  B1 B2
       (H1 H1' H2 : heap block) (rho1 rho1c rho1' rho2 : env) b d
       (Scope Funs : Ensemble var) fenv  (Hs : ToMSet Scope)
       (Hf : ToMSet Funs) (FVs FVs': list var)
       (c : cTag) (Γ Γ' : var),
            
      (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; PreG; PostG; b; d) (H2, rho2)) ->
      (forall j, Fun_inv k j PreG PostG b d rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
      (forall j, FV_inv k j PreG PostG b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->

      injective_subdomain (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)) b ->
      Disjoint _ (image b (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)))
               (env_locs rho2 (image fenv (Funs \\ Scope)) :|:
               image' d (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope))) ->

      Disjoint _ (Γ' |: image fenv (Funs \\ Scope)) (name_in_fundefs B1) ->
    
      (* Free variables invariant for new fundefs *)
      (forall j, FV_inv k j PreG PostG b d rho1c H1 rho2 H2 c
                   (Empty_set _) (Empty_set _) Γ' FVs') -> (* no scope, no funs yet *)

      FromList FVs' <--> occurs_free_fundefs B1 ->
      NoDup FVs' ->

      unique_functions B1 ->
      
      env_locs rho1c (FromList FVs') \subset env_locs rho1 (FromList FVs') ->
      FromList FVs' \subset Scope \\ name_in_fundefs B1 ->
      
      Closure_conversion_fundefs ct B1 c FVs' B1 B2 ->
      
      def_closures B1 B1 rho1 H1 rho1c = (H1', rho1') -> 
      
      (forall j, Fun_inv k j PreG PostG b d
                    rho1' H1' (def_funs B2 B2 rho2) H2
                    (Scope \\ name_in_fundefs B1) (name_in_fundefs B1 :|: Funs) (extend_fundefs' fenv B1 Γ') FVs).
  Proof with (now eauto with Ensembles_DB).
    Opaque cc_approx_exp.
    induction k as [k IHk] using lt_wf_rec1.  
    intros B1 B2 H1 H1' H2 rho1 rho1c rho1' rho2 b d
           Scope Funs fenv Hs Hf FVs FVs' c Γ Γ' 
           Hcc Hfun Hfv Hinj Hd Hdis Hfvs' Hfveq Hnd
           Hun1 Hincl Hfvinc Hccf1 Hclo j.
    destruct (Hfvs' j) as  (Hwf & vs & lenv & Hgetlenv & Hget' & HallP).
    simpl in Hclo.

    intros f1 Hin Hnin.
    edestruct (@Dec _ (name_in_fundefs B1) _ f1) as [ Hfin | Hfnin ]. 
    - edestruct def_closures_exists as [lf [Hgetf [Hgetlf Hfresh]]]; try eassumption.
      exists lf, lenv, B1, f1, rho1c, B2, f1.
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
        
        { rewrite Union_commut, Union_Same_set in Hc.
          eapply reach'_set_monotonic in Hc; [| eapply env_locs_monotonic; eassumption ].
          rewrite env_locs_Union, reach'_Union in Hc. inv Hc. 
          - eapply reach'_set_monotonic in H; [| eapply env_locs_def_funs; [ reflexivity | now eauto ] ].

            rewrite <- well_formed_reach_subheap_same in H.
             
             eapply reachable_in_dom in H. eapply Hfresh. eassumption.
             
             eapply well_formed_antimon; [| eapply FV_reach1; try eassumption ].
             eapply reach'_set_monotonic. eapply env_locs_monotonic... tci.
             
             eapply Included_trans; [| eapply FV_dom1; [ | eassumption | eassumption | eassumption ]; tci ].
             eapply env_locs_monotonic...
             
             eapply well_formed_antimon; [| eapply FV_reach1; try eassumption ].
             eapply reach'_set_monotonic. eapply env_locs_monotonic... tci.
             
             eapply Included_trans; [| eapply FV_dom1; [ | eassumption | eassumption | eassumption ]; tci ].
             eapply env_locs_monotonic...
             
             eapply def_funs_subheap. now eauto.

          -  rewrite reach_unfold in H. inv H. 
                 
             eapply def_closures_env_locs_fresh. eassumption. eassumption. eassumption.
             constructor; [| eassumption ]. rewrite env_locs_Singleton; eauto. reflexivity.
                 
             eapply reach'_set_monotonic in H0. 
             * rewrite <- well_formed_reach_subheap_same in H0. eapply reachable_in_dom in H0.
               eapply Hfresh. eassumption.
               
               eapply FV_reach1; [ | eassumption | eassumption | eassumption ]; tci.
               eapply FV_dom1; [ | eassumption | eassumption | eassumption ]; tci.
               eapply FV_reach1; [ | eassumption | eassumption | eassumption ]; tci.
               eapply FV_dom1; [ | eassumption | eassumption | eassumption ]; tci.
               eapply def_funs_subheap. now eauto.
             * eapply Included_trans.
               eapply post_set_monotonic; eapply env_locs_monotonic;
               eapply Setminus_Included; eapply def_closures_post; eassumption.
               
               eapply Included_trans. eapply def_closures_post. eassumption. 
               rewrite <- Hfveq. eapply Included_trans. eassumption.
               eapply env_locs_monotonic. eapply Included_trans. eassumption.
               unfold FV... 
        
          - eapply Included_trans.
            eapply reach'_set_monotonic. rewrite <- Hfveq. eassumption.
            eapply reach'_set_monotonic. eapply Included_trans.
            eapply env_locs_monotonic. eassumption.
            rewrite <- def_closures_env_locs'; try eassumption.
            eapply env_locs_monotonic. unfold FV. rewrite !Setminus_Union_distr.
            rewrite (Setminus_Disjoint (Scope \\ name_in_fundefs B1))...
            eapply Disjoint_Setminus_l. reflexivity. }
   
      * erewrite def_funs_eq. reflexivity. reflexivity.
        rewrite <- closure_conversion_fundefs_Same_set. eassumption. eassumption.
      * eassumption.
      * rewrite extend_fundefs'_get_s.
        erewrite def_funs_neq. eassumption. reflexivity.
        intros Hc. eapply Hdis.
        rewrite closure_conversion_fundefs_Same_set.
        constructor. now left. eassumption.
        eassumption. eassumption.
      * eapply Proper_cc_approx_clos;
        [ symmetry; eassumption | reflexivity | reflexivity | ].

        eapply FV_inv_cc_approx_clos; [ | | | ].

        eapply FV_inv_heap_mon. eapply def_funs_subheap. now eauto.
        now eapply HL.subheap_refl. 

        eassumption. now eauto with Ensembles_DB.
        eassumption. eassumption.
      * destruct (alloc (Constr _ [FunPtr B2 f1; Loc lenv]) H2)
          as [lenv2 H2'] eqn:Ha'.
        simpl cc_approx_val'. erewrite !(gas _ _ _ _ _ Ha'); eauto.
        split; [ rewrite extend_gss; reflexivity |].
        rewrite Hgetlf. 
        split; [ rewrite extend_gss; reflexivity |].
        
        { split.
          (* Closure environment relation *)
          - intros i Hlt. setoid_rewrite <- Hfveq. 
            eapply FV_inv_cc_approx_clos; [ | | eassumption | eassumption ].
            eapply FV_inv_heap_mon. eapply def_funs_subheap. now eauto.
            eapply HL.alloc_subheap. eassumption. intros j'.
 
            eapply FV_inv_rename_ext; [ now eauto | | ]. 
 
            eapply f_eq_subdomain_extend_not_In_S_l.
            intros Hc. eapply reachable_in_dom in Hc. contradiction.
            eapply FV_inv_reach1. eassumption.
            eapply FV_inv_dom1. eassumption.
            reflexivity.

            eapply f_eq_subdomain_extend_not_In_S_l.
            intros Hc. eapply reachable_in_dom in Hc. contradiction.
            eapply FV_inv_reach1. eassumption.
            eapply FV_inv_dom1. eassumption.
            reflexivity.

            now eauto with Ensembles_DB.

          - intros b1 b2 rhoc' rhoc1 rhoc2 H3 H3' H4 lr xs1 ft ef vs1 vs2.
            intros Heq1 Hinj1 Heq2 Hinj2 Hf' Hdef Hset.
            edestruct Closure_conversion_fundefs_find_def as
                (Γ'' & e2 & C' & Hfind & Hclo').
            eassumption. eassumption.
            edestruct (setlist_length rhoc1 (def_funs B2 B2 (M.empty value))
                                      rhoc2 xs1 vs1 vs2)
              as [rho2' Hset2]; [ admit (* add length vs1 = lngth v2 *)
                                | now apply Hset | ].
            
            { do 3 eexists. split; [| split; [| split ]].
              - eassumption.
              - simpl. rewrite Hset2. reflexivity.
              - admit. (* size after GC
                            TODO remove live from log. rel. add size reachable?
                        *)
              - admit. (* Apply IH for expressions. Show well-formedness etc.... *) } }

    - inv Hnin. contradiction. 
      edestruct (Hfun j) as
          (l1 & lenv' & B1' & g1 & rhoc & B2' & g2 & Hgetf1 & Hnin' & Hgetf1' & Hgetl1 & Hext & Henvc & Hrel).
      intros Hc. eapply Hin. constructor; eauto. eassumption.
      eexists l1, lenv', B1', g1, rhoc, B2', g2.
      split; [| split; [| split; [| split; [| split; [| split ]]]]]. 
      + erewrite def_closures_get_neq; eassumption.
      + intros Hc. eapply Hnin'. rewrite reach'_Union in Hc.
        rewrite reach'_Union.
        inv Hc. 
        eapply def_closures_reach in H0; try eassumption.
        inv H0.

        * left. eapply reach'_set_monotonic; [| eassumption ].
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
        * exfalso. eapply def_closures_env_locs_Disjoint. eassumption.
          constructor; eauto. eexists; eauto.
        * eapply well_formed_antimon; [| eapply FV_reach1; try eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          do 2 eapply Setminus_Included_Included_Union.
          eapply Included_trans.
          eapply FV_Setminus1. now tci.
          eapply Included_trans. eapply Included_Union_compat. reflexivity. 
          eapply FV_Union2. now eauto with Ensembles_DB.
          tci.
        * eapply Included_trans; [| eapply FV_dom1; [ | eassumption | eassumption | eassumption ]; tci ].
          eapply env_locs_monotonic.
          do 2 eapply Setminus_Included_Included_Union.
          eapply Included_trans.
          eapply FV_Setminus1. now tci.
          eapply Included_trans. eapply Included_Union_compat. reflexivity. 
          eapply FV_Union2. now eauto with Ensembles_DB.
        * eapply Included_trans. rewrite <- Hfveq. eassumption.
          eapply Included_trans. eapply env_locs_monotonic. eassumption.
          eapply Included_trans; [| eapply reach'_extensive ].
          eapply env_locs_monotonic. unfold FV.
          rewrite !Setminus_Union_distr. rewrite !Setminus_Union.
          rewrite Union_assoc. rewrite (Union_Same_set (name_in_fundefs B1)).
          rewrite (Union_commut [set f1]) at 1. rewrite <- !Setminus_Union.
          rewrite (Setminus_Disjoint _ [set f1])...
          now eauto with Ensembles_DB.

        * rewrite <- well_formed_reach_subheap_same in H0; [| | | eapply def_funs_subheap; now eauto ].
          rewrite post_Singleton in H0; [| eapply def_funs_subheap; now eauto ].          
          right. now rewrite post_Singleton; eauto.

          rewrite post_Singleton; [| eapply def_funs_subheap; now eauto ].
          
          eapply well_formed_antimon; [| eapply FV_reach1; try eassumption ].
          rewrite (reach_unfold H1 (env_locs _ _ )). eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic.
          eapply Included_trans ; [| eapply post_set_monotonic with (S1 := [set l1]) ].
          rewrite post_Singleton; eauto. reflexivity.
          eapply get_In_env_locs with (v := Loc l1); try eassumption.

          edestruct (@Dec _ Scope _ f1). left. now left.
          left. right. constructor; eauto. now tci.

          rewrite post_Singleton; [| eapply def_funs_subheap; now eauto ].

          eapply Included_trans; [| eapply reachable_in_dom;
                                    [ eapply FV_reach1; try eassumption
                                    | eapply FV_dom1; try eassumption ] ].
          rewrite (reach_unfold H1 (env_locs _ _ )). eapply Included_Union_preserv_r.
          eapply Included_trans; [| eapply reach'_extensive ].
          eapply Included_trans ; [| eapply post_set_monotonic with (S1 := [set l1]) ].
          rewrite post_Singleton; eauto. reflexivity.
          eapply get_In_env_locs with (v := Loc l1); try eassumption.
          
          edestruct (@Dec _ Scope _ f1). left. now left.
          left. right. constructor; eauto. now tci.
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
            (l1' & lenv'' & B1'' & g1' & rhoc' & B2'' & g2' & Hgetf2 & Hnin''
             & Hgetf2' & Hgetl1' & Hext' & Henvc' & Hrel').
        intros Hin'. eapply Hin. now constructor; eauto. 
        eassumption. 
        repeat subst_exp. eassumption.

      + destruct (alloc (Constr _ [FunPtr B2' g2; Loc lenv']) H2) as [l2' H2''] eqn:Ha.
        eapply cc_approx_val_heap_monotonic.
        eapply def_funs_subheap. now eauto.
        now eapply HL.subheap_refl. intros j'.
        edestruct (Hfun j') as
            (l1' & lenv'' & B1'' & g1' & rhoc' & B2'' & g2' & Hgetf2 & Hnin''
            & Hgetf2' & Hgetl1' & Hext' & Henvc' & Hrel').
        intros Hin'. eapply Hin. now constructor; eauto. 
        eassumption. repeat subst_exp. rewrite Ha in Hrel'.
        eassumption.
  Admitted.



  Lemma project_var_size_ps_cardinal Scope Funs {Hf : ToMSet Funs} Scope' Funs' {Hf' : ToMSet Funs'}
        fenv c x FVs Γ C :
    project_var ct Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    PS.cardinal (@mset Funs Hf)  =
    PS.cardinal (@mset Funs' Hf') + PS.cardinal (@mset (Funs \\ Funs') _).
  Proof.
    intros Hvar. assert (Hvar' := Hvar). 
    rewrite PS_cardinal_union. 
    eapply Proper_carinal. eapply Same_set_From_set.
    rewrite FromSet_union.
    do 3 setoid_rewrite <- mset_eq at 1.
    eapply project_var_Scope_Funs_eq in Hvar.
    eapply Union_Setminus_Same_set. now tci.
    eapply project_var_Funs_l. eassumption.
    eapply FromSet_disjoint.
    do 2 setoid_rewrite <- mset_eq at 1.
    eapply Disjoint_Setminus_r. reflexivity. 
  Qed.

  Lemma project_vars_size_ps_cardinal Scope Funs {Hf : ToMSet Funs} Scope' Funs' {Hf' : ToMSet Funs'}
        fenv c xs FVs Γ C :
    project_vars ct Scope Funs fenv c Γ FVs xs C Scope' Funs' ->
    PS.cardinal (@mset Funs Hf)  =
    PS.cardinal (@mset Funs' Hf') + PS.cardinal (@mset (Funs \\ Funs') _).
  Proof with (now eauto with Ensembles_DB).
    intros Hvars. induction Hvars.
    - rewrite PS_cardinal_union. 
      eapply Proper_carinal. eapply Same_set_From_set.
      rewrite FromSet_union.
      do 3 setoid_rewrite <- mset_eq at 1.
      rewrite Setminus_Same_set_Empty_set...
      eapply FromSet_disjoint.
      do 2 setoid_rewrite <- mset_eq at 1.
      eapply Disjoint_Setminus_r. reflexivity. 
    - rewrite PS_cardinal_union. 
      eapply Proper_carinal. eapply Same_set_From_set.
      rewrite FromSet_union.
      do 3 setoid_rewrite <- mset_eq at 1.
      rewrite <- Union_Setminus_Same_set. reflexivity.
      now tci.
      eapply Included_trans.

      eapply project_vars_Funs_l. eassumption.
      eapply project_var_Funs_l. eassumption.

      eapply FromSet_disjoint.
      do 2 setoid_rewrite <- mset_eq at 1.
      eapply Disjoint_Setminus_r. reflexivity. 
  Qed.

  Lemma project_vars_ToMSet (Scope1 : Ensemble positive) (Scope2 : Ensemble var)
        { Hs : ToMSet Scope1 } (Funs1 Funs2 : Ensemble var) (fenv : var -> var) 
        (c : cTag) (Γ : var) (FVs : list var) (ys : list var) 
        (C1 : exp_ctx) :
    project_vars Inv.Size.Util.clo_tag Scope1 Funs1 fenv c Γ FVs ys C1 Scope2 Funs2 -> ToMSet Scope2.
  Proof.
  Admitted.

  Lemma project_vars_ToMSet_Funs (Scope1 : Ensemble positive) (Scope2 : Ensemble var)
        (Funs1 Funs2 : Ensemble var)  { Hf : ToMSet Funs1 } (fenv : var -> var) 
        (c : cTag) (Γ : var) (FVs : list var) (ys : list var) 
        (C1 : exp_ctx) :
    project_vars Inv.Size.Util.clo_tag Scope1 Funs1 fenv c Γ FVs ys C1 Scope2 Funs2 -> ToMSet Funs2.
  Proof.
  Admitted.
    

  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct (k : nat) (H1 H2 : heap block)
        (rho1 rho2 : env) (e1 e2 : exp) (C : exp_ctx)
        (Scope Funs : Ensemble var) {Hs : ToMSet Scope} {Hf : ToMSet Funs} (FVs : list var)
        fenv (β : Inj) (δ : EInj) (c : cTag) (Γ : var) :
    (* [Scope] invariant *)
    (forall j, (H1, rho1) ⋞ ^ (Scope ; k ; j ; PreG; PostG ; β; δ) (H2, rho2)) ->
    (* Free variable invariant *)
    (forall j, FV_inv k j PreG PostG β δ rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    (* Functions in scope invariant *)
    (forall j, Fun_inv k j PreG PostG β δ rho1 H1 rho2 H2  Scope Funs fenv FVs) ->

    injective_subdomain
      (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)) β ->
    Disjoint _ (image β (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)))
             (env_locs rho2 (image fenv (Funs \\ Scope)) :|:
             image' δ (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope))) ->

    Disjoint _ (Γ |: image fenv (Funs \\ Scope)) (bound_var e1 :|: FV Scope Funs FVs) ->

    (* The free variables of e are defined in the environment *)
    binding_in_map (FV Scope Funs FVs) rho1 ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e1 ->
    
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion ct Scope Funs fenv c Γ FVs e1 e2 C ->
    
    (forall j, (e1, rho1, H1) ⪯ ^ (k ; j ;
                              Pre (3*PS.cardinal (@mset Funs Hf)); PreG;
                              Post 0 (3*PS.cardinal (@mset Funs Hf)) (Funs \\ Scope); PostG)
          (C |[ e2 ]|, rho2, H2)).
  Proof with now eauto with Ensembles_DB.
    revert H1 H2 rho1 rho2 e1 e2 C Scope Hs Funs Hf FVs fenv β δ c Γ.
    induction k as [k IHk] using lt_wf_rec1.  
    intros H1 H2 rho1 rho2 e1 e2 C Scope Hs Funs Hf FVs fenv β δ c Γ
           Henv HFVs Hfun Hinj Him Hdis Hbind Hun Hcc.
    assert (Hfv := Closure_conversion_pre_occurs_free_Included _ _ _ _ _ _ _ _ _ Hcc).
    assert (Hfv' := Closure_conversion_occurs_free_Included _ _ _ _ _ _ _ _ _ Hcc).
    induction e1 using exp_ind'; try clear IHe1.
    - (* case Econstr *)
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
      eapply Disjoint_Included; [ | | eassumption ]...
      specialize (Hfun 0); eapply Fun_inv_weak_in_Fun_inv; eassumption.
      specialize (HFVs 0); eapply FV_inv_weak_in_FV_inv; eassumption.
      
      intros j.
      (* process right ctx *)
      eapply cc_approx_exp_right_ctx_compat
      with (IL2 := (Post (cost_ctx_full C) (3*PS.cardinal (@mset Funs' _)) (Funs' \\ Scope')));
        [ | | | | | | now eapply Hct | ].
      
      + erewrite (project_vars_size_ps_cardinal Scope Funs Scope' Funs'); [| now eapply H13 ].
        rewrite NPeano.Nat.mul_add_distr_l.
        eapply PostCtxCompat_vars_r. eassumption. omega.
      + Set Printing Implicit. idtac. 
        erewrite (project_vars_size_ps_cardinal Scope Funs Scope' Funs'); [| now eapply H13 ].
        rewrite NPeano.Nat.mul_add_distr_l.
        eapply (PreCtxCompat_vars_r Scope Scope' Funs Funs').
        eassumption.
      + eapply well_formed_antimon; [| eapply FV_reach1; try eassumption; now tci ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        
      + eapply well_formed_antimon; [| eapply FV_reach2;
                                       [| eassumption | eassumption | eassumption | ]; tci ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        eapply binding_in_map_antimon; [| eassumption ]...

      + eapply Included_trans; [| eapply FV_dom1 with (Scope := Scope); try eassumption ].
        eapply env_locs_monotonic. eassumption.

      + eapply Included_trans; [| eapply FV_dom2 with (Scope := Scope); try eassumption ].
        eapply env_locs_monotonic. eassumption.
        eapply binding_in_map_antimon; [| eassumption ]...
      + Set Printing Implicit.
        idtac. edestruct project_vars_correct with (Scope := Scope) as (Hd' & Henv' & HFVs' & Hvars);
        try eassumption.
        eapply Disjoint_Included; [ | | eassumption ]...
        
        (* process Econstr one the right and left *)
        eapply cc_approx_exp_constr_compat
        with (IIL2 := Pre (3 * PS.cardinal (@mset Funs Hf))
             (IL2 := Post 0 (size_cc_heap (env_locs rho1 Funs) H1') (Funs \\ Scope));
              [ | | | | | | |  |  ].
        * admit.

        * admit.

        * admit.

        * eapply well_formed_antimon; [| eapply FV_reach1 with (Scope := Scope);
                                         try eassumption; now tci ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.

        * admit. (* WF easy *)
        * admit. (* easy assert *)
        * admit. (* easy assert *)
        * admit.
        * (* Inductive case *)  
          {  intros vs1 vs2 l1 l2 H1'' H2'' Hleq Ha1' Ha2 Hall j1. repeat subst_exp.
             
            (* (* monotonicity of the local invariant *)  *)
            (* assert (Hfeq : f_eq_subdomain (reach' H1 (env_locs rho1 (FV Scope FVs))) b (b {l1 ~> l2})). *)
            (* { eapply f_eq_subdomain_extend_not_In_S_r; [| reflexivity ]. *)
            (*   intros Hc. eapply reachable_in_dom in Hc. *)
            (*   edestruct Hc as [vc Hgetc]. erewrite alloc_fresh in Hgetc; eauto. congruence. *)
            (*   eassumption. eassumption. } *)
            (* assert (Hfeq' : f_eq_subdomain (reach' H1 (env_locs rho1 (FV Scope FVs))) d (d {l1 ~> None})). *)
            (* { eapply f_eq_subdomain_extend_not_In_S_r; [| reflexivity ]. *)
            (*   intros Hc. eapply reachable_in_dom in Hc. *)
            (*   edestruct Hc as [vc Hgetc]. erewrite alloc_fresh in Hgetc; eauto. congruence. *)
            (*   eassumption. eassumption. } *)
            (* Induction hypothesis *)
            { eapply IHk;
              [ | | | | | | | | | | | | | |  ].
              * simpl in *. omega.
              * now eauto with typeclass_instances.
              * { intros j2.  
                  eapply cc_approx_env_set_alloc_Constr with (b := b {l1 ~> l2}) (d := d {l1 ~> None});
                    try eassumption.
                  - eapply well_formed_antimon; [| now apply Hwf1 ].
                    eapply reach'_set_monotonic. eapply env_locs_monotonic.
                    unfold FV...
                  - eapply well_formed_antimon; [| now apply Hwf2 ].
                    eapply reach'_set_monotonic. eapply env_locs_monotonic.
                    unfold FV_cc...
                  - eapply Included_trans; [| eassumption ].
                    eapply env_locs_monotonic.
                    unfold FV...
                  - eapply Included_trans; [| eassumption ].
                    eapply env_locs_monotonic.
                    unfold FV...
                  - eapply well_formed_antimon. eapply reach'_set_monotonic.
                    eassumption.
                eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic...
              - eapply well_formed_antimon. eapply reach'_set_monotonic.
                eassumption.
                eapply project_vars_well_formed; eauto.
                eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic.
                eassumption. eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
              - eapply Included_trans. eassumption.
                eapply Included_trans; [| eassumption ].
                eapply env_locs_monotonic...
              - eapply Included_trans. eassumption.
                eapply project_vars_env_locs; eauto. eapply Included_trans. 
                eapply env_locs_monotonic. eassumption. eassumption.
                eapply well_formed_antimon.
                eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
                eassumption.
              - eapply cc_approx_env_rename_ext.
                eapply cc_approx_env_P_antimon.
                eapply cc_approx_env_P_monotonic. now eauto.
                simpl in *; omega.
                now eauto with Ensembles_DB.

                eapply f_eq_subdomain_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic.
                unfold FV...

                eapply f_eq_subdomain_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic.
                unfold FV...

              - rewrite extend_gss. reflexivity.
              - rewrite extend_gss. reflexivity.
              - intros j3 Hlt3. eapply Forall2_monotonic_strong; [| now eapply Hall ].
                intros x1 x2 Hin1 Hin2 Hrel.

                assert (Hincl : val_loc x1 \subset env_locs rho1 (FV Scope FVs)).
                { eapply Included_trans; [| now eapply env_locs_monotonic; eauto ].
                  eapply Included_trans; [| eassumption ].
                  simpl. eapply In_Union_list. eapply in_map. eassumption. }

                assert (Hc : ~ In positive (reach' H1 (val_loc x1)) l1). 
                { intros Hc. eapply reachable_in_dom in Hc.
                  destruct Hc as [v1 Hgetv1]. erewrite alloc_fresh in Hgetv1; try eassumption.
                  congruence.
                  
                  eapply well_formed_antimon; [| eassumption ].
                  eapply reach'_set_monotonic. eassumption.

                  eapply Included_trans; eassumption. }
                
                eapply cc_approx_val_rename_ext. now eapply Hrel.
                
                eapply f_eq_subdomain_extend_not_In_S_l; [| reflexivity ]; eassumption.
                eapply f_eq_subdomain_extend_not_In_S_l; [| reflexivity ]; eassumption. }
          * intros j'. 
            { eapply FV_inv_set_not_in_FVs.
              - eapply FV_inv_heap_mon; try (now eapply HL.alloc_subheap; eauto).
                + eapply well_formed_antimon; [| eassumption ].
                  eapply reach'_set_monotonic. eapply env_locs_monotonic.
                  unfold FV...
                + eapply well_formed_antimon; [| eassumption ].
                  eapply reach'_set_monotonic. eapply env_locs_monotonic.
                  unfold FV_cc. now eauto 20 with Ensembles_DB.
                + eapply Included_trans; [| eassumption ].
                  eapply env_locs_monotonic.
                  unfold FV...
                + eapply Included_trans; [| eassumption ].
                  eapply env_locs_monotonic.
                  unfold FV_cc. now eauto 20 with Ensembles_DB.
                + eapply FV_inv_rename_ext.
                  eapply FV_inv_Scope_mon. eapply FV_inv_monotonic.
                  eauto. simpl in *; omega. now eauto with Ensembles_DB.
                  symmetry. eapply f_eq_subdomain_antimon; [| eassumption ].
                  eapply reach'_set_monotonic. eapply env_locs_monotonic...
                  symmetry. eapply f_eq_subdomain_antimon; [| eassumption ].
                  eapply reach'_set_monotonic. eapply env_locs_monotonic...
              - intros Hc. inv Hc; eauto.
              - intros Hc. eapply Hnin. subst; eauto. }
          * assert
              (Hinc :
                 reach' H1'
                        (env_locs (M.set v (Loc l1) rho1)
                                  (FV (v |: Scope) FVs)) \\ [set l1]
                        \subset
                  reach' H1 (env_locs rho1 (FV Scope FVs))
              ).
            { eapply Included_trans. eapply Included_Setminus_compat.
              eapply Included_trans;
                [| eapply reach'_alloc_set with (H' := H1')
                                                (S := FV Scope FVs)];
              try eassumption.
              eapply reach'_set_monotonic. eapply env_locs_monotonic.
              now eauto 20 with Ensembles_DB.
              eapply Included_trans. eassumption.
              eapply Included_trans; [| eapply reach'_extensive ].
              eapply env_locs_monotonic. eapply Included_trans; [ eassumption |]...
              reflexivity. 
              rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set,
              Union_Empty_set_neut_l.
              eapply Setminus_Included_preserv.
              eapply reach'_set_monotonic. eapply env_locs_monotonic.
              now eauto 20 with Ensembles_DB. }

            eapply injective_subdomain_extend'.
            { eapply injective_subdomain_antimon; eassumption. }
            { intros Hc. eapply image_monotonic in Hc; [| eassumption ].
              admit. }
              (* eapply image_FV in Hc; try eassumption. *)
              (* eapply reachable_in_dom in Hc. *)
              (* destruct Hc as [vc Hgetc]. erewrite alloc_fresh in Hgetc; eauto. congruence. *)
              (* eapply well_formed_antimon; [| eassumption ]. *)
              (* unfold FV_cc. rewrite !env_locs_Union, !reach'_Union. *)
              (* eapply Included_Union_preserv_r.  *)
              (* eapply Included_Union_compat. *)
              (* reflexivity. *)
              (* rewrite (reach_unfold H2' (env_locs _ _))... *)
              (* eapply Union_Included. eapply Included_trans; [| eassumption ]. *)
              (* eapply env_locs_monotonic. unfold FV_cc... *)
              (* eapply Included_trans; [| eapply reachable_in_dom; eauto ]. *)
              (* rewrite !env_locs_Union, !reach'_Union. *)
              (* eapply Included_Union_preserv_r. *)
              (* eapply Included_trans. eapply Included_post_reach'. *)
              (* eapply reach'_set_monotonic. eapply env_locs_monotonic. unfold FV_cc... *)
          (* eapply binding_in_map_antimon; [| eassumption ]... } *)
          * admit.
          * admit. 
          * assert (Hseq : (FV (v |: Scope) FVs) \subset
                                                      (FV Scope FVs) :|: [set v]).
            { unfold FV. eapply Union_Included; [| now eauto with Ensembles_DB ]... }
            eapply well_formed_antimon. eapply reach'_set_monotonic.
            eapply env_locs_monotonic. eassumption.
            eapply well_formed_reach_alloc'; try eassumption.
            rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
            eassumption.
            rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
            eassumption.
            rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
            eapply Included_trans. eassumption.
            eapply Included_trans; [| eapply reach'_extensive ].
            eapply env_locs_monotonic. eassumption.
          * eapply Included_trans. now eapply env_locs_set_Inlcuded'.
            rewrite HL.alloc_dom; [| eassumption ].
            eapply Included_Union_compat. reflexivity.
            eapply Included_trans; [| eassumption ].
            eapply env_locs_monotonic. now eauto 20 with Ensembles_DB.
          * assert (Hseq : (FV_cc (v |: Scope) Γ) \subset
                           (FV_cc Scope  Γ) :|: [set v]).
            { unfold FV_cc. eapply Union_Included; [| now eauto with Ensembles_DB ]... }
            eapply well_formed_antimon. eapply reach'_set_monotonic.
            eapply env_locs_monotonic. eassumption.
            eapply well_formed_reach_alloc; eauto.
            eapply well_formed_antimon; [| eassumption ].
            eapply reach'_set_monotonic. eapply env_locs_monotonic...
            eapply Included_trans;[| eassumption ].
            eapply env_locs_monotonic...
            eapply Included_trans. eassumption. 
            eapply Included_trans. eapply reach'_extensive.
            eapply Included_trans. eapply project_vars_reachable; eauto.
            eapply Included_trans. eapply reach'_set_monotonic. eapply env_locs_monotonic.
            eassumption. erewrite project_vars_heap with (H := H2) (H' := H2'); eauto.
            rewrite project_vars_env_locs_subset with (rho := rho2) (rho' := rho2'); eauto.
            reflexivity.
            eapply Disjoint_Included_l; [| eapply Disjoint_sym; eassumption ]...
          * eapply Included_trans. now eapply env_locs_set_Inlcuded'.
            rewrite HL.alloc_dom; [| eassumption ].
            eapply Included_Union_compat. reflexivity.
            eapply Included_trans; [| eassumption ].
            eapply env_locs_monotonic. now eauto 20 with Ensembles_DB.
          * now eauto.
          * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
            now eauto 20 with Ensembles_DB.
          * intros f Hfin. eauto. }
    - (* case Eproj *)
      inv Hcc.
      admit.
      
    - (* case Ecase nil *)
      inv Hcc.
      admit.
    - (* case Ecase cons *)
      inv Hcc. (* TODO change compat *) 
      admit.
    - (* case Efun *)
      inv Hcc.
      
      edestruct (binding_in_map_getlist _ rho1 (FVs') Hbind) as [vl Hgetl].
      eapply Included_trans; [| eassumption ].
      rewrite <- H3. normalize_occurs_free...
      
      edestruct project_vars_ctx_to_heap_env as [H2' [rho2' [m Hct]]]; try eassumption.
      specialize (HFVs 0); eapply FV_inv_weak_in_FV_inv; eassumption.
      
      edestruct project_vars_correct as (Hd' & Henv' & HFVs' & Hvars);
        try eassumption.
      eapply binding_in_map_antimon; [| eassumption ]...
      
      rewrite <- app_ctx_f_fuse in *. intros j.
      
      (* process right ctx 1 : project fvs *)
      eapply cc_approx_exp_right_ctx_compat; [ | | | | | | eassumption | ].
      
      + eapply PostCtxCompat_vars_r. eassumption.
        
      + eapply PreCtxCompat_vars_r. eassumption.
      
      + eapply well_formed_antimon. eapply reach'_set_monotonic.
        now eapply env_locs_monotonic; eauto.
        eassumption.

      + eapply well_formed_antimon. eapply reach'_set_monotonic.
        now eapply env_locs_monotonic; eauto.
        eassumption.
      
      + eapply Included_trans; [| eassumption ]. now eapply env_locs_monotonic; eauto.
      + eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic; eauto.

      + assert (Hwf2' := Hwf2).
        assert (Hlocs2' := Hlocs2). 
        eapply project_vars_well_formed' in Hwf2; try eassumption;
        [| eapply Disjoint_Included_r; try eassumption; unfold FV_cc; now eauto with Ensembles_DB ].
        eapply project_vars_env_locs' in Hlocs2; try eassumption;
        [| eapply Disjoint_Included_r; try eassumption; unfold FV_cc; now eauto with Ensembles_DB ].
        
        edestruct cc_approx_var_env_getlist as [vl' [Hgetl2 Hcc]].
        eapply (Hvars j). eassumption.
        
        destruct (alloc (Constr c' vl') H2') as [lenv H1'] eqn:Hal.
        
        (* process right ctx 2 : make environment *)
        eapply cc_approx_exp_right_ctx_compat; [ | | | | | | | ].
        * admit. (* inv *)
        * admit. (* inv *)

        * eapply well_formed_antimon. eapply reach'_set_monotonic.
          now eapply env_locs_monotonic; eauto.
          eassumption.
        * eapply well_formed_antimon; [| eassumption ]. eapply reach'_set_monotonic.
          eapply env_locs_monotonic; eauto. simpl. normalize_occurs_free.
          admit. (* sets *)
        * eapply Included_trans; [| eassumption ]. now eapply env_locs_monotonic; eauto.
        * eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic; eauto. admit.
        * econstructor; eauto. now constructor; eauto.

        * (* Efun compat *)
          { eapply cc_approx_exp_fun_compat.
            - admit. (* inv *)
            - admit. (* inv *)
            - admit. (* inv *)
            - eapply well_formed_antimon; [| eassumption ].
              eapply reach'_set_monotonic. eapply env_locs_monotonic...
            - eapply Included_trans; [| eassumption ].
              eapply env_locs_monotonic...
            - { intros H11 rc1 rc2 henv Hdef. 
                subst.

                assert (Hrsub :
                          reach' H11 (env_locs rc1 (FV Scope FVs \\ name_in_fundefs f2)) \subset
                          reach' H1 (env_locs rho1 (FV Scope FVs))).
                { eapply Included_trans. eapply reach'_set_monotonic. 
                  eapply env_locs_def_funs; [ reflexivity | now eauto ].
                  rewrite <- well_formed_reach_def_closed_same;
                  [ | | | | eassumption ].
                  * eapply reach'_set_monotonic.
                    eapply env_locs_monotonic...
                  * eapply well_formed_antimon; [| eassumption ].
                    eapply reach'_set_monotonic.
                    eapply env_locs_monotonic...
                  * eapply Included_trans; [| eassumption ].
                    eapply env_locs_monotonic...
                  * eapply Included_trans.
                    eapply Included_trans; [| eapply restrict_env_env_locs ].
                    eapply env_locs_monotonic. now eauto with Ensembles_DB.
                    eapply restrict_env_correct. now eapply fundefs_fv_correct.

                    eapply env_locs_monotonic.
                    eapply Included_trans;
                      [| eapply Included_Setminus_compat; [ eassumption | reflexivity ] ].
                    normalize_occurs_free. rewrite Setminus_Union_distr.
                    eapply Included_Union_preserv_l .
                    rewrite Setminus_Disjoint. reflexivity.

                    eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint. }
                
                edestruct make_closures_ctx_to_heap_env
                with (rho := def_funs B' B' (M.set Γ' (Loc lenv) rho2'))
                  as (H2c & rho2c & mc & Hctxclo);
                  [ eassumption | admit (* binding in map *)| ].
                 
                edestruct make_closures_correct as (b' & d' & Hrel & Hinv & Hinj' & Hdis');
                  [ eassumption | | | | | | | | |  | | eassumption | | | | | | ].
                
                + (* well-formed H11 *) 
                  eapply well_formed_reach_alloc_def_funs with (S := FV Scope FVs);
                  [ | | | eassumption ].
                  eassumption. eassumption.
                  eapply Included_trans.
                  eapply Included_trans; [| eapply restrict_env_env_locs ].
                  eapply env_locs_monotonic. now eauto with Ensembles_DB.
                  eapply restrict_env_correct. eapply fundefs_fv_correct.
                  eapply Included_trans; [| eapply reach'_extensive ].
                  eapply env_locs_monotonic.
                  eapply Included_trans; [| eassumption ].
                  normalize_occurs_free...
                + (* env_locs rc1 *)
                  eapply def_closures_env_locs_in_dom.
                  eassumption. eassumption.
                + (* well-formed H1' (def_funs B' B' (M.set Γ' (Loc lenv) rho2')) *)
                  eapply well_formed_antimon.
                  * eapply reach'_set_monotonic.
                    eapply def_funs_env_loc.
                  * eapply well_formed_antimon;
                    [| eapply well_formed_reach_alloc with (S := FromList FVs'' :|: FV_cc Scope Γ) ].
                    eapply reach'_set_monotonic.
                    eapply env_locs_monotonic. unfold FV_cc...

                    eapply project_vars_well_formed'. eassumption. eassumption.
                    eapply Disjoint_Included_r; [ | eassumption ].
                    unfold FV_cc... eassumption. eassumption.

                    eapply project_vars_env_locs'. eassumption. eassumption.
                    eapply Disjoint_Included_r; [ | eassumption ].
                    unfold FV_cc... eassumption. eassumption.

                    eassumption.

                    simpl.
                    rewrite env_locs_Union, reach'_Union.
                    eapply Included_Union_preserv_l.
                    rewrite env_locs_FromList; [| eassumption ].
                    eapply reach'_extensive.

                + (* env_locs (def_funs B' B' (M.set Γ' (Loc lenv) rho2')) *)
                  eapply Included_trans. eapply def_funs_env_loc.
                  eapply Included_trans. eapply env_locs_set_Inlcuded'.
                  rewrite HL.alloc_dom; [| eassumption ].
                  eapply Included_Union_compat. reflexivity.

                  eapply Included_trans; [| eapply project_vars_env_locs' ];
                  [| eassumption | eassumption | | eassumption | eassumption ].

                  eapply env_locs_monotonic. unfold FV_cc...
                  eapply Disjoint_Included_r; [ | eassumption ].
                  unfold FV_cc...

                + admit. (* Disjoint + fresh fun locs after def_closures *)
                + admit. (* post fun locs after def_closures reachable *)
                + rewrite env_locs_Singleton with (v := Loc lenv); [| ].
                  * (* image b \in reach Η2 \in dom H2 <> lenv *)
                    admit.
                  * (* Γ' <> name B' *)  admit.
                + intros j'.
                  rewrite <- (Union_Same_set (name_in_fundefs f2) (name_in_fundefs f2)).
                  rewrite closure_conversion_fundefs_Same_set at 2; [| eassumption ].
                  rewrite <- Setminus_Union.
                  eapply def_funs_cc_approx_env.
                  eapply def_closures_cc_approx_env; [ | | | | | eassumption ].
                  eapply well_formed_antimon; [| eassumption ].
                  eapply reach'_set_monotonic. eapply env_locs_monotonic.
                  unfold FV...
                  eapply Included_trans; [| eassumption ].
                  eapply env_locs_monotonic. unfold FV...
                  (* well_formed (reach' H1' (env_locs (M.set Γ' (Loc lenv) rho2') Scope)) H1' *)
                  admit.
                  (* env_locs (M.set Γ' (Loc lenv) rho2') Scope \subset dom H1' *)
                  admit.
                  (* (H1, rho1) ⋞ ^ (Scope; ?k; j'; ?GI; ?GP; ?b; ?d) (H1', M.set Γ' (Loc lenv) rho2') *)
                  admit.
                  reflexivity.
                + (* (3)_ IH for def_clo + def_funs *) admit.
                + (* (2) FV_inv after def_closures + def_funs *)
                  setoid_rewrite <- (Union_Same_set (name_in_fundefs B') (name_in_fundefs f2));
                  [| eapply closure_conversion_fundefs_Same_set; eassumption ].
                  setoid_rewrite <- Union_assoc.
                  intros j'.
                  eapply def_funs_FV_inv.
                  eapply def_closures_FV_inv; [ | | | | | eassumption ].
                  eapply well_formed_antimon; [| eassumption ].
                  eapply reach'_set_monotonic. eapply env_locs_monotonic.
                  unfold FV...
                  eapply Included_trans; [| eassumption ].
                  eapply env_locs_monotonic. unfold FV...
                  (* well_formed (reach' H1' (env_locs (M.set Γ' (Loc lenv) rho2') Scope)) H1' *)
                  admit.
                  (* env_locs (M.set Γ' (Loc lenv) rho2') Scope \subset dom H1' *)
                  admit.
                  (* (H1, rho1) ⋞ ^ (Scope; ?k; j'; ?GI; ?GP; ?b; ?d) (H1', M.set Γ' (Loc lenv) rho2') *)
                  admit.

                  intros Hc; eapply Hnin. normalize_bound_var. left.
                  eapply name_in_fundefs_bound_var_fundefs.
                  eapply closure_conversion_fundefs_Same_set; eassumption.
                + eapply Hun; eauto.
                + intros Hc. eapply Hnin. normalize_bound_var. left.
                  eapply name_in_fundefs_bound_var_fundefs. eassumption.
                + intros Hc.  eapply H7. now left.
                + eapply injective_subdomain_antimon. eassumption.
                  eassumption.
                + eapply Disjoint_Included; [| | now apply Him ].
                  eapply image'_monotonic. eassumption.
                  eapply image_monotonic. eassumption.
                + (* process right ctx 3 : make closures *)
                  { eapply cc_approx_exp_right_ctx_compat; [ | | | | | | | ]. 
                    - admit. (* inv *)
                    - admit. (* inv *)
                  
                    - (* well-formed H11 *) 
                      eapply well_formed_antimon; [| eapply well_formed_reach_alloc_def_funs ];
                      [| now apply Hwf1 | | | eassumption ].
                      + eapply reach'_set_monotonic. eapply env_locs_monotonic. 
                        eapply Included_trans;
                          [| eapply Included_Union_compat; [ eassumption | reflexivity ]].
                        normalize_occurs_free. rewrite <- Union_assoc.
                        eapply Included_Union_preserv_r.
                        rewrite <- Union_Setminus; tci...
                      + eassumption.
                      + eapply Included_trans.
                        eapply Included_trans; [| eapply restrict_env_env_locs ].
                        eapply env_locs_monotonic. now eauto with Ensembles_DB.
                        eapply restrict_env_correct. now eapply fundefs_fv_correct.
                        eapply Included_trans; [| eapply reach'_extensive ].
                        eapply env_locs_monotonic.
                        eapply Included_trans; [| eassumption ].
                        normalize_occurs_free...
                    - (* well_formed H1' *)
                      eapply well_formed_antimon.
                      * eapply reach'_set_monotonic.
                        eapply def_funs_env_loc.
                      * eapply well_formed_antimon;
                        [| eapply well_formed_reach_alloc with (S := FromList FVs'' :|: FV_cc Scope Γ) ].
                        eapply reach'_set_monotonic.
                        eapply env_locs_monotonic.
                        (* lemmas for FV of contexts *) admit.
                        
                        eapply project_vars_well_formed'. eassumption. eassumption.
                        eapply Disjoint_Included_r; [ | eassumption ].
                        unfold FV_cc... eassumption. eassumption.
                        
                        eapply project_vars_env_locs'. eassumption. eassumption.
                        eapply Disjoint_Included_r; [ | eassumption ].
                        unfold FV_cc... eassumption. eassumption.
                        
                        eassumption.
                        
                        simpl.
                        rewrite env_locs_Union, reach'_Union.
                        eapply Included_Union_preserv_l.
                        rewrite env_locs_FromList; [| eassumption ].
                        eapply reach'_extensive.
                        
                    - eapply Included_trans;
                      [| eapply def_closures_env_locs_in_dom; eassumption ].
                      eapply env_locs_monotonic; eauto.
                      eapply Included_trans;
                        [| eapply Included_Union_compat; [ eassumption | reflexivity ] ].
                      normalize_occurs_free.
                      rewrite <- Union_assoc. eapply Included_Union_preserv_r.
                      rewrite Union_commut. rewrite Union_Setminus_Included.
                      now eauto with Ensembles_DB.
                      tci.
                      reflexivity.
                    - eapply Included_trans. eapply def_funs_env_loc.
                      eapply Included_trans. eapply env_locs_set_Inlcuded'.
                      rewrite HL.alloc_dom; try eassumption.
                      eapply Included_Union_compat. reflexivity.
                      eapply Included_trans; [| eassumption ].
                      eapply env_locs_monotonic.
                      (* lemmas about FV of contexts *) admit.
                    - eassumption.
                    - (*  IH *) 
                      eapply IHk with (Scope := (name_in_fundefs f2 :|: Scope));
                      [ | | | | | | | | | | | | | | eassumption ].
                      + (* XXX add assumption in compat *)
                        admit. (* simpl in *. omega. *)
                      + tci.
                      + eassumption.
                      + eassumption.
                      + eassumption.
                      + admit. (* ? *)
                      + eassumption.
                      + (* well-formed H11 *) 
                        admit. (* already proved *)
                      + (* env_locs rc1 *) admit. (* already proved *)
                      + eapply make_closures_well_formed. eassumption. eassumption.
                        unfold FV_cc... (* ???? *) admit.
                        eapply Included_trans. eapply def_funs_env_loc.
                        eapply Included_trans. eapply env_locs_set_Inlcuded'.
                        rewrite HL.alloc_dom; eauto.
                        eapply Included_Union_compat. reflexivity.
                        (* easy + set lemmas *) admit. 
                        (* well_formed H1' *) admit.
                      + eapply make_closures_env_locs; [ eassumption | eassumption | | | | ].
                        unfold FV_cc... (* ??? *) admit.
                        admit. admit.
                      + intros Hc. eapply Hnin.
                        normalize_bound_var. now right.
                      + admit. (* binding in map Funs - easy lemma *)
                      + intros x Hin. eapply Hun. now constructor. } } }      
    - (* case Eapp *)
      inv Hcc.
      
      edestruct (binding_in_map_getlist _ rho1 (v :: l) Hbind) as [vl Hgetl].
      eapply Included_trans; [| eassumption ].
      rewrite FromList_cons. normalize_occurs_free...
      
      edestruct project_vars_ctx_to_heap_env as [H2' [rho2' [m Hct]]]; try eassumption.
      specialize (HFVs 0); eapply FV_inv_weak_in_FV_inv; eassumption.

      intros j.
      (* process right ctx *)
      eapply cc_approx_exp_right_ctx_compat;
        [ | | | | | | eassumption | ].
      
      eapply PostCtxCompat_vars_r. eassumption.
      
      eapply PreCtxCompat_vars_r. eassumption.
      
      eapply well_formed_antimon. eapply reach'_set_monotonic. now eapply env_locs_monotonic; eauto.
      eassumption.
      
      eapply well_formed_antimon. eapply reach'_set_monotonic. now eapply env_locs_monotonic; eauto.
      eassumption.
      
      eapply Included_trans; [| eassumption ]. now eapply env_locs_monotonic; eauto.
      eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic; eauto.
      simpl in Hgetl. destruct (M.get v rho1) eqn:Hgetv; try congruence. 
      destruct (getlist l rho1) eqn:Hgetl1; try congruence. inv Hgetl.
      
      assert (Hwf2' := Hwf2).
      assert (Hlocs2' := Hlocs2). 
      eapply project_vars_well_formed' in Hwf2; try eassumption;
      [| eapply Disjoint_Included_r; try eassumption; unfold FV_cc; now eauto with Ensembles_DB ].
      eapply project_vars_env_locs' in Hlocs2; try eassumption;
      [| eapply Disjoint_Included_r; try eassumption; unfold FV_cc; now eauto with Ensembles_DB ].
      
      edestruct project_vars_correct as (Hd' & Henv' & HFVs' & Hvars);
        try eassumption.
      eapply binding_in_map_antimon; [| eassumption ]...

      specialize (Hvars j). inv Hvars. 
      eapply cc_approx_exp_app_compat; [ | | | | | | | | | | | | eassumption | eassumption ].
      + admit. (* XX change def *)
      + admit. (* XX change def *)        
      + eapply PostAppCompat. constructor; eassumption.
        eapply le_trans. eapply project_vars_cost. eassumption. simpl. omega.
        intros Hc.
        eapply project_vars_not_In_free_set. eassumption.
        eapply Disjoint_Included_r; [| eassumption ]. unfold FV_cc...
        constructor. eassumption. rewrite FromList_cons. right. eassumption.
        intros Hc.
        eapply project_vars_not_In_free_set. eassumption.
        eapply Disjoint_Included_r; [| eassumption ]. unfold FV_cc...
        constructor; [| rewrite FromList_cons; right; eassumption ].
        eassumption.
      + eapply PostBase.
        eapply le_trans.
        eapply project_vars_cost. eassumption. simpl. omega.
      + eapply PostGC.
      + eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eassumption. 
      + eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        unfold AppClo. repeat normalize_occurs_free. rewrite !FromList_cons.
        eapply Union_Included. now eauto with Ensembles_DB.
        rewrite !Setminus_Union_distr. eapply Union_Included. now eauto with Ensembles_DB.
        eapply Union_Included. rewrite Setminus_Same_set_Empty_set. now eauto with Ensembles_DB.
        now eauto with Ensembles_DB.
      + eapply Included_trans; [| eassumption ].
        eapply env_locs_monotonic. eassumption.
      + eapply Included_trans; [| eassumption ].
        eapply env_locs_monotonic.
        unfold AppClo. repeat normalize_occurs_free. rewrite !FromList_cons.
        eapply Union_Included. now eauto with Ensembles_DB.
        rewrite !Setminus_Union_distr. eapply Union_Included. now eauto with Ensembles_DB.
        eapply Union_Included. rewrite Setminus_Same_set_Empty_set. now eauto with Ensembles_DB.
        now eauto with Ensembles_DB.
      + intros Hc. eapply Hd'. rewrite FromList_cons. split; eauto.
      + intros Hc. eapply Hd'. rewrite FromList_cons. split; eauto.
      + intros Hc; subst; eauto.
    - (* case Eprim *)
      intros ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? Hstep. inv Hstep. simpl in Hcost. omega. 
    - (* case Ehalt *)
      inv Hcc.y
      admit.
  