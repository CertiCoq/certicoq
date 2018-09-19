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

  Lemma Fun_inv_setlist_r k j GI GP b rho1 H1 rho2 rho2' H2 Scope Funs fenv FVs xs vs :
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs ->
    Disjoint _ (FromList xs) (Funs \\ Scope) ->
    Disjoint _ (FromList xs) (image fenv (Funs \\ Scope)) ->
    setlist xs vs rho2 = Some rho2' ->
    Fun_inv k j GI GP b rho1 H1 rho2' H2 Scope Funs fenv FVs.
  Proof.
    intros Hfun Hnin1 Hnin2 Hset x Hnin Hin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                      & Hget2 & Hget3 & Hget4 & Henv & Heq).
    eassumption. eassumption.
    destruct Henv as [Hbeq Henv]. subst.
    
    do 7 eexists. repeat split; try eassumption.
    erewrite <- setlist_not_In; eauto.
    intros Hc. eapply Hnin1. constructor; eauto. now constructor; eauto.
    erewrite <- setlist_not_In; eauto.    
    intros Hc. eapply Hnin2. constructor; eauto.
    eexists; split; eauto. now constructor; eauto.
  Qed.

  Lemma Fun_inv_setlist_l k j GI GP b rho1 rho1' H1 rho2 H2 Scope Funs fenv FVs xs vs :
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs ->
    Disjoint _ (FromList xs) (Funs \\ Scope) ->
    Disjoint _ (reach' H1 (Union_list (map val_loc vs))) (env_locs rho1 (Funs \\ Scope)) ->
    setlist xs vs rho1 = Some rho1' ->
    Fun_inv k j GI GP b rho1' H1 rho2 H2 Scope Funs fenv FVs.
  Proof.
    intros Hfun Hnin1 Hnin2 Hset x Hnin Hin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                      & Hget2 & Hget3 & Hget4 & Henv & Heq).
    eassumption. eassumption.
    destruct Henv as [Hbeq Henv]. subst.
    
    do 7 eexists. repeat split; try eassumption.
    erewrite <- setlist_not_In; eauto.
    intros Hc. eapply Hnin1. constructor; eauto. now constructor; eauto.
    rewrite reach'_Union in *. intros Hc. eapply Hsub.
    inv Hc; [| now right ].
    eapply reach'_set_monotonic in H;
      [| eapply env_locs_monotonic; eapply Included_Union_preserv_l; reflexivity ].
    eapply reach'_set_monotonic in H; [| eapply env_locs_setlist_Included; eassumption ]. 
    rewrite reach'_Union in H. inv H. now left.
    exfalso. eapply Hnin2. constructor; eauto.
    eexists; split; eauto. now constructor; eauto.
    rewrite Hget1. reflexivity. 
  Qed.

  Lemma Fun_inv_suffle_setlist k j GI GP b rho1 H1 rho2 rho2' rho2'' H2 Scope Funs fenv FVs
        x v xs vs:
    Fun_inv k j GI GP b rho1 H1 (M.set x v rho2') H2 Scope Funs fenv FVs ->
    setlist xs vs rho2 = Some rho2' ->
    setlist xs vs (M.set x v rho2) = Some rho2'' ->
    ~ x \in FromList xs ->
    Fun_inv k j GI GP b rho1 H1 rho2'' H2 Scope Funs fenv FVs.
  Proof. 
    intros Hfun Hset1 Hset2 Hninx y Hnin Hin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    eassumption. eassumption.
    destruct Henv as [Hbeq Henv]. subst.
    
    do 7 eexists. repeat split; try eassumption.
    - destruct (var_dec x y); subst.
      + rewrite M.gss in *.  inv Hget2.
        erewrite <- setlist_not_In; eauto.
        rewrite M.gss. reflexivity.
      + edestruct (set_setlist_permut rho2 rho2') as [rho2''' [Hset3 Heqr]].
        eassumption. eassumption. rewrite Hset2 in Hset3. inv Hset3.
        rewrite <- Heqr. eassumption.
    - destruct (var_dec x (fenv y)); subst.
      + rewrite M.gss in *. inv Hget4.
        erewrite <- setlist_not_In; eauto.
        rewrite M.gss. reflexivity.
      + edestruct (set_setlist_permut rho2 rho2') as [rho2''' [Hset3 Heqr]].
        eassumption. eassumption. rewrite Hset2 in Hset3. inv Hset3.
        rewrite <- Heqr. eassumption.
  Qed.

  Lemma Fun_inv_suffle_def_funs k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs
        x v B1 B2:
    Fun_inv k j GI GP b rho1 H1 (M.set x v (def_funs B1 B2 rho2)) H2 Scope Funs fenv FVs ->
    ~ x \in (name_in_fundefs B1) ->
    Fun_inv k j GI GP b rho1 H1 (def_funs B1 B2 (M.set x v rho2)) H2 Scope Funs fenv FVs.
  Proof.
    intros Hfun Hninx y Hnin Hin.
    edestruct Hfun as (l1 & lenv & B1' & g1 & rhoc & B2' & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    eassumption. eassumption.
    destruct Henv as [Hbeq Henv]. subst.
    
    do 7 eexists. repeat split; try eassumption.
    - destruct (var_dec y x); subst.
      + rewrite M.gss in *. inv Hget2.
        erewrite def_funs_neq; [| reflexivity | eassumption ].
        rewrite M.gss. reflexivity.
      + rewrite M.gso in Hget2; [| eassumption ].
        destruct (@Dec _ (name_in_fundefs B1) _ y).
        * erewrite def_funs_eq in Hget2; [| reflexivity | eassumption ].
          inv Hget2.
          erewrite def_funs_eq; [| reflexivity | eassumption ].
          reflexivity.
        * erewrite def_funs_neq in Hget2; [| reflexivity | eassumption ].
          erewrite def_funs_neq; [| reflexivity | eassumption ].
          rewrite M.gso; eassumption.
    - destruct (var_dec (fenv y) x); subst.
      + rewrite M.gss in *. inv Hget4.
        erewrite def_funs_neq; [| reflexivity | eassumption ].
        rewrite M.gss. reflexivity.
      + rewrite M.gso in Hget4; [| eassumption ].
        destruct (@Dec _ (name_in_fundefs B1) _ (fenv y)).
        * erewrite def_funs_eq in Hget4; [| reflexivity |  eassumption ].
          inv Hget4.
        * erewrite def_funs_neq in Hget4; [| reflexivity | eassumption ].
          erewrite def_funs_neq; [| reflexivity | eassumption ].
          rewrite M.gso; eassumption.
  Qed.

  Lemma Fun_inv_suffle_setlist_l k j GI GP b rho1 H1 rho2 rho2' rho2'' H2 Scope Funs fenv FVs
        x v xs vs:
    Fun_inv k j GI GP b rho1 H1 rho2'' H2 Scope Funs fenv FVs ->
    setlist xs vs rho2 = Some rho2' ->
    setlist xs vs (M.set x v rho2) = Some rho2'' ->
    ~ x \in FromList xs ->
            Fun_inv k j GI GP b rho1 H1 (M.set x v rho2') H2 Scope Funs fenv FVs.
  Proof. 
    intros Hfun Hset1 Hset2 Hninx y Hnin Hin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    eassumption. eassumption.
    destruct Henv as [Hbeq Henv]. subst.
    
    do 7 eexists. repeat split; try eassumption.
    - destruct (var_dec x y); subst.
      + rewrite M.gss in *.  inv Hget2.
        erewrite <- setlist_not_In; eauto.
        rewrite M.gss. reflexivity.
      + edestruct (set_setlist_permut rho2 rho2') as [rho2''' [Hset3 Heqr]].
        eassumption. eassumption. rewrite Hset2 in Hset3. inv Hset3.
        rewrite Heqr. eassumption.
    - destruct (var_dec x (fenv y)); subst.
      + rewrite M.gss in *. inv Hget4.
        erewrite <- setlist_not_In; eauto.
        rewrite M.gss. reflexivity.
      + edestruct (set_setlist_permut rho2 rho2') as [rho2''' [Hset3 Heqr]].
        eassumption. eassumption. rewrite Hset2 in Hset3. inv Hset3.
        rewrite Heqr. eassumption.
  Qed.

  Lemma Fun_inv_suffle_def_funs_l k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs
        x v B1 B2:
    Fun_inv k j GI GP b rho1 H1 (def_funs B1 B2 (M.set x v rho2)) H2 Scope Funs fenv FVs ->
    ~ x \in (name_in_fundefs B1) ->
    Fun_inv k j GI GP b rho1 H1 (M.set x v (def_funs B1 B2 rho2)) H2 Scope Funs fenv FVs.
  Proof.
    intros Hfun Hninx y Hnin Hin.
    edestruct Hfun as (l1 & lenv & B1' & g1 & rhoc & B2' & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    eassumption. eassumption.
    destruct Henv as [Hbeq Henv]. subst.
    
    do 7 eexists. repeat split; try eassumption.
    - destruct (var_dec y x); subst.
      + rewrite M.gss in *. inv Hget2.
        erewrite def_funs_neq; [| reflexivity | eassumption ].
        rewrite M.gss. reflexivity.
      + rewrite M.gso; [| eassumption ].
        destruct (@Dec _ (name_in_fundefs B1) _ y).
        * erewrite def_funs_eq in Hget2; [| reflexivity | eassumption ].
          inv Hget2.
          erewrite def_funs_eq; [| reflexivity | eassumption ].
          reflexivity.
        * erewrite def_funs_neq in Hget2; [| reflexivity | eassumption ].
          erewrite def_funs_neq; [| reflexivity | eassumption ].
          rewrite M.gso in Hget2; eassumption.
    - destruct (var_dec (fenv y) x); subst.
      + rewrite M.gss in *. inv Hget4.
        erewrite def_funs_neq; [| reflexivity | eassumption ].
        rewrite M.gss. reflexivity.
      + rewrite M.gso; [| eassumption ].
        destruct (@Dec _ (name_in_fundefs B1) _ (fenv y)).
        * erewrite def_funs_eq in Hget4; [| reflexivity |  eassumption ].
          inv Hget4.
        * erewrite def_funs_neq in Hget4; [| reflexivity | eassumption ].
          erewrite def_funs_neq; [| reflexivity | eassumption ].
          rewrite M.gso in Hget4; eassumption.
  Qed.

  Lemma Fun_inv_Scope_Disjoint k j GI GP b rho1 H1 rho2 H2 Scope Scope' Funs fenv FVs :
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs ->
    Disjoint _ (env_locs rho1 Funs) (reach' H1 (env_locs rho1 Scope')) ->
    Fun_inv k j GI GP b rho1 H1 rho2 H2 (Scope' :|: Scope) Funs fenv FVs.
  Proof.
    intros Hfun Hdis1 x Hnin Hin.
    edestruct Hfun as (l1 & lenv & B1' & g1 & rhoc & B2' & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    intros Hc. eapply Hnin. right. eassumption. eassumption.
    destruct Henv as [Hbeq Henv]. subst.

    do 7 eexists. repeat split; try eassumption.


    intros Hc. eapply Hsub. rewrite reach'_Union in *.
    inv Hc; [| now right ].
    left.
    eapply reach'_set_monotonic in H; [| eapply env_locs_monotonic;
                                         eapply Included_Setminus_compat;
                                         [ eapply FV_Union1 | reflexivity ] ].
    rewrite Setminus_Union_distr in H.
    rewrite env_locs_Union, reach'_Union in H.
    inv H; [| eassumption ].
    exfalso. eapply Hdis1. constructor.
    eexists; split; eauto. rewrite Hget1. reflexivity.
    eapply reach'_set_monotonic; [| eassumption ].
    eapply env_locs_monotonic. now eauto with Ensembles_DB.
  Qed.

  Lemma def_closures_FV_inv Scope {Hc : ToMSet Scope} Funs FVs Γ k j GIP GP b B1 B2 envc c rho1 H1 rho1' H1' rho2 H2 :
    (forall j, FV_inv k j GIP GP b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    def_closures B1 B2 rho1 H1 envc = (H1', rho1') ->
    FV_inv k j GIP GP b rho1' H1' rho2 H2 c Scope (name_in_fundefs B1 :|: Funs) Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    revert H1 rho1 H1' rho1' j.
    induction B1; intros H1 rho1 H1' rho1' j Hfv Hdef.
    - simpl in Hdef.
      destruct (def_closures B1 B2 rho1 H1) as (H1'', rho1'') eqn:Hdef'.
      destruct (alloc (Clos _ _) H1'') as [la H1a] eqn:Hal.
      inv Hdef. 
      simpl. eapply Proper_FV_inv_Funs. rewrite <- Union_assoc. reflexivity. reflexivity. reflexivity.
      eapply FV_inv_FV_eq with (Scope := v |: Scope) (Funs := name_in_fundefs B1 :|: Funs). 
      tci. tci.
      eapply FV_inv_set_not_in_FVs_l.
      eapply FV_inv_heap_mon; [ | | ].
      * eapply HL.alloc_subheap. eassumption.
      * eapply HL.subheap_refl.
      * intros j'.
        eapply IHB1 in Hdef'.
        eassumption.
        eassumption.
      * now eauto with Ensembles_DB. 
    - inv Hdef. simpl.
      eapply Proper_FV_inv_Funs. rewrite Union_Empty_set_neut_l. reflexivity. 
      reflexivity. reflexivity. eauto.
  Qed.

  Lemma res_equiv_locs_eq (S : Ensemble var) (b1 b2 : loc -> loc) (H1 H2 : heap block)
        (l1 l2 : loc):
    (Loc l1, H1) ≈_( b1, b2) (Loc l2, H2) ->
    b1 l1 = b2 l2. 
  Proof.
    intros Heq. rewrite res_equiv_eq in Heq.
    destruct Heq as [Heq _]. eassumption.
  Qed. 
    
  Lemma setlist_FV_inv Scope {Hc : ToMSet Scope} Funs FVs Γ k j GIP GP b c rho1 H1 rho1' rho2 H2
        xs vs :
    FV_inv k j GIP GP b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    setlist xs vs rho1 = Some rho1' ->
    FV_inv k j GIP GP b rho1' H1 rho2 H2 c (FromList xs :|: Scope) Funs Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    revert vs H1 rho1 rho1' j.
    induction xs; intros vs H1 rho1 rho1' j Hfv Hdef.
    - destruct vs; try inv Hdef.
      eapply Proper_FV_inv_Scope. normalize_sets. rewrite Union_Empty_set_neut_l. reflexivity. 
      reflexivity. reflexivity. reflexivity. eauto.
    - simpl in Hdef.
      eapply Proper_FV_inv_Scope. normalize_sets. rewrite <- Union_assoc. reflexivity.
      reflexivity. reflexivity. reflexivity.
      destruct vs; try congruence. 
      destruct (setlist xs vs rho1) as [rho1''| ] eqn:Hset; try congruence.
      inv Hdef. 
      eapply FV_inv_set_not_in_FVs_l.
      eapply IHxs. eassumption. eassumption.
  Qed.

  Lemma FV_inv_rho_swap Scope {Hc : ToMSet Scope} Funs FVs Γ Γ' k j GIP GP b c rho1 H1 rho2 rho2' H2 :
    FV_inv k j GIP GP b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    M.get Γ rho2 = M.get Γ' rho2' ->
    FV_inv k j GIP GP b rho1 H1 rho2' H2 c Scope Funs Γ' FVs.
  Proof.
    intros Hfvs Heq. 
    destruct Hfvs as (Hwf & Hkey & vs & lenv'' & Hgetlenv & Hget' & HallP).
    split; [| split ]; try eassumption.
    - rewrite env_locs_Singleton in *; eauto.
      rewrite <- Heq. eassumption.
    - do 2 eexists. split.
      rewrite <- Heq. eassumption.
      split; eassumption.
  Qed.

  Lemma FV_inv_heap_env_equiv Scope Funs FVs Γ k j GIP GP b c rho1 H1 rho1' H1' rho2 H2 rho2' H2' 
        (β1 β2 : Inj) :
    FV_inv k j GIP GP b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->

    Full_set _ |- (H1, rho1) ⩪_(id, β1) (H1', rho1') ->
    injective_subdomain (reach' H1' (env_locs rho1' (Full_set _))) β1 -> 
    [set Γ] |- (H2, rho2) ⩪_(β2, id) (H2', rho2') ->
    injective_subdomain (reach' H2 (env_locs rho2 (Full_set _))) β2 ->

    FV_inv k j GIP GP (β2 ∘ b ∘ β1) rho1' H1' rho2' H2' c Scope Funs Γ FVs.
  Proof.
    intros Hfvs Heq1 Hinj1 Heq2 Hinj2. 
    destruct Hfvs as (Hwf & Hkey & vs & lenv'' & Hgetlenv & Hget' & HallP).
    split; [| split ]; try eassumption.
    - eapply well_formed_respects_heap_env_equiv. eassumption.
      eapply heap_env_equiv_antimon. eassumption. reflexivity.
    - rewrite <- heap_env_equiv_key_set. eassumption. eassumption.
    - edestruct heap_env_equiv_env_get as [lenv' [Hget Hres]]. eassumption.
      eapply heap_env_equiv_antimon. eassumption. reflexivity. reflexivity.
      rewrite res_equiv_eq in *. destruct lenv'; try contradiction. 
      rewrite <- res_equiv_eq in *.
      edestruct res_equiv_get_Constr as [vs' [Hhget Hres']]; eauto.
      
      do 2 eexists. split; eauto. split; eauto. 
      assert (Hinj2' : injective_subdomain (reach' H2 (Union_list (map val_loc vs))) β2).
      { eapply injective_subdomain_antimon. eassumption. 
        rewrite (reach'_idempotent H2 (env_locs _ _)). 
        eapply reach'_set_monotonic. eapply Included_trans; [| eapply Included_post_reach' ].
        eapply Included_trans; [| eapply post_set_monotonic; eapply get_In_env_locs; eauto; now constructor ].
        simpl. rewrite post_Singleton; eauto. reflexivity. }

      clear Hhget. 
      revert HallP vs' Hres' Heq1 Hinj1 Hinj2'; clear.
      intros Hall1.
      induction Hall1; intros vs' Hall2 Heq1 Hinj1 Hinj2.
      + inv Hall2.
        now constructor. 
      + inv Hall2. eapply IHHall1 in H6; eauto. constructor; [| eassumption ].
        intros Hnin.
        edestruct H as [v1 [Hgetx1 Hres1]]. eassumption.        
        edestruct heap_env_equiv_env_get as [lenv' [Hget Hres]]. eassumption.
        eassumption. now constructor. 
        eexists; split; eauto. 
        eapply cc_approx_val_res_eq.

        eassumption. eassumption.
        eapply injective_subdomain_antimon. eassumption.
        eapply reach'_set_monotonic. eapply get_In_env_locs. now constructor.
        eassumption.
        
        eassumption.
        eapply injective_subdomain_antimon. eassumption.
        eapply reach'_set_monotonic. simpl. now eauto with Ensembles_DB.

        eapply injective_subdomain_antimon. eassumption.
        eapply reach'_set_monotonic. simpl. now eauto with Ensembles_DB.
  Qed.     

  Lemma FV_inv_heap_f_eq_subdomain Scope Funs FVs Γ k j GIP GP b c rho1 H1 rho2 H2 b':
    FV_inv k j GIP GP b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (FromList FVs))) b b' ->
    FV_inv k j GIP GP b' rho1 H1 rho2 H2 c Scope Funs Γ FVs.
  Proof. 
    intros Hfvs Heq1. 
    destruct Hfvs as (Hwf & Hkey & vs & lenv'' & Hgetlenv & Hget' & HallP).
    split; [| split ]; try eassumption.
    do 2 eexists. split; eauto. split; eauto.
    revert HallP Heq1; clear.
    intros Hall1. induction Hall1; intros Heq.
    + now constructor.
    + constructor; eauto.
      intros Hc.
      edestruct H as [v1 [Hgetx1 Hcc]]. eassumption.
      eexists; split; eauto.
      eapply cc_approx_val_rename_ext. eassumption.

      eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].
      normalize_sets. rewrite env_locs_Union, reach'_Union. eapply Included_Union_preserv_l.
      eapply reach'_set_monotonic. eapply get_In_env_locs; try eassumption. reflexivity.

      eapply IHHall1. 
      eapply f_eq_subdomain_antimon; [| eassumption ].
      normalize_sets. rewrite env_locs_Union, reach'_Union. eapply Included_Union_preserv_r.
      reflexivity.
  Qed. 

  Lemma binding_in_map_def_closures (S : Ensemble M.elt) (rho1 rho1' : env) H1 H1' B1 B1' v :
    binding_in_map S rho1 ->
    def_closures B1 B1' rho1 H1 v = (H1', rho1') ->
    binding_in_map (name_in_fundefs B1 :|: S) rho1'.
  Proof. 
    revert H1' rho1'. induction B1; intros H2 rho2 Hbin Hclo.
    - simpl in *.
      destruct (def_closures B1 B1' rho1 H1 v) as [H' rho'] eqn:Hd.
      destruct (alloc (Clos (FunPtr B1' v0) v) H')as [l' H''] eqn:Ha. 
      inv Hclo.
      rewrite <- Union_assoc. rewrite Union_commut. eapply binding_in_map_set.
      eauto.
    - inv Hclo. simpl. eapply binding_in_map_antimon; [| eassumption ].
      eauto with Ensembles_DB.
  Qed.

  Lemma env_locs_setlist_Disjoint ys ls rho rho' S :
      setlist ys ls rho = Some rho'  ->
      Disjoint _ S (FromList ys) ->
      env_locs rho S <--> env_locs rho' S. 
  Proof with now eauto with Ensembles_DB.
    revert rho' S ls; induction ys; intros rho' S ls Hset Hd.
    - destruct ls; inv Hset. reflexivity.
    - destruct ls; try discriminate. simpl in *.
      destruct (setlist ys ls rho) eqn:Hset'; try discriminate.
      inv Hset. rewrite env_locs_set_not_In. eapply IHys.
      eassumption.
      eapply Disjoint_Included_r; [| eassumption ].
      normalize_sets...
      intros Hc; eapply Hd. constructor; eauto.
      normalize_sets. now left. 
  Qed.

  Lemma env_locs_setlist_In ys ls rho rho' :
      setlist ys ls rho = Some rho'  ->
      env_locs rho' (FromList ys) \subset Union_list (map val_loc ls). 
  Proof with now eauto with Ensembles_DB.
    revert rho' ls; induction ys; intros rho' ls Hset.
    - destruct ls; inv Hset. normalize_sets. rewrite env_locs_Empty_set...
    - destruct ls; try discriminate. simpl in *. 
      destruct (setlist ys ls rho) eqn:Hset'; try discriminate.
      inv Hset. normalize_sets. rewrite env_locs_Union.
      rewrite env_locs_Singleton; [| rewrite M.gss; reflexivity ].
      eapply Union_Included. now eapply Included_Union_preserv_l. 
      eapply Included_trans. eapply env_locs_set_Inlcuded'. eapply Included_Union_compat.
      reflexivity. eapply Included_trans; [| eapply IHys; eassumption ].
      eapply env_locs_monotonic...
  Qed.

      
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
           (β : Inj) (c : cTag) (Γ : var),
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
             (e1, rho1, H1) ⪯ ^ (m; j; Pre Funs; PreG; Post 0; PostG) (C |[ e2 ]|, rho2, H2)) :
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
           Hgetenv1 Hgetenv2 Hincl Hccf1 Hclo j.

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
            
            
            edestruct (setlist_length rhoc1 (def_funs B2 B2 (M.empty value))
                                      rhoc2 xs1 vs1 vs2) 
              as [rho2' Hset2]; [ eassumption (* add length vs1 = lngth v2 *)
                                | now apply Hset | ].
            { do 3 eexists. split; [| split ]. 
              - eassumption.
              - simpl. rewrite Hset2. reflexivity.
              - intros i Hlt b' Hall Hfeq. split.
                + admit. (* size after GC
                            TODO remove live from log. rel. add size reachable?
                          *)
                + assert (Hpre : PreG (name_in_fundefs B1) = Pre (name_in_fundefs B1))
                    by reflexivity.
                  assert (Hpost : PostG (FromList xs1) (name_in_fundefs B1) = Post 0)
                    by admit.
                  rewrite Hpre, Hpost.
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

                  assert (Ha : key_set rhoc' <--> key_set rho1c).
                  { rewrite res_equiv_eq in Heq1. destruct Heq1 as [Hbeq1 Hres]. 

                    unfold id in *; subst.
                    eapply def_funs_subheap in Hgetenv1; eauto.
                    rewrite Hgetenv1, Hget in Hres. simpl in Hres.
                    eapply heap_env_equiv_key_set. symmetry. eassumption. }
                  
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
                  
                  eapply IHexp with (Scope := (FromList xs1)) (Funs := name_in_fundefs B1)
                                                              (fenv := extend_fundefs' id B1 Γ'')
                                                              (β := b');
                    [ | | | | | | | | | eassumption ].
                  * eassumption.
                  * tci.
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
                                              eapply find_def_correct; eassumption ]... } }
        
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
            eapply def_closures_env_locs; try eapply Hclo 
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

  Admitted.

  Lemma FV_inv_env_constr k j PG QG b rho1 H1 rho2 H2 c FVs Γ lenv vs1 vs2 :
    key_set rho1 <--> FromList FVs ->
    M.get Γ rho2 = Some (Loc lenv) ->
    get lenv H2 = Some (Constr c vs2) ->
    getlist FVs rho1 = Some vs1 ->
    (forall j,  Forall2
             (fun v1 v2 : value =>
                Res (v1, H1) ≺ ^ (k; j; PG; QG; b) Res (v2, H2)) vs1 vs2) ->
    FV_inv k j PG QG b rho1 H1 rho2 H2 c (Empty_set _) (Empty_set _) Γ FVs. 
  Proof.
    intros Hkey Hget1 Hget2 Hgl Hall.
    split; [| split ].
    - rewrite env_locs_Singleton; [| eassumption ]. simpl.
      rewrite reach_unfold. eapply well_formed_Union.
      + intros x bl Hinx Hget. inv Hinx. repeat subst_exp. simpl.
        eapply Forall2_dom2. exact 0. eassumption. eassumption. (* XXX redundant params *)
        eapply Forall2_forall. tci. eassumption.
      + rewrite post_Singleton; [| eassumption ]. simpl. 
        eapply Forall2_reach2. eassumption. exact Some.  (* XXX redundant params *)
        eapply Forall2_forall. tci. eassumption.
    - rewrite Hkey. 
      + unfold FV. rewrite !Union_Empty_set_neut_l, !Setminus_Empty_set_neut_r, Union_Empty_set_neut_l. 
        reflexivity.
    - do 2 eexists. split; [| split ]; try eassumption.
      specialize (Hall j). revert Hgl Hall. clear.
      intros Hgl Hall. revert FVs Hgl.
      induction Hall; intros FVs Hgl.
      + destruct FVs as [| x FVs ]; try inv Hgl.
        now constructor.
        destruct (M.get x rho1) eqn:Hgetx; try congruence.
        destruct (getlist FVs rho1) eqn:Hgetlst; try congruence. 
      + destruct FVs as [| z FVs ]; try inv Hgl.
        destruct (M.get z rho1) eqn:Hgetx; try congruence.
        destruct (getlist FVs rho1) eqn:Hgetlst; try congruence. 
        inv H3. constructor; eauto.
  Qed.

  Lemma key_set_binding_in_map_alt (S : PS.t) (rho : env) :
    binding_in_map (FromSet S) rho ->
    key_set (restrict_env S rho) <--> FromSet S.
  Proof.
    intros Hbin.
    assert (HR : Restrict_env (FromSet S) rho (restrict_env S rho)). 
    { eapply restrict_env_correct. reflexivity. }
    split. 
    eapply key_set_Restrict_enc. eassumption.

    intros x Hin. edestruct Hbin as [v Hget1]. eassumption.
    destruct HR as [Hs1 Hr]. 
    unfold key_set, In. rewrite <- Hs1, Hget1; eauto.
  Qed.

  Lemma restrict_env_getlist S rho rho' xs vs :
    Restrict_env S rho rho' -> 
    getlist xs rho = Some vs -> 
    FromList xs \subset S ->
    getlist xs rho' = Some vs. 
  Proof with (now eauto with Ensembles_DB).
    revert vs. induction xs; intros vs HR Hget Hin.
    - inv Hget. reflexivity.
    - simpl in Hget.
      destruct (M.get a rho) eqn:Hgeta; try congruence.
      destruct (getlist xs rho) eqn:Hgetxs; try congruence.
      inv Hget. normalize_sets.
      assert (HR' := HR). 
      simpl. destruct HR as [Heq _].
      rewrite <- Heq, Hgeta; eauto.
      erewrite IHxs; eauto. eapply Included_trans; [| eassumption ]...
  Qed.

  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct (k : nat) (H1 H2 : heap block)
        (rho1 rho2 : env) (e1 e2 : exp) (C : exp_ctx)
        (Scope Funs : Ensemble var) {Hs : ToMSet Scope} {Hf : ToMSet Funs} (FVs : list var)
        fenv (β : Inj) (c : cTag) (Γ : var) :
    (* [Scope] invariant *)
    (forall j, (H1, rho1) ⋞ ^ (Scope ; k ; j ; PreG; PostG ; β) (H2, rho2)) ->
    (* Free variable invariant *)
    (forall j, FV_inv k j PreG PostG β rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    (* Functions in scope invariant *)
    (forall j, Fun_inv k j PreG PostG β rho1 H1 rho2 H2  Scope Funs fenv FVs) ->

    Disjoint _ (Γ |: image fenv (Funs \\ Scope)) (bound_var e1 :|: FV Scope Funs FVs) ->
    
    (* The free variables of e are defined in the environment *)
    binding_in_map (FV Scope Funs FVs) rho1 ->
    (* (* The blocks of functions have unique function names *) *)
    (* fundefs_names_unique e1 -> *)
    (* Freshness requirements *)
    unique_bindings e1 ->
    Disjoint _ (bound_var e1) (FV Scope Funs FVs) ->
    
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion ct Scope Funs fenv c Γ FVs e1 e2 C ->
    
    (forall j, (e1, rho1, H1) ⪯ ^ (k ; j ;
                              Pre Funs; PreG;
                              Post 0; PostG)
          (C |[ e2 ]|, rho2, H2)).
  Proof with now eauto with Ensembles_DB.
    revert H1 H2 rho1 rho2 e1 e2 C Scope Hs Funs Hf FVs fenv β c Γ.
    induction k as [k IHk] using lt_wf_rec1.  
    intros H1 H2 rho1 rho2 e1 e2 C Scope Hs Funs Hf FVs fenv β c Γ
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
    
    induction e1 using exp_ind'; try clear IHe1.
    Focus 5.

 {   (* case Efun *)
    inv Hcc. 

    assert (Hf' : ToMSet Funs').
    { eapply project_vars_ToMSet_Funs. eassumption. eassumption. }
    assert (Hs' : ToMSet Scope').
    { eapply (project_vars_ToMSet Scope Scope' Funs). eassumption. }

    assert (Hfveq : occurs_free (Econstr_c Γ' c' FVs' Hole_c |[ Efun B' (Ce |[ e' ]|) ]|) \subset
                                FV_cc Scope' Funs' fenv Γ). 
    { simpl. repeat normalize_occurs_free.
      assert (Hclof := H13). eapply Closure_conversion_occurs_free_fundefs_Included in H13.
      rewrite closure_conversion_fundefs_Same_set with (B2 := B') in H13; [| eassumption ].
      rewrite Setminus_Same_set_Empty_set in H13. eapply Included_Empty_set_l in H13.
      rewrite <- H13, Union_Empty_set_neut_l. eapply Closure_conversion_occurs_free_Included in H16. 
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
    
    (* process right ctx 1 : projec-t fvs *)
    eapply cc_approx_exp_right_ctx_compat; [ | | | | | | eassumption | ].
      
    + eapply PostCtxCompat_vars_r with (k := 3 * PS.cardinal (fundefs_fv f2));
      [| | | | eassumption | ]; try eassumption.
      rewrite <- plus_n_O. eapply le_trans. eapply project_vars_cost_eq'.
      eassumption. eapply mult_le_compat_l.
      rewrite PS.cardinal_spec. eapply Same_set_FromList_length. eassumption.
      rewrite <- FromSet_elements. rewrite <- H3, <- fundefs_fv_correct. reflexivity.
    + eapply (PreCtxCompat_vars_r Scope Scope' Funs Funs'); eassumption.
    + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
      eapply reach'_set_monotonic. now eapply env_locs_monotonic; eauto.
    + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
      eapply reach'_set_monotonic. now eapply env_locs_monotonic; eauto.
    + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
      eapply Included_trans. now eapply env_locs_monotonic; eauto.
      eapply reach'_extensive. 
    + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
      eapply Included_trans. now eapply env_locs_monotonic; eauto.
      eapply reach'_extensive.  
    + eapply cc_approx_exp_right_ctx_compat;
      [ | | | | | | econstructor; try eassumption; now constructor | ].
      * admit. (* bounds for right projection *)
      * admit. (* bounds *)
      * eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. now eapply env_locs_monotonic; eauto.
      * eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic... 
      * eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans. now eapply env_locs_monotonic; eauto.
        eapply reach'_extensive.
      * eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ].
        eapply env_locs_monotonic...
      * { eapply cc_approx_exp_fun_compat with (IIL1 := PreG (name_in_fundefs f2 :|: Funs') ). 
          - eapply PostFunsCompat. reflexivity.
          - eapply PreFunsCompat.
            inv Hunb. eapply unique_bindings_fundefs_unique_functions. 
            eassumption.
          - eapply PostBase. reflexivity.
          - eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
            eapply reach'_set_monotonic. eapply env_locs_monotonic...
          - eapply Included_trans; [| eapply env_locs_closed; eassumption ].
            eapply Included_trans; [| eapply reach'_extensive ].
            eapply env_locs_monotonic...
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

            eapply IHk with (Scope := Scope' \\ name_in_fundefs f2) (β :=  b' {el ~> lenv});
              [| | | | | | | | | eassumption (* CC *) ].
            + simpl in *. omega. 
            + tci.
            + intros j1.
              rewrite <- Setminus_Disjoint with (s2 := name_in_fundefs f2);
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
              intros Hc'. eapply H6. left. right.
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
              intros Hc. subst. eapply H6. right. right. reflexivity.
              rewrite <- closure_conversion_fundefs_Same_set; [| eassumption ].
              intros Hc. eapply Hdis. constructor. now left.
              normalize_bound_var. left. left.
              eapply name_in_fundefs_bound_var_fundefs. eassumption.
            + (* Fun_inv : IH fundefs *)
              eapply Closure_conversion_fundefs_correct with (b :=  b' {el ~> lenv}) (H1 := H1').
              * intros. eapply IHk; [| | | | | | | | | eassumption ]; try eassumption.
                omega.
              * tci.
              * tci.
              * rewrite <- project_vars_FV_eq; [| eassumption ].
                eapply reach'_closed. rewrite <- well_formed_reach_alloc_same. 
                eapply well_formed_alloc. eapply well_formed'_closed; eassumption. eassumption.
                subst. simpl. eapply Included_trans. eapply restrict_env_env_locs.
                eapply restrict_env_correct. reflexivity.
                rewrite <- (fundefs_fv_correct f2).
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
                
                admit. (* XXX fix *)

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
                intros Hc. eapply H6. left. right.
                rewrite project_vars_FV_eq; [| eassumption ]. now left; right.
                intros Hc. eapply H6. 
                rewrite project_vars_FV_eq; [| eassumption ]. right.
                left. right. eapply image_monotonic; [| eassumption ].
                eapply Included_Setminus_compat.
                eapply project_vars_Funs_l. eassumption.
                eapply project_vars_Scope_l. eassumption.
              * intros j1.  
                eapply FV_inv_env_constr with (rho1 := rhoc) (FVs := FVs'); subst.
                
                rewrite key_set_binding_in_map_alt; rewrite <- (fundefs_fv_correct f2).
                eassumption. eapply binding_in_map_antimon; [| eassumption ].
                eapply Included_trans; [| eassumption ].
                normalize_occurs_free...
                
                rewrite M.gss. reflexivity.
                
                erewrite gas. reflexivity. eassumption.

                eapply restrict_env_getlist. eapply restrict_env_correct. 
                reflexivity. eassumption. rewrite <- (fundefs_fv_correct f2). now eapply H3.

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

                eapply Disjoint_Singleton_l. intros Hc. eapply H6. left.
                normalize_bound_var. left. left.
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
                eapply restrict_env_correct. reflexivity. rewrite <- (fundefs_fv_correct f2).
                rewrite H3.  eapply env_locs_monotonic. unfold FV. rewrite !Setminus_Union_distr.
                do 2 eapply Included_Union_preserv_l. eapply Included_Setminus.
                eapply Disjoint_Setminus_r. eapply project_vars_In; eassumption.               
                eapply project_vars_In. eassumption.
              * eassumption.
              * eassumption.
            + eapply Disjoint_Included with (s2 := bound_var (Efun f2 e1) :|: FV Scope Funs FVs).
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
                intros Hc. eapply H6. left. eassumption.
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
              eapply Disjoint_Included_l; [ | eapply Hfresh ]. normalize_bound_var... } }

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
      with (IL2 := (Post (cost_ctx_full C))); [ | | | | | | now eapply Hct | ].
      
      + eapply PostCtxCompat_vars_r; [| | | | eassumption |  ]; try eassumption.
        omega. 
      + eapply (PreCtxCompat_vars_r Scope Scope' Funs Funs').
        eassumption.
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        
      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ]. 
        eapply env_locs_monotonic. eassumption.

      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ]. 
        eapply env_locs_monotonic. eassumption.

      + edestruct project_vars_correct with (Scope := Scope) as
            (b' & Henv' & Hfun' & HFVs' & Hinj');
        try eassumption.
        eapply Disjoint_Included; [ | | now apply Hdis ]...
        
        (* process Econstr one the right and left *)
        eapply cc_approx_exp_constr_compat
        with (IIL2 := Pre Funs') (IL2 := Post 0);
          [ | | | | | | |  | ].
        * eapply PostConstrCompat. eassumption.
          unfold cost_env_app_exp_out.
          eapply project_vars_cost_eq'. eassumption.
          eapply Forall2_refl_strong. intros x Hin.
          eapply Henv'. eapply project_vars_In. eassumption. eassumption.
        * eapply PreConstrCompat.
          eapply Forall2_refl_strong. intros x Hin.
          eapply Henv'. eapply project_vars_In. eassumption. eassumption.
        * eapply PostBase.
          unfold cost_env_app_exp_out. eapply project_vars_cost_eq'. eassumption.
       
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
              [ | | | | | | | | | | | eassumption (* CC *) ].
              * simpl in *. omega.
              * now eauto with typeclass_instances.
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
              * { eapply injective_subdomain_antimon with
                  (S := l1 |: (reach' H1 (env_locs rho1 (FV Scope' Funs' FVs)) \\
                                      env_locs rho1 (Funs' \\ Scope'))).
                  - eapply injective_subdomain_extend'.
                    + rewrite Setminus_Union_distr.
                      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
                      eapply injective_subdomain_antimon; [ eassumption |]... 
            
                    + rewrite Setminus_Union_distr.
                      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
                      intros Hc.

                      eapply image_monotonic in Hc;
                        [|  eapply Setminus_Included ].
                      eapply FV_image_reach in Hc; try eassumption.
                      eapply reachable_in_dom in Hc.
                      eapply HL.alloc_not_In_dom; eassumption.

                      eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
                      eapply reach'_set_monotonic. eapply env_locs_monotonic...

                      eapply Included_trans; [| eapply env_locs_closed; eassumption ].
                      eapply Included_trans; [| eapply reach'_extensive ]. 
                      eapply env_locs_monotonic...
            
                  - eapply Setminus_Included_Included_Union. 
                     
                    eapply Included_trans.
                    eapply reach'_set_monotonic. eapply env_locs_monotonic.
                    eapply FV_Union1.
                    
                    rewrite (Union_commut [set v]). 
                    eapply Included_trans.
                    eapply reach'_alloc_set_alt; [| eassumption ]. 
                    eapply Included_trans. eassumption.
                    eapply Included_trans; [| eapply reach'_extensive ] . 
                    eapply env_locs_monotonic. unfold FV. 
                    rewrite !Setminus_Union_distr. 
                    do 3 eapply Included_Union_preserv_l. rewrite Setminus_Disjoint.
                    
                    eapply project_vars_In. eassumption.
                    eapply Disjoint_Singleton_r. intros Hc. eapply Hfresh. constructor.
                    normalize_bound_var. now right. rewrite project_vars_FV_eq; [| eassumption ].
                    now left; left.
                    
                    rewrite env_locs_set_not_In. rewrite Setminus_Union_distr.
                    rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r. 
                    rewrite <- !Union_assoc. eapply Included_Union_compat. reflexivity.
                    rewrite Setminus_Disjoint. rewrite (Union_commut [set v]), <- Setminus_Union.
                    rewrite (Setminus_Disjoint _ [set v]).
                    rewrite <- Union_Setminus. now eauto with Ensembles_DB.
                    now tci.
                    eapply Disjoint_Singleton_r. intros Hc. eapply Hfresh.
                    constructor. normalize_bound_var. now right.
                    rewrite project_vars_FV_eq; [| eassumption ]. left. right. eassumption. 

                    eapply Disjoint_Singleton_r. intros Hc. eapply Hfresh.
                    constructor. normalize_bound_var. now right. 
                    rewrite project_vars_FV_eq; eassumption.

                    intros Hc. inv Hc. eauto. }
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
              * intros f Hfin. eauto.
              * inv Hunb. eassumption.
              * inv Hunb.
                eapply Disjoint_Included_r.
                eapply FV_Union1.
                eapply Union_Disjoint_r.
                eapply Disjoint_Singleton_r. eassumption.
                rewrite <- project_vars_FV_eq; [| eassumption ].
                eapply Disjoint_Included_l; [| eassumption ]. normalize_bound_var...                
            } }

    - (* case Eproj *)
      inv Hcc.
      admit.
      
    - (* case Ecase nil *)
      inv Hcc.
      admit.
    - (* case Ecase cons *)
      inv Hcc. (* TODO change compat *) 
      admit.
    - admit.
    - (* case Eapp *)
      inv Hcc.
      
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
        [ | | | | | | eassumption | ].
      
      + eapply (PostCtxCompat_vars_r Scope Scope' Funs Funs').
        now eapply H5. rewrite <- plus_n_O.
        eapply project_vars_cost_eq'. eassumption.
      + eapply (PreCtxCompat_vars_r Scope Scope' Funs Funs').
        now eapply H5.
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        
      + eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.

      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ]. 
        eapply env_locs_monotonic. eassumption.

      + eapply Included_trans; [| eapply env_locs_closed; eassumption ].
        eapply Included_trans; [| eapply reach'_extensive ]. 
        eapply env_locs_monotonic. eassumption.

      + assert (Hf' : ToMSet Funs') by (eapply project_vars_ToMSet_Funs; eauto). 
        (* inversion H5; subst. *)

        edestruct project_vars_correct with (Scope := Scope) as
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

          simpl. omega.
          
          intros Hc. eapply H4. constructor. now apply H15.
          left. left. left.
          eapply project_vars_In. eassumption. now right.

          intros Hc. eapply H4. constructor. now apply H12.
          left. left. left.
          eapply project_vars_In. eassumption. now right.
          
        * eapply PostBase. simpl. omega. 
          
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
    - (* case Eprim *)
      admit. 
    - (* case Ehalt *)
      inv Hcc.
      admit.
  