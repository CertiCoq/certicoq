(* Compatibility lemmas for logical relations.
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2017
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util
     List_util Heap.heap Heap.heap_defs Heap.space_sem
     Heap.cc_log_rel tactics.
From compcert Require Import lib.Coqlib.

Import ListNotations.



Module Compat (H : Heap).
  
  Module LR := CC_log_rel H.

  Import H LR LR.Sem LR.Sem.Equiv LR.Sem.Equiv.Defs.
    (** Conditions *)

    Variable (IG : GInv). (* Final global *)
    Variable (ILi : nat -> Inv). (* Final local indexed by a natural number indicating the amount of time units already spent for evaluation of the RHS program *) 
    Variable (IIG : GIInv). (* Global initial *)
    Variable (IIL1 IIL2 : IInv). (* Local initial *)
    
    Variable (F : nat). (* A constant factor*)
    
    Variable
      (InvCostTimeout :
         forall (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp) (k c : nat),
           IIL1 (H1, rho1, e1) (H2, rho2, e2) ->
           ILi k (c, size_heap H1) (c - k, size_heap H2)).
    
    Variable
      (InvCostBase :
         forall (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp) (k c : nat),
           c >= 1 ->
           IIL1 (H1, rho1, e1) (H2, rho2, e2) ->
           ILi k (c, size_heap H1) (c, size_heap H2)).
    
    
    (** * Compatibility properties for local conditions *)

    Variable
      (InvCompat_str :
         forall (k1 k2 c1 c2 c1' c2' m1 m2 : nat),
           
           ILi k2 (c1 - c1', m1) (c2 - c2', m2) -> 

           c1' <= c2' + (k1 - k2) <= c1' + F*c1' ->

           ILi k1 (c1, m1) (c2, m2)).
    
    Variable
      (InvTransfer :
         forall (k c1 c2 c m1 m2 : nat),
           ILi (k + c) (c1, m1) (c2, m2) ->
           ILi k (c1, m1) (c2 + c, m2)).

      
    (** Constructor compatibility *)
    Lemma cc_approx_exp_constr_compat (k j : nat)
          (b : Inj) (H1 H2 : heap block)  (rho1 rho2 : env)
          (x1 x2 : var) (t : cTag) (ys1 ys2 : list var) (e1 e2 : exp) (r1 r2 : nat) (a1 a2 : nat)
          
          (IInvConstrCompat :
             forall (H1 H2 H1' H2' : heap block) (rho1 rho2 : env)
               (b1 b2 : block) (l1 l2 : loc),
               IIL1 (H1, rho1, Econstr x1 t ys1 e1) (H2, rho2, Econstr x2 t ys2 e2) ->
               alloc b1 H1 = (l1, H1') -> 
               alloc b2 H2 = (l2, H2') ->
               size_val b1 = size_val b2 ->
               locs b1 \subset reach' H1 (env_locs rho1 (occurs_free (Econstr x1 t ys1 e1))) ->
               locs b2 \subset reach' H2 (env_locs rho2 (occurs_free (Econstr x2 t ys2 e2))) ->
               IIL2 (H1', M.set x1 (Loc l1) rho1, e1) (H2', M.set x2 (Loc l2) rho2, e2)) : 

      well_formed (reach' H1 (env_locs rho1 (occurs_free (Econstr x1 t ys1 e1)))) H1 ->
      well_formed (reach' H2 (env_locs rho2 (occurs_free (Econstr x2 t ys2 e2)))) H2 ->
      (env_locs rho1 (occurs_free (Econstr x1 t ys1 e1))) \subset dom H1 ->
      (env_locs rho2 (occurs_free (Econstr x2 t ys2 e2))) \subset dom H2 ->

      Forall2 (cc_approx_var_env k j IIG IG b H1 rho1 H2 rho2) ys1 ys2 ->

      (r1 - r2) <= F*(cost (Econstr x1 t ys1 e1)) ->

      (forall i vs1 vs2 l1 l2 H1' H2',
         i < k ->
         (* allocate a new location for the constructed value *)
         alloc (Constr t vs1) H1 = (l1, H1') ->
         alloc (Constr t vs2) H2 = (l2, H2') ->
         Forall2 (fun l1 l2 => (Res (l1, H1)) ≺ ^ (i ; j ; IIG ; IG ; b) (Res (l2, H2))) vs1 vs2 ->
         (e1, M.set x1 (Loc l1) rho1, H1') ⪯ ^ (i ; j ; IIL2 ; IIG ; ILi r2 ; IG)
         (e2, M.set x2 (Loc l2) rho2, H2')) ->
      
      (Econstr x1 t ys1 e1, rho1, H1) ⪯ ^ (k ; j ; IIL1 ; IIG ; ILi r1 ; IG) (Econstr x2 t ys2 e2, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hwf1 Hwf2 Hdom1 Hdom2 Hall Hleq Hpre b1 b2 H1' H2' rho1' rho2' v1 c1 m1
             Heq1 Hinj1 Heq2 Hinj2 HII Hleq1 Hstep1 Hstuck1.
      assert (Hall' := Hall).
      inv Hstep1.
      (* Timeout! *)
      - { exists OOT, (c1 - r1). eexists. exists id. repeat split. 
          - econstructor. simpl. erewrite <- Forall2_length; [| eassumption ].
            simpl in Hcost. omega. reflexivity.
          - simpl. eapply injective_subdomain_Empty_set. 
          - eapply InvCostTimeout. eassumption.
          - now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { edestruct (cc_approx_var_env_getlist IIG IG k j rho1' rho2') as [vs2 [Hget' Hpre']];
          [| eauto |]; eauto. 
          eapply Forall2_monotonic_strong; [| eassumption ].
          intros x1' x2' Hin1 Hin2 Hvar.

          eapply cc_approx_var_env_heap_env_equiv; try eassumption.

          normalize_occurs_free... normalize_occurs_free...
          edestruct heap_env_equiv_env_getlist as [vs1' [Hget1' Hall1]];
            [| symmetry; now apply Heq1 | |]; try eassumption.
          normalize_occurs_free...
          edestruct heap_env_equiv_env_getlist as [vs2' [Hget2' Hall2]];
            [| symmetry; now apply Heq2 | |]; try eassumption.
          normalize_occurs_free...
          destruct (alloc (Constr t vs1') H1) as [l1 H1''] eqn:Hal1.
          destruct (alloc (Constr t vs2) H2') as [l2 H''] eqn:Hal2'.
          destruct (alloc (Constr t vs2') H2) as [l2' H2''] eqn:Hal2.
          eapply Forall2_length in Hall.
          assert (Hlen : @length M.elt ys1 = @length M.elt ys2).
          { erewrite (@getlist_length_eq value ys1 vs); [| eassumption ].
            erewrite (@getlist_length_eq value ys2 vs2); [| eassumption ].
            eapply Forall2_length. eassumption. }

          edestruct Hpre with (i := k - (cost (Econstr x1 t ys1 e1)))
                                (b1 := extend b1 l l1)
                                (b2 := extend b2 l2' l2)
            as [v2 [c2 [m2 [b' [Hstep [HS [Hinj Hval]]]]]]]; 
            [ | eassumption | eassumption | | | | | | | |  eassumption | | ].
          - simpl in Hcost. simpl. omega.
          - edestruct (cc_approx_var_env_getlist IIG IG k j rho1 rho2) as [vs2'' [Hget'' Hall'']];
            [| eauto |]; eauto. subst_exp.
            eapply Forall2_monotonic; [| eassumption ]. intros ? ? H.
            eapply cc_approx_val_monotonic.
            now eapply H. omega.
          - eapply heap_env_equiv_alloc; [| | | | | | | eassumption | eassumption | | ].
            + eapply reach'_closed. eassumption. eassumption.
            + eapply reach'_closed.
              eapply well_formed_respects_heap_env_equiv.
              now apply Hwf1. eassumption.
              eapply env_locs_in_dom; eassumption.
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. simpl.
              rewrite env_locs_FromList; eauto. reflexivity.
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. simpl.
              rewrite env_locs_FromList; eauto. reflexivity.
            + eapply heap_env_equiv_antimon. eapply heap_env_equiv_rename_ext. 
              eassumption.
              reflexivity.

              eapply f_eq_subdomain_extend_not_In_S_r.
              intros Hr. eapply reachable_in_dom in Hr.
              eapply alloc_fresh in Halloc. destruct Hr as [s Hgetl]. congruence.
              eapply well_formed_respects_heap_env_equiv.
              now apply Hwf1. eassumption.
              eapply env_locs_in_dom; eassumption.
              reflexivity.
              normalize_occurs_free...
            + rewrite extend_gss. reflexivity.
            + simpl. split. reflexivity.

              eapply Forall2_symm_strong; [| eassumption ].
              intros l3 l4 Hin1 Hin2 Hin. simpl in Hin. symmetry in Hin.
              eapply res_equiv_rename_ext. eassumption.
              reflexivity.

              eapply f_eq_subdomain_extend_not_In_S_r.

              intros Hr. eapply reachable_in_dom in Hr.
              eapply alloc_fresh in Halloc. destruct Hr as [s Hgetl]. congruence. 

              eapply well_formed_antimon;
                [| eapply well_formed_respects_heap_env_equiv; (try now apply Hwf1); try eassumption ].
              eapply reach'_set_monotonic. simpl.
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l.

              rewrite env_locs_FromList; try eassumption. 
              eapply In_Union_list. eapply in_map. eassumption.
              eapply Included_trans; [| eapply env_locs_in_dom; eassumption ].
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l.
              rewrite env_locs_FromList; try eassumption. 
              eapply In_Union_list. eapply in_map. eassumption.
              
              reflexivity.
          - eapply injective_subdomain_antimon.
            eapply injective_subdomain_extend. eassumption.
            
            intros Hc. eapply image_monotonic in Hc; [| now eapply Setminus_Included ].  
            eapply heap_env_equiv_image_reach in Hc; try eassumption.
            eapply (image_id (reach' H1 (env_locs rho1 (occurs_free (Econstr x1 t ys1 e1)))))
              in Hc.
            eapply reachable_in_dom in Hc; try eassumption. destruct Hc as [v1' Hgetv1'].
            erewrite alloc_fresh in Hgetv1'; try eassumption. congruence.

            eapply Included_trans. eapply reach'_set_monotonic. eapply env_locs_monotonic.
            eapply occurs_free_Econstr_Included.
            eapply reach'_alloc_set; [| eassumption ]. 
            eapply Included_trans; [| eapply reach'_extensive ].
            normalize_occurs_free. rewrite env_locs_Union.
            eapply Included_Union_preserv_l. 
            rewrite env_locs_FromList; eauto. reflexivity.
          - eapply heap_env_equiv_alloc; [| | | | | | | now apply Hal2 | now apply Hal2' | | ].
            + eapply reach'_closed. eassumption. eassumption.
            + eapply reach'_closed.
              eapply well_formed_respects_heap_env_equiv.
              now apply Hwf2. eassumption.
              eapply env_locs_in_dom; eassumption.
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. simpl.
              rewrite env_locs_FromList; eauto. reflexivity.
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. simpl.
              rewrite env_locs_FromList; eauto. reflexivity.
            + eapply heap_env_equiv_antimon. eapply heap_env_equiv_rename_ext. 
              eassumption.

              eapply f_eq_subdomain_extend_not_In_S_r.
              intros Hr. eapply reachable_in_dom in Hr. 
              eapply alloc_fresh in Hal2. destruct Hr as [s Hgetl]. congruence.
              now apply Hwf2. eassumption. reflexivity. reflexivity.
              normalize_occurs_free...

            + rewrite extend_gss. reflexivity.  
            + symmetry. eapply block_equiv_rename_ext.
              split; eauto. reflexivity.

              eapply f_eq_subdomain_extend_not_In_S_r.
              intros Hr. eapply reachable_in_dom in Hr. 
              eapply alloc_fresh in Hal2. destruct Hr as [s Hgetl]. congruence.
              eapply well_formed_antimon; try eassumption.
              eapply reach'_set_monotonic.
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. 
              rewrite env_locs_FromList; eauto. reflexivity.

              eapply Included_trans; [| eassumption ].
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. 
              rewrite env_locs_FromList; eauto. reflexivity.

              reflexivity.

          - eapply injective_subdomain_antimon.
            eapply injective_subdomain_extend. eassumption.
            
            intros Hc. eapply image_monotonic in Hc; [| now eapply Setminus_Included ].  
            eapply heap_env_equiv_image_reach in Hc; try (symmetry; eassumption).
            eapply (image_id (reach' H2' (env_locs rho2' (occurs_free (Econstr x2 t ys2 e2)))))
              in Hc.
            eapply reachable_in_dom in Hc; try eassumption. destruct Hc as [v1' Hgetv1'].
            erewrite alloc_fresh in Hgetv1'; try eassumption. congruence.

            eapply well_formed_respects_heap_env_equiv. eassumption. eassumption.

            eapply Included_trans; [| eapply env_locs_in_dom; eassumption ].
            reflexivity.

            eapply Included_trans. eapply reach'_set_monotonic. eapply env_locs_monotonic.
            eapply occurs_free_Econstr_Included.
            eapply reach'_alloc_set; [| eassumption ]. 
            eapply Included_trans; [| eapply reach'_extensive ].
            normalize_occurs_free. rewrite env_locs_Union.
            eapply Included_Union_preserv_l. 
            rewrite env_locs_FromList; eauto. reflexivity.
              
          - eapply IInvConstrCompat; [ eassumption | eassumption | eassumption | | | ].
            simpl.
            eapply getlist_length_eq in Hget.
            eapply getlist_length_eq in Hget'. congruence.
            eapply Included_trans; [| now eapply reach'_extensive ].
            normalize_occurs_free. rewrite env_locs_Union.
            eapply Included_Union_preserv_l. rewrite env_locs_FromList.
            simpl. reflexivity. eassumption.
            eapply Included_trans; [| now eapply reach'_extensive ].
            normalize_occurs_free. rewrite env_locs_Union.
            eapply Included_Union_preserv_l. rewrite env_locs_FromList.
            simpl. reflexivity. eassumption.
          - simpl. simpl in Hcost. omega.
          - intros i. edestruct (Hstuck1 (i + cost (Econstr x1 t ys1 e1))) as [r' [m' Hstep']].
            inv Hstep'.
            * omega.
            * rewrite NPeano.Nat.add_sub in Hbs0. repeat subst_exp.
              repeat eexists; eauto.  
          - repeat eexists; eauto.
            + eapply Eval_constr_per_cc with (c := c2 + cost (Econstr x2 t ys2 e2))
              ; [ | | | rewrite NPeano.Nat.add_sub ]; try eassumption.
              simpl. omega.
            + simpl. eapply InvCompat_str with (c2' := S (length ys1)).
              replace (length ys2) with (length ys1).
              replace (c2 + S (length ys1) - S (length ys1)) with c2 by omega.
              eassumption. simpl. simpl in Hleq. omega.
            + rewrite cc_approx_val_eq. eapply cc_approx_val_monotonic.
              rewrite <- cc_approx_val_eq. eassumption. omega. }
    Qed.
    
    (** Projection compatibility *)
    Lemma cc_approx_exp_proj_compat (k : nat) (H1 H2 : heap block) (rho1 rho2 : env) (b : Inj)
          (x1 x2 : var) (t : cTag) (n : N) (y1 y2 : var) (e1 e2 : exp) (r1 r2 : nat)

          (IInvProjCompat :
             forall (H1 H2 : heap block) (rho1 rho2 : env) (v1 v2 : value),
               IIL1 (H1, rho1, Eproj x1 t n y1 e1) (H2, rho2, Eproj x2 t n y2 e2) ->
               val_loc v1 \subset reach' H1 (env_locs rho1 (occurs_free (Eproj x1 t n y1 e1))) ->
               val_loc v2 \subset reach' H2 (env_locs rho2 (occurs_free (Eproj x2 t n y2 e2))) ->
               IIL2 (H1, M.set x1 v1 rho1, e1) (H2, M.set x2 v2 rho2, e2)) :

      (forall j, cc_approx_var_env k j IIG IG b H1 rho1 H2 rho2 y1 y2) ->

      r1 - r2 <= F*(cost (Eproj x1 t n y1 e1)) ->

      (forall i v1 v2,
         i < k ->
         (forall j, (Res (v1, H1)) ≺ ^ (i ; j ; IIG ; IG; b) (Res (v2, H2))) ->
         (forall j, (e1, M.set x1 v1 rho1, H1) ⪯ ^ (i ; j ; IIL2 ; IIG ; ILi r2 ; IG) (e2, M.set x2 v2 rho2, H2))) ->
      
      (forall j, (Eproj x1 t n y1 e1, rho1, H1) ⪯ ^ (k ; j ; IIL1 ; IIG ; ILi r1 ; IG) (Eproj x2 t n y2 e2, rho2, H2)).
    Proof with (now eauto with Ensembles_DB).
      intros Hall Hleq Hpre j b1 b2 H1' H2' rho1' rho2' v1 c1 m1
             Heq1' Hinj1 Heq2' Hinj2 HII Hleq1 Hstep1 Hstuck. inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost. exists OOT, (c1 - r1). eexists. exists id. repeat split. 
          - econstructor. simpl; omega. reflexivity.
          - eapply injective_subdomain_Empty_set.
          - eapply InvCostTimeout. eassumption.
          - now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { pose (cost1 := cost (Eproj x1 t n y1 e1)).
          pose (cost2 := costCC (Eproj x2 t n y2 e2)).
          assert (Hall' := Hall).
          
          eapply (cc_approx_var_env_heap_env_equiv
                    _ _
                    (occurs_free (Eproj x1 t n y1 e1))
                    (occurs_free (Eproj x2 t n y2 e2)) _ (S j)) in Hall;
          [| eassumption | eassumption | eassumption | eassumption
           | normalize_occurs_free; now eauto with Ensembles_DB
           | normalize_occurs_free; now eauto with Ensembles_DB ].
          edestruct Hall as [l2 [Hget' Hcc']]; eauto.
          destruct l2 as [l' | l' f]; [| contradiction ].
          simpl in Hcc'. rewrite Hgetl in Hcc'.
          destruct (get l' H2') as [[ t2 vs' | | ] |] eqn:Hgetl';
            (try destruct Hcc' as [Hteq Hcc']); try contradiction.
          
          edestruct heap_env_equiv_env_get as [l1 [Hgetl1 Hres1]]; [ now apply Hgety | | | ].
          symmetry. eassumption. now eauto.
          edestruct heap_env_equiv_env_get as [l2 [Hgetl2 Hres2]]; [ now apply Hget' | | | ].
          symmetry. eassumption. now eauto.

          edestruct (Hall' (S j))  as [l2' [Hgetl2'' Hcc]]; eauto. repeat subst_exp. 
          
          assert (Hres1' := Hres1). assert (Hres2' := Hres2). rewrite res_equiv_eq in Hres1, Hres2.
          destruct l1 as [l1 |]; try contradiction.
          destruct l2' as [l2 |]; try contradiction.
          
          simpl in Hres1, Hres2. rewrite Hgetl in Hres1. rewrite Hgetl' in Hres2.
          destruct (get l1 H1) as [bl1 |] eqn:Hgetl1'; (try destruct Hres1 as [Hb1 Hres1]); try contradiction.
          destruct (get l2 H2) as [bl2 |] eqn:Hgetl2'; (try destruct Hres2 as [Hb2 Hres2]); try contradiction.
          destruct bl1 as [t1 vs1 | | ]; try contradiction.
          destruct bl2 as [t2' vs2 | | ]; try contradiction.
          destruct Hres1 as [Hteq Hallvs1]; subst. destruct Hres2 as [Hteq' Hallvs2]; subst.
          
          simpl in Hcc. rewrite Hgetl1' in Hcc. rewrite Hgetl2' in Hcc.
          destruct Hcc as [Hbeq [Hteq Hcc]]. subst.
          
          edestruct (Forall2_nthN _ _ _ _ _ Hallvs1 Hnth) as [v1' [Hnth' Hv1]].
          edestruct (Forall2_nthN
                       (fun l1 l2 => cc_approx_val k j IIG IG b (Res (l1, H1)) (Res (l2, H2))) vs1)
            as [l3' [Hnth'' Hval']]; eauto.
          (* eapply Hcc. unfold cost1. simpl. simpl in Hcost. omega. *)
          
          edestruct (Forall2_nthN (fun v1 v2 : value => (v1, H2) ≈_( b2, id) (v2, H2'))) as [v2' [Hnth2' Hv2]].
          eapply Forall2_symm_strong; [| eassumption ]. intros. now symmetry; eauto. eassumption.
          
          edestruct Hpre with (i := k - cost1) (c1 := c1 - cost1) as [v2 [c2 [m2 [b' [Hstep [Hinj' [HS Hres]]]]]]];
            [ | | | | | | | omega | eassumption | | ].  
          - unfold cost1. simpl. simpl in Hcost. omega.
          - intros j'.
            
            edestruct (Hall' (S j'))  as [l2'' [Hgetl2'' Hcc'']]; eauto. repeat subst_exp. 

            simpl in Hcc''. rewrite Hgetl1' in Hcc''. rewrite Hgetl2' in Hcc''.
            destruct Hcc'' as [_ [_ Hcc'']].
            
            edestruct (Forall2_nthN
                         (fun l1 l2 => cc_approx_val k j' IIG IG b (Res (l1, H1)) (Res (l2, H2))) vs1)
              as [v2'' [Hnth2 Hv2']]; eauto.

            eapply cc_approx_val_monotonic.
            rewrite <- cc_approx_val_eq. 
            repeat subst_exp. eassumption. omega.
            
          - eapply heap_env_equiv_set.
            eapply heap_env_equiv_antimon. eassumption.
            normalize_occurs_free... symmetry. eassumption.
          - eapply injective_subdomain_antimon. eassumption.

            rewrite (reach'_idempotent H1' (env_locs rho1' (occurs_free (Eproj x1 t n y1 e1)))).
            eapply reach'_set_monotonic.
            eapply Included_trans.
            eapply env_locs_set_Inlcuded'.
            eapply Union_Included.

            eapply Included_trans; [| eapply Included_post_reach' ].
            normalize_occurs_free. rewrite env_locs_Union, post_Union. eapply Included_Union_preserv_l.
            rewrite env_locs_Singleton; eauto. simpl. erewrite post_Singleton; eauto.
            simpl. eapply In_Union_list. eapply in_map. eapply nthN_In. eassumption.

            eapply Included_trans; [| eapply reach'_extensive ].
            eapply env_locs_monotonic. normalize_occurs_free...
          - eapply heap_env_equiv_set.
            eapply heap_env_equiv_antimon. eassumption.
            normalize_occurs_free...
            repeat subst_exp. eassumption.
          - eapply injective_subdomain_antimon. eassumption.

            rewrite (reach'_idempotent H2 (env_locs rho2 (occurs_free (Eproj x2 t n y2 e2)))).
            eapply reach'_set_monotonic.
            eapply Included_trans.
            eapply env_locs_set_Inlcuded'.
            eapply Union_Included.
            
            eapply Included_trans; [| eapply Included_post_reach' ].
            normalize_occurs_free. rewrite env_locs_Union, post_Union. eapply Included_Union_preserv_l.
            rewrite env_locs_Singleton; eauto. simpl. erewrite post_Singleton; eauto.
            simpl. eapply In_Union_list. eapply in_map. eapply nthN_In. eassumption.

            eapply Included_trans; [| eapply reach'_extensive ].
            eapply env_locs_monotonic. normalize_occurs_free...
          - eapply IInvProjCompat. eassumption.
            eapply Included_trans; [| eapply Included_post_reach' ].
            normalize_occurs_free. rewrite env_locs_Union, post_Union. eapply Included_Union_preserv_l.
            rewrite env_locs_Singleton; eauto. simpl. erewrite post_Singleton; eauto.
            simpl. eapply In_Union_list. eapply in_map. eapply nthN_In. eassumption.
            eapply Included_trans; [| eapply Included_post_reach' ].
            normalize_occurs_free. rewrite env_locs_Union, post_Union. eapply Included_Union_preserv_l.
            rewrite env_locs_Singleton; eauto. simpl. erewrite post_Singleton; eauto.
            simpl. eapply In_Union_list. eapply in_map. eapply nthN_In. eassumption.
          - intros i. edestruct (Hstuck (i + cost1)) as [r' [m' Hstep']].
            inv Hstep'.
            * unfold cost1 in Hcost0. omega.
            * simpl in Hbs0. rewrite NPeano.Nat.add_sub in Hbs0.
              repeat subst_exp.
              do 2 eexists. eassumption.
          - repeat eexists; eauto. eapply Eval_proj_per_cc with (c := c2 + cost2); try eassumption.
            unfold cost2. simpl; omega. simpl. rewrite NPeano.Nat.add_sub.
            eassumption.
            eapply InvCompat_str with (c2' := cost1).
            unfold cost1, cost2. simpl. rewrite NPeano.Nat.add_sub. eassumption. 
            simpl; simpl in Hleq; omega.
            rewrite cc_approx_val_eq in *.
            eapply cc_approx_val_monotonic. eassumption.
            unfold cost1, cost2. simpl. simpl in Hcost. omega. }
    Qed.
    
    (** Case compatibility *)
    Lemma cc_approx_exp_case_nil_compat (k j : nat) (H1 H2 : heap block) (rho1 rho2 : env) (x1 x2 : var) (c : nat) :
      c <= F * (cost (Ecase x1 [])) -> 
      (Ecase x1 [], rho1, H1) ⪯ ^ (k ; j ; IIL1 ; IIG ; ILi c ; IG) (Ecase x2 [], rho2, H2).
    Proof.
      intros Hleq b1 b2 H1' H2' rho1' rho2' v1 c1 m1 Heq1 Hinj1 Heq2 Hinj2 HII Hleq1 Hstep1 Hns. inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost. exists OOT, (c1 - c). eexists. eexists id. repeat split. 
          - econstructor. simpl; omega. reflexivity. 
          - now firstorder.
          - eapply InvCostTimeout.
            eassumption.
          - now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { simpl in Htag. discriminate. }
    Qed.
    
    Lemma cc_approx_exp_case_compat (k j : nat) (b : Inj) (H1 H2 : heap block) (rho1 rho2 : env) (x1 x2 : var) (t : cTag)
          (e1 e2 : exp) (Pats1 Pats2 : list (cTag * exp)) (r1 r2 : nat)
 
      (IInvCaseHdCompat :
         forall (H1 H2 : heap block) (rho1 rho2 : env),
           IIL1 (H1, rho1, Ecase x1 ((t, e1) :: Pats1)) (H2, rho2, Ecase x2 ((t, e2) :: Pats2)) ->
           IIL2 (H1, rho1, e1) (H2, rho2, e2))

      (IInvCaseTlCompat :
         forall (H1 H2 : heap block) (rho1 rho2 : env),
           IIL1 (H1, rho1, Ecase x1 ((t, e1) :: Pats1)) (H2, rho2, Ecase x2 ((t, e2) :: Pats2)) ->
           IIL1 (H1, rho1, Ecase x1 Pats1) (H2, rho2, Ecase x2 Pats2)) :
        
      cc_approx_var_env k j IIG IG b H1 rho1 H2 rho2 x1 x2 ->

      (r1 - r2) <= F * (cost (Ecase x1 Pats1)) -> 

      (forall i H1 H2 rho1 rho2,
         i < k -> 
         (e1, rho1, H1) ⪯ ^ (i ; j ; IIL2 ; IIG ; ILi r2 ; IG) (e2, rho2, H2)) ->

      (Ecase x1 Pats1, rho1, H1) ⪯ ^ (k ; j ; IIL1 ; IIG ; ILi r1 ; IG) (Ecase x2 Pats2, rho2, H2) ->

      (Ecase x1 ((t, e1) :: Pats1), rho1, H1) ⪯ ^ (k ; j ; IIL1 ; IIG ; ILi r1 ; IG) (Ecase x2 ((t, e2) :: Pats2), rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hvar Hleq Hexp_hd Hexp_tl b1 b2 H1' H2' rho1' rho2'
             v1 c1 m1 Heq1 Hinj1 Heq2 Hinj2 HII Hleq1 Hstep1 Hstuck1.
      inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost. exists OOT, (c1 - r1). eexists. exists id. repeat split. 
          - econstructor. simpl; omega. reflexivity. 
          - eapply injective_subdomain_Empty_set.
          - eapply InvCostTimeout. eassumption.
          - now rewrite cc_approx_val_eq. }
      - { pose (cost1 := cost (Ecase x1 ((t, e1) :: Pats1))).
          pose (cost2 := costCC (Ecase x2 ((t, e2) :: Pats2))).
          eapply (cc_approx_var_env_heap_env_equiv
                    _ _
                    (occurs_free (Ecase x1 ((t, e1) :: Pats1)))
                    (occurs_free (Ecase x2 ((t, e2) :: Pats2)))) in Hvar;
          [| eassumption | eassumption | eassumption | eassumption
           | normalize_occurs_free; now eauto with Ensembles_DB | normalize_occurs_free; now eauto with Ensembles_DB ].
          edestruct Hvar as [l' [Hgety' Hcc]]; eauto.
          destruct l' as [l' |l' f ]; [| contradiction ].
          simpl in Hcc. rewrite Hgetl in Hcc. 
          destruct (get l' H2') as [[ t' vs' | | ] |] eqn:Hgetl';
            (try destruct Hcc as [Hbeq Hcc]); try contradiction.
          destruct Hcc as [Heq Hall']; subst. simpl in Hall', Hcost.
          simpl in Htag. destruct (M.elt_eq t t') eqn:Heq; subst.
          - inv Htag.
            edestruct Hexp_hd with (i := k - cost1) (c1 := c1 - cost1) as [v2 [c2 [m2 [b' [Hstep [Hinj' [HS Hres]]]]]]]. 
            + unfold cost1; simpl; omega.
            + eapply heap_env_equiv_antimon. now eapply Heq1.
              normalize_occurs_free...
            + eapply injective_subdomain_antimon. eassumption.
              eapply reach'_set_monotonic. eapply env_locs_monotonic.
              normalize_occurs_free...
            + eapply heap_env_equiv_antimon. now eapply Heq2.
              normalize_occurs_free...
            + eapply injective_subdomain_antimon. eassumption.
              eapply reach'_set_monotonic. eapply env_locs_monotonic.
              normalize_occurs_free...
            + eapply IInvCaseHdCompat; eassumption.
            + unfold cost1. simpl; omega.
            + eassumption.
            + intros i. edestruct (Hstuck1 (i + cost1)) as [r' [m'' Hstep']].
              inv Hstep'.
              * exists OOT. eexists. econstructor; eauto. unfold cost1 in Hcost0.
               omega. 
              * repeat subst_exp.
                simpl in Htag; rewrite Heq in Htag; inv Htag.
                simpl in Hbs0. rewrite NPeano.Nat.add_sub in Hbs0.
                do 2 eexists. eassumption.
            + repeat eexists; eauto.
              * eapply Eval_case_per_cc with (c := c2 + cost2)
                ; [ | | | | rewrite NPeano.Nat.add_sub ]; try eassumption.
                unfold cost2. omega. now simpl; rewrite Heq. 
              * simpl. eapply InvCompat_str with (c2' := cost1).
                unfold cost2, cost1. simpl. rewrite NPeano.Nat.add_sub.
                eassumption. simpl; simpl in Hleq; omega.
              * rewrite cc_approx_val_eq. eapply cc_approx_val_monotonic.
                rewrite <- cc_approx_val_eq. eassumption. unfold cost1. simpl. omega.
          - edestruct Hexp_tl as [v2 [c2 [m2 [b' [Hstep2 [Hinj' [HS Hpre2]]]]]]];
               [ | | | | | | now econstructor; eauto | | ].
            + eapply heap_env_equiv_antimon; [ eassumption |].
              normalize_occurs_free...
            + eapply injective_subdomain_antimon. eassumption.
              eapply reach'_set_monotonic. eapply env_locs_monotonic.
              normalize_occurs_free...
            + eapply heap_env_equiv_antimon; [ eassumption |].
              normalize_occurs_free...
            + eapply injective_subdomain_antimon. eassumption.
              eapply reach'_set_monotonic. eapply env_locs_monotonic.
              normalize_occurs_free...
            + eapply IInvCaseTlCompat; eassumption.
            + simpl in Hcost. omega.
            + intros i. edestruct (Hstuck1 i) as [r' [m'' Hstep']].
              inv Hstep'.
              * exists OOT. eexists. econstructor; eauto.
              * repeat subst_exp.
                simpl in Htag0; rewrite Heq in Htag0. repeat subst_exp.
                simpl in Hbs0.
                do 2 eexists. eapply Eval_case_gc.
                simpl in Hcost0. simpl. omega.
                eassumption. eassumption. eassumption. eassumption.
            + inv Hstep2.
              * (* Timeout! *)
                { simpl in Hcost0. exists OOT, c2. eexists. exists b'. repeat split.
                  - econstructor. simpl. eassumption. reflexivity. 
                  - eassumption.
                  - eassumption.
                  - eassumption. }
              * (* termination *)
                { repeat eexists; eauto.
                  - eapply Eval_case_per_cc with (c := c2); eauto.
                    simpl. repeat subst_exp.
                    rewrite Heq. eassumption.
                } }
    Qed.
    
    (** Halt compatibility *)
    Lemma cc_approx_exp_halt_compat (k : nat) (H1 H2 : heap block) (rho1 rho2 : env) (x1 x2 : var) (r : nat) :
      r <= F * (cost (Ehalt x1)) -> 
          
      cc_approx_var_env k IIG IG H1 rho1 H2 rho2 x1 x2 ->
      
      (Ehalt x1, rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi r ; IG) (Ehalt x2, rho2, H2).
    Proof.
      intros Hleq Hvar H1' H2' rho1' rho2' v1 c1 m1 HII Heq1 Heq2 Hleq1 Hstep1 Hstuck1.
      inv Hstep1.
      - (* Timeout! *)
        { simpl in Hcost. exists OOT, (c1 - r). eexists. repeat split. 
          - econstructor; eauto. simpl. omega.
          - rewrite <- plus_n_O. eapply InvCostTimeout.
            eassumption.
          - now rewrite cc_approx_val_eq. }
      - pose (cost1 := cost (Ehalt x1)).
        pose (cost2 := cost (Ehalt x2)).
        eapply (cc_approx_var_env_heap_env_equiv
                  _ _
                  (occurs_free (Ehalt x1))
                  (occurs_free (Ehalt x2))) in Hvar;
          [| eassumption | eassumption | now constructor | now constructor ]. 
        edestruct Hvar as [l' [Hgety' Hcc]]; eauto.
        eexists. exists c1. repeat eexists.
        * eapply Eval_halt_per_cc. simpl. simpl in Hcost. omega. eassumption.
          reflexivity.
        * eapply InvCostBase. eassumption. eassumption.
        * rewrite cc_approx_val_eq in *.
          eapply cc_approx_val_monotonic. eassumption.
          omega.
    Qed.

    (** XXX move/name *)
    Lemma heap_env_equiv_def_funs' (S : Ensemble var) (H1 H2 : heap block) 
          (rho1 rho2 : M.t value) (B B' : fundefs) : 
      S \\ (name_in_fundefs B) |- (H1, rho1) ⩪ (H2, rho2) ->
      S |- (H1, def_funs B B' rho1) ⩪ (H2, def_funs B B' rho2).
    Proof with now eauto with Ensembles_DB.
      revert S. induction B; simpl; intros S Heq.
      - eapply heap_env_equiv_set.
        + eapply IHB. eapply heap_env_equiv_antimon...
        + rewrite res_equiv_eq. simpl. split; eauto.
      - eapply heap_env_equiv_antimon...
    Qed.

    (** Abstraction compatibility *)
    Lemma cc_approx_exp_fun_compat (k : nat) rho1 rho2 H1 H2 B1 e1 B2 e2 r1 r2
          (IInvFunCompat :
             forall H1 H1' H1''  H2  rho1 rho1' rho1'' rho2 env_loc, 
               IIL1 (H1, rho1, Efun B1 e1) (H2, rho2, Efun B2 e2) ->
               restrict_env (fundefs_fv B1) rho1 = rho1' ->
               alloc (Env rho1') H1 = (env_loc, H1') ->
               def_closures B1 B1 rho1 H1' env_loc = (H1'', rho1'') ->
               IIL2 (H1'', rho1'', e1) (H2, def_funs B2 B2 rho2, e2)) :

      well_formed (reach' H1 (env_locs rho1 (occurs_free (Efun B1 e1)))) H1 ->
      (env_locs rho1 (occurs_free (Efun B1 e1))) \subset dom H1 ->
      

      fundefs_num_fv B1 <= (r1 - r2) <= F*(cost (Efun B1 e1)) -> 

      (forall i  H1 H1' H1'' rho1' rho_clo env_loc,
         i < k ->
         
         restrict_env (fundefs_fv B1) rho1 = rho_clo ->
         alloc (Env rho_clo) H1 = (env_loc, H1') ->

         def_closures B1 B1 rho1 H1' env_loc = (H1'', rho1') ->

         (e1, rho1', H1'') ⪯ ^ (i; IIL2 ; IIG ; ILi r2 ; IG)
         (e2, def_funs B2 B2 rho2, H2)) ->
      (Efun B1 e1, rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi r1 ; IG) (Efun B2 e2, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hwf Hdom Hleq Hpre H1' H2' rho1' rho2' v1 c1
             m1 Heq1 Heq2 HII Hleq1 Hstep1 Hstuck1.
      inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost. exists OOT, (c1 - r1).
          - eexists. repeat split. econstructor. simpl.
            omega. reflexivity.
            eapply InvCostTimeout. eassumption.
            now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { destruct (alloc (Env (restrict_env (fundefs_fv B1) rho1)) H1)
            as [env_loc3 H3] eqn:Ha3.
          destruct (def_closures B1 B1 rho1 H3 env_loc3)
            as [H3' rho3] eqn:Hdef3.
          edestruct Hpre with (i := k - cost (Efun B1 e1)) as [v2 [c2 [m2 [Hstep [HS Hval]]]]]
          ; [ | reflexivity | now apply Ha3 | now apply Hdef3 | | | | | eassumption | | ].
          - simpl in Hcost. simpl. omega.
          - assert (Hequiv : occurs_free_fundefs B1 :|: occurs_free e1 \\ name_in_fundefs B1 |- (H', rho1') ⩪ (H3, rho1)).
            { eapply heap_env_equiv_weaking_cor.
              * eapply well_formed_antimon;
                [| eapply well_formed_respects_heap_env_equiv; [ now apply Hwf | eassumption ] ].
                eapply reach'_set_monotonic.
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic.
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply Included_trans; [| eapply env_locs_in_dom; [ eassumption |]].
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
                eassumption.
              * eapply Included_trans; [| eassumption ].
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply heap_env_equiv_antimon. symmetry. eassumption.
                normalize_occurs_free. rewrite Setminus_Union_distr...
              * eapply HL.alloc_subheap. eassumption.
              * eapply HL.alloc_subheap. eassumption. }
            eapply heap_env_equiv_antimon with (S1 := occurs_free_fundefs B1 :|: occurs_free e1);
            [| now eauto with Ensembles_DB ].
            setoid_rewrite <- Hdef3. setoid_rewrite <- Hfuns. (* strange *)
            symmetry.
            eapply heap_env_equiv_def_funs. 
            + eapply closed_alloc'; [| | eassumption ].
              * eapply reach'_closed.
                eapply well_formed_respects_heap_env_equiv. now apply Hwf.
                eassumption.
                eapply env_locs_in_dom; eassumption.
              * eapply Included_trans; [| now eapply reach'_extensive ].
                simpl. eapply Included_trans.
                eapply restrict_env_env_locs.
                eapply restrict_env_correct.
                eapply fundefs_fv_correct.
                eapply env_locs_monotonic. normalize_occurs_free...
            + eapply closed_alloc'; [| | eassumption ].
              * eapply reach'_closed; eassumption.
              * eapply Included_trans; [| now eapply reach'_extensive ].
                simpl.
                simpl. eapply Included_trans.
                eapply restrict_env_env_locs.
                eapply restrict_env_correct.
                eapply fundefs_fv_correct.
                eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [| now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free.
              rewrite Setminus_Union_distr...
            + eapply Included_trans; [| now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free.
              rewrite Setminus_Union_distr...
            + eapply gas. eassumption.
            + eapply gas. eassumption.
            + eapply Included_trans; [| now eapply reach'_extensive ].
              simpl. eapply Included_trans.
              eapply restrict_env_env_locs.
              eapply restrict_env_correct.
              eapply fundefs_fv_correct.
              eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [| now eapply reach'_extensive ].
              simpl. eapply Included_trans.
              eapply restrict_env_env_locs.
              eapply restrict_env_correct.
              eapply fundefs_fv_correct.
              eapply env_locs_monotonic. normalize_occurs_free...
            + rewrite Setminus_Union_distr, Setminus_Disjoint.
              now eauto with Ensembles_DB.
              eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
            + rewrite res_equiv_eq.
              simpl. erewrite !gas; try eassumption. simpl. 
              eapply heap_env_equiv_restrict_env with (S' := occurs_free_fundefs B1).
              * eapply heap_env_equiv_antimon. now apply Hequiv.
                rewrite Setminus_Union_distr, Setminus_Disjoint.
                eapply Included_Union_preserv_l. reflexivity.
                eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
              * reflexivity.
              * eapply restrict_env_correct.
                eapply fundefs_fv_correct.
              * eapply restrict_env_correct.
                eapply fundefs_fv_correct.
            + eapply heap_env_equiv_weaking_cor.
              * eapply well_formed_antimon;
                [| eapply well_formed_respects_heap_env_equiv; [ now apply Hwf | eassumption ] ].
                eapply reach'_set_monotonic.
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic.
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply Included_trans; [| eapply env_locs_in_dom; [ eassumption |]].
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
                eassumption.
              * eapply Included_trans; [| eassumption ].
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply heap_env_equiv_antimon. symmetry. eassumption.
                normalize_occurs_free. rewrite Setminus_Union_distr...
              * eapply HL.alloc_subheap. eassumption.
              * eapply HL.alloc_subheap. eassumption.
          - eapply heap_env_equiv_def_funs'.
            eapply heap_env_equiv_antimon. eassumption.
            normalize_occurs_free...
          - eapply IInvFunCompat; eauto.
          - simpl; omega.
          - intros i. edestruct (Hstuck1 (i + cost (Efun B1 e1))) as [r' [m' Hstep']].
            inv Hstep'.
            * omega.
            * rewrite NPeano.Nat.add_sub in Hbs0. repeat subst_exp.
              repeat eexists. eassumption.
          - repeat eexists; eauto.
            + eapply Eval_fun_per_cc with (c := c2 + costCC (Efun B2 e2)); try eassumption.
              simpl. omega. reflexivity. simpl.
              rewrite NPeano.Nat.add_sub. eassumption.
            + simpl. eapply InvCompat_str with (c2' := 1).
              rewrite NPeano.Nat.add_sub. eassumption.
              simpl. simpl in Hleq. omega. 
            + rewrite cc_approx_val_eq in *. 
              eapply cc_approx_val_monotonic. eassumption.
              simpl. simpl in Hcost. omega. }
    Qed.
    

    Variable
      (InvCompat1_str_gc :
         forall (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp)
           (k1 k2 c1 c2 c1' c2' m1 m2 : nat),

           IIL2 (H1, rho1, e1) (H2, rho2, e2) ->

           ILi k2 (c1 - c1', m1) (c2 - c2', m2) -> 

           c1' <= c2' + (k1 - k2) <= c1' + F*c1' ->

           ILi k1 (c1, max m1 (size_heap H1)) (c2, max m2 (size_heap H2))).
    
    Variable
      (IGinILi : inclusion _ IG (ILi 0)).

    Variable
      (IIL2inIIG : inclusion _ IIL2 IIG).

    Variable
      (II_gc :
         forall (H1 H2 H1' H2' : heap block) (rho1 rho2 : env) (e1 e2 : exp),
           IIL2 (H1, rho1, e1) (H2, rho2, e2) ->
           live (env_locs rho1 (occurs_free e1)) H1 H1' ->
           live (env_locs rho2 (occurs_free e2)) H2 H2' ->
           IIL2 (H1', rho1, e1) (H2', rho2, e2)).
    
    (** Application compatibility *)
    Lemma cc_approx_exp_app_compat (k : nat) (H1 H2 : heap block) (rho1 rho2 : env) (f1 : var) (xs1 : list var)
          (f2 f2' Γ : var) (xs2 : list var) (t : fTag) (c : nat)
          (IInvAppCompat :
             forall (H1 H2 H1' : heap block) (rho1 rho_clo rho_clo1 rho_clo2 rho2 rho2' : env)
               (B1 : fundefs) (f1 f1' : var) (ct1 : cTag) 
               (xs1 xs1' : list var) (e1 : exp) (l1 env_loc1 : loc)
               (vs1 : list value) 

               (B2 : fundefs) (f2 f3 : var) (c ct2 : cTag) (xs2 xs2' : list var) 
               (e2 : exp) (l2 env_loc2 : loc) (vs2 : list value),
               IIL1 (H1, rho1, Eapp f1 t xs1) (H2, rho2, AppClo f2 t xs2 f2' Γ) ->
               (* not exactly classy.... Can we make it a bit more abstract? *)
               M.get f1 rho1 = Some (Loc l1) ->
               get l1 H1 = Some (Clos (FunPtr B1 f1') (Loc env_loc1)) ->
               get env_loc1 H1 = Some (Env rho_clo) ->
               find_def f1' B1 = Some (ct1, xs1', e1) ->
               getlist xs1 rho1 = Some vs1 ->
               def_closures B1 B1 rho_clo H1 env_loc1 = (H1', rho_clo1) ->
               setlist xs1' vs1 rho_clo1 = Some rho_clo2 ->

               M.get f2 rho2 = Some (Loc l2) ->
               getlist xs2 rho2 = Some vs2 ->
               get l2 H2 = Some (Constr c [FunPtr B2 f3; Loc env_loc2]) ->
               Some rho2' =
               setlist xs2' (Loc env_loc2 :: vs2) (def_funs B2 B2 (M.empty value)) ->
               find_def f3 B2 = Some (ct2, xs2', e2) ->

               IIL2 (H1', rho_clo2, e1) (H2, rho2', e2)) :
      
      well_formed (reach' H1 (env_locs rho1 (occurs_free (Eapp f1 t xs1)))) H1 ->
      well_formed (reach' H2 (env_locs rho2 (occurs_free (AppClo f2 t xs2 f2' Γ)))) H2 ->
      (env_locs rho1 (occurs_free (Eapp f1 t xs1))) \subset dom H1 ->
      (env_locs rho2 (occurs_free (AppClo f2 t xs2 f2' Γ))) \subset dom H2 ->
      
      ~ Γ \in (f2 |: FromList xs2) ->
      ~ f2' \in (f2 |: FromList xs2) ->
      Γ <> f2' ->

      c + 3 <= F * (cost (Eapp f1 t xs1)) -> 
      length xs1 = length xs2 ->

      cc_approx_var_env k IIG IG H1 rho1 H2 rho2 f1 f2 ->
      Forall2 (cc_approx_var_env k IIG IG H1 rho1 H2 rho2) xs1 xs2 ->
      (* II (H1, rho1, Eapp f1 t xs1) (H2, rho2, AppClo f2 t xs2 f2' Γ)  -> *)
      (Eapp f1 t xs1, rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi c ; IG) (AppClo f2 t xs2 f2' Γ, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hwf1 Hwf2 Hs1 Hs2 Hnin1 Hnin2 Hneq Hleqc Hlen Hvar Hall
             H1' H2' rho1' rho2' v1 c1 m1 Heq1 Heq2 HII Hleq1 Hstep1 Hstuck1.
      eapply (cc_approx_var_env_heap_env_equiv
                    _ _
                    (occurs_free (Eapp f1 t xs1))
                    (occurs_free (AppClo f2 t xs2 f2' Γ))) in Hvar;
          [| eassumption | eassumption 
           | normalize_occurs_free; now eauto with Ensembles_DB
           | unfold AppClo; normalize_occurs_free; now eauto with Ensembles_DB ].
      inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost.
          edestruct (Hstuck1 (cost (Eapp f1 t xs1))) as [v1 [m1 Hstep1]].
          inv Hstep1; [ omega | ].
          exists OOT, (c1 - c). destruct (lt_dec (c1 - c) 1).
          - eexists. repeat split. now constructor; eauto.
            rewrite <- plus_n_O.
            eapply InvCostTimeout.
            eassumption.
            now rewrite cc_approx_val_eq.
          - edestruct Hvar as [l2 [Hget' Hcc]]; eauto.
            simpl in Hcc. rewrite Hgetl in Hcc. destruct l2 as [l2 | ]; [| contradiction ]. 
            destruct (get l2 H2') as [v |] eqn:Hget2; try contradiction.
            simpl in Hcc.
            destruct v as [ ? [| [| B2 f3 ] [| [ env_loc' |] [|] ]] | | ]; try contradiction.
            edestruct Hcc with (vs2 := vs) as (xs2' & e2 & rho2'' & Hfind' & Hset' & Hi'); try eassumption.
            reflexivity. reflexivity.
            destruct (lt_dec (c1 - c - 1) 1).
            + eexists. repeat split. unfold AppClo.
              eapply Eval_proj_per_cc; eauto.
              simpl. omega. reflexivity.
              now econstructor; simpl; eauto.
              rewrite <- !plus_n_O.
              eapply InvCostTimeout. eassumption.
              now rewrite cc_approx_val_eq.
            + eexists. repeat split. unfold AppClo.
              eapply Eval_proj_per_cc; eauto.
              simpl. omega. reflexivity.
              eapply Eval_proj_per_cc; eauto.
              simpl. omega.
              rewrite M.gso. eassumption.
              intros Heq; subst. now eauto with Ensembles_DB.
              reflexivity.
              econstructor; simpl; eauto.
              erewrite <- Forall2_length; [| eassumption ]. omega.
              rewrite <- !plus_n_O.
              eapply InvCostTimeout. eassumption.
              now rewrite cc_approx_val_eq. }
      (* Termination *) 
      - { simpl in Hcost.
          eapply Forall2_monotonic_strong in Hall; (* yiiiiiikes *)
            [| intros x1 x2 Hin1 Hin2 Hyp;
               eapply (cc_approx_var_env_heap_env_equiv
                         _ _
                         (occurs_free (Eapp f1 t xs1))
                         (occurs_free (AppClo f2 t xs2 f2' Γ))) in Hyp;
               [ now eapply Hyp | eassumption | eassumption 
                 | normalize_occurs_free; now eauto with Ensembles_DB
                 | unfold AppClo; repeat normalize_occurs_free; rewrite FromList_cons ];
             right; constructor;
             [ right; constructor;
               [ now eauto with Ensembles_DB
               | now intros Hc; inv Hc; eapply Hnin1; eauto ]
             | now intros Hc; inv Hc; eapply Hnin2; eauto ] ].
          edestruct (cc_approx_var_env_getlist IIG IG k rho1' rho2') as [vs2 [Hgetl' Hcc']];
            [ eassumption | now eauto |].
          edestruct Hvar as [l2 [Hget' Hcc]]; eauto.
          simpl in Hcc. rewrite Hgetl in Hcc. destruct l2 as [l2 | ]; [| contradiction ]. 
          destruct (get l2 H2') as [v |] eqn:Hget2; try contradiction.
          simpl in Hcc.
          destruct v as [ ? [| [| B2 f3 ] [| [ env_loc' |] [|] ]] | | ]; try contradiction.
          edestruct Hcc as (xs2' & e2 & rho2'' & Hfind' & Hset' & Hi'); try eassumption.
          reflexivity. reflexivity.
          edestruct (live_exists (env_locs rho2'' (occurs_free e2)) H2') as [H2'' Hgc'].
          edestruct Hi' with (i := k - cost (Eapp f1 t xs1)) as [r2 [c2 [m2 [Hbs2 [Hig Hcc2]]]]];
            [ | | | | | | eassumption | | ]. 
          + simpl. omega.
          + eapply Forall2_monotonic_strong; [| eassumption ].
            intros v v' Hinv Hinv' Heq. rewrite cc_approx_val_eq.
            eapply cc_approx_val_monotonic with (k := k).
            assert (Hrv : val_loc v \subset env_locs rho1' (occurs_free (Eapp f1 t xs1))).
            { normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. rewrite env_locs_FromList.
              simpl. eapply In_Union_list.
              eapply in_map. eassumption. eassumption. }
            assert (Hrv' : val_loc v' \subset env_locs rho2' (occurs_free (AppClo f2 t xs2 f2' Γ))).
            { unfold AppClo. repeat normalize_occurs_free.
              rewrite FromList_cons, !Setminus_Union_distr, !env_locs_Union.
              do 2 eapply Included_Union_preserv_r.
              eapply Included_Union_preserv_l. eapply Included_Union_preserv_r.
              rewrite !Setminus_Disjoint.
              rewrite env_locs_FromList.
              simpl. eapply In_Union_list.
              eapply in_map. eassumption. eassumption. 
              now eapply Disjoint_Singleton_r; intros Hc; eapply Hnin1; eauto.
              now eapply Disjoint_Singleton_r; intros Hc; inv Hc; eapply Hnin2; eauto. }
            eapply cc_approx_val_heap_monotonic;
              [ | | | | | now eapply HL.subheap_refl | ].
            * eapply well_formed_respects_heap_env_equiv in Hwf1; [| eassumption ].
              eapply well_formed_antimon; [| now apply Hwf1 ].
              now eapply reach'_set_monotonic.
            * eapply well_formed_respects_heap_env_equiv in Hwf2; [| eassumption ].
              eapply well_formed_antimon; [| now apply Hwf2 ].
              now eapply reach'_set_monotonic.
            * eapply Included_trans; [| eapply reachable_in_dom; try eassumption ].
              eapply Included_trans; [| now eapply reach'_extensive ].
              eassumption.
              eapply well_formed_respects_heap_env_equiv in Hwf1; [| eassumption ].
              eassumption.
              eapply env_locs_in_dom; eassumption.
            * eapply Included_trans; [| eapply reachable_in_dom; try eassumption ].
              eapply Included_trans; [| now eapply reach'_extensive ].
              eassumption.
              eapply well_formed_respects_heap_env_equiv in Hwf2; [| eassumption ].
              eassumption.
              eapply env_locs_in_dom; eassumption.
            * eapply def_funs_subheap. eauto.
            * eassumption.
            * simpl; omega.
          + eapply heap_env_equiv_heap_equiv.
            destruct Hgc as [? ?]. eassumption.
          + eapply heap_env_equiv_heap_equiv.
            destruct Hgc' as [? ?]. eassumption.
          + eapply IIL2inIIG.  
            eapply II_gc; [| eassumption | eassumption ].
            eapply IInvAppCompat; try eassumption.
          + simpl; omega.
          + intros i. edestruct (Hstuck1 (i + cost (Eapp f1 t xs1))) as [r' [m' Hstep']].
            inv Hstep'.
            * omega.
            * rewrite NPeano.Nat.add_sub in Hbs0. repeat subst_exp.
              eapply live_deterministic in Hgc0; [| now apply Hgc ].
              edestruct big_step_gc_heap_env_equiv as [r1 [m1 [Hgc1 _]]]. eassumption.
              eapply heap_env_equiv_heap_equiv. symmetry. eassumption.
              do 2 eexists. eassumption.
          + repeat eexists.
            * eapply Eval_proj_per_cc with (c := c2 + 1 + 1 + costCC (Eapp f2' t (Γ :: xs2))).
              simpl; omega.
              eassumption. eassumption. reflexivity.
              eapply Eval_proj_per_cc. simpl; omega.
              rewrite M.gso. eassumption.
              intros Hc. subst. eapply Hnin2. now left; eauto.
              eassumption. reflexivity.
              eapply Eval_app_per_cc. omega.
              rewrite M.gso. rewrite M.gss. reflexivity.
              now intros Hc; subst; eauto.
              eassumption.
              simpl. rewrite M.gss.
              rewrite !getlist_set_neq. now rewrite Hgetl'.
              intros Hc. eapply Hnin2. now eauto.
              intros Hc. eapply Hnin1. now eauto.
              now eauto. eassumption. reflexivity.
              replace (c2 + 1 + 1 + costCC (Eapp f2' t (Γ :: xs2))
                        - 1 - 1 - costCC (Eapp f2' t (Γ :: xs2))) with c2.
              eassumption. omega.
            * simpl.
              eapply InvCompat1_str_gc with (c2' := 1 + 1 + S (S (length xs2)));
                [ | | ].
              eapply IInvAppCompat; eassumption.
              replace (c2 + 1 + 1 + S (S (length xs2)) - (1 + 1 + S (S (length xs2)))) with c2 by omega. 
              eapply IGinILi. eassumption. simpl. rewrite <- !Hlen. simpl in Hleqc.
              omega.
            * rewrite cc_approx_val_eq in *. eapply cc_approx_val_monotonic.
              eassumption. simpl. omega. }
    Qed.
    
    Require Import L6.ctx.

    Fixpoint costCC_ctx_full (c : exp_ctx) : nat :=
      match c with
        | Econstr_c x t ys c => 1 + length ys + costCC_ctx_full c
        | Eproj_c x t n y c => 1 + costCC_ctx_full c
        | Efun1_c B c => 1 + costCC_ctx_full c (* XXX maybe revisit *)
        | Eprim_c x p ys c => 1 + length ys + costCC_ctx_full c
        | Hole_c => 0
        | Efun2_c _ _ => 0 (* maybe fix but not needed for now *)
        | Ecase_c _ _ _ _ _ => 0
      end.
    
    Fixpoint costCC_ctx (c : exp_ctx) : nat :=
      match c with
        | Econstr_c x t ys c => 1 + length ys
        | Eproj_c x t n y c => 1 
        | Efun1_c B c => 1
        | Eprim_c x p ys c => 1 + length ys
        | Hole_c => 0
        | Efun2_c _ _ => 0 (* maybe fix but not needed for now *)
        | Ecase_c _ _ _ _ _ => 0
      end.
    
   
    (* Interpretation of a context as a heap and an environment *) 
    Inductive ctx_to_heap_env : exp_ctx -> heap block -> env -> heap block -> env -> nat -> Prop :=
    | Hole_c_to_heap_env :
        forall H rho,
          ctx_to_heap_env Hole_c H rho H rho 0
    | Econstr_c_to_rho :
        forall H H' H'' rho rho' x t ys C vs l c,
          getlist ys rho = Some vs ->
          alloc (Constr t vs) H = (l, H') ->
          
          ctx_to_heap_env C H' (M.set x (Loc l) rho)  H'' rho'  c -> 
          
          ctx_to_heap_env (Econstr_c x t ys C) H rho H'' rho' (c + costCC_ctx (Econstr_c x t ys C))

    | Eproj_c_to_rho :
        forall H H' rho rho' x N t y C vs v t' l c,
          
          M.get y rho = Some (Loc l) ->
          get l H = Some (Constr t' vs) ->
          nthN vs N = Some v ->
          
          ctx_to_heap_env C H (M.set x v rho)  H' rho'  c -> 
          
          ctx_to_heap_env (Eproj_c x t N y C) H rho H' rho' (c + costCC_ctx (Eproj_c x t N y C)).


    Lemma comp_ctx_f_Hole_c C :
      comp_ctx_f C Hole_c = C
    with comp_f_ctx_f_Hole_c f : 
     comp_f_ctx_f f Hole_c = f.
    Proof.
      - destruct C; simpl; eauto;
        try (rewrite comp_ctx_f_Hole_c; reflexivity). 
        rewrite comp_f_ctx_f_Hole_c. reflexivity.
      - destruct f; simpl; eauto.
        rewrite comp_ctx_f_Hole_c; reflexivity.
        rewrite comp_f_ctx_f_Hole_c. reflexivity.
    Qed.
    

    Lemma cc_approx_exp_right_ctx_compat 
          (k : nat) rho1 rho2 rho2' H1 H2 H2' e1 C C' e2 c c' (II : exp_ctx -> IInv)
          (IInvCtxCompat :
             forall H1 H2 H2' rho1 rho2 rho2' e1 e2 C C' c, 
               II C' (H1, rho1, e1) (H2, rho2, C |[ e2 ]|) ->
               ctx_to_heap_env C H2 rho2 H2' rho2' c ->
               II (comp_ctx_f C' C) (H1, rho1, e1) (H2', rho2', e2)) :

      well_formed (reach' H1 (env_locs rho1 (occurs_free e1))) H1 ->
      well_formed (reach' H2 (env_locs rho2 (occurs_free (C |[ e2 ]|)))) H2 ->
      (env_locs rho1 (occurs_free e1)) \subset dom H1 ->
      (env_locs rho2 (occurs_free (C |[ e2 ]|))) \subset dom H2 ->

      ctx_to_heap_env C H2 rho2 H2' rho2' c' ->
      (e1, rho1, H1) ⪯ ^ (k; II (comp_ctx_f C' C) ; IIG ; ILi (c' + c) ; IG) (e2, rho2', H2') ->
      (e1, rho1, H1) ⪯ ^ (k ; II C' ; IIG ; ILi c ; IG) (C |[ e2 ]|, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hwf1 Hwf2 Henv1 Henv2 Hctx. revert c C'. induction Hctx; intros c1 C' Hpre.
      - intros ? ? ? ? ? ? ? ? ? ? ? ? ?. eapply Hpre; eauto.
        rewrite comp_ctx_f_Hole_c. eassumption.
      - rewrite <- plus_assoc in Hpre.
        replace (Econstr_c x t ys C) with (comp_ctx_f (Econstr_c x t ys Hole_c) C) in Hpre by reflexivity.
        rewrite <- comp_ctx_f_assoc with (c2 := Econstr_c x t ys Hole_c) in Hpre. 
        eapply IHHctx in Hpre.
        intros H1' H2' rho1' rho2' v1 k1 m1 Heq1 Heq2 HII Hleq1 Hstep1 Hstuck1.
        edestruct heap_env_equiv_env_getlist as [vs' [Hlst Hall]]; try eassumption.
        simpl. normalize_occurs_free...
        destruct (alloc (Constr t vs') H2') as [l2 H2''] eqn:Halloc.
        specialize (Hpre H1' H2'' rho1' (M.set x (Loc l2) rho2')).
        edestruct Hpre as [r1 [c3 [m2 [Hstep2 [Hinv Hccr]]]]]. 
        + eassumption.
        + eapply heap_env_equiv_alloc;
          [ | | | | | | | now apply H2 | now apply Halloc | ].
          eapply reach'_closed; try eassumption.
          eapply reach'_closed.
          eapply well_formed_respects_heap_env_equiv; eassumption.
          eapply env_locs_in_dom; eassumption.
          eapply Included_trans; [| now eapply reach'_extensive ].
          simpl. normalize_occurs_free.
          eapply env_locs_monotonic...
          eapply Included_trans; [| now eapply reach'_extensive ].
          simpl. normalize_occurs_free.
          eapply env_locs_monotonic...
          simpl.
          eapply Included_trans; [| now eapply reach'_extensive ].
          normalize_occurs_free. rewrite env_locs_Union.
          eapply Included_Union_preserv_l. rewrite env_locs_FromList.
          reflexivity. eassumption.
          simpl.
          eapply Included_trans; [| now eapply reach'_extensive ].
          normalize_occurs_free. rewrite env_locs_Union.
          eapply Included_Union_preserv_l. rewrite env_locs_FromList.
          reflexivity. eassumption.
          eapply heap_env_equiv_antimon. eassumption.
          simpl. normalize_occurs_free...
          split. reflexivity. eassumption.
        + eapply IInvCtxCompat with (C := Econstr_c x t ys Hole_c). eassumption. 
          econstructor. eassumption. eassumption. econstructor.
        + eassumption.
        + eassumption.
        + eassumption.
        + eexists. eexists (c3 + costCC (Econstr x t ys (C |[ e2 ]|))).
          eexists. split. simpl. eapply Eval_constr_per_cc; try eassumption.
          simpl. omega. simpl. rewrite NPeano.Nat.add_sub. eassumption.
          split; [| eassumption ].
          simpl. eapply InvTransfer. rewrite plus_comm.
          eassumption.
        + eapply well_formed_antimon with
          (S2 := reach' H' (env_locs (M.set x (Loc l) rho) (FromList ys :|: occurs_free (C |[ e2 ]|)))).
          eapply reach'_set_monotonic. eapply env_locs_monotonic...
          eapply well_formed_reach_alloc'; try eassumption.
          eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply env_locs_monotonic. 
          simpl. normalize_occurs_free... 
          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic. 
          simpl. normalize_occurs_free...
          eapply Included_trans; [| now eapply reach'_extensive ].
          rewrite env_locs_Union. 
          eapply Included_Union_preserv_l. rewrite env_locs_FromList.
          simpl. reflexivity. eassumption.
        + eapply Included_trans.
          eapply env_locs_set_Inlcuded'.
          rewrite HL.alloc_dom; try eassumption.
          eapply Included_Union_compat. reflexivity.
          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic. simpl. normalize_occurs_free...
      - rewrite <- plus_assoc in Hpre.
        replace (Eproj_c x t N y C) with (comp_ctx_f (Eproj_c x t N y Hole_c) C) in Hpre by reflexivity.
        rewrite <- comp_ctx_f_assoc with (c2 := Eproj_c x t N y Hole_c) in Hpre. 
        eapply IHHctx in Hpre.
        intros H1' H2' rho1' rho2' v1 k1 m1 Heq1 Heq2 HII Hleq1 Hstep1 Hstuck1.
        eapply Heq2 in H0; [| now constructor ].
        edestruct H0 as [l' [Hget' Heql]].
        rewrite res_equiv_eq in Heql. destruct l' as[l' |]; try contradiction.
        simpl in Heql. rewrite H2 in Heql. 
        destruct (get l' H2') eqn:Hgetl'; try contradiction.
        destruct b as [c' vs'| | ]; try contradiction.
        destruct Heql as [Heqt Hall]; subst.
        edestruct (Forall2_nthN _ vs vs' _ _ Hall H3) as [v' [Hnth' Hv]].
        specialize (Hpre H1' H2' rho1' (M.set x v' rho2')).
        edestruct Hpre as [r1 [c3 [m2 [Hstep2 [Hinv Hccr]]]]]. 
        + eassumption.
        + eapply heap_env_equiv_set; try eassumption.
          eapply heap_env_equiv_antimon. eassumption.
          simpl. normalize_occurs_free...
        + eapply IInvCtxCompat with (C := Eproj_c x t N y Hole_c). eassumption. 
          econstructor. eassumption. eassumption. eassumption. econstructor.
        + eassumption.
        + eassumption.
        + eassumption.
        + eexists. eexists (c3 + costCC_ctx (Eproj_c x t N y C)).
          eexists. split. simpl. eapply Eval_proj_per_cc; try eassumption.
          simpl. omega. simpl. rewrite NPeano.Nat.add_sub. eassumption.
          split; [| eassumption ].
          simpl. eapply InvTransfer. rewrite plus_comm. eassumption.
        + eapply well_formed_antimon with
          (S2 := reach' H (env_locs (M.set x v rho) ([set y] :|: occurs_free (C |[ e2 ]|)))).
          eapply reach'_set_monotonic. eapply env_locs_monotonic...
          eapply well_formed_reach_set'.
          eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply env_locs_monotonic. 
          simpl. normalize_occurs_free...
          rewrite env_locs_Union, reach'_Union.
          eapply Included_Union_preserv_l. rewrite env_locs_Singleton; eauto.
          eapply Included_trans; [| eapply Included_post_reach' ].
          simpl. rewrite post_Singleton; eauto. simpl.
          eapply In_Union_list. eapply in_map.
          eapply nthN_In; eassumption.
        + eapply Included_trans.
          eapply env_locs_set_Inlcuded'.
          eapply Union_Included.
          eapply Included_trans; [| eapply reachable_in_dom; eassumption ].
          simpl. normalize_occurs_free. rewrite env_locs_Union, reach'_Union.
          eapply Included_Union_preserv_l. rewrite env_locs_Singleton; eauto.
          eapply Included_trans; [| eapply Included_post_reach' ].
          simpl. rewrite post_Singleton; eauto. simpl.
          eapply In_Union_list. eapply in_map.
          eapply nthN_In; eassumption.
          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic. simpl. normalize_occurs_free...
    Qed.

End Compat.


