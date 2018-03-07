From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions closure_conversion closure_conversion_util
     closure_conversion_correct.

From L6.Heap Require Import heap heap_defs heap_equiv space_sem cc_log_rel size_cps.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module ClosureConversionCorrect (H : Heap).

  Module Size := Size H.
  
  Import H Size.Compat.LR.Sem.Equiv Size.Compat.LR.Sem.Equiv.Defs Size.Compat.LR.Sem Size.Compat.LR
         Size.Compat Size.
  
  Variable clo_tag : cTag.
  
  (** * Postcondition *)
  (** Enforces that the resource consumption of the target is within certain bounds *)
  Definition Post
             k (* time units already spent *)
             i (* step index *)
             (p1 p2 : heap block * env * exp * nat * nat) :=
    match p1, p2 with
      | (H1, rho1, e1, c1, m1), (H2, rho2, e2, c2, m2) =>
        c1 <= c2 + k <= 7 * c1 * (max_exp_env i H1 rho1 e1) + 7 * sizeOf_exp e1 /\
        m1 <= m2 <= 4 * m1 * (max_exp_env i H1 rho1 e1) + 4 * sizeOf_exp e1
    end.

  (** Enforces that the resource consumption of the target is within certain bounds *)
  Definition PostL
             k (* time units already spent *)
             i H1 rho1 e1
             (p1 p2 : nat * nat) :=
    match p1, p2 with
      | (c1, m1), (c2, m2) =>
        c1 <= c2 + k <= 7 * c1 * (max_exp_env i H1 rho1 e1) + 7 * sizeOf_exp e1 /\
        m1 <= m2 <= 4 * m1 * (max_exp_env i H1 rho1 e1) + 4 * sizeOf_exp e1
    end.
  
  (** * Precondition *)
  (** Enforces that the initial heaps have related sizes *)
  Definition Pre
             C (* Context already processed *)
             i (* step index *)
             (p1 p2 : heap block * env * exp) :=
    let m := cost_alloc_ctx C in 
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        size_heap H1 + m  <= size_heap H2 <=
        4 * (size_heap H1 + m) * (max_exp_env i H1 rho1 e1) + 4 * sizeOf_exp e1
    end.

  (** * Properties of the cost invariants *)

  (** Transfer units from the accumulator to the cost of e2 *)
  Lemma Post_transfer i (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp)
        (k c1 c2 c m1 m2 : nat) : 
    Post (k + c) i (H1, rho1, e1, c1, m1) (H2, rho2, e2, c2, m2) ->
    Post k i (H1, rho1, e1, c1, m1) (H2, rho2, e2, c2 + c, m2).
  Proof.
    simpl. intros H. omega.
  Qed.


  (** TODO move *)

  Lemma ctx_to_heap_env_size_heap C rho1 rho2 H1 H2 c :
    ctx_to_heap_env C H1 rho1 H2 rho2 c ->
    size_heap H2 = size_heap H1 + cost_alloc_ctx C.
  Proof.
    intros Hctx; induction Hctx; eauto.
    simpl. rewrite IHHctx.
    unfold size_heap.
    erewrite (HL.size_with_measure_alloc _ _ _ H H');
      [| reflexivity | eassumption ].
    erewrite getlist_length_eq; [| eassumption ].
    simpl. omega.
  Qed.

  (** Process the evaluation context of the right expression *)
  Lemma IP_ctx_to_heap_env
        i (H1 H2 H2' : heap block) (rho1 rho2 rho2' : env)
        (e1 e2 : exp) (C C' : exp_ctx) (c : nat) : 
    Pre C' i (H1, rho1, e1) (H2, rho2, C |[ e2 ]|) ->
    ctx_to_heap_env C H2 rho2 H2' rho2' c ->
    Pre (comp_ctx_f C' C) i (H1, rho1, e1) (H2', rho2', e2).
  Proof.
    intros [HP1 Hp2] Hctx. unfold Pre in *.
    erewrite (ctx_to_heap_env_size_heap C rho2 rho2' H2 H2'); [| eassumption ].
    rewrite cost_alloc_ctx_comp_ctx_f in *. split. omega.
    assert (Hgrt1 := max_exp_env_grt_1 i H1 rho1 e1).
    eapply le_trans. eapply plus_le_compat_r. eassumption.
    rewrite plus_assoc.
    rewrite <- (mult_assoc _ (size_heap H1 + cost_alloc_ctx C' + cost_alloc_ctx C)).
    rewrite Nat.mul_add_distr_r. rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_add_distr_l.  rewrite <- !plus_assoc. eapply plus_le_compat.
    rewrite <- Nat.mul_add_distr_l. rewrite <- mult_assoc. omega.
    rewrite plus_comm. eapply plus_le_compat_r.
    eapply le_trans;
      [| eapply mult_le_compat_l; eapply mult_le_compat_l; eassumption ].
    omega. 
  Qed.
  

  (** * Lemmas about [project_var] and [project_vars] *)
  
  Lemma project_var_get Scope Funs σ c Γ FVs S1 x x' C1 S2 rho1 H1 rho2 H2 m y:
    project_var clo_tag Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    ctx_to_heap_env C1 H1 rho1 H2 rho2 m ->
    ~ In _ S1 y ->
    M.get y rho1 = M.get y rho2. 
  Proof.
    intros Hvar Hctx Hin. inv Hvar.
    - inv Hctx. reflexivity.
    - inv Hctx.
      destruct (var_dec y x'); subst.
      contradiction.
      inv H16. now rewrite M.gso.
    - inv Hctx. inv H19.
      destruct (var_dec y x'); subst.
      contradiction.
      now rewrite M.gso.
  Qed.    
  
  Lemma project_vars_get Scope Funs σ c Γ FVs S1 xs xs' C1 S2 rho1 H1 rho2 H2 m y:
    project_vars clo_tag Scope Funs σ c Γ FVs S1 xs xs' C1 S2 ->
    ctx_to_heap_env C1 H1 rho1 H2 rho2 m ->
    ~ In _ S1 y ->
    M.get y rho1 = M.get y rho2. 
  Proof.
    revert Scope Funs Γ FVs S1 xs' C1 S2 rho1 H1 rho2 H2 m y.
    induction xs; intros Scope Funs Γ FVs S1 xs' C1 S2 rho1 H1 rho2 H2 m y Hproj Hctx Hnin.
    - inv Hproj. inv Hctx. reflexivity.
    - inv Hproj.  
      edestruct ctx_to_heap_env_comp_ctx_f_l as [rho'' [H'' [m1 [m2  [Hctx1 [Hctx2 Hadd]]]]]]; eauto.
      subst. eapply project_var_get in Hctx1; eauto.
      eapply IHxs in Hctx2; eauto.
      rewrite Hctx1, <- Hctx2. reflexivity.
      intros Hc. eapply Hnin.
      eapply project_var_free_set_Included; eassumption.
  Qed.
  
  Lemma project_var_getlist Scope Funs σ c Γ FVs S1 x x' C1 S2 rho1 H1 rho2 H2 m ys :
    project_var clo_tag Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    ctx_to_heap_env C1 H1 rho1 H2 rho2 m ->
    Disjoint _ S1 (FromList ys) ->
    getlist ys rho1 = getlist ys rho2. 
  Proof.
    revert rho1 H1 rho2 H2 m; induction ys; intros rho1 H1 rho2 H2 m Hproj Hctx Hnin.
    - reflexivity. 
    - simpl.
      rewrite FromList_cons in Hnin. eapply Disjoint_sym in Hnin.
      erewrite project_var_get; eauto.
      erewrite IHys; eauto.
      eapply Disjoint_sym. eapply Disjoint_Union_r. eassumption.
      intros Hc. eapply Hnin. eauto.
  Qed.        


  Lemma project_vars_getlist Scope Funs σ c Γ FVs S1 xs xs' C1 S2 rho1 H1 rho2 H2 m ys :
    project_vars clo_tag Scope Funs σ c Γ FVs S1 xs xs' C1 S2 ->
    ctx_to_heap_env C1 H1 rho1 H2 rho2 m ->
    Disjoint _ S1 (FromList ys) ->
    getlist ys rho1 = getlist ys rho2. 
  Proof.
    revert rho1 H1 rho2 H2 m; induction ys; intros rho1 H1 rho2 H2 m  Hproj Hctx Hnin.
    - reflexivity. 
    - simpl.
      rewrite FromList_cons in Hnin. eapply Disjoint_sym in Hnin. 
      erewrite project_vars_get; eauto.
      erewrite IHys; eauto.
      eapply Disjoint_sym. eapply Disjoint_Union_r. eassumption.
      intros Hc. eapply Hnin. eauto.
  Qed.        
  
  Lemma project_var_ctx_to_heap_env Scope Funs σ c Γ FVs x x' C S S' v1 rho1 rho2 H2:
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    Fun_inv_weak rho1 rho2 Scope Funs σ c Γ ->
    FV_inv_weak rho1 rho2 H2 Scope Funs c Γ FVs ->
    M.get x rho1 = Some v1 ->
    exists H2' rho2' s, ctx_to_heap_env C H2 rho2 H2' rho2' s.
  Proof.
    intros Hproj HFun HFV Hget. inv Hproj.
    - repeat eexists; econstructor; eauto.
    - edestruct HFun as
          [vf [venv [Hnin [Hget1 Hget2]]]]; eauto.
      destruct (alloc (Constr clo_tag [vf; venv]) H2) as [l' H2'] eqn:Hal.
      repeat eexists; econstructor; eauto.
      simpl. rewrite Hget2, Hget1. reflexivity. constructor.
    - edestruct HFV as [vs [l [v' [Hget1 [Hget2 Hnth']]]]]; eauto.
      repeat eexists. econstructor; eauto. constructor. 
  Qed.
  
  Lemma project_vars_ctx_to_heap_env Scope Funs σ c Γ FVs xs xs' C S S' vs1 rho1 rho2 H2:
    Disjoint _ S (Union var Scope
                        (Union var (image σ (Setminus _ Funs Scope))
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
    
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    Fun_inv_weak rho1 rho2 Scope Funs σ c Γ ->
    FV_inv_weak rho1 rho2 H2 Scope Funs c Γ FVs ->
    getlist xs rho1 = Some vs1 ->
    exists H2' rho2' s, ctx_to_heap_env C H2 rho2 H2' rho2' s.
  Proof.
    intros HD Hvars HFun HFV.
    (* assert (HD' := Hvars). *)
    revert Scope Funs Γ FVs xs' C S S' vs1
           rho1 rho2 H2 HD  Hvars HFun HFV.
    induction xs;
      intros Scope Funs Γ FVs xs' C S S' vs1
             rho1 rho2 H2 HD Hvars HFun HFV Hgetlist.
    - inv Hvars. repeat eexists; econstructor; eauto.
    - inv Hvars. simpl in Hgetlist.
      destruct (M.get a rho1) eqn:Hgeta1; try discriminate. 
      destruct (getlist xs rho1) eqn:Hgetlist1; try discriminate.
      edestruct project_var_ctx_to_heap_env with (rho1 := rho1) as [H2' [rho2' [s Hctx1]]]; eauto.
      inv Hgetlist.
      edestruct IHxs with (H2 := H2') (rho2 := rho2') as [H2'' [rho2'' [s' Hctx2]]]; [| eassumption | | | eassumption | ].
      + eapply Disjoint_Included_l; [| eassumption ].
        eapply project_var_free_set_Included. eassumption.
      + intros f v' Hnin Hin Hget.
        edestruct HFun as
            [vf [venv [Hnin' [Hget1 Hget2]]]]; eauto.
        repeat eexists; eauto.
        * erewrite <- project_var_get; try eassumption.
          intros Hin'. eapply HD. constructor. now eauto.
          right. left. eexists. now eauto.
        * erewrite <- project_var_get; try eassumption.
          intros Hin'. eapply HD. constructor. now eauto.
          right. right. right. reflexivity.
      + intros x N v' Hnin1 Hnin2 Hnth Hget.
        edestruct HFV as [vs [l' [v'' [Hget1 [Hget2 Hnth']]]]]; eauto.
        repeat eexists; eauto.
        * erewrite <- project_var_get; try eassumption.
          intros Hin'. eapply HD. constructor. now eauto.
          right. right. right. reflexivity.
        * erewrite ctx_to_heap_env_subheap. reflexivity.
          eassumption. eassumption.
      + exists H2'', rho2'', (s + s'). eapply ctx_to_heap_env_comp_ctx_f_r; eassumption.
  Qed.

  (** [project_var] preserves env_locs in dom *)
  Lemma project_var_env_locs Scope Funs σ c Γ FVs x x' C S S' e k rho H rho' H':
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    env_locs rho (occurs_free (C |[ e ]|)) \subset dom H ->
    env_locs rho' (occurs_free e) \subset dom  H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl; eauto.
    - inv H15.
      rewrite HL.alloc_dom; [| eassumption ].
      eapply Included_trans. eapply env_locs_set_Inlcuded'.
      eapply Included_Union_compat. reflexivity.
      eapply Included_trans; [| eassumption ]. simpl. normalize_occurs_free...
    - inv H18.
      eapply Included_trans. eapply env_locs_set_Inlcuded'.
      simpl. eapply Union_Included.
      + eapply Included_trans; [| eapply reachable_in_dom; eauto ].
        simpl. normalize_occurs_free.
        rewrite (reach_unfold H' (env_locs rho (Γ |: (occurs_free e \\ [set x'])))).
        eapply Included_Union_preserv_r. 
        eapply Included_trans; [| eapply reach'_extensive ]. rewrite !env_locs_Union, env_locs_Singleton; eauto.
        rewrite post_Union. eapply Included_Union_preserv_l. simpl.
        rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
      + eapply Included_trans; [| eassumption ]. simpl. normalize_occurs_free...
  Qed.

  (** [project_var] preserves well-formedness *)
  Lemma project_var_well_formed Scope Funs σ c Γ FVs x x' C S S' e k rho H rho' H':
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    (env_locs rho (occurs_free (C |[ e ]|))) \subset dom H ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    well_formed (reach' H' (env_locs rho' (occurs_free e))) H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl; eauto.
    - inv H15.
      eapply well_formed_antimon; [| eapply well_formed_reach_alloc; try eassumption ].
      + eapply reach'_set_monotonic. eapply env_locs_monotonic.
        simpl. normalize_occurs_free.
        rewrite <- Union_assoc.
        eapply Included_Union_preserv_r. eapply Included_Union_Setminus.
        now eauto with typeclass_instances.
      + simpl. normalize_occurs_free. rewrite env_locs_Union, reach'_Union; eauto.
        eapply Included_Union_preserv_l.
        rewrite !FromList_cons, !FromList_nil, !env_locs_Union, env_locs_Empty_set, Union_Empty_set_neut_r.
        simpl in *. destruct (M.get (σ x) rho) eqn:Hget; try congruence.
        destruct (M.get Γ rho) eqn:Hget'; try congruence. inv H13.
        simpl. rewrite Union_Empty_set_neut_r. rewrite !env_locs_Singleton; try eassumption.
        eapply reach'_extensive.
    - inv H18.
      eapply well_formed_antimon; [| eapply well_formed_reach_set; try eassumption ].
      + eapply reach'_set_monotonic. eapply env_locs_monotonic.
        simpl. normalize_occurs_free.
        rewrite <- Union_assoc.
        eapply Included_Union_preserv_r. eapply Included_Union_Setminus.
        now eauto with typeclass_instances.
      + simpl. eapply well_formed_antimon; try eassumption.
        simpl. normalize_occurs_free. rewrite (reach_unfold H' (env_locs rho (Γ |: (occurs_free e \\ [set x'])))).
        eapply Included_Union_preserv_r. 
        eapply reach'_set_monotonic. rewrite !env_locs_Union, env_locs_Singleton; eauto.
        rewrite post_Union. eapply Included_Union_preserv_l. simpl.
        rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
  Qed.

  Lemma project_vars_env_locs Scope Funs σ c Γ FVs xs xs' C S S' e k rho H rho' H':
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    env_locs rho (occurs_free (C |[ e ]|)) \subset dom H ->
    env_locs rho' (occurs_free e) \subset dom  H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho H rho' H' k e. 
    induction Hvar; intros rho1 H1 rho2 H2 k e Hctx Hlocs Hwf.
    - inv Hctx. simpl in *; eauto.
    - edestruct ctx_to_heap_env_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      rewrite <- app_ctx_f_fuse in *.
      eapply IHHvar; try eassumption.
      eapply project_var_well_formed; try eassumption.
      eapply project_var_env_locs; try eassumption. 
  Qed.
  
  
  Lemma project_vars_well_formed Scope Funs σ c Γ FVs xs xs' C S S' e k rho H rho' H':
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    (env_locs rho (occurs_free (C |[ e ]|))) \subset dom H ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    well_formed (reach' H' (env_locs rho' (occurs_free e))) H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho H rho' H' k e. 
    induction Hvar; intros rho1 H1 rho2 H2 k e Hctx Hlocs Hwf.
    - inv Hctx. simpl in *; eauto.
    - edestruct ctx_to_heap_env_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      rewrite <- app_ctx_f_fuse in *.
      eapply IHHvar; try eassumption.
      eapply project_var_env_locs; try eassumption.
      eapply project_var_well_formed; try eassumption. 
  Qed.
  
      
  (** * Lemmas about [Fun_inv] *)
  Lemma Fun_inv_weak_in_Fun_inv k P1 P2 rho1 H1 rho2 H2 β Scope Funs σ c Γ :
    Fun_inv k P1 P2 β rho1 H1 rho2 H2 Scope Funs σ c Γ ->
    Fun_inv_weak rho1 rho2 Scope Funs σ c Γ.
  Proof.
    intros HFun f v' Hnin Hin Hget.
    edestruct HFun as
        [vf [venv [Hnin' [Hget1 [Hget2 _]]]]]; eauto.
  Qed.

  (** * Lemmas about [FV_inv] *)
  Lemma FV_inv_weak_in_FV_inv k P1 P2 rho1 H1 rho2 H2 β Scope Funs c Γ FVs :
    FV_inv k P1 P2 β rho1 H1 rho2 H2 Scope Funs c Γ FVs ->
    FV_inv_weak rho1 rho2 H2 Scope Funs c Γ FVs.
  Proof.
    intros HFV x N v' Hnin1 Hnin2 Hnth Hget.
    edestruct HFV as [vs [l' [v'' [Hget1 [Hget2 [Hnth' _]]]]]]; eauto.
    firstorder.
  Qed.
  
  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct (k : nat) (H1 H2 : heap block)
        (rho1 rho2 : env) (e1 e2 : exp) (C : exp_ctx)
        (Scope Funs : Ensemble var) (FVs : list var)
        (σ : var -> var) (β : Inj) (c : cTag) (Γ : var) :
    (* [Scope] invariant *)
    (forall j, (H1, rho1) ⋞ ^ (Scope ; k ; j ; Pre Hole_c ; Post 0 ; β) (H2, rho2)) ->
    (* [Fun] invariant *)
    Fun_inv k (Pre Hole_c) (Post 0) β rho1 H1 rho2 H2 Scope Funs σ c Γ ->
    (* Free variables invariant *)
    FV_inv k (Pre Hole_c) (Post 0) β rho1 H1 rho2 H2 Scope Funs c Γ FVs ->
    (* location renaming is injective *)
    injective_subdomain (reach H1 (env_locs rho1 Scope)) β ->
    
    (* well-formedness *)
    well_formed (reach' H1 (env_locs rho1 (occurs_free e1))) H1 ->
    (env_locs rho1 (occurs_free e1)) \subset dom H1 ->
    well_formed (reach' H2 (env_locs rho2 (occurs_free (C |[ e2 ]|)))) H2 ->
    (env_locs rho2 (occurs_free (C |[ e2 ]|))) \subset dom H2 ->

    (* [Γ] (the current environment parameter) is not bound in e *)
    ~ In _ (bound_var e1) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e1) rho1 ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e1 ->
    (* function renaming is injective in the [Funs] subdomain *)
    injective_subdomain Funs σ ->
    (* function renaming codomain is not shadowed by other vars *)
    Disjoint _ (image σ (Setminus _ Funs Scope)) (bound_var e1) ->

    
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion clo_tag Scope Funs σ c Γ FVs e1 e2 C ->
    
    (forall j, (e1, rho1, H1) ⪯ ^ (k ; j ; Pre Hole_c k ; Pre Hole_c; PostL 0 k H1 rho1 e1 ; Post 0) (C |[ e2 ]|, rho2, H2)).
  Proof with now eauto with Ensembles_DB.
    revert H1 H2 rho1 rho2 e1 e2 C Scope Funs FVs σ β c Γ.
    induction k as [k IHk] using lt_wf_rec1.
    intros H1 H2 rho1 rho2 e1 e2 C Scope Funs FVs σ β c Γ
           Henv Hfun HFVs Hinjb Hwf1 Hlocs1 Hwf2 Hlos2 Hnin Hbind Hun Hinj Hd Hcc.
    induction e1 using exp_ind'; try clear IHe1.
    - (* case Econstr *)
      inv Hcc.
      
      edestruct (binding_in_map_getlist _ rho1 l Hbind) as [vl Hgetl].
      normalize_occurs_free...
      
      edestruct project_vars_ctx_to_heap_env as [H2' [rho2' [m Hct]]]; try eassumption.
      eapply Fun_inv_weak_in_Fun_inv; eassumption.
      eapply FV_inv_weak_in_FV_inv; eassumption.

      intros j.
      (* process right ctx *)
      eapply cc_approx_exp_right_ctx_compat
      with (ILi := fun c => PostL c k H1 rho1 (Econstr v t l e1)) (II := fun C => Pre C k);
        [ now intros; eapply Post_transfer; eauto | now intros; eapply IP_ctx_to_heap_env; eauto
          | eassumption | eassumption | eassumption | eassumption | eassumption | ].
      rewrite <- plus_n_O.
      replace (comp_ctx_f Hole_c C) with C by eauto.
      (* process Econstr one the right and left *)
      eapply cc_approx_exp_constr_compat
      with (ILi := fun c => PostL c k H1 rho1 (Econstr v t l e1))
           (r2 := 0)
           (IIL2 := Pre Hole_c (k - cost H1 rho1 (Econstr v t l e1)));
        [ | | | eassumption | | eassumption  | | | | ].
      + admit. (* bounds timeout compat *)
      + admit. (* bounds - pick F *)
      + admit. (* pre - allocation *) (* TODO maybe we need less assumptions *)
      + admit. (* well-formed project vars *)
      + admit. (* env_locs project vars *)
      + admit. (* project_vars_correct *)
      + admit. (* bounds -- find F *)
      + (* Inductive case *)
        intros vs1 vs2 l1 l2 H1' H2'' Hleq Ha1 Ha2 Hr1 Hr2 Hall.
        (* monotonicity of the local invariant *)
        eapply cc_approx_exp_rel_mon with (LP1 := PostL 0 (k - cost H1 rho1 (Econstr v t l e1)) H1' (M.set v (Loc l1) rho1) e1). 
        (* Induction hypothesis *)
        { eapply IHk;
          [ | | | | | | | | | | | | eassumption | | eassumption ].
          * simpl in *. omega.
          * admit. (* cc env set alloc *)
          * admit. (* fun inv env_set_alloc *)
          * admit. (* FV inv env set alloc *)
          * admit. (* inj subdomain extend *)
          * eapply well_formed_antimon;
            [| rewrite occurs_free_Econstr in Hwf1;
               eapply well_formed_reach_alloc'; try eassumption ]. 
            eapply reach'_set_monotonic. eapply env_locs_monotonic...
            eapply Included_trans; [| eassumption ]. normalize_occurs_free...
            rewrite env_locs_Union. eapply Included_trans. eassumption.
            normalize_occurs_free. rewrite env_locs_Union...
          * eapply Included_trans. now eapply env_locs_set_Inlcuded'.
            rewrite HL.alloc_dom; [| eassumption ].
            eapply Included_Union_compat. reflexivity.
            eapply Included_trans; [| eassumption ].
            normalize_occurs_free...
          * admit. (* need to prove WF for project vars first *)
          * eapply Included_trans. now eapply env_locs_set_Inlcuded'.
            rewrite HL.alloc_dom; [| eassumption ].
            eapply Included_Union_compat. reflexivity.
            (* need to prove env_locs for project vars first *)
            admit.
          * now eauto.
          * eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
            eapply occurs_free_Econstr_Included.
          * intros f Hfin. eauto.
          * eapply Disjoint_Included_r;
              [| eapply Disjoint_Included_l; [ apply image_monotonic | now apply Hd ]].
            normalize_bound_var... now eauto with Ensembles_DB. }
        { admit. }
        
    - (* case Eproj *)
      inv Hcc.
      admit.
      
    - (* case Ecase nil *)
      inv Hcc.
      admit.
    - (* case Ecase cons *)
      inv Hcc. (* TODO change compat *) 
      admit.
    - (* case Eproj *)
      inv Hcc.
      admit.
    - (* case Efun *)
      inv Hcc.
      admit.
    - (* case Eapp *)
      inv Hcc.
      admit.
    - (* case Eprim *)
      intros ? ? ? ? ? ? ? ? Hstep. inv Hstep.
    - (* case Ehalt *)
      inv Hcc.
      admit.
  Abort'