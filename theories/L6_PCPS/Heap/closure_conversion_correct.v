From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics.

From L6.Heap Require Import heap heap_defs heap_equiv space_sem cc_log_rel size_cps closure_conversion
     closure_conversion_util.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega Permutation.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module ClosureConversionCorrect (H : Heap).

   Module Size := Size H.
  
   Import H Size.Util.C.LR.Sem.Equiv Size.Util.C.LR.Sem.Equiv.Defs
          Size.Util.C.LR.Sem Size.Util.C.LR Size.Util.C Size.Util Size.
  
  (** Invariant about the free variables *) 
  Definition FV_inv (k j : nat) (IP : GIInv) (P : GInv) (b : Inj) (d : EInj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope : Ensemble var) (Γ : var) (FVs : list var) : Prop :=
    exists (vs : list value) (l : loc),
      M.get Γ rho2 = Some (Loc l) /\
      get l H2 = Some (Constr c vs) /\
      Forall2_P Scope
                (fun (x : var) (v2 : value)  =>
                   exists v1, M.get x rho1 = Some v1 /\
                         Res (v1, H1) ≺ ^ ( k ; j ; IP ; P ; b; d) Res (v2, H2)) FVs vs.

  
  (** Version without the logical relation. Useful when we're only interested in other invariants. *)
  
  (** Invariant about the free variables *) 
  Definition FV_inv_weak (rho1 : env) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope : Ensemble var) (Γ : var) (FVs : list var) : Prop :=
    exists (vs : list value) (l : loc),
      M.get Γ rho2 = Some (Loc l) /\
      get l H2 = Some (Constr c vs) /\
      Forall2_P Scope
                (fun (x : var) (v2 : value)  =>
                   exists v1, M.get x rho1 = Some v1) FVs vs.
  
  
  (** * Lemmas about [FV_inv] *)
  Lemma FV_inv_cc_approx_clos  (k j : nat) (IP : GIInv) (P : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Γ : var) (FVs : list var) l : 
    FV_inv k j IP P b d rho1 H1 rho2 H2 c (Empty_set _) Γ FVs ->
    M.get Γ rho2 = Some (Loc l) ->
    (rho1, H1) << ^ (k; j; IP; P; b; d; (FromList FVs)) (l, H2).
  Proof.
    intros (vs & l' & Hget1 & Hget2 & Hall) Hget1'. subst_exp.
    clear Hget1. eexists c, vs. setoid_rewrite Hget2. clear Hget2. 
    induction Hall.
    - eexists []. split. rewrite !FromList_nil. reflexivity.
      split. now constructor. split. reflexivity.
      constructor.
    - edestruct H as [v1 [Hget1 Hres1]]. intros Hc; now inv Hc.
      edestruct IHHall as (FLs & Heq & Hnd & Hget' & Hal').
      destruct v1 as [l1|]; try contradiction.
      destruct y as [l2|]; try contradiction.  
      eexists (x :: FLs). split. rewrite !FromList_cons, Heq. reflexivity.
      split.
      admit. (* extra assumption *)
      split. reflexivity.
      econstructor.

      eexists; split. eassumption. rewrite cc_approx_val_eq. eassumption.

      eassumption. 
  Admitted.

  Lemma FV_inv_j_monotonic (k j' j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs ->
    j' <= j ->
    FV_inv k j' GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs.
  Proof.
    intros Hfv Hlt. 
    destruct Hfv as (v & vs & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros x1 x2 Hin1 Hin3 Hnp [v' [Hget Hres]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.

  Lemma FV_inv_monotonic (k k' j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs ->
    k' <= k ->
    FV_inv k' j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs.
  Proof.
    intros Hfv Hlt. 
    destruct Hfv as (v & vs & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros x1 x2 Hin1 Hin3 Hnp [v' [Hget Hres]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.
      
  Lemma FV_inv_weak_in_FV_inv k j P1 P2 rho1 H1 rho2 H2 β d c Scope Γ FVs :
    FV_inv k j P1 P2 β d rho1 H1 rho2 H2 c Scope Γ FVs ->
    FV_inv_weak rho1 rho2 H2 c Scope Γ FVs.
  Proof.
    intros (x1 & x2  & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros ? ? ? ? ? [? [? ? ]]. eexists; eauto.
  Qed.

  Lemma Forall2_P_exists
        {A B : Type} (P1 : A -> Prop) (P2 : A -> B -> Prop) (l1 : list A) (l2 : list B) (x : A) :
    List.In x l1 ->
    ~ P1 x ->
    Forall2_P P1 P2 l1 l2 ->
    exists y : B, List.In y l2 /\ P2 x y.
  Proof.
    intros Hin HP1 Hall. induction Hall.
    - inv Hin.
    - inv Hin.
      + eexists; split; eauto. now left.
      + edestruct IHHall as [z [Hinz Hp2]]; eauto.
        eexists. split. right. eassumption. 
        eassumption.
  Qed.

  Lemma FV_inv_image_reach k P1 P2 rho1 H1 rho2 H2 b d c
        Scope Γ FVs :
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Γ FVs) ->
    image b (reach' H1 (env_locs rho1 (FromList FVs \\ Scope)))
    :|: image' d (reach' H1 (env_locs rho1 (FromList FVs \\ Scope))) \subset
    reach' H2 (post H2 (env_locs rho2 [set Γ])).
  Proof.
    intros Hres l' [l'' [l [Hin Heq]] | l'' [l [Hin Heq]]].
    + destruct Hin as [n [_ Hp]].
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.

      edestruct (Hres n) as (vs1 & loc_env & Hget1 & Hget2 & Hall).
    
      rewrite env_locs_Singleton; eauto.
      simpl. rewrite post_Singleton; eauto. simpl. subst.

      destruct Hin as [y [Hin' Hall']].
      destruct (M.get y rho1) as [ [|] | ] eqn:Hgety; try inv Hall'. 
      
      inv Hin'.
      edestruct (@Forall2_P_exists loc) with (x := y) as [v2 [Hin'' Hv]]; try eassumption.
      
      destruct Hv as [v1' [Hgety' Hv]]. repeat subst_exp.
      edestruct v2 as [ l2' |]; try contradiction.
      
      eapply reach'_set_monotonic. 
      eapply In_Union_list. eapply in_map. eassumption. 
      eapply cc_approx_val_image_eq with (v1 := Loc l1); try eassumption;
      [| left; eexists; split; eauto; eexists; split; eauto; now constructor ].
      intros j.

      edestruct (Hres j) as (vs1' & loc_env' & Hget1' & Hget2' & Hall').
      repeat subst_exp.

      edestruct (@Forall2_P_exists loc) with (x := y) as [v2' [Hin2' Hv']]; [| | now apply Hall' |]; try eassumption.
      
      destruct Hv' as [v1' [Hgety' Hv']]. repeat subst_exp.

      assert (Heq1 : v2' = Loc (b l1)).
      { destruct v2'; try contradiction.
        destruct Hv' as [Heqv _]. subst. reflexivity. }

      assert (Heq2 : l2' = b l1).
      { destruct Hv as [Heqv _]. subst. reflexivity. }
      subst. repeat subst_exp. eassumption.

    + destruct Hin as [n [_ Hp]].
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      
      edestruct (Hres n) as (vs1 & loc_env & Hget1 & Hget2 & Hall).
    
      rewrite env_locs_Singleton; eauto.
      simpl. rewrite post_Singleton; eauto. simpl. subst.
      
      destruct Hin as [y [Hin' Hall']].
      destruct (M.get y rho1) as [ [|] | ] eqn:Hgety; try inv Hall'. 
      
      inv Hin'.
      edestruct (@Forall2_P_exists loc) with (x := y) as [v2 [Hin'' Hv]]; try eassumption.
      
      destruct Hv as [v1' [Hgety' Hv]]. repeat subst_exp.
      edestruct v2 as [ l2' |]; try contradiction.
      
      eapply reach'_set_monotonic. 
      eapply In_Union_list. eapply in_map. eassumption. 
      eapply cc_approx_val_image_eq with (v1 := Loc l1); try eassumption;
      [| right; eexists; split; eauto; eexists; split; eauto; now constructor ].

      intros j.
      
      edestruct (Hres j) as (vs1' & loc_env' & Hget1' & Hget2' & Hall').
      repeat subst_exp.

      edestruct (@Forall2_P_exists loc) with (x := y) as [v2' [Hin2' Hv']]; [| | now apply Hall' |]; try eassumption.
      
      destruct Hv' as [v1' [Hgety' Hv']]. repeat subst_exp.

      assert (Heq1 : v2' = Loc (b l1)).
      { destruct v2'; try contradiction.
        destruct Hv' as [Heqv _]. subst. reflexivity. }

      assert (Heq2 : l2' = b l1).
      { destruct Hv as [Heqv _]. subst. reflexivity. }
      subst. repeat subst_exp. eassumption.
  Qed. 

  Lemma FV_inv_set_not_in_FVs_l (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope : Ensemble var) (Γ : var) (FVs : list var) x v  :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs ->
    ~ x \in (FromList FVs \\ Scope) ->
    FV_inv k j GII GI b d (M.set x v rho1) H1 rho2 H2 c Scope Γ FVs.
  Proof.
    intros (x1 & x2 & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros y1 v2 Hin Hnin Hp [v1 [Hget Hall1]].
    eexists; split; eauto.
    rewrite M.gso; eauto.
    intros Hc; subst. eapply H; constructor; eauto. 
  Qed.

  Lemma FV_inv_set_not_in_FVs_r (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope : Ensemble var) (Γ : var) (FVs : list var) x v  :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs ->
    x <> Γ ->
    FV_inv k j GII GI b d rho1 H1 (M.set x v rho2) H2 c Scope Γ FVs.
  Proof.
    intros (x1 & x2 & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    rewrite M.gso; eauto.
  Qed. 
  
  Lemma FV_inv_set_not_in_FVs (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope : Ensemble var) (Γ : var) (FVs : list var) x y v v'  :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs ->
    ~ x \in (FromList FVs \\ Scope) ->
    y <> Γ ->
    FV_inv k j GII GI b d (M.set x v rho1) H1 (M.set y v' rho2) H2 c Scope Γ FVs.
  Proof.
    intros. eapply FV_inv_set_not_in_FVs_r; eauto.
    eapply FV_inv_set_not_in_FVs_l; eauto.
  Qed.
  

  (** [FV_inv] is heap monotonic  *)
  Lemma FV_inv_heap_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 H1' : heap block) (rho2 : env) (H2 H2' : heap block)
        (c : cTag) (Scope : Ensemble var) (Γ : var) (FVs : list var) :
    well_formed (reach' H1 (env_locs rho1 (FromList FVs \\ Scope))) H1 ->
    well_formed (reach' H2 (env_locs rho2 [set Γ])) H2 ->
    env_locs rho1 (FromList FVs \\ Scope) \subset dom H1 ->
    env_locs rho2 [set Γ] \subset dom H2 ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs ->
    FV_inv k j GII GI b d rho1 H1' rho2 H2' c Scope Γ FVs.
  Proof.
    intros Hw1 Hw2 He1 He2 Hs1 Hs2.
    intros (x1 & x2 & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros y1 v2 Hin1 Hin2 Hp [v1 [Hget3 Hrel]].
    eexists; split; eauto. 
    eapply cc_approx_val_heap_monotonic; try eassumption.
    eapply well_formed_antimon; [| eassumption ].
    eapply reach'_set_monotonic.
    eapply Included_trans;
      [| eapply env_locs_monotonic; eapply Singleton_Included ].
    rewrite env_locs_Singleton; eauto. reflexivity.
    now constructor; eauto.
    eapply well_formed_antimon; [| eassumption ].
    rewrite (reach_unfold H2 (env_locs rho2 [set Γ])).
    eapply Included_Union_preserv_r.
    eapply reach'_set_monotonic.
    rewrite env_locs_Singleton; eauto.
    simpl. rewrite post_Singleton; eauto.
    eapply In_Union_list. eapply in_map.
    eassumption.
    eapply Included_trans; [| eassumption ].
    eapply Included_trans; [| eapply env_locs_monotonic; eapply Singleton_Included ].
    rewrite env_locs_Singleton; eauto. reflexivity.
    now constructor; eauto.
    eapply Included_trans; [| eapply reachable_in_dom; eassumption ].
    rewrite (reach_unfold H2 (env_locs rho2 [set Γ])).
    eapply Included_Union_preserv_r.
    eapply Included_trans; [| eapply reach'_extensive ].
    rewrite env_locs_Singleton; eauto.
    simpl. rewrite post_Singleton; eauto.
    eapply In_Union_list. eapply in_map.
    eassumption.
  Qed.
  
  (** [FV_inv] under rename extension  *)
  Lemma FV_inv_rename_ext (k j : nat) (GII : GIInv) (GI : GInv) (b b' : Inj) (d d' : EInj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env) 
        (c : cTag) (Scope : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (FromList FVs \\ Scope))) b' b ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (FromList FVs \\ Scope))) d' d ->
    FV_inv k j GII GI b' d' rho1 H1 rho2 H2 c Scope Γ FVs.
  Proof.
    intros (x1 & x2 & Hget1 & Hget2 & Hall) Hfeq.
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros y1 v2 Hin1 Hin2 Hp [v1 [Hget3 Hrel]].
    eexists; split; eauto.
    eapply cc_approx_val_rename_ext; try eassumption.
    eapply f_eq_subdomain_antimon; try eassumption.
    eapply reach'_set_monotonic.
    eapply get_In_env_locs; eauto.
    constructor; eauto.
    eapply f_eq_subdomain_antimon; try eassumption.
    eapply reach'_set_monotonic.
    eapply get_In_env_locs; eauto.
    constructor; eauto. 
  Qed.


  (** [FV_inv] monotonic *)
  Lemma FV_inv_Scope_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env) 
        (c : cTag) (Scope Scope' : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs ->
    Scope \subset Scope' -> 
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope' Γ FVs.
  Proof.
    intros (x1 & x2 & Hget1 & Hget2 & Hall) Hfeq.
    repeat eexists; eauto. eapply Forall2_P_monotonic. eassumption.
    now eauto with Ensembles_DB. 
  Qed.
  
  
  (** * Lemmas about [project_var] and [project_vars] *)
  
    
  Lemma project_var_ctx_to_heap_env Scope c Γ FVs x x' C S S' v1 rho1 rho2 H2:
    project_var Scope c Γ FVs S x x' C S' ->
    FV_inv_weak rho1 rho2 H2 c Scope Γ FVs ->
    M.get x rho1 = Some v1 ->
    exists H2' rho2' s, ctx_to_heap_env_CC C H2 rho2 H2' rho2' s.
  Proof.
    intros Hproj HFV Hget. inv Hproj.
    - repeat eexists; econstructor; eauto.
    - edestruct HFV as (v & vs  & Hget1 & Hget2 & Hall).
      edestruct Forall2_P_nthN as [v2 [Hnth Hr]]; eauto.
      repeat eexists. econstructor; eauto.
      constructor.
  Qed.
  
  Lemma project_vars_ctx_to_heap_env Scope c Γ FVs xs xs' C S S' vs1 rho1 rho2 H2:
    Disjoint _ S (FV_cc Scope Γ) ->
    
    project_vars Scope c Γ FVs S xs xs' C S' ->
    FV_inv_weak rho1 rho2 H2 c Scope Γ FVs ->
    getlist xs rho1 = Some vs1 ->
    exists H2' rho2' s, ctx_to_heap_env_CC C H2 rho2 H2' rho2' s.
  Proof.
    intros HD Hvars HFV.
    revert Scope Γ FVs xs' C S S' vs1
           rho1 rho2 H2 HD  Hvars HFV.
    induction xs;
      intros Scope Γ FVs xs' C S S' vs1
             rho1 rho2 H2 HD Hvars HFV Hgetlist.
    - inv Hvars. repeat eexists; econstructor; eauto.
    - inv Hvars. simpl in Hgetlist.
      destruct (M.get a rho1) eqn:Hgeta1; try discriminate.
      destruct (getlist xs rho1) eqn:Hgetlist1; try discriminate.
      edestruct project_var_ctx_to_heap_env with (rho1 := rho1) as [H2' [rho2' [s Hctx1]]]; eauto.
      inv Hgetlist.
      edestruct IHxs with (H2 := H2') (rho2 := rho2') as [H2'' [rho2'' [s' Hctx2]]]; [| eassumption | | eassumption | ].
      + eapply Disjoint_Included_l; [| eassumption ].
        eapply project_var_free_set_Included. eassumption.
      + edestruct HFV as [v' [vs [Hget [Hget1 Hall]]]]; eauto.
        repeat eexists; eauto.
        * erewrite <- project_var_get; try eassumption.
          intros Hin'. eapply HD. constructor. now eauto.
          right. reflexivity.
        * erewrite <- (project_var_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ H7). eassumption.
          eassumption.
      + exists H2'', rho2'', (s + s'). eapply ctx_to_heap_env_CC_comp_ctx_f_r; eassumption.
  Qed.
  

  Lemma project_var_preserves_cc_approx GII GI k j H1 rho1 H2 rho2 H2' rho2' b d
        Scope c Γ FVs x x' C S S' m y y' :
    project_var Scope c Γ FVs S x x' C S' ->
    cc_approx_var_env k j GII GI b d H1 rho1 H2 rho2 y y' ->
    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->
    ~ y' \in S ->
    cc_approx_var_env k j GII GI b d H1 rho1 H2' rho2' y y'.
  Proof.     
    intros Hproj Hcc Hctx Hnin.
    destruct Hproj; inv Hctx; eauto.
    - inv H18. eapply cc_approx_var_env_set_neq_r; eauto.
      intros Hc; subst; eauto.
  Qed.
  
  Lemma project_vars_preserves_cc_approx GII GI k j H1 rho1 H2 rho2 H2' rho2' b d
        Scope c Γ FVs xs xs' C S S' m y y' :
    project_vars Scope c Γ FVs S xs xs' C S' ->
    cc_approx_var_env k j GII GI b d H1 rho1 H2 rho2 y y' ->
    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->
    ~ y' \in S ->
    cc_approx_var_env k j GII GI b d H1 rho1 H2' rho2' y y'.
  Proof.
    intros Hvars. revert m H1 rho1 H2 rho2 H2' rho2'.
    induction Hvars; intros m H1 rho1 H2 rho2 H2' rho2' Hcc Hctx Hnin.
    - inv Hctx. eassumption.
    - edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]]; eauto.
      subst.
      eapply IHHvars; [| eassumption | ].
      eapply project_var_preserves_cc_approx; try eassumption.
      intros Hc.
      eapply Hnin. eapply project_var_free_set_Included; eauto.
  Qed.  

  (** Correctness of [project_var] *)
  Lemma project_var_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b d
        Scope c Γ FVs x x' C S S' m :
    project_var Scope c Γ FVs S x x' C S' ->
    
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b; d) (H2, rho2)) ->
    (forall j, FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs) ->

    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->
    
    binding_in_map Scope rho1 ->
    Disjoint _ S (FV_cc Scope Γ) ->

    ~ In _ S' x' /\
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b; d) (H2', rho2'))  /\
    (forall j, FV_inv k j GII GI b d rho1 H1 rho2' H2' c Scope Γ FVs) /\
    (forall j, cc_approx_var_env k j GII GI b d H1 rho1 H2' rho2' x x').

  Proof with (now eauto with Ensembles_DB).
    intros Hproj Hcc Henv Hctx Hbin Hd.
    inv Hproj.
    - inv Hctx. split. intros Hc. eapply Hd; eauto. constructor; eauto. left; eauto.
      split; [| split ]; eauto.
      intros j; eapply Hcc. eassumption.
    - inv Hctx. inv H18.
      split; [| split; [| split ]]. repeat split.
      + intros Hc. inv Hc. eauto.
      + intros j. eapply cc_approx_env_P_set_not_in_P_r. now eauto.
        intros Hc. eapply Hd; eauto. constructor; eauto.
        left; eauto.
      + intros h. 
        edestruct Henv as (v1 & vs1 & Hget1 & Hget2 & Hall).
        repeat eexists; eauto. 
        rewrite M.gso; eauto. intros Heq; subst. eapply Hd. constructor; eauto.
        right. reflexivity.
      + intros j v' Hget.
        edestruct (Henv j) as (v1 & vs1 & Hget1 & Hget2 & Hall).
        eexists. rewrite M.gss. split. reflexivity.
        edestruct (Forall2_P_nthN _ _ _ _ FVs _ N _ Hall H0) as (v2 & Hnth' & vs4 & Hget4 & Hrel).
        eassumption. repeat subst_exp. eassumption.
  Qed.
  
  (** Correctness of [project_vars] *)
  Lemma project_vars_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b d
        Scope c Γ FVs xs xs' C S S' m :
    project_vars Scope c Γ FVs S xs xs' C S' ->
    
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b; d) (H2, rho2)) ->
    (forall j, FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Γ FVs) ->

    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->

    binding_in_map Scope rho1 -> 
    Disjoint _ S (FV_cc Scope Γ) ->

    Disjoint _ (FromList xs') S' /\
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b; d) (H2', rho2'))  /\
    (forall j, FV_inv k j GII GI b d rho1 H1 rho2' H2' c Scope Γ FVs) /\
    (forall j, Forall2 (fun x x' => cc_approx_var_env k j GII GI b d H1 rho1 H2' rho2' x x') xs xs').
  Proof with (now eauto with Ensembles_DB).
    intros Hvars. revert m H1 rho1 H2 rho2 H2' rho2'.
    induction Hvars; intros m H1 rho1 H2 rho2 H2' rho2' Hcc Hfv Hctx Hb Hd. 
    - inv Hctx. split; [| split; [| split ]]; eauto.
      rewrite FromList_nil...
    - rewrite FromList_cons in *. 
      edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      subst.
      eassumption. subst.
      edestruct project_var_correct as (Hd' & Hcc' & Hfv' & Hall');
        try eassumption.
      edestruct IHHvars as (Hd'' & Hcc'' & Hfv'' & Hall'');
      try eassumption.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply project_var_free_set_Included. eassumption.
      split; [| split; [| split ]]; eauto.
      * eapply Union_Disjoint_l. 
        eapply Disjoint_Included_r.
        eapply project_vars_free_set_Included. eassumption.
        eapply Disjoint_Singleton_l. eassumption.
        eapply Disjoint_Included_r; [| eassumption ].
        unfold FV_cc...
      * intros j. constructor; eauto.
        eapply project_vars_preserves_cc_approx; eauto.
  Qed.

  (** [project_var] preserves injectiveness *)
  Lemma project_var_same_set
        Scope c Γ FVs x x' C S S'  :
    project_var Scope c Γ FVs S x x' C S' ->
    x |: (FV Scope FVs) <--> FV Scope FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hvar. rewrite Union_Same_set. reflexivity.
    eapply Singleton_Included. eapply project_var_In_Union.
    eassumption.
  Qed.

  Lemma project_vars_same_set
        Scope c Γ FVs x x' C S S'  :
    project_vars Scope c Γ FVs S x x' C S' ->
    (FromList x) :|: (FV Scope FVs) <--> FV Scope FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hvar. rewrite Union_Same_set. reflexivity.
    eapply project_vars_In_Union.
    eassumption.
  Qed. 
  

  Lemma heap_elements_filter_monotonic {A} S1 `{HS1 : ToMSet S1}  S2 `{HS2 : ToMSet S2} (H : heap A):  
    S1 \subset S2 ->
    Subperm (heap_elements_filter S1 H) (heap_elements_filter S2 H).
  Proof.
    intros Hsub. eapply incl_Subperm.
    eapply heap_elements_filter_NoDup.
    intros [l1 b] Hin. eapply heap_elements_filter_sound in Hin.
    destruct Hin as [Hget Hin].
    eapply heap_elements_filter_complete; eauto.
  Qed.
      
  Lemma size_wirh_measure_filter_monotonic {A} S1 `{HS1 : ToMSet S1}  S2 `{HS2 : ToMSet S2} (f : A -> nat) H :
    S1 \subset S2 ->
    size_with_measure_filter f S1 H <=
    size_with_measure_filter f S2 H.
  Proof.
    intros Hseq. 
    unfold size_with_measure_filter.
    eapply fold_left_subperm.
    constructor.
    now econstructor.
    intros ? ? ?. omega.
    intros. omega.
    intros. omega.
    intros. omega.
    eapply heap_elements_filter_monotonic. eassumption.
  Qed.

  Lemma cc_approx_val_size k j GIP GP b d H1 H2 x y v v' :
    Res (Loc x, H1) ≺ ^ (k; S j; GIP; GP; b; d) Res (Loc y, H2) ->
    get x H1 = Some v ->
    get y H2 = Some v' ->
    size_val v <= size_val v' <= (size_val v) *  (1 + max_vars_heap H1).
  Proof.
    intros Hres Hget1 Hget2. simpl in Hres. rewrite Hget1, Hget2 in Hres.
    destruct Hres as [Hbeq Hres]; subst.
    destruct v as [c1 vs1 | [| B1 f1] rho_clo ]; try contradiction;
    destruct v' as [c2 vs2 | ]; try contradiction.
    - destruct Hres as [Heq1 [Heq2 Hall]]; subst.
      simpl. specialize (Hall 0 (NPeano.Nat.lt_0_succ _)).
      erewrite (Forall2_length _ _ _ Hall).
      simpl.
      replace (length vs2 * S (max_vars_heap H1)) with
      (length vs2 + length vs2 * (max_vars_heap H1)).
      split. omega.
      eapply le_n_S.
      rewrite plus_comm. apply le_plus_trans. apply le_plus_trans.
      omega.
      
      replace (S (max_vars_heap H1)) with (1 + max_vars_heap H1) by omega.
      rewrite NPeano.Nat.mul_add_distr_l. omega.

    - simpl. split. omega.

      destruct vs2 as [| [|] [| [|] [|] ]]; try contradiction.

      destruct Hres as [Hdeq Hall].
      eapply le_n_S.
      rewrite <- plus_n_O. 
      eapply le_trans; [| eapply  max_vars_heap_get ]; eauto. simpl.
      omega.
  Qed.

  Lemma Forall2_length {A B} (R : A -> B -> Prop) l1 l2 :
    Forall2 R l1 l2 -> length l1 = length l2. 
  Proof.
    revert l2. induction l1 as [| x xs IHxs ]; intros l2 H.
    - inv H; eauto.
    - inv H. simpl. f_equal. eauto.
  Qed.

  
  Lemma cc_approx_val_size_env k j GIP GP b d H1 H2 x y v v' :
    Res (Loc x, H1) ≺ ^ (k; S j; GIP; GP; b; d) Res (Loc y, H2) ->
    get x H1 = Some v ->
    get y H2 = Some v' ->
    size_val v <=
    size_val v' + size_with_measure_filter size_val (image' d [set x]) H2 <=
    (size_val v) * (1 + max_vars_heap H1).
  Proof.
    intros Hres Hget1 Hget2. simpl in Hres. rewrite Hget1, Hget2 in Hres.
    destruct Hres as [Hbeq Hres]; subst.
    destruct v as [c1 vs1 | [| B1 f1] rho_clo ]; try contradiction;
    destruct v' as [c2 vs2 | ]; try contradiction.
    - destruct Hres as [Heq1 [Heq2 Hall]]; subst.
      simpl. specialize (Hall 0 (NPeano.Nat.lt_0_succ _)).
      erewrite (Forall2_length _ _ _ Hall).
      simpl.
      replace (length vs2 * S (max_vars_heap H1)) with
      (length vs2 + length vs2 * (max_vars_heap H1)).
      split. omega. 
      erewrite HL.size_with_measure_Same_set with (S' := Empty_set _);
        [| erewrite image'_Singleton_None; try eassumption; reflexivity ].
      rewrite HL.size_with_measure_filter_Empty_set. rewrite <- !plus_n_O.
      
      eapply le_n_S.  
      rewrite plus_comm. apply le_plus_trans.
      apply le_plus_trans.
      omega.
      
      replace (S (max_vars_heap H1)) with (1 + max_vars_heap H1) by omega.
      rewrite NPeano.Nat.mul_add_distr_l. omega.

    - simpl. split. omega.

      destruct vs2 as [| [|] [| [|] [|] ]]; try contradiction.
      
      destruct Hres as [Hdeq [Henv _]].
      eapply le_n_S.
      rewrite <- plus_n_O. simpl. 
      eapply le_trans; [| eapply  max_vars_heap_get ]; eauto. simpl.

      erewrite HL.size_with_measure_Same_set with (S' :=[set l] :|: Empty_set _);
        [| erewrite image'_Singleton_Some; try eassumption; now eauto with Ensembles_DB ].
      
      rewrite plus_comm. simpl.

      specialize (Henv 0 (NPeano.Nat.lt_0_succ _)).
      destruct Henv as (c & vs' & FLs & Heq & Hnd & Hget & Hall).
      
      do 2 eapply le_n_S.
      erewrite HL.size_with_measure_filter_add_In;
        [| intros Hc; now inv Hc | eassumption].
      rewrite HL.size_with_measure_filter_Empty_set. rewrite <- !plus_n_O.
      simpl. eapply le_n_S.
      erewrite <- Forall2_length; try eassumption.

      eapply le_trans. eapply occurs_free_fundefs_cardinality.
      now eapply Heq. eassumption. omega. 
  Qed.
  
  Lemma size_reachable_leq S1 `{HS1 : ToMSet S1}  S2 `{HS2 : ToMSet S2}
        H1 H2 k GIP GP b d :
    (forall j, S1 |- H1 ≼ ^ (k ; j ; GIP ; GP ; b ; d ) H2) ->
    (* image b S1 \subset S2 -> *)
    S2 <--> image b S1 :|: image' d S1 ->
    injective_subdomain S1 b ->
    (* injective_subdomain' S1 d -> *)
    Disjoint _ (image b S1) (image' d S1) ->
    size_with_measure_filter size_val S1 H1 <=
    size_with_measure_filter size_val S2 H2 <=
    size_with_measure_filter size_val S1 H1 * (1 + (max_vars_heap H1)).
  Proof with (now eauto with Ensembles_DB).
    assert (HS1' := HS1).
    revert HS1 S2 HS2.
    set (P := (fun S1 => 
                 forall (HS1 : ToMSet S1) (S2 : Ensemble positive) (HS2 : ToMSet S2),
                   (forall j, S1 |- H1 ≼ ^ (k; j; GIP; GP; b; d) H2) ->
                   S2 <--> image b S1 :|: image' d S1 ->
                   injective_subdomain S1 b ->
                   Disjoint _ (image b S1) (image' d S1) ->
                   size_with_measure_filter size_val S1 H1 <=
                   size_with_measure_filter size_val S2 H2 <=
                   (size_with_measure_filter size_val S1 H1) * (1 + (max_vars_heap H1))
              )). 
    assert (HP : Proper (Same_set var ==> iff) P).
    { intros S1' S2' Hseq. unfold P.
      split; intros.
      
      assert (HMS1' : ToMSet S1').
      { eapply ToMSet_Same_set. symmetry. eassumption. eassumption. }
      erewrite <- (@HL.size_with_measure_Same_set _ _ _ _ _ _ _ Hseq).
      eapply H; try eassumption; repeat setoid_rewrite Hseq at 1; try eassumption.

      assert (HMS2' : ToMSet S2').
      { eapply ToMSet_Same_set; eassumption. }
      erewrite (@HL.size_with_measure_Same_set _ _ _ _ _ _ _ Hseq).
      eapply H; try eassumption; repeat setoid_rewrite <- Hseq at 1; try eassumption. }
    
    eapply (@Ensemble_ind P HP); [| | eassumption ].
    - intros HS1 S2 HS2 Hcc Heq1 Hinj1 HD.
      rewrite !HL.size_with_measure_filter_Empty_set.
      rewrite image_Empty_set, image'_Empty_set in Heq1.
      rewrite Union_Empty_set_neut_r in Heq1.
      (* simpl. *)
      (* eapply Included_Empty_set_l in Hsub2. symmetry in Hsub2. *)
      erewrite (@HL.size_with_measure_Same_set _ _ _ _ _ _ _ Heq1).
      rewrite HL.size_with_measure_filter_Empty_set. omega.
    - intros x S1' HS Hnin IHS HS1 S2 HS2 Hheap Heq1 Hinj1 HD.
      rewrite !image_Union, !image'_Union, !image_Singleton in Heq1.
      
      assert (Hseq : S2 <--> b x |: (S2 \\ [set b x])).
      { eapply Union_Setminus_Same_set; tci.
        rewrite Heq1... }
      
      erewrite (HL.size_with_measure_Same_set _ S2 (b x |: (S2 \\ [set b x])));
        try eassumption.
      
      assert (Hcc : (forall j, Res (Loc x, H1) ≺ ^ (k ; j ; GIP ; GP ; b ; d) Res (Loc (b x), H2))).
      { intros j; eapply Hheap. now left. }

      destruct (get x H1) as [v | ] eqn:Hget1;
        [| destruct (Hcc 0) as [_ Hcc']; rewrite Hget1 in Hcc'; contradiction ].
      destruct (get (b x) H2) as [v' | ] eqn:Hget2;
        [| destruct (Hcc 0) as [_ Hcc']; rewrite Hget1, Hget2 in Hcc';
           destruct v as [ | [|] ]; try contradiction ].
      
      erewrite !HL.size_with_measure_filter_add_In; try eassumption;
      [| intros Hc; inv Hc; now eauto ].

      
      assert (Himbeq : image b S1' \\ [set b x] <--> image b S1').
      { rewrite Setminus_Disjoint. reflexivity.
        rewrite <- image_Singleton.
        eapply injective_subdomain_Union_not_In_image.
        eapply injective_subdomain_antimon; [ eassumption |]...
        eapply Disjoint_Singleton_r. eassumption. }
      
      destruct (d x) as [env_loc |] eqn:Hdx.
      + assert (Hdec : Decidable (image' d S1')) by tci.
        
        destruct Hdec as [Hdec]. destruct (Hdec env_loc).

        * assert (Hyp : size_with_measure_filter size_val S1' H1 <=
                        size_with_measure_filter size_val (S2 \\ [set b x]) H2 <=
                        size_with_measure_filter size_val S1' H1 * (1 + max_vars_heap H1)).
          { eapply IHS.
            - intros j. eapply cc_approx_heap_antimon; [| eapply Hheap ]...
            - rewrite Heq1.
              rewrite Setminus_Union_distr. rewrite Setminus_Union_distr, Himbeq.
              rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
              rewrite Setminus_Disjoint. rewrite image'_Singleton_Some; eauto.
              rewrite (Union_Same_set [set env_loc]); [| now eauto with Ensembles_DB ]. reflexivity.
              rewrite <- image'_Union.
              eapply Disjoint_sym. eapply Disjoint_Included; [ | | eassumption ].
              eapply image'_monotonic...
              rewrite <- image_Singleton. eapply image_monotonic...
            - eapply injective_subdomain_antimon; [ eassumption |]...
            - eapply Disjoint_Included; [ | | eassumption ].
              eapply image'_monotonic...
              eapply image_monotonic...
          }
  
          assert (Hleqv : size_val v <= size_val v' <= (size_val v) *  (1 + max_vars_heap H1)).
          { eapply (cc_approx_val_size k 0); try eassumption.
            apply Hheap. now left. } 
          
          split. omega.
          rewrite Nat.mul_add_distr_r. omega.

        * assert (Hyp : size_with_measure_filter size_val S1' H1 <=
                        size_with_measure_filter size_val (S2 \\ [set b x] \\ [set env_loc]) H2 <=
                        size_with_measure_filter size_val S1' H1 * (1 + max_vars_heap H1)).
          { eapply IHS.
            - intros j. eapply cc_approx_heap_antimon; [| eapply Hheap ]...
            - rewrite Heq1.
              rewrite Setminus_Union_distr. rewrite Setminus_Union_distr. rewrite Setminus_Union_distr.
              rewrite Himbeq.
              
              rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
              rewrite Setminus_Disjoint.
              
              rewrite Setminus_Union_distr.
              rewrite Setminus_Union_distr.

              
              rewrite Setminus_Included_Empty_set. rewrite Union_Empty_set_neut_l.
              
              rewrite Setminus_Disjoint.
              rewrite Setminus_Disjoint.
              reflexivity.
              eapply Disjoint_sym. eapply Disjoint_Included; [ | | eassumption ].
              eapply image'_monotonic...
              rewrite <- image_Singleton. eapply image_monotonic...
              
              eapply Disjoint_Singleton_r. intros Hc. inv Hc. now eapply n; eauto.

              rewrite image'_Singleton_Some; eauto...

              eapply Disjoint_Included; [ | | eassumption ].
              rewrite image'_Union, image'_Singleton_Some; eauto...
              eapply image_monotonic...
            - eapply injective_subdomain_antimon; [ eassumption |]...
            - eapply Disjoint_Included; [ | | eassumption ].
              eapply image'_monotonic...
              eapply image_monotonic... }
          
          assert (Hseq' : (S2 \\ [set b x]) <--> env_loc |: (S2 \\ [set b x] \\ [set env_loc])).
          { rewrite <- Union_Setminus_Same_set; tci. reflexivity.
            rewrite Heq1. rewrite image'_Singleton_Some; eauto.
            rewrite !Setminus_Union_distr.
            eapply Included_Union_preserv_r. eapply Included_Union_preserv_l.
            rewrite Setminus_Disjoint. reflexivity.
            eapply Disjoint_sym.
            eapply Disjoint_Included; [ | | eassumption ].
            rewrite image'_Union, image'_Singleton_Some; eauto...
            rewrite <- image_Singleton. eapply image_monotonic... }
          erewrite (HL.size_with_measure_Same_set _ _ _ _ _ Hseq').
          erewrite HL.size_with_measure_filter_Union; [| now eauto with Ensembles_DB ].

          rewrite plus_assoc.  
          assert (Hleqv : size_val v <=
                          size_val v' + size_with_measure_filter size_val [set env_loc] H2 <=
                          (size_val v) *  (1 + max_vars_heap H1)).
          { erewrite (HL.size_with_measure_Same_set _ [set env_loc] (image' d [set x])).
            eapply (cc_approx_val_size_env k 0); try eassumption.
            eapply Hheap. now left.
            now rewrite image'_Singleton_Some; eauto. 
          }
          split. omega.
          rewrite Nat.mul_add_distr_r. omega. 
      + assert (Hyp : size_with_measure_filter size_val S1' H1 <=
                        size_with_measure_filter size_val (S2 \\ [set b x]) H2 <=
                        size_with_measure_filter size_val S1' H1 * (1 + max_vars_heap H1)).
          { eapply IHS.
            - intros j. eapply cc_approx_heap_antimon; [| eapply Hheap ]...
            - rewrite Heq1.
              rewrite Setminus_Union_distr. rewrite Setminus_Union_distr, Himbeq.
              rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
              rewrite Setminus_Disjoint. rewrite image'_Singleton_None; eauto...
              eapply Disjoint_sym. eapply Disjoint_Included; [ | | eassumption ].
              rewrite <- image'_Union...
              rewrite <- image_Singleton. eapply image_monotonic...
            - eapply injective_subdomain_antimon; [ eassumption |]...
            - eapply Disjoint_Included; [ | | eassumption ].
              eapply image'_monotonic...
              eapply image_monotonic...
          }

          assert (Hleqv : size_val v <= size_val v' <= (size_val v) * (1 + max_vars_heap H1)).
          { eapply (cc_approx_val_size k 0); try eassumption.
            eapply Hheap. now left. }
          split. omega.
          rewrite Nat.mul_add_distr_r. omega. 
  Qed.
    
  

  Lemma make_closures_env_locs_well_formed B Γ C H rho H' rho' k S :
    make_closures Size.Util.clo_tag B Γ C ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    name_in_fundefs B \subset S ->
    Γ \in S ->
    env_locs rho S \subset dom H ->
    well_formed (reach' H (env_locs rho S)) H ->
    env_locs rho' S \subset dom H' /\
    well_formed (reach' H' (env_locs rho' S)) H'.
  Proof with (now eauto with Ensembles_DB).
    intros Hclo. revert S H rho H' rho' k.
    induction Hclo; intros S H1 rho1 H2 rho2 k Hctx Hin1 Hin2 Henv Hwf.
    - inv Hctx. simpl.
      split; eassumption.
    - inv Hctx. 
      (* edestruct ctx_to_heap_env_CC_comp_ctx_f_l *)
      (*   as (rho3 & H3 & m1 & m2 & Hctx1 & Hctx2 & Hplus). *)
      (* eassumption. subst. *)
      (* inv Hctx2. *)
      simpl in H11. 
      destruct (M.get f rho1) eqn:Hgetf; try congruence.
      destruct (M.get Γ rho1) eqn:Hgetg; try congruence. inv H12.
      eapply IHHclo.
      + eassumption.
      + eapply Included_trans; [| eassumption ].
        simpl...
      + eassumption.
      + eapply Included_trans. eapply env_locs_set_Inlcuded'.
        rewrite HL.alloc_dom; try eassumption.
        eapply Included_Union_compat. reflexivity.
        eapply Included_trans; [| eassumption ].
        eapply env_locs_monotonic...
      + rewrite <- (Union_Same_set S S); [| reflexivity ].
        eapply well_formed_reach_alloc'; try eassumption.
        * eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply env_locs_monotonic...
        * eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic...
        * rewrite (Union_commut S). rewrite (Union_Same_set (S \\ _) S); try now eauto with Ensembles_DB.
          simpl. 
          eapply Included_trans; [| eapply reach'_extensive ].
          inv H11.
          simpl in Hin1.
          eapply Union_Included. eapply  get_In_env_locs; [| eassumption ]...
          rewrite Union_Empty_set_neut_r. 
          eapply  get_In_env_locs; [| eassumption ]...
  Qed.
  
  Corollary make_closures_env_locs B  Γ C H rho H' rho' k S :
    make_closures Size.Util.clo_tag B  Γ C ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    name_in_fundefs B \subset S ->
    Γ \in S ->
    env_locs rho S \subset dom H ->
    well_formed (reach' H (env_locs rho S)) H ->
    env_locs rho' S \subset dom H'.
  Proof with (now eauto with Ensembles_DB).
    eapply make_closures_env_locs_well_formed.
  Qed.

  Corollary make_closures_well_formed B Γ C H rho H' rho' k S:
    make_closures Size.Util.clo_tag B  Γ C ->
    ctx_to_heap_env_CC C H rho H' rho' k ->
    name_in_fundefs B \subset S ->
    Γ \in S ->
    env_locs rho S \subset dom H ->
    well_formed (reach' H (env_locs rho S)) H ->
    well_formed (reach' H' (env_locs rho' S)) H'.
  Proof with (now eauto with Ensembles_DB).
    eapply make_closures_env_locs_well_formed.
  Qed.

  Lemma make_closures_get C rho1 H1 rho1' H1'
        Γ B x m :
    make_closures Size.Util.clo_tag B Γ C ->
    ctx_to_heap_env_CC C H1 rho1 H1' rho1' m ->
    ~ x \in name_in_fundefs B ->
    M.get x rho1 = M.get x rho1'.
  Proof.
    intros Hcc. revert rho1 H1 rho1' H1' m.
    induction Hcc; intros rho1 H1 rho1' H1' m Hctx Hin.
    - inv Hctx. reflexivity.
    - inv Hctx. eapply IHHcc in H12. rewrite <- H12.
      rewrite M.gso. reflexivity.
      intros Hc. subst; eapply Hin; left; eauto.
      intros Hc. eapply Hin; right; eauto.      
  Qed.

  Definition Fun_inv k j GI GP b d rho1 H1 rho2 H2 Funs Γ :=
    forall f, f \in Funs ->
         exists l1 lenv B g,
           M.get f rho1 = Some (Loc l1) /\
           M.get f rho2 = Some (FunPtr B g) /\
           M.get Γ rho2 = Some (Loc lenv) /\
           let '(l2, H2') := alloc (Constr Size.Util.clo_tag [FunPtr B g; Loc lenv]) H2 in
           Res (Loc l1, H1) ≺ ^ (k; j; GI; GP; b{l1 ~> l2}; d{l1 ~> Some lenv}) Res (Loc l2, H2'). 
  

  Lemma Fun_inv_set_r k j GI GP b d rho1 H1 rho2 H2 funs Γ f v : 
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 funs Γ ->
    ~ f \in funs -> f <> Γ ->
    Fun_inv k j GI GP b d rho1 H1 (M.set f v rho2) H2 funs Γ.
  Proof.
    intros Hfun Hnin1 Hnin2 x Hin.
    edestruct Hfun as (l1 & lenv & B1' & g & Hget1 & Hget2 & Hget3 & Heq). eassumption.
    repeat eexists; try eassumption. rewrite M.gso. eassumption.
    intros Hc. subst. now eauto.
    rewrite M.gso. eassumption. intros Hc. now subst.
  Qed.


  Lemma compose_extend {B C} (f : B -> C) (g : positive -> B) x y :
    f_eq (f ∘ g {x ~> y}) ((f ∘ g) {x ~> f y}).
  Proof.
    intros z. unfold compose. simpl. 
    destruct (var_dec x z); subst. simpl.
    - rewrite !extend_gss. reflexivity.
    - rewrite !extend_gso. reflexivity.
      now eauto. now eauto.
  Qed.

  Lemma compose_id_extend {B} S (f : B -> positive)  x y :
    ~ x \in image f S ->
    f_eq_subdomain S (id {x ~> y} ∘ f) f.
  Proof.
    intros Hneq z Hin. unfold compose.
    rewrite extend_gso. reflexivity.
    intros Hc; eapply Hneq.
    eexists; split; eauto.
  Qed.    

  Lemma compose_lift_id_extend {B} S (f : B -> option positive)  x y :
    ~ x \in image' f S ->
    f_eq_subdomain S (lift (id {x ~> y}) ∘ f) f.
  Proof.
    intros Hneq z Hin. unfold compose, lift.
    destruct (f z) eqn:Heq; eauto.
    rewrite extend_gso. reflexivity.
    intros Hc; eapply Hneq.
    eexists; split; subst; eauto.
  Qed.  

  Lemma res_equiv_subheap S H1 H1' v :
    well_formed (reach' H1 S) H1 ->
    S \subset dom H1 ->
    val_loc v \subset reach' H1 S ->
    H1 ⊑ H1' ->
    (v, H1) ≈_(id, id) (v, H1').
  Proof.
    intros Hwf Hsub1 Hsub2 Hsub3.
    eapply res_equiv_weakening; try eassumption.
    eapply reach'_closed; eassumption.
    eapply reach'_closed; eassumption.
    reflexivity.
    eapply HL.subheap_refl.
  Qed.

  Lemma well_formed_reach_subheap_same 
    (S : Ensemble loc) (H H' : heap block) : 
    well_formed (reach' H S) H ->
    S \subset dom H -> H ⊑ H' ->
    reach' H S <--> reach' H' S.
  Proof.
    intros Hwf Hsub Hsub'; split; intros l [n1 [_ Hr]]. 
    - eexists; split.
      now constructor.
      eapply (well_formed_post_n_subheap_same _ H H') in Hr; try eassumption.
    - eexists; split.
      now constructor.
      eapply (well_formed_post_n_subheap_same _ H H') in Hr; try eassumption.
  Qed.

  Lemma well_formed_post_subheap_same 
        (S : Ensemble loc) (H H' : heap block) : 
    well_formed (reach' H S) H ->
    S \subset dom H -> H ⊑ H' ->
    post H S <--> post H' S.
  Proof.
    intros Hwf Hsub Hsub'.
    eapply well_formed_post_n_subheap_same with (n := 1); eassumption.
  Qed.

  Lemma Fun_inv_subheap k j GI GP b d rho1 H1 H1' rho2 H2 H2' funs Γ :
    well_formed (reach' H1 (env_locs rho1 funs)) H1 ->
    env_locs rho1 funs \subset dom H1 ->
    
    well_formed (reach' H2 (env_locs rho2 [set Γ])) H2 ->
    env_locs rho2 [set Γ] \subset dom H2 ->

    image b (reach' H1 (post H1 (env_locs rho1 funs))) :|:
    image' d (reach' H1 (post H1 (env_locs rho1 funs))) \subset dom H2 ->
    
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 funs Γ ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    Fun_inv k j GI GP b d rho1 H1' rho2 H2' funs Γ.
  Proof.
    intros Hwf1 Henv1 hwf2 Henv2 Him Hfun Hsub1 Hsub2 x Hin.
    edestruct Hfun as (l1 & lenv & B1' & g & Hget1 & Hget2 & Hget3 & Heq). eassumption.
    repeat eexists; try eassumption.

    destruct (alloc (Constr Size.Util.clo_tag [FunPtr B1' g; Loc lenv]) H2) as [l2 H4] eqn:Ha. 
    destruct (alloc (Constr Size.Util.clo_tag [FunPtr B1' g; Loc lenv]) H2') as [l2' H4'] eqn:Ha'.

    eapply cc_approx_val_rename_ext
    with (β' := ((id {l2 ~> l2'}) ∘ (b {l1 ~> l2}) ∘ id))
         (δ' := (lift (id {l2 ~> l2'}) ∘ (d {l1 ~> Some lenv}) ∘ id)).
    - eapply cc_approx_val_res_eq.
      eassumption. eapply res_equiv_subheap; try eassumption.
      eapply Included_trans; [| eapply reach'_extensive ].
      eapply get_In_env_locs; eassumption.
      now firstorder.
      
      * rewrite res_equiv_eq. simpl. split.
        rewrite extend_gss; reflexivity.
        
        do 2 (erewrite gas; eauto). simpl. split.
        reflexivity.
        constructor.
        rewrite res_equiv_eq. split; reflexivity.

        constructor; [| now constructor ].
        
        eapply res_equiv_rename_ext;
          [| eapply f_eq_subdomain_extend_not_In_S_r; [| reflexivity ] | reflexivity ].
        
        eapply res_equiv_weakening;
          [| | reflexivity | now eapply HL.alloc_subheap; eauto
           | eapply HL.subheap_trans; [| eapply HL.alloc_subheap]; eassumption | | ].
        
        now eapply reach'_closed; eauto.
        now eapply reach'_closed; eauto.

        eapply Included_trans; [| eapply reach'_extensive ].
        eapply get_In_env_locs; now eauto.

        eapply Included_trans; [| eapply reach'_extensive ].
        eapply get_In_env_locs; now eauto.

        intros Hc1.
        rewrite <- env_locs_Singleton with (v := Loc lenv) in Hc1; try eassumption. 
        rewrite <- well_formed_reach_alloc_same in Hc1;
          [| eassumption | eassumption | eassumption ].

        eapply reachable_in_dom in Hc1; try eassumption. destruct Hc1 as [b' Hget].
        erewrite alloc_fresh in Hget; eauto. congruence.

      * eapply injective_subdomain_extend'. now firstorder.
        rewrite image_id.
        rewrite reach_unfold. rewrite Setminus_Union_distr.
        rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        simpl. rewrite post_Singleton; [| erewrite gas; eauto ]. simpl.
        rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r.
        intros Hc. destruct Hc as [Hc1 Hc2].
        
        rewrite <- env_locs_Singleton with (v := Loc lenv) in Hc1; try eassumption. 
        
        rewrite <- well_formed_reach_alloc_same in Hc1;
          [| eassumption | eassumption | eassumption ].
        
        eapply reachable_in_dom in Hc1; try eassumption. destruct Hc1 as [b' Hget].
        eapply Hsub2 in Hget.  
        erewrite alloc_fresh in Hget; eauto. congruence.
        
    - rewrite Combinators.compose_id_right. 
      rewrite compose_extend. rewrite extend_gss.
      eapply f_eq_subdomain_antimon.
      eapply Included_Union_Setminus with (s2 := [set l1]). 
      now tci.
      rewrite Union_commut. eapply f_eq_subdomain_extend.
      symmetry. eapply compose_id_extend.

      intros Hc.
      rewrite reach_unfold, Setminus_Union_distr,
      Setminus_Same_set_Empty_set, Union_Empty_set_neut_l in Hc.

      assert (Hsub' : reach' H1 (post H1 (val_loc (Loc l1))) \subset
                        reach' H1 (env_locs rho1 funs)).
      { rewrite (reach_unfold H1 (env_locs rho1 funs)).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. eapply post_set_monotonic.
        eapply get_In_env_locs; eassumption. }

      assert (Hin2 : l2 \in dom H2).
      { eapply Him. left. 
        eapply image_monotonic; [| eassumption ].
        eapply Included_trans. eapply Setminus_Included.
         
        rewrite <- well_formed_post_subheap_same, <- well_formed_reach_subheap_same;
          try eassumption.

        eapply reach'_set_monotonic. eapply post_set_monotonic.
        eapply get_In_env_locs; eassumption.
        eapply well_formed_antimon; [| eassumption ].
        eassumption. 
        
        eapply Included_trans; [| eapply reachable_in_dom; eassumption ]. 
        eapply Included_trans; [| eassumption ]. eapply reach'_extensive.

        eapply well_formed_antimon; [| eassumption ].
         eapply reach'_set_monotonic.
        eapply get_In_env_locs; eassumption.

        eapply Included_trans; [| eassumption ]. 
        
        eapply get_In_env_locs; eassumption.

      }

      destruct Hin2 as [b' Hget].
      erewrite alloc_fresh in Hget; eauto. congruence. 

    - rewrite Combinators.compose_id_right.
      rewrite compose_extend. simpl extend. rewrite extend_gso.
      
      eapply f_eq_subdomain_antimon.
      eapply Included_Union_Setminus with (s2 := (val_loc (Loc l1))). 
      now tci.
      rewrite Union_commut. eapply f_eq_subdomain_extend.
      symmetry. eapply compose_lift_id_extend.

      intros Hc.
      rewrite reach_unfold, Setminus_Union_distr,
      Setminus_Same_set_Empty_set, Union_Empty_set_neut_l in Hc.

      assert (Hsub' : reach' H1 (post H1 (val_loc (Loc l1))) \subset
                        reach' H1 (env_locs rho1 funs)).
      { rewrite (reach_unfold H1 (env_locs rho1 funs)).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. eapply post_set_monotonic.
        eapply get_In_env_locs; eassumption. }

      assert (Hin2 : l2 \in dom H2).
      { eapply Him. right. 
        eapply image_monotonic; [| eassumption ].
        eapply Included_trans. eapply Setminus_Included.
        
        rewrite <- well_formed_post_subheap_same, <- well_formed_reach_subheap_same;
          try eassumption.
        
        eapply reach'_set_monotonic. eapply post_set_monotonic.
        eapply get_In_env_locs; eassumption.
        eapply well_formed_antimon; [| eassumption ].
        eassumption. 
        
        eapply Included_trans; [| eapply reachable_in_dom; eassumption ]. 
        eapply Included_trans; [| eassumption ]. eapply reach'_extensive.

        eapply well_formed_antimon; [| eassumption ].
         eapply reach'_set_monotonic.
        eapply get_In_env_locs; eassumption.

        eapply Included_trans; [| eassumption ]. 
        
        eapply get_In_env_locs; eassumption.

      }
     
      destruct Hin2 as [b' Hget].
      erewrite alloc_fresh in Hget; eauto. congruence.

      intros Hc. subst. 
      
      assert (Hd : l2 \in dom H2).
      { eapply reachable_in_dom; try eassumption.
        eapply reach'_extensive. eapply get_In_env_locs; eauto.
        reflexivity. }

      destruct Hd as [b' Hget].
      erewrite alloc_fresh in Hget; eauto. congruence.
  Qed.
  
  Lemma Fun_inv_rename_ext k j GI GP b b' d d' rho1 H1 rho2 H2 funs Γ :
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 funs Γ ->
    f_eq_subdomain (reach' H1 (env_locs rho1 funs)) b b' ->
    f_eq_subdomain (reach' H1 (env_locs rho1 funs)) d d' ->
    Fun_inv k j GI GP b' d' rho1 H1 rho2 H2 funs Γ.
  Proof.
    intros Hfun Heq1 Heq2 x Hin.
    edestruct Hfun as (l1 & lenv & B1' & g & Hget1 & Hget2 & Hget3 & Heq). eassumption.
    repeat eexists; try eassumption.
    destruct (alloc (Constr Size.Util.clo_tag [FunPtr B1' g; Loc lenv]) H2) as [l2 H2'].
    assert (Hseq : l1 |: (reach' H1 (val_loc (Loc l1))) <--> reach' H1 (val_loc (Loc l1))).
    { split. eapply Union_Included. eapply Singleton_Included. eapply reach'_extensive.
      reflexivity. reflexivity.
      eapply Included_Union_preserv_r. reflexivity. }
    eapply cc_approx_val_rename_ext. eassumption.

    rewrite <- Hseq.  eapply f_eq_subdomain_extend. symmetry.
    eapply f_eq_subdomain_antimon; [ | eassumption ]. eapply reach'_set_monotonic.
    eapply get_In_env_locs. eassumption. eassumption.

    rewrite <- Hseq.  eapply f_eq_subdomain_extend. symmetry.
    eapply f_eq_subdomain_antimon; [ | eassumption ]. eapply reach'_set_monotonic.
    eapply get_In_env_locs. eassumption. eassumption.
  Qed.
  

  Instance Proper_FV_inv k j GI GP b d rho1 H1 rho2 H2 c :
    Proper (Same_set _ ==> eq ==> eq ==> iff)
           (FV_inv k j GI GP b d rho1 H1 rho2 H2 c). 
  Proof.
    intros S1 S2 Hseq x1 x2 Heq1 y1 y2 Heq2; subst.
    split; intros (vs & l & Hget1 & Hget2 & Hall1).
    do 2 eexists.
    split. eassumption.
    split. eassumption.
    eapply Forall2_P_monotonic; eauto. now eapply Hseq. 
    do 2 eexists.
    split. eassumption.
    split. eassumption.
    eapply Forall2_P_monotonic; eauto. now eapply Hseq. 
  Qed.

  Instance Proper_Fun_inv k j GI GP b d rho1 H1 rho2 H2 :
    Proper (Same_set _ ==> eq ==> iff)
           (Fun_inv k j GI GP b d rho1 H1 rho2 H2). 
  Proof.
    intros S1 S2 Hseq x1 x2 Heq1; subst.
    split; intros Hfv f Hin.
    edestruct (Hfv f) as (l1 & len & B & g & Hgfet & Hgetf2 & Hgete & Hres).
    now eapply Hseq. do 4 eexists.
    split. eassumption.
    split. eassumption.
    split. eassumption. eassumption.
    edestruct (Hfv f) as (l1 & len & B & g & Hgfet & Hgetf2 & Hgete & Hres).
    now eapply Hseq. do 4 eexists.
    split. eassumption.
    split. eassumption.
    split. eassumption. eassumption.
  Qed.

  Instance Proper_FV : Proper (Same_set _ ==> eq ==> Same_set _) FV.
  Proof.
    intros s1 s2 Hseq x1 x2 Heq; subst; unfold FV;
    rewrite !Hseq at 1; reflexivity.
  Qed.

  Instance Proper_FV_cc : Proper (Same_set _ ==> eq ==> Same_set _) FV_cc.
  Proof.
    intros s1 s2 Hseq x1 x2 Heq; subst; unfold FV_cc;
    rewrite !Hseq at 1; reflexivity.
  Qed.

  Lemma FV_image_reach k P1 P2 rho1 H1 rho2 H2 b d c
        Scope Γ FVs :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b; d) (H2, rho2)) ->
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Γ FVs) ->
    image b (reach' H1 (env_locs rho1 (FV Scope FVs)))
    :|: image' d (reach' H1 (env_locs rho1 (FV Scope FVs))) \subset
    reach' H2 (env_locs rho2 (FV_cc Scope Γ)).
  Proof with (now eauto with Ensembles_DB).
    intros Hcc Henv l' [l Hin | l Hin].
    - unfold FV in Hin. unfold FV_cc.
      rewrite env_locs_Union, reach'_Union, image_Union in Hin.
      inv Hin.
      
      + eapply reach'_set_monotonic; [| eapply cc_approx_env_image_reach_included; try eassumption ].
        eapply env_locs_monotonic... now left.

      + rewrite env_locs_Union, reach'_Union.  right.
        rewrite reach_unfold. right.
        eapply FV_inv_image_reach. eassumption.
        now left.

    - unfold FV in Hin. unfold FV_cc.
      rewrite env_locs_Union, reach'_Union, image'_Union in Hin.
      inv Hin.
      
      + eapply reach'_set_monotonic; [| eapply cc_approx_env_image_reach_included; try eassumption ].
        eapply env_locs_monotonic... now right.
        
      + rewrite env_locs_Union, reach'_Union.  right.
        rewrite reach_unfold. right.
        eapply FV_inv_image_reach. eassumption.
        now right.
  Qed.

  Lemma def_closures_post B1 B2 rho H rho' H' rc :
    def_closures B1 B2 rho H rc = (H', rho') ->
    post H' (env_locs rho' (name_in_fundefs B1)) \subset
    env_locs rc (occurs_free_fundefs B2).
  Proof with  (now eauto with Ensembles_DB).
    revert rho rho' H H'. induction B1; intros rho rho' H H' Hdef; simpl.
    - simpl in Hdef.
      destruct (def_closures B1 B2 _ _ _) as [H'' rho''] eqn:Hclo.
      destruct (alloc _ H'') as [l1 H'''] eqn:Ha.
      inv Hdef. 
      rewrite env_locs_Union, post_Union, env_locs_Singleton;
      [| now rewrite M.gss; eauto ].

      eapply Union_Included.

      + simpl. rewrite post_Singleton; [| now erewrite gas; eauto ].
        reflexivity.

      + assert (Hclo' := Hclo). eapply IHB1 in Hclo.

        eapply Included_trans.
        eapply post_set_monotonic. eapply env_locs_set_Inlcuded'.

        rewrite post_Union. 
        simpl. rewrite post_Singleton; [| now erewrite gas; eauto ].

        eapply Union_Included; [ reflexivity |].
        eapply Included_trans. eapply post_alloc. eassumption.

        eapply Union_Included.

        eapply Included_trans; [| eassumption ].
        eapply post_set_monotonic.
        eapply env_locs_monotonic...

        reflexivity.
    - rewrite env_locs_Empty_set, post_Empty_set...
  Qed.

 
  Lemma make_closures_correct k GI GP b d C c rho1 H1 rho2 H2 rho2'
        H2' Scope Funs FVs B1 Γ Γ' m :
    (* make closures *)
    make_closures Size.Util.clo_tag B1 Γ' C ->

    (* well-formedness *)
    well_formed (reach' H1 (env_locs rho1 (FV Scope FVs))) H1 ->
    env_locs rho1 (FV Scope FVs)  \subset dom H1  ->
    well_formed (reach' H2 (env_locs rho2 (Γ' |: FV_cc Scope Γ))) H2 ->
    env_locs rho2 (Γ' |: FV_cc Scope Γ) \subset dom H2  ->

    (* Closure pointers are fresh locations *)
    (forall f, f \in Funs ->
          Disjoint _ (env_locs rho1 [set f])
                   (reach' H1 (env_locs rho1 (FV Scope FVs :|: (Funs \\ [set f]))))) ->
 
    post H1 (env_locs rho1 Funs) \subset reach' H1 (env_locs rho1 ((FV Scope FVs \\ Funs))) ->
    
    Disjoint _ (env_locs rho2 ([set Γ'])) (image b (reach' H1 (env_locs rho1 (FV Scope FVs)))) ->
    
    (* Environment relations *)
    (forall j, (H1, rho1) ⋞ ^ (Scope \\ Funs; k; j; GI; GP; b; d) (H2, rho2)) ->
    (forall j, Fun_inv k j GI GP b d rho1 H1  rho2 H2 Funs Γ') ->
    (forall j, FV_inv k j GI GP b d rho1 H1 rho2 H2 c Scope Γ FVs) ->

    (* Context interpretation *)
    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->

    (* names *)
    unique_functions B1 ->
    ~ Γ \in (name_in_fundefs B1) ->
    ~ Γ' \in (name_in_fundefs B1) ->
    Funs \subset (name_in_fundefs B1) ->

    (* Injectivity  *)
    injective_subdomain (reach' H1 (env_locs rho1 ((FV Scope FVs) \\ Funs))) b ->
    Disjoint _ (image b (reach' H1 (env_locs rho1 ((FV Scope FVs) \\ Funs))))
             (image' d (reach' H1 (env_locs rho1 ((FV Scope FVs) \\ Funs)) )) ->

    
    exists b' d',
      (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GI; GP; b'; d') (H2', rho2')) /\
      (forall j, FV_inv k j GI GP b' d' rho1 H1 rho2' H2' c Scope Γ FVs) /\ 
      injective_subdomain (reach' H1 (env_locs rho1 (FV Scope FVs))) b' /\
      Disjoint _ (image b' (reach' H1 (env_locs rho1 (FV Scope FVs))))
               (image' d'  (reach' H1 (env_locs rho1 (FV Scope FVs)))).
  Proof with (now eauto with Ensembles_DB).
    intros Hclo.
    revert m rho1 H1 rho2 H2 rho2' H2' Scope Funs b d.
    induction Hclo as [Γ'' | f xs t e B ];
      intros m rho1 H1 rho2 H2 rho2' H2' Scope Funs b d
             Hwf1 Hlocs1 Hwf2 Hlocs2 Hdis Hrsub Henvim
             Hlr Hfun Hfv Hctx Hun Hnin Hnin' Hsubf Hin1 Hdinj.
    - inv Hctx. simpl name_in_fundefs.
      assert (Hseq : Funs <--> Empty_set _).
      { simpl in Hsubf...  }
      repeat setoid_rewrite Hseq at 1. 
      repeat setoid_rewrite Union_Empty_set_neut_l at 1.
      simpl in *.
      rewrite !Hseq in Hdinj at 1.
      rewrite !Hseq in Hin1 at 1.
      setoid_rewrite Hseq in Hfv. 
      rewrite !Setminus_Empty_set_neut_r in Hdinj at 1.
      rewrite !Setminus_Empty_set_neut_r in Hin1.
      setoid_rewrite Union_Empty_set_neut_l in Hfv.
      
      do 2 eexists.
      split; [| split; [| split ]]; try eassumption.
      intros. eapply Hlr. constructor; eauto.
      intros Hc; rewrite Hseq in Hc; now inv Hc.
      
    - inv Hctx.
      simpl name_in_fundefs in Hsubf.
      simpl in H11.
       
      assert (Hseq : Funs :|: Scope \subset
                          (Funs \\ [set f]) :|: (f |: Scope)).
      { rewrite <- Union_Included_Union_Setminus;
        try now eauto with Ensembles_DB. tci. }

      edestruct (Hfun 0) as (l1 & lenv & B1' & g & Hget1 & Hget2 & Hget3 & Heq).
      now left.
      
      repeat setoid_rewrite Hseq at 1.
      
      simpl in H11. rewrite Hget2, Hget3 in H11. inv H11.

      rewrite H12 in Heq.

      assert (Hsub : reach' H1 (env_locs rho1 (FV (f |: Scope) FVs)) \\ [set l1] \subset
                     reach' H1 (env_locs rho1 (FV Scope FVs))).
      { eapply Setminus_Included_Included_Union. unfold FV.
        rewrite <- Union_assoc. 
        rewrite env_locs_Union, reach'_Union, env_locs_Singleton; eauto. simpl.
        rewrite reach_unfold.
        rewrite <- !Union_assoc. rewrite (Union_commut [set l1]).
        eapply Included_Union_compat; [| reflexivity ].
        
        eapply Union_Included;
          [|  eapply reach'_set_monotonic; eapply env_locs_monotonic;
              unfold FV; now eauto with Ensembles_DB ].

        rewrite (reach'_idempotent H1 (env_locs rho1 _)).
        eapply reach'_set_monotonic.
        eapply Included_trans;
          [| eapply Included_trans; [ now apply Hrsub |]].

        eapply post_set_monotonic. 
        simpl.
        rewrite env_locs_Union, env_locs_Singleton; eauto...

        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        unfold FV... }

      assert (Hsub' : reach' H1 (env_locs rho1 ((FV (f |: Scope) FVs) \\ name_in_fundefs B)) \\
                             [set l1] \subset
                      reach' H1 (env_locs rho1 ((FV Scope FVs) \\ name_in_fundefs (Fcons f t xs e B)))).
      { rewrite <- (Union_Setminus_Included [set f] Scope); [| | reflexivity ]; tci.
        eapply Setminus_Included_Included_Union. unfold FV.
        rewrite <- Union_assoc. rewrite Setminus_Union_distr.
        rewrite Setminus_Disjoint; [| now inv Hun; eapply Disjoint_Singleton_l; eauto ].
        rewrite env_locs_Union, reach'_Union, env_locs_Singleton; eauto. simpl.
        rewrite reach_unfold.
        rewrite <- !Union_assoc. rewrite (Union_commut [set l1]).
        eapply Included_Union_compat; [| reflexivity ].
        
        eapply Union_Included.

        rewrite (reach'_idempotent H1 (env_locs rho1 _)).
        eapply reach'_set_monotonic.
        eapply Included_trans;
          [| eapply Included_trans; [ now apply Hrsub |]].
        
        eapply post_set_monotonic. 
        simpl.
        rewrite env_locs_Union, env_locs_Singleton; eauto...
        
        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        unfold FV...

        eapply reach'_set_monotonic. eapply env_locs_monotonic.

        rewrite !Setminus_Union_distr, !Setminus_Union.
        unfold FV.
        eapply Included_Union_compat. reflexivity.
        
        eapply Included_Setminus_compat. reflexivity.

        rewrite (Union_Setminus_Included [set f] Scope); [| | reflexivity ]; tci...        
      }
      
      inv Hun.

      eapply IHHclo with (b := b {l1 ~> l}) (d := d{l1 ~> Some lenv});
        [ | | | | | | | | | | eassumption | eassumption | | | | ].
      + unfold FV. eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. simpl.
        unfold FV. eapply Union_Included.
        eapply Union_Included...
        now eauto with Ensembles_DB.
      + eapply Included_trans; [| eassumption ]. 
        eapply env_locs_monotonic. unfold FV.
        eapply Union_Included.
        eapply Union_Included...
        now eauto with Ensembles_DB.
      + unfold FV_cc. 
        assert (Hseq1 : (Γ0 |: (f |: Scope :|: [set Γ])) <--> (Γ0 |: (Scope :|: [set Γ])) :|: [set f]).
        { rewrite <- (Union_assoc [set f]), (Union_commut [set f])... }
        rewrite Hseq1.
        eapply well_formed_reach_alloc'; try eassumption.
        * rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r. eassumption.
        * rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r. eassumption.
        * simpl. rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r.
          eapply Singleton_Included.
          rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
          eapply reach'_extensive. eapply get_In_env_locs; [| eassumption |].
          now left. reflexivity.
      + eapply Included_trans. eapply env_locs_set_Inlcuded'.
        rewrite HL.alloc_dom; try eassumption.
        eapply Included_Union_compat. reflexivity.
        eapply Included_trans; [| eassumption ].
        unfold FV_cc; eapply env_locs_monotonic.
        rewrite !Setminus_Union_distr...
      + intros f1 Hinf1. eapply Disjoint_Included_r; [ | eapply Hdis; right; eassumption ].
        simpl. eapply reach'_set_monotonic. eapply env_locs_monotonic.
        unfold FV.
        rewrite Setminus_Union_distr. rewrite (Setminus_Disjoint [set f] [set f1]).
        eapply Union_Included; try eauto with Ensembles_DB.
        now eapply Union_Included; try eauto with Ensembles_DB.

        eapply Disjoint_Singleton_l. intros Hc; inv Hc; eauto.
      + eapply Included_trans. eapply Included_trans; [| now eapply Hrsub ].
        eapply post_set_monotonic.
        eapply env_locs_monotonic...
        eapply reach'_set_monotonic. unfold FV.
        eapply env_locs_monotonic.
        rewrite (Union_commut [set f]) at 2. rewrite <- Setminus_Union.
        rewrite (Union_Setminus_Included _ _ [set f]); eauto with typeclass_instances.
        now eauto with Ensembles_DB.
        now eauto with Ensembles_DB.
      + rewrite env_locs_set_not_In.
        eapply Disjoint_Included_r.

        eapply image_extend_Included'.

        eapply Union_Disjoint_r.

        eapply Disjoint_Included_r.
        eapply image_monotonic.
        eapply Included_trans; [| now apply Hsub ].
        eapply Included_Setminus_compat; [| reflexivity ].
        eapply reach'_set_monotonic.
        unfold FV. eapply env_locs_monotonic...

        eassumption.
        
        rewrite env_locs_Singleton; eauto. simpl. 

        eapply Disjoint_Singleton_l. intros Hc; inv Hc.
        assert (Hninl : ~ lenv \in dom H2).
        { intros [b1 Hc]. erewrite alloc_fresh in Hc; eauto.
          congruence. }

        exfalso. eapply Hninl. eapply reachable_in_dom; try eassumption.

        eapply reach'_extensive. eapply get_In_env_locs; eauto.
        unfold FV_cc...
        
        intros Hc; inv Hc; eapply Hnin'; now left.
        
      + assert (Hsub'' : f |: Scope \\ name_in_fundefs B \subset f |: (Scope \\ name_in_fundefs (Fcons f t xs e B))).
        { intros x Hin.
          destruct (var_dec x f); subst; eauto.  
          inv Hin; eauto. inv H; eauto. right; constructor; eauto.
          intros Hc; inv Hc; eauto. inv H; eauto. }
        
        intros j.

        edestruct (Hfun j) as (l1' & lenv' & B2 & g' & Hget1' & Hget2' & Hget3' & Heq').
        now left. repeat subst_exp.
        
        rewrite H12 in Heq'.
        
        eapply cc_approx_env_P_antimon; [| eassumption ].
        eapply cc_approx_env_P_union. 
        * intros x Hin v Hget. inv Hin. subst_exp. eexists. rewrite M.gss. split.
          reflexivity. eassumption.
        * { eapply cc_approx_env_P_set_not_in_P_r.
            eapply cc_approx_env_heap_monotonic.
            - eapply well_formed_antimon; try now apply Hwf1.
              eapply reach'_set_monotonic.
              eapply env_locs_monotonic...
            - eapply well_formed_antimon; try now apply Hwf2.
              eapply reach'_set_monotonic.
              eapply env_locs_monotonic...
            - eapply Included_trans; [| eassumption ].
              eapply env_locs_monotonic...
            - eapply Included_trans; [| eassumption ].
              eapply env_locs_monotonic...
            - eapply HL.subheap_refl.
            - eapply HL.alloc_subheap. eassumption.
            - eapply cc_approx_env_rename_ext.
              eapply cc_approx_env_P_antimon; [ now apply Hlr |]...
              + eapply f_eq_subdomain_extend_not_In_S_r.
                intros Hc. eapply Hdis. now left.
                constructor. rewrite env_locs_Singleton; eauto. reflexivity.
                eapply reach'_set_monotonic; [| eassumption ].
                eapply env_locs_monotonic. simpl... reflexivity. 
              + eapply f_eq_subdomain_extend_not_In_S_r.
                intros Hc. eapply Hdis. now left.
                constructor. rewrite env_locs_Singleton; eauto. reflexivity.
                eapply reach'_set_monotonic; [| eassumption ].
                eapply env_locs_monotonic. simpl... reflexivity. 
            - intros Hc; inv Hc; eauto. eapply H0; now left. }
      + intros j.
        
        eapply Fun_inv_set_r; [ eapply Fun_inv_rename_ext | | ].
        * eapply Fun_inv_subheap;
          [ | | | | | intros x Hin; eapply Hfun; now right | | ].
          
          eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic...

          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic...

          eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic...

          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic...

          intros lc Hin. eapply reachable_in_dom. eassumption. eassumption.
          
          rewrite !env_locs_Union, !reach'_Union. right.
          
          eapply Included_Union_compat in Hin;
            [| eapply image_monotonic; eapply reach'_set_monotonic;
               eapply Included_trans; [| now apply Hrsub ]
             | eapply image'_monotonic; eapply reach'_set_monotonic;
               eapply Included_trans; [| now apply Hrsub ] ].
          unfold FV in Hin. rewrite <- !reach'_idempotent, !Setminus_Union_distr in Hin at 1.
          rewrite !env_locs_Union, !reach'_Union, image_Union, image'_Union in Hin at 1.
          rewrite <- Union_assoc, (Union_assoc (image _ _) (image' _ _)) in Hin. 
          rewrite (Union_commut (image _ _) (image' _ _)) in Hin.
          rewrite <- (Union_assoc (image' _ _) (image _ _)) in Hin. 
          rewrite (Union_assoc (image _ _) (image' _ _)) in Hin. 
          
          unfold FV_cc. rewrite env_locs_Union, reach'_Union.
          { inv Hin.
            - left.
              eapply reach'_set_monotonic; [| eapply cc_approx_env_image_reach_included; try eassumption ].
              eapply env_locs_monotonic...
            - right. rewrite reach_unfold. right. 
              eapply FV_inv_image_reach. eassumption.
              rewrite !(Union_commut _ Scope) at 1. rewrite <- !Setminus_Union at 1.
              eassumption. }

          eapply post_set_monotonic. eapply env_locs_monotonic...
          eapply post_set_monotonic. eapply env_locs_monotonic...

          eapply HL.subheap_refl. eapply HL.alloc_subheap. eassumption. 
        * eapply f_eq_subdomain_extend_not_In_S_r.
          intros Hc. eapply Hdis. now left.
          constructor. rewrite env_locs_Singleton; eauto. reflexivity.
          eapply reach'_set_monotonic; [| eassumption ].
          eapply env_locs_monotonic. simpl. rewrite !Setminus_Union_distr.
          rewrite (Setminus_Disjoint (name_in_fundefs B) [set f]).
          now eauto with Ensembles_DB. eapply Disjoint_Singleton_r.
          eassumption. reflexivity. 

        * eapply f_eq_subdomain_extend_not_In_S_r.
          intros Hc. eapply Hdis. now left.
          constructor. rewrite env_locs_Singleton; eauto. reflexivity.
          eapply reach'_set_monotonic; [| eassumption ].
          eapply env_locs_monotonic. simpl. rewrite !Setminus_Union_distr.
          rewrite (Setminus_Disjoint (name_in_fundefs B) [set f]).
          now eauto with Ensembles_DB. eapply Disjoint_Singleton_r.
          eassumption. reflexivity. 

        * eassumption.
        * intros hc. eapply Hnin'. subst. now left.
      + intros j. eapply FV_inv_set_not_in_FVs_r.
        eapply FV_inv_Scope_mon with (Scope := f |: name_in_fundefs B :|: Scope);
          try eauto with Ensembles_DB.
        
        eapply FV_inv_heap_mon;
          [ | | | | now eapply HL.subheap_refl | now eapply HL.alloc_subheap; eauto | ].
        * eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic. unfold FV...
        * eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic. unfold FV_cc...
        * eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic. unfold FV...
        * eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic. unfold FV_cc...
        * eapply FV_inv_rename_ext. now eauto.

          symmetry.
          eapply f_eq_subdomain_extend_not_In_S_r.
          intros Hc. eapply Hdis. now left.
          constructor. rewrite env_locs_Singleton; eauto. reflexivity.
          eapply reach'_set_monotonic; [| eassumption ]. 
          eapply env_locs_monotonic. simpl. unfold FV...
          reflexivity.
          
          symmetry.
          eapply f_eq_subdomain_extend_not_In_S_r.
          intros Hc. eapply Hdis. now left.
          constructor. rewrite env_locs_Singleton; eauto. reflexivity.
          eapply reach'_set_monotonic; [| eassumption ]. 
          eapply env_locs_monotonic. simpl. unfold FV...
          reflexivity.

        * intros Hc. subst. eapply Hnin. now left.
      + intros Hc. subst. eapply Hnin. now right.
      + intros Hc. subst. eapply Hnin'. now right.
      + eapply injective_subdomain_extend'. 
        eapply injective_subdomain_antimon; [ eassumption |].
        now apply Hsub'. 
         
        intros Him. eapply image_monotonic in Him; [| eassumption ].
        unfold FV in Him. rewrite Setminus_Union_distr, env_locs_Union, reach'_Union, image_Union in Him.
        

        assert (Hinr2 : In loc (reach' H2 (env_locs rho2 (FV_cc Scope Γ))) l).
        { unfold FV_cc. rewrite env_locs_Union, reach'_Union.
          inv Him.
          - left.
            eapply reach'_set_monotonic; [| eapply cc_approx_env_image_reach_included; try eassumption ].
            eapply env_locs_monotonic...
            now left.
          - right. rewrite reach_unfold. right. 
            eapply FV_inv_image_reach. eassumption.
            left. eapply image_monotonic; [| eassumption ].
            eapply reach'_set_monotonic. eapply env_locs_monotonic... }
        
        eapply reachable_in_dom in Hinr2. destruct Hinr2 as [b1 Hgetl].
        erewrite alloc_fresh in Hgetl; eauto. congruence. 
        
        eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic...
        
        eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic...
      + eapply Disjoint_Included_l.
        eapply image_extend_Included'.
        eapply Disjoint_Included_r.
        eapply image'_extend_Included_Some.

        eapply Union_Disjoint_l.
        eapply Union_Disjoint_r.
        
        eapply Disjoint_Included; [| | eassumption ].
        
        eapply image'_monotonic.
        
        eapply Included_trans; [| eassumption ].
        eapply Included_Setminus_compat; [| reflexivity ]. 
        eapply reach'_set_monotonic; eapply env_locs_monotonic; unfold FV...

        eapply image_monotonic.

        eapply Included_trans; [| eassumption ].
        eapply Included_Setminus_compat; [| reflexivity ]. 
        eapply reach'_set_monotonic; eapply env_locs_monotonic; unfold FV...
        
        eapply Disjoint_sym.
        eapply Disjoint_Included; [| | now apply Henvim ].
        eapply image_monotonic. eapply Included_trans. eassumption.
        eapply reach'_set_monotonic. eapply env_locs_monotonic...

        rewrite env_locs_Singleton; eauto...
        
        eapply Disjoint_Singleton_l.
        
        intros Hc. inv Hc.
        
        eapply image'_monotonic in H; [| eassumption ].
        
        * unfold FV in H.
          rewrite Setminus_Union_distr, env_locs_Union, reach'_Union, image'_Union in H.
          
          assert (Hinr2 : In loc (reach' H2 (env_locs rho2 (FV_cc Scope Γ))) l).
          { unfold FV_cc. rewrite env_locs_Union, reach'_Union.
            inv H.
            - left.
              eapply reach'_set_monotonic; [| eapply cc_approx_env_image_reach_included; try eassumption ].
              eapply env_locs_monotonic...
              now right.
            - right. rewrite reach_unfold. right. 
              eapply FV_inv_image_reach; try eassumption.
              right. eapply image'_monotonic; [| eassumption ].
              eapply reach'_set_monotonic. eapply env_locs_monotonic... }

          eapply reachable_in_dom in Hinr2. destruct Hinr2 as [b1 Hgetl].
          erewrite alloc_fresh in Hgetl; eauto. congruence. 
        
          eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic...
          
          eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic...
        * inv H.
          assert (Hdom : l \in dom H2).
          { eapply reachable_in_dom. eassumption. eassumption.
            eapply reach'_extensive.
            eapply get_In_env_locs; [| eassumption |].
            now left. reflexivity. }
          destruct Hdom as [b1 Hgetl].
          erewrite alloc_fresh in Hgetl; eauto. congruence. 
  Qed.
  

  Lemma reach'_subheap H H' S : 
    well_formed (reach' H S) H ->
    S \subset dom H ->
    H ⊑ H' ->
    reach' H S <-->reach' H' S.
  Proof. 
    intros Hwf Hsub Hsub'. split.
    - intros x [n [_ Hin]].
      eexists. split. now constructor.
      eapply (well_formed_post_n_subheap_same S H H') in Hin; eassumption.
    - intros x [n [_ Hin]].
      eexists. split. now constructor.
      eapply (well_formed_post_n_subheap_same S H H') in Hin; eassumption.
  Qed.

  Lemma well_formed_subheap H H' S :
    well_formed S H ->
    S \subset dom H ->
    H ⊑ H' ->
    well_formed S H'.
  Proof. 
    intros Hwf Henv Hsub x b Hget Hin.
    eapply Included_trans.
    eapply Hwf; eauto.
    eapply Henv in Hget.
    destruct Hget as [b' Hget]. rewrite Hget.
    now erewrite Hsub in Hin; eauto.

    eapply HL.dom_subheap. eassumption.
  Qed.
    
  Lemma def_closures_cc_approx_env Scope k j GIP GP b d B1 B2 envc rho1 H1 rho1' H1' rho2 H2 :
    well_formed (reach' H1 (env_locs rho1 Scope)) H1 ->
    (env_locs rho1 Scope) \subset dom H1 ->
    well_formed (reach' H2 (env_locs rho2 Scope)) H2 ->
    (env_locs rho2 Scope) \subset dom H2 ->

    (H1, rho1) ⋞ ^ (Scope; k; j; GIP; GP; b; d) (H2, rho2) ->

    def_closures B1 B2 rho1 H1 envc = (H1', rho1') ->
    (H1', rho1') ⋞ ^ (Scope \\ name_in_fundefs B1; k; j; GIP; GP; b; d) (H2, rho2).
  Proof with (now eauto with Ensembles_DB).
    revert H1 rho1 H1' rho1'.
    induction B1; intros H1 rho1 H1' rho1' Hwf1 Henv1 Hwf2 Henv2 Hcc Hdef.
    - simpl in Hdef.
      destruct (def_closures B1 B2 rho1 H1) as (H1'', rho1'') eqn:Hdef'.
      destruct (alloc (Clos _ _) H1'') as [la H1a] eqn:Hal.
      inv Hdef.
      eapply cc_approx_env_P_set_not_in_P_l.
      assert (Hdef := Hdef').
      eapply IHB1 in Hdef'.
      + eapply cc_approx_env_P_antimon. 
        eapply cc_approx_env_heap_monotonic; [ | | | | | | eassumption ].
        * eapply well_formed_antimon.
          eapply reach'_set_monotonic.
          eapply env_locs_def_funs; eauto.
          eapply env_locs_monotonic... 
          rewrite <- reach'_subheap; try eassumption.

          eapply well_formed_subheap. eassumption.

          eapply reachable_in_dom. eassumption. eassumption.

          now eapply def_funs_subheap; eauto.
          now eapply def_funs_subheap; eauto.
        * eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply env_locs_monotonic...
        * eapply Included_trans. 
          eapply env_locs_def_funs; eauto.
          eapply Included_trans.
          eapply env_locs_monotonic. now apply Setminus_Included.
          eassumption.
          eapply HL.dom_subheap.
          now eapply def_funs_subheap; eauto.
        * eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic...
        * eapply HL.alloc_subheap. eassumption.
        * eapply HL.subheap_refl.
        * simpl...
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + intros Hc; inv Hc. eapply H0; now left.
    - rewrite Setminus_Empty_set_neut_r.
      inv Hdef. eassumption.
  Qed.

  Lemma def_funs_cc_approx_env Scope k j GIP GP b d B1 B2 rho1 H1 rho2 H2 :
    (H1, rho1) ⋞ ^ (Scope; k; j; GIP; GP; b; d) (H2, rho2) ->

    (H1, rho1) ⋞ ^ (Scope \\ name_in_fundefs B1; k; j; GIP; GP; b; d) (H2, def_funs B1 B2 rho2).
  Proof with (now eauto with Ensembles_DB).
    induction B1; intros Hcc.
    - simpl def_funs.
      eapply cc_approx_env_P_set_not_in_P_r.
      eapply cc_approx_env_P_antimon.
      eapply IHB1. eassumption.
      now eauto with Ensembles_DB.
      intros Hc; inv Hc. eapply H0; now left.
    - simpl name_in_fundefs.
      rewrite Setminus_Empty_set_neut_r. eassumption.
  Qed.

  Lemma def_closures_FV_inv Scope FVs Γ k j GIP GP b d B1 B2 envc c rho1 H1 rho1' H1' rho2 H2 :
    well_formed (reach' H1 (env_locs rho1 (FromList FVs \\ Scope))) H1 ->
    (env_locs rho1 (FromList FVs \\ Scope)) \subset dom H1 ->
    well_formed (reach' H2 (env_locs rho2 [set Γ])) H2 ->
    (env_locs rho2 [set Γ]) \subset dom H2 ->

    FV_inv k j GIP GP b d rho1 H1 rho2 H2 c Scope Γ FVs ->

    def_closures B1 B2 rho1 H1 envc = (H1', rho1') ->
    FV_inv k j GIP GP b d rho1' H1' rho2 H2 c (name_in_fundefs B1 :|: Scope) Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    revert H1 rho1 H1' rho1'.
    induction B1; intros H1 rho1 H1' rho1' Hwf1 Henv1 Hwf2 Henv2 Hfv Hdef.
    - simpl in Hdef.
      destruct (def_closures B1 B2 rho1 H1) as (H1'', rho1'') eqn:Hdef'.
      destruct (alloc (Clos _ _) H1'') as [la H1a] eqn:Hal.
      inv Hdef.
      eapply FV_inv_set_not_in_FVs_l.
      assert (Hdef := Hdef').
      eapply IHB1 in Hdef'.
      + eapply FV_inv_Scope_mon.
        eapply FV_inv_heap_mon; [ | | | | | | eassumption ].
        * eapply well_formed_antimon.
          eapply reach'_set_monotonic.
          rewrite Union_commut, <- Setminus_Union. 
          eapply env_locs_def_funs; eauto.
          eapply env_locs_monotonic. now eapply Setminus_Included.
          rewrite <- reach'_subheap; try eassumption.
          
          eapply well_formed_subheap. eassumption.

          eapply reachable_in_dom. eassumption. eassumption.

          now eapply def_funs_subheap; eauto.
          now eapply def_funs_subheap; eauto.
        * eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply env_locs_monotonic...
        * eapply Included_trans. 
          rewrite Union_commut, <- Setminus_Union. 
          
          eapply env_locs_def_funs; eauto.
          eapply Included_trans.
          eapply env_locs_monotonic. now apply Setminus_Included.
          eassumption.
          eapply HL.dom_subheap.
          now eapply def_funs_subheap; eauto.
        * eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic...
        * eapply HL.alloc_subheap. eassumption.
        * eapply HL.subheap_refl.
        * simpl...
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + eassumption.
      + intros Hc; inv Hc. eapply H0; left; now left.
    - inv Hdef. eapply FV_inv_Scope_mon; [ eassumption |]...
  Qed.

  Lemma def_funs_FV_inv Scope Γ FVs c k j GIP GP b d B1 B2 rho1 H1 rho2 H2 :
    FV_inv k j GIP GP b d rho1 H1 rho2 H2 c Scope Γ FVs ->
    ~ Γ \in name_in_fundefs B1 ->
    FV_inv k j GIP GP b d rho1 H1 (def_funs B1 B2 rho2) H2 c (name_in_fundefs B1 :|: Scope) Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    induction B1; intros Hcc Hnin.
    - simpl def_funs.
      eapply FV_inv_set_not_in_FVs_r.
      eapply FV_inv_Scope_mon.
      eapply IHB1. eassumption.
      intros Hc. eapply Hnin; now right.
      now eauto with Ensembles_DB.
      intros Hc; inv Hc. eapply Hnin; now left.
    - simpl name_in_fundefs.
      eapply FV_inv_Scope_mon; [ eassumption |]...
  Qed.

  Lemma Closure_conversion_fundefs_find_def B1' B1 B2 c FVs f e1 ft xs:
      Closure_conversion_fundefs Size.Util.clo_tag B1' c FVs B1 B2 ->
      find_def f B1 = Some (ft, xs, e1) ->
      exists Γ e2 C Cf,
        find_def f B2 = Some (ft, Γ :: xs, Cf |[ C |[ e2 ]| ]|) /\
        make_closures Size.Util.clo_tag B1' Γ Cf /\
        Closure_conversion Size.Util.clo_tag (FromList xs :|: name_in_fundefs B1') c Γ FVs e1 e2 C.
  Proof.
    intros Hc Hdef; induction Hc.
    - simpl in Hdef.
      destruct (M.elt_eq f f0); subst.
      + inv Hdef. do 4 eexists. split; [| split ].
        * simpl. rewrite Coqlib.peq_true. reflexivity.
        * eassumption.
        * eassumption.
      + edestruct IHHc as (Γ & e2 & C' & Cf' & Hfind & Hmake & Hclo).
        * eassumption.
        * do 4 eexists. split; [| split ].
          simpl. rewrite Coqlib.peq_false; now eauto. eassumption.
          eassumption.
    - inv Hdef.
  Qed.

  Lemma make_closures_ctx_to_heap_env clo_tag B Γ C H rho :
    make_closures clo_tag B Γ C ->
    binding_in_map (Γ |: name_in_fundefs B) rho ->  
    exists H' rho' m,
      ctx_to_heap_env_CC C H rho H' rho' m.
  Proof with (now eauto with Ensembles_DB).
    intros Hclo. revert H rho. induction Hclo; intros H rho Hin.
    - do 3 eexists. econstructor.
    - edestruct (Hin f) as [l Hget]. now right; left.
      edestruct (Hin Γ) as [l' Hget']. now left.

      destruct (alloc (Constr clo_tag [l; l']) H) as [l1 H2'] eqn:Ha.
      edestruct (IHHclo H2' (M.set f (Loc l1) rho)) as (H'' & rho'' & m & Hctx).
      + eapply binding_in_map_antimon; [| eapply binding_in_map_set; eassumption ].
        simpl...
      + do 3 eexists. econstructor.
        simpl. rewrite Hget, Hget'. reflexivity.
        eassumption. eassumption.
  Qed.


  Lemma Closure_conversion_fundefs_correct
    (k : nat) :
    (* The IH *)
    forall  B1 B1' B1'' B2 B2'
       (H1 H1' H2 : heap block) (rho1 rho1c rho1' rho2 : env) b d
       (Scope Funs : Ensemble var)
       (H : ToMSet Funs) (FVs FVs': list var)
       (c : cTag) (Γ Γ' : var),
      well_formed (reach' H1 (env_locs rho1 (FV Scope FVs))) H1 ->
      env_locs rho1 (FV Scope FVs) \subset dom H1  ->
      well_formed (reach' H2 (env_locs rho2 (Γ' |: FV_cc Scope Γ))) H2 ->
      env_locs rho2 (Γ' |: FV_cc Scope Γ) \subset dom H2  ->
      injective_subdomain (reach' H1 (env_locs rho1 (FV Scope FVs))) b ->
      
      (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; PreG Funs; fun _ : nat => Post 0; b; d) (H2, rho2)) ->
      (forall j, Fun_inv k j (PreG Funs) (fun _ : nat => Post 0) b d rho1 H1 rho2 H2 Scope Γ) ->
      (forall j, FV_inv k j (PreG Funs) (fun _ : nat => Post 0) b d rho1 H1 rho2 H2 c Scope Γ FVs) ->
      
      (* Free variables invariant for new fundefs *)
      (forall j, FV_inv k j (PreG Funs) (fun i => Post 0) b d rho1c H1 rho2 H2 c
                   (Empty_set _) Γ' FVs') -> (* no scope, no funs yet *)
      FromList FVs' <--> occurs_free_fundefs B1' -> 

      fundefs_names_unique_fundefs B1 ->
      fundefs_names_unique_fundefs B1' ->

      (* B1'' is dummy *)
      Closure_conversion_fundefs Size.Util.clo_tag B1'' c FVs' B1 B2 ->
      (* for the inner def funs *)
      Closure_conversion_fundefs Size.Util.clo_tag B1' c FVs' B1' B2' ->    
      
      def_closures B1 B1' rho1 H1 rho1c = (H1', rho1') ->
      
      (forall j, Fun_inv k j (PreG Funs) (fun _ : nat => Post 0) b d rho1' H1' (def_funs B2 B2' rho2) H2
                    (name_in_fundefs B1) Γ').
  Proof with (now eauto with Ensembles_DB).
    Opaque cc_approx_exp.
    induction B1;
    intros B1' B1'' B2 B2' H1 H1' H2 rho1 rho1c rho1' rho2 b d
           Scope Funs H FVs FVs' c Γ Γ' 
           Hwf1 Hlocs1 Hwf2 Hlocs2 Hinj _ _ _ Hfvs' Hfveq
           Hun1 Hun2 Hccf1 Hccf2 Hclo j v' Hin.
    destruct (Hfvs' j) as (vs & lenv & Hgetlenv & Hget' & HallP).
    simpl in Hclo.
    - inv Hccf1. 
      destruct (def_closures B1 B1' rho1 H1 rho1c) as [Hc rhoc] eqn:Hdef'.
      destruct (alloc (Clos (FunPtr B1' v) rho1c) Hc) as [l1 H1''] eqn:Ha.
      inv Hclo.
      destruct (var_dec v v'); subst.
      + setoid_rewrite M.gss.
        exists l1, lenv, B2', v'. split. reflexivity.
        split. reflexivity. split. admit. (* disjoint *)
        destruct (alloc (Constr Size.Util.clo_tag [FunPtr B2' v'; Loc lenv]) H2)
          as [l2 H2''] eqn:Ha'.
        simpl. do 2 (erewrite gas; eauto). split.
        rewrite extend_gss. reflexivity.
        split. 
        rewrite extend_gss. reflexivity.
        split.
        * (* seems easy *) admit. 
        * intros b1 b2 rhoc' rhoc1 rhoc2 H3 H3' H4 lr xs1 ft ef vs1 vs2.
          intros Heq1 Hinj1 Heq2 Hinj2 Hf Hdef Hset.
          edestruct Closure_conversion_fundefs_find_def as
              (Γ'' & e2 & C' & Cf' & Hfind & Hmake & Hclo).
          now apply Hccf2. eassumption.
           
          edestruct (setlist_length rhoc1 (def_funs B2' B2' (M.empty value)) rhoc2 xs1 vs1 vs2)
            as [rho2' Hset2]; [ admit | now apply Hset | ].

          { do 3 eexists. split; [| split; [| split ]].
            - eassumption.
            - simpl. rewrite Hset2. reflexivity.
            - admit.
            - edestruct make_closures_ctx_to_heap_env
              with (rho := rho2')
                as (H2c & rho2c & mc & Hctxclo);
                  [ now apply Hmake | admit (* binding in map *)| ].
              
              edestruct (make_closures_correct i) as (b'' & d'' & Hrel & Hinv & Hinj' & Hdis');
                [ now apply Hmake | | | | | | | | | |
                | now apply Hctxclo | now eapply Hun2; eauto | | | | | ].
              
                + (* well-formed H11 *) 
                  eapply well_formed_reach_alloc_def_funs with (S := FV (Empty_set _) FVs');
                  [ | | | now apply Hdef ].
                  unfold FV.
                  rewrite Union_Empty_set_neut_l, Setminus_Empty_set_neut_r, Hfveq.

                  eapply well_formed_respects_heap_env_equiv; [| eassumption ].

                  rewrite reach'_alloc; [| eassumption | eapply reach'_extensive ].
                  
                  eapply well_formed_alloc; [| eassumption |].

                  eapply well_formed_antimon;
                    [
                    | eapply well_formed_reach_alloc_def_funs;
                      [ now apply Hwf1 | now apply Hlocs1 |  | now apply Hdef' ] ].
                  unfold FV.
                  admit.
                  (* eassumption. eassumption. *)
                  (* eapply Included_trans. *)
                  (* eapply Included_trans; [| eapply restrict_env_env_locs ]. *)
                  (* eapply env_locs_monotonic. now eauto with Ensembles_DB. *)
                  (* eapply restrict_env_correct. eapply fundefs_fv_correct. *)
                  (* eapply Included_trans; [| eapply reach'_extensive ]. *)
                  (* eapply env_locs_monotonic. *)
                  (* eapply Included_trans; [| eassumption ]. *)
                  (* normalize_occurs_free... *)
                  admit. admit. admit. admit. 
                + (* env_locs rc1 *)
                  eapply def_closures_env_locs_in_dom.
                  eassumption. admit.
                + (* well-formed H1' (def_funs B' B' (M.set Γ' (Loc lenv) rho2')) *)
                  admit.
                  (* eapply well_formed_antimon. *)
                  (* * eapply reach'_set_monotonic. *)
                  (*   eapply def_funs_env_loc. *)
                  (* * eapply well_formed_antimon; *)
                  (*   [| eapply well_formed_reach_alloc with (S := FromList FVs'' :|: FV_cc Scope Γ) ]. *)
                  (*   eapply reach'_set_monotonic. *)
                  (*   eapply env_locs_monotonic. unfold FV_cc... *)

                  (*   eapply project_vars_well_formed'. eassumption. eassumption. *)
                  (*   eapply Disjoint_Included_r; [ | eassumption ]. *)
                  (*   unfold FV_cc... eassumption. eassumption. *)

                  (*   eapply project_vars_env_locs'. eassumption. eassumption. *)
                  (*   eapply Disjoint_Included_r; [ | eassumption ]. *)
                  (*   unfold FV_cc... eassumption. eassumption. *)

                  (*   eassumption. *)

                  (*   simpl. *)
                  (*   rewrite env_locs_Union, reach'_Union. *)
                  (*   eapply Included_Union_preserv_l. *)
                  (*   rewrite env_locs_FromList; [| eassumption ]. *)
                  (*   eapply reach'_extensive. *)

                + (* env_locs (def_funs B' B' (M.set Γ' (Loc lenv) rho2')) *)
                  (* eapply Included_trans. eapply def_funs_env_loc. *)
                  (* eapply Included_trans. eapply env_locs_set_Inlcuded'. *)
                  (* rewrite HL.alloc_dom; [| eassumption ]. *)
                  (* eapply Included_Union_compat. reflexivity. *)

                  (* eapply Included_trans; [| eapply project_vars_env_locs' ]; *)
                  (* [| eassumption | eassumption | | eassumption | eassumption ]. *)

                  (* eapply env_locs_monotonic. unfold FV_cc... *)
                  (* eapply Disjoint_Included_r; [ | eassumption ]. *)
                  (* unfold FV_cc... *)
                  admit. 
                + admit. (* Disjoint + fresh fun locs after def_closures *)
                + admit. (* post fun locs after def_closures reachable *)
                + rewrite env_locs_Singleton with (v := Loc lenv); [| ].
                  * (* image b \in reach Η2 \in dom H2 <> lenv *)
                    admit.
                  * (* Γ' <> name B' *) admit.
                + intros j''. rewrite Setminus_Empty_set_abs_r.
                  eapply cc_approx_env_Empty_set.
                + cc_approx_env_P _neut_l. (* make_clo + IH k *)  admit.
                + }
      + simpl. setoid_rewrite (@M.gso _ v' v); eauto.
        setoid_rewrite (@M.gso _ Γ' v); eauto.
        eapply Fun_inv_subheap;
          [ | | | |
            | (eapply IHB1;
               [ | | | | | | | | | | | | eassumption | | ])
            | | | ]; try eassumption.
        * eapply well_formed_antimon; 
          [| eapply well_formed_reach_alloc_def_funs;
             [ now apply Hwf1 | | | eassumption ]
          ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          unfold FV...
          eassumption.
          (* env_locs rho1c (occurs_free_fundefs B1') \subset
             reach' H1 (env_locs rho1 (FV Scope FVs)) *)
          admit.
        * eapply Included_trans;
          [| eapply def_closures_env_locs_in_dom; eassumption ].
          eapply env_locs_monotonic. unfold FV...
        * eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply Included_trans. eapply def_funs_env_loc.
          eapply env_locs_monotonic...
        * eapply Included_trans. eapply def_funs_env_loc.
          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic...
        * admit.
        * intros B' Hin'. inv Hin'; subst; eauto.
          specialize (Hun1 _ (or_intror eq_refl)). inv Hun1. eassumption.
        * eapply HL.alloc_subheap. eassumption.
        * eapply HL.subheap_refl.
        * inv Hin; eauto. inv H0; exfalso; eauto.
        * admit. (* extra assumption *)
    - inv Hin.
      
  (* Lemma make_closures_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b *)
  (*       Scope Funs c Γ FVs xs xs' C S S' m : *)
  (*   make_closures Size.Util.clo_tag B fvset Γ' C -> *)
    
    
  (*   ctx_to_heap_env_CC C H2 rho2 H2' rho2' m -> *)

  (*   binding_in_map Scope rho1 ->  *)
  (*   Disjoint _ S (FV_cc Scope Funs Γ) -> *)

  (*   Disjoint _ (FromList xs') S' /\ *)
  (*   (forall j, (H1, rho1) ⋞ ^ ((((name_in_fundefs B) :&: fvset) :|: Scope) ; k; j; GII; GI; b) (H2', rho2'))  /\ *)
  (*   (forall j, Fun_inv k j GII GI b rho1 H1 rho2' H2' (((name_in_fundefs B) :&: fvset) :|: Scope) Funs) /\ *)
  (*   (forall j, FV_inv k j GII GI b rho1 H1 rho2' H2' c (((name_in_fundefs B) :&: fvset) :|: Scope) Funs Γ FVs. *)
  (* Proof with (now eauto with Ensembles_DB). *)
  (*   Intros Hvars. revert m H1 rho1 H2 rho2 H2' rho2'. *)
  (*   induction Hvars; intros m H1 rho1 H2 rho2 H2' rho2' Hcc Hfun Hfv Hctx Hb Hd.  *)
  (*   - inv Hctx. split; [| split; [| split ; [| split ]]]; eauto. *)
  (*     rewrite FromList_nil... *)
  (*   - rewrite FromList_cons in *.  *)
  (*     edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]]. *)
  (*     subst. *)
  (*     eassumption. subst. *)
  (*     edestruct project_var_correct as (Hd' & Hcc' & Hfun' & Hfv' & Hall'); *)
  (*       try eassumption. *)
  (*     edestruct IHHvars as (Hd'' & Hcc'' & Hfun'' & Hfv'' & Hall''); *)
  (*     try eassumption. *)
  (*     eapply Disjoint_Included_l; [| eassumption ]. *)
  (*     eapply project_var_free_set_Included. eassumption. *)
  (*     split; [| split; [| split ; [| split ]]]; eauto. *)
  (*     * eapply Union_Disjoint_l.  *)
  (*       eapply Disjoint_Included_r. *)
  (*       eapply project_vars_free_set_Included. eassumption. *)
  (*       eapply Disjoint_Singleton_l. *)
  (*       eapply project_var_not_In_free_set'. eassumption. *)
  (*       eapply Disjoint_Included_r; [| eassumption ]. *)
  (*       unfold FV_cc... *)
  (*       eapply Disjoint_sym. eapply project_vars_not_In_free_set'. eassumption. *)
  (*       eapply Disjoint_Included_l. *)
  (*       eapply project_var_free_set_Included. eassumption. *)
  (*       eapply Disjoint_Included_r; [| eassumption ]. *)
  (*       unfold FV_cc... *)
  (*     * intros j. constructor; eauto . *)
  (*       eapply project_vars_preserves_cc_approx; eauto. *)
  (* Qed. *)
*)

  Lemma FV_inv_binding_in_map k j P Q b d rho1 H1 rho2 H2 c Scope Γ FVs :
    FV_inv k j P Q b d rho1 H1 rho2 H2 c Scope Γ FVs ->
    binding_in_map [set Γ ] rho2.
  Proof.
    intros (vs & l & Hget & _).
    intros x Hin; inv Hin; eauto.
  Qed.

  Lemma binding_in_map_Union {A} S1 S2 (rho : M.t A) :
    binding_in_map S1 rho ->
    binding_in_map S2 rho ->
    binding_in_map (S1 :|: S2) rho.
  Proof.
    intros Hin1 Hin2 x Hin. inv Hin; eauto.
  Qed.

  Lemma cc_approx_env_binding_in_map Scope k j P Q b d rho1 H1 rho2 H2 :
    (H1, rho1) ⋞ ^ (Scope; k; j; P; Q; b; d) (H2, rho2) ->
    binding_in_map Scope rho1 ->
    binding_in_map Scope rho2.
  Proof.
    intros Henv Hbin x Hin.
    edestruct (Hbin x) as [l Hget]. eassumption.
    edestruct Henv as [l' [Hget' _]]. eassumption.
    eassumption. eauto.
  Qed. 

  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct (k : nat) (H1 H2 : heap block)
        (rho1 rho2 : env) (e1 e2 : exp) (C : exp_ctx)
        (Scope Funs : Ensemble var) `{HD: Decidable _ Scope} `{ToMSet Funs} (FVs : list var)
        (β : Inj) (δ : EInj) (c : cTag) (Γ : var) :
    (* [Scope] invariant *)
    (forall j, (H1, rho1) ⋞ ^ (Scope ; k ; j ; PreG Funs; (fun i => Post 0) ; β; δ) (H2, rho2)) ->
    (* Free variable invariant *)
    (forall j, FV_inv k j (PreG Funs) (fun i => Post 0) β δ rho1 H1 rho2 H2 c Scope Γ FVs) ->

    injective_subdomain (reach' H1 (env_locs rho1 (FV Scope FVs))) β ->
    Disjoint _ (image β (reach' H1 (env_locs rho1 (FV Scope FVs))))
             (image' δ (reach' H1 (env_locs rho1 (FV Scope FVs)))) ->    
    
    (* well-formedness *)
    well_formed (reach' H1 (env_locs rho1 (FV Scope FVs))) H1 ->
    (env_locs rho1 (FV Scope FVs)) \subset dom H1 ->
    well_formed (reach' H2 (env_locs rho2 (FV_cc Scope Γ))) H2 ->
    (env_locs rho2 (FV_cc Scope Γ)) \subset dom H2 ->
    
    (* [Γ] (the current environment parameter) is not bound in e *)
    ~ In _ (bound_var e1) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (FV Scope FVs) rho1 ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e1 ->
    
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion Size.Util.clo_tag Scope c Γ FVs e1 e2 C ->
    
    (forall j, (e1, rho1, H1) ⪯ ^ (k ; j ; Pre ; PreG Funs ; Post 0 ; fun i => Post 0) (C |[ e2 ]|, rho2, H2)).

  Proof with now eauto with Ensembles_DB.
    revert H1 H2 rho1 rho2 e1 e2 C Scope HD Funs H FVs β δ c Γ.
    induction k as [k IHk] using lt_wf_rec1.  
    intros H1 H2 rho1 rho2 e1 e2 C Scope HD Funs HMSet FVs b d c Γ
           Henv HFVs Hinj1 Hinj2 Him Hwf1 Hlocs1 Hwf2 Hlocs2 Hnin Hbind Hun Hcc.
    assert (Hfv := Closure_conversion_pre_occurs_free_Included _ _ _ _ _ _ _ Hcc).
    assert (Hfv' := Closure_conversion_occurs_free_Included _ _ _ _ _ _ _ Hcc Hun).
    induction e1 using exp_ind'; try clear IHe1.
    - (* case Econstr *)
      inv Hcc.
      
      edestruct (binding_in_map_getlist _ rho1 l Hbind) as [vl Hgetl].
      eapply project_vars_In_Union. eassumption.
       
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
      
      assert (Hwf2' := Hwf2).
      assert (Hlocs2' := Hlocs2). 
      eapply project_vars_well_formed' in Hwf2; try eassumption;
      [| eapply Disjoint_Included_r; try eassumption; unfold FV_cc; now eauto with Ensembles_DB ].
      eapply project_vars_env_locs' in Hlocs2; try eassumption;
      [| eapply Disjoint_Included_r; try eassumption; unfold FV_cc; now eauto with Ensembles_DB ].
      
      edestruct project_vars_correct as (Hd' & Henv' & HFVs' & Hvars);
        try eassumption.
      eapply binding_in_map_antimon; [| eassumption ]...
      
      (* process Econstr one the right and left *)
      eapply cc_approx_exp_constr_compat; [ | | | | | | | eassumption |  ].
      + eapply PostConstrCompat. eapply (Hvars 0).
        eapply project_vars_cost. eassumption.
      + eapply PreConstrCompat. eapply (Hvars 0).
      + eapply PostBase. simpl.
        eapply le_trans.
        eapply project_vars_cost. eassumption. omega.
      + eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
      + eapply project_vars_well_formed; eauto.
        eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic.
        eassumption. eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
      + eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic.
        eassumption.
      + eapply project_vars_env_locs; eauto. eapply Included_trans. 
        eapply env_locs_monotonic. eassumption. eassumption.
        eapply well_formed_antimon.
        eapply reach'_set_monotonic. eapply env_locs_monotonic. eassumption.
        eassumption.

      + (* Inductive case *)  
        intros vs1 vs2 l1 l2 H1' H2'' Hleq Ha1 Ha2 Hr1 Hr2 Hall j1.
        (* monotonicity of the local invariant *) 
        assert (Hfeq : f_eq_subdomain (reach' H1 (env_locs rho1 (FV Scope FVs))) b (b {l1 ~> l2})).
        { eapply f_eq_subdomain_extend_not_In_S_r; [| reflexivity ].
          intros Hc. eapply reachable_in_dom in Hc.
          edestruct Hc as [vc Hgetc]. erewrite alloc_fresh in Hgetc; eauto. congruence.
          eassumption. eassumption. }
        assert (Hfeq' : f_eq_subdomain (reach' H1 (env_locs rho1 (FV Scope FVs))) d (d {l1 ~> None})).
        { eapply f_eq_subdomain_extend_not_In_S_r; [| reflexivity ].
          intros Hc. eapply reachable_in_dom in Hc.
          edestruct Hc as [vc Hgetc]. erewrite alloc_fresh in Hgetc; eauto. congruence.
          eassumption. eassumption. }
        (* Induction hypothesis *)
        { eapply IHk;
          [ | | | | | | | | | | | | | | eassumption ].
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
  