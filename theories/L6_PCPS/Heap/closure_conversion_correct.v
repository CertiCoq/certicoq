From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics.

From L6.Heap Require Import heap heap_defs heap_equiv space_sem cc_log_rel size_cps closure_conversion
     closure_conversion_util.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega.

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
    H1 << ^ (k; j; IP; P; b; d; env_locs rho1 (FromList FVs)) (l, H2).
  Proof.
    intros (vs & l' & Hget1 & Hget2 & Hall) Hget1'. subst_exp.
    clear Hget1. eexists c, vs. setoid_rewrite Hget2. clear Hget2.
    induction Hall.
    - eexists []. split. reflexivity. split. rewrite !FromList_nil, env_locs_Empty_set.
      reflexivity.
      constructor.
    - edestruct H as [v1 [Hget1 Hres1]]. intros Hc; now inv Hc.
      edestruct IHHall as (FLs & _ & Heq & Hal').
      destruct v1 as [l1|]; try contradiction.
      destruct y as [l2|]; try contradiction. 
      
      eexists; split. reflexivity. split; [| constructor 2; try eassumption ].
      rewrite !FromList_cons, env_locs_Union. eapply Same_set_Union_compat.
      rewrite env_locs_Singleton; try eassumption. simpl; reflexivity.
      eassumption.
      rewrite cc_approx_val_eq. eassumption.
  Qed.


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

  Require Import Permutation.
  

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
      + assert (Hdec : Decidable (image' d S1')) by admit.
        
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

          Lemma cc_approx_heap_size k j GIP GP b d H1 H2 x y v v' :
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
              rewrite <- plus_n_O. simpl. 

              simpl. 
              NPeano.Nat.lt_0_1).
            
          assert (Hleqv : size_val v <= size_val v' <= (size_val v) *  (1 + max_vars_heap H1)).
          { admit. } 
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
          { admit. } 
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

          assert (Hleqv : size_val v <= size_val v' <= (size_val v) *  (1 + max_vars_heap H1)).
          { admit. } 
          split. omega.
          rewrite Nat.mul_add_distr_r. omega. 
  Admitted.
  
    
  Lemma size_reachable_leq S1 `{HS1 : ToMSet S1}  S2 `{HS2 : ToMSet S2}
        H1 H2 k GIP GP b d :
    (forall j, S1 |- H1 ≼ ^ (k ; j ; GIP ; GP ; b ; d ) H2) ->
    image b S1 \subset S2 ->
    (* S2 \subset image b S1 :|: image' d S1 -> *)
    injective_subdomain S1 b ->
    (* injective_subdomain' S1 d -> *)
    (* Disjoint _ (image b S1) (image' d S1) ->  *)
    size_with_measure_filter size_val S1 H1 <=
    size_with_measure_filter size_val S2 H2.
    (* (size_with_measure_filter size_val S1 H1) * (1 + (max_vars_heap H1)). *)
  Proof with (now eauto with Ensembles_DB).
    assert (HS1' := HS1).
    revert HS1 S2 HS2.
    set (P := (fun S1 => 
                 forall (HS1 : ToMSet S1) (S2 : Ensemble positive) (HS2 : ToMSet S2),
                   (forall j, S1 |- H1 ≼ ^ (k; j; GIP; GP; b; d) H2) ->
                   image b S1 \subset S2 ->
                   S2 \subset image b S1 :|: image' d S1 ->
                   injective_subdomain S1 b ->
                   injective_subdomain' S1 d ->
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
    - intros HS1 S2 HS2 Hcc Hsub1 Hsub2 Hinj1 (* Hinj2 HD *) _ _.
      rewrite !HL.size_with_measure_filter_Empty_set.
      rewrite image_Empty_set, image'_Empty_set in Hsub2.
      rewrite Union_Empty_set_neut_r in Hsub2.
      simpl.
      eapply Included_Empty_set_l in Hsub2. symmetry in Hsub2.
      erewrite (@HL.size_with_measure_Same_set _ _ _ _ _ _ _ Hsub2).
      rewrite HL.size_with_measure_filter_Empty_set. omega.
    - intros x S1' HS Hnin IHS HS1 S2 HS2 Hheap Hsub1 Hsub2 Hinj1 (* Hinj2 HD *) _ _.
      rewrite !image_Union, !image'_Union, !image_Singleton in Hsub2.
      rewrite !image_Union, !image_Singleton in Hsub1.
      assert (Hseq : S2 <--> b x |: (image' d [set x]) :|: (S2 \\ (b x |: (image' d [set x])))). 
      { 
      Hsub2.
      unfold mset.
      assert (HS1'' := HS1). eapply ToMSet_add in HS1''; [| eassumption ]. 
      assert (Hseq : S2 <--> b x |: (image' d [set x]) :|: (S2 \\ (b x |: (image' d [set x])))). 
      { eapply Union_Setminus_Same_set.
        eapply Decidable_Union. eapply DecidableSingleton_positive.
        
        destruct (d x) eqn:Heqd.
        eapply Decidable_Same_set. 
        erewrite image'_Singleton_Some. reflexivity. eassumption.
        now eauto with typeclass_instances.

        eapply Decidable_Same_set. 
        erewrite image'_Singleton_None. reflexivity. eassumption.
        now eauto with typeclass_instances.
        eapply I
        rewrite Heq. now eauto with Ensembles_DB. }

      assert (HS2' : ToMSet (S2 \\ (b x |: image' d [set x])))
        by now eauto with typeclass_instances.
      
      specialize (IHS HS1'' _ HS2').
       
      assert (Hcc : (forall j, Res (Loc x, H1) ≺ ^ (k ; j ; GIP ; GP ; b ; d) Res (Loc (b x), H2))).
      { intros j; eapply Hheap. now left. }
      
      assert (Hseq' : b x |: image b S1' :|: (image' d [set x] :|: image' d S1') <-->
                        b x |: image' d [set x] :|: (image b S1' :|: image' d S1')).

      { rewrite <- Union_assoc, (Union_assoc (image b S1'))... }
      rewrite Hseq' in Heq.
      
      assert (Hseq'' :  S2 \\ (b x |: image' d [set x]) <--> image b S1' :|: image' d S1').
      { rewrite Heq. rewrite Setminus_Union_distr.
        rewrite Setminus_Same_set_Empty_set. rewrite Union_Empty_set_neut_l.
        rewrite Setminus_Disjoint. reflexivity.
        rewrite image_Union, image'_Union, image_Singleton in HD.
        
        eapply Union_Disjoint_l; eapply Union_Disjoint_r. 
        + eapply Disjoint_Singleton_r. intros [y [Hin Hc]].
          eapply Hinj1 in Hc. now subst; eauto.
          now right. now left.
        + eapply Disjoint_Included; [| | eassumption ]...
        + eapply Disjoint_sym. eapply Disjoint_Included; [| | eassumption ]...
        + constructor. intros l1. intros [l2 [y [Hin1 Hc1]] [y' [Hin2 Hc2]]].
          inv Hin2. eapply Hinj2 in Hc2. eapply Hc2 in Hc1. now subst; eauto.
          now left. now right. }

      destruct (get x H1) as [v | ] eqn:Hget1;
        [| destruct (Hcc 0) as [_ Hcc']; rewrite Hget1 in Hcc'; contradiction ]. 
      
      erewrite (HL.size_with_measure_Same_set _ _ _ _ H2 Hseq).
      erewrite HL.size_with_measure_filter_add_In; try eassumption. 
      erewrite HL.size_with_measure_filter_Union.
      + assert (Hleq :
                  size_with_measure_filter size_val S1' H1 <=
                  size_with_measure_filter size_val (S2 \\ (b x |: image' d [set x]))
                                           H2 <=
                  size_with_measure_filter size_val S1' H1 * (1 + max_vars_heap H1)).
        { eapply IHS.
          - intros j. eapply cc_approx_heap_antimon; [| now eapply Hheap; eauto ]...
          - eassumption.
          - eapply injective_subdomain_antimon; [ eassumption |]...
          - eapply injective_subdomain'_antimon; [ eassumption |]...
          - eapply Disjoint_Included; [| | eassumption ]... }
        assert (Hleqv : size_val v <=
                        size_with_measure_filter size_val (b x |: image' d [set x]) H2 <=
                        (size_val v) *  (1 + max_vars_heap H1)).
        { admit. } 
        split. omega.
        rewrite Nat.mul_add_distr_r. omega. 
      + eapply Disjoint_Setminus_r. reflexivity.
  Admitted. 
  

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
           (forall H2',
              H2 ⊑ H2' ->
              let '(l2, H2'') := alloc (Constr Size.Util.clo_tag [FunPtr B g; Loc lenv]) H2' in
              Res (Loc l1, H1) ≺ ^ (k; j; GI; GP; b{l1 ~> l2}; d{l1 ~> Some lenv}) Res (Loc l2, H2'')). 
  
  Lemma cc_approx_val_heap_monotonic_alloc_l GIP GP (k j : nat) (β : Inj)
        δ (H1 H2 H2' H3 H3' : heap block)
       b l1 l3 l3' :
     well_formed (reach' H1 [set l1]) H1 ->
     well_formed (reach' H2 (locs b)) H2 ->
     l1 \in dom H1 ->
     locs b \subset dom H2 ->
     H2 ⊑ H2' ->
     alloc b H2 = (l3, H3) ->
     Res (Loc l1, H1) ≺ ^ (k ; j; GIP ; GP ; β {l1 ~> l3}; δ) Res (Loc l3, H3) ->
     alloc b H2' = (l3', H3') ->
     Res (Loc l1, H1) ≺ ^ (k ; j; GIP ; GP; β {l1 ~> l3'}; δ) Res (Loc l3', H3').
  Proof with (now eauto with Ensembles_DB).
    intros Hwf1 Hwf2 Hin1 Hin2 Hsub1 Ha1 Hcc Ha2.
     simpl in Hcc. destruct Hcc as [Heq Hcc].
     erewrite (gas _ _ _ _ _ Ha1) in Hcc. 
     destruct (get l1 H1) as [b1|] eqn:Hget1;
       try contradiction;
       try (now destruct b1 as [c1 vs1 | [? | B1 f1 ] env_loc1 ]; contradiction).
     destruct b1 as [c1 vs1 | [? | B1 f1 ] env_loc1 ];
       destruct b as [c2 vs2 | ]; try contradiction. 
    + destruct Hcc as [Hceq [Hd Hlt]].
      split. rewrite extend_gss. reflexivity.
      rewrite Hget1. erewrite gas; eauto. split. eassumption.
      split. eassumption. intros i Hleq. simpl.
      eapply Forall2_monotonic_strong; [| eapply Hlt; eassumption ].
      intros x1 x2 Hinx1 Hinx2 Hr.
      rewrite cc_approx_val_eq in *. admit.
    + destruct vs2 as [| [|] [| [|] [|] ]]; try contradiction.
      destruct Hcc as [Heq1 Hall]. split. rewrite extend_gss. reflexivity.
      rewrite Hget1. erewrite gas; eauto. simpl. split. eassumption.
      intros. 
  Abort.

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

  Lemma Fun_inv_subheap k j GI GP b d rho1 H1 rho2 H2 H2' funs Γ :
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 funs Γ ->
    H2 ⊑ H2' ->
    Fun_inv k j GI GP b d rho1 H1 rho2 H2' funs Γ.
  Proof.
    intros Hfun Hsub x Hin.
    edestruct Hfun as (l1 & lenv & B1' & g & Hget1 & Hget2 & Hget3 & Heq). eassumption.
    repeat eexists; try eassumption.
    intros H2'' Hsub'. eapply Heq. eapply HL.subheap_trans; eassumption.
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
    intros H2'' Hsub'. specialize (Heq H2'' Hsub').
    destruct (alloc (Constr Size.Util.clo_tag [FunPtr B1' g; Loc lenv]) H2'') as [l2 H2'].
    assert (Hseq : l1 |: (reach' H1 (val_loc (Loc l1))) <--> reach' H1 (val_loc (Loc l1))).
    { split. eapply Union_Included. eapply Singleton_Included. eapply reach'_extensive. reflexivity. reflexivity.
      eapply Included_Union_preserv_r. reflexivity. }
    eapply cc_approx_val_rename_ext. eassumption.

    rewrite <- Hseq.  eapply f_eq_subdomain_extend. symmetry.
    eapply f_eq_subdomain_antimon; [ | eassumption ]. eapply reach'_set_monotonic.
    eapply get_In_env_locs. eassumption. eassumption.

    rewrite <- Hseq.  eapply f_eq_subdomain_extend. symmetry.
    eapply f_eq_subdomain_antimon; [ | eassumption ]. eapply reach'_set_monotonic.
    eapply get_In_env_locs. eassumption. eassumption.
  Qed.


  Instance Proper_FV_inv k j GI GP b d rho1 H1 rho2 H2 c : Proper (Same_set _ ==> eq ==> eq ==> iff)
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

  Lemma make_closures_correct k j GI GP b d C c rho1 H1 rho2 H2 rho2'
        H2' Scope FVs B1 Γ m :
    (* make closures *)
    make_closures Size.Util.clo_tag B1 Γ C ->
    (* well-formedness *)
    well_formed (reach' H1 (env_locs rho1 (FV Scope FVs :|: name_in_fundefs B1))) H1 ->
    env_locs rho1 (FV Scope FVs :|: name_in_fundefs B1) \subset dom H1  ->
    well_formed (reach' H2 (env_locs rho2 (FV_cc Scope Γ))) H2 ->
    env_locs rho2 (FV_cc Scope Γ) \subset dom H2  ->
    (* Closure pointers are fresh locations *)
    (forall f, f \in name_in_fundefs B1 ->
                Disjoint _ (env_locs rho1 [set f])
                         (reach' H1 (env_locs rho1 (FV Scope FVs :|: (name_in_fundefs B1 \\ [set f]))))) ->
    reach' H1 (post H1 (env_locs rho1 (name_in_fundefs B1))) \subset reach' H1 (env_locs rho1 (FV Scope FVs)) -> 
    
    (* Environment relations *)
    (H1, rho1) ⋞ ^ (Scope; k; j; GI; GP; b; d) (H2, rho2) ->
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 (name_in_fundefs B1) Γ ->
    FV_inv k j GI GP b d rho1 H1 rho2 H2 c Scope Γ FVs -> 
    (* Context interpretation *)
    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->

    (* names *)
    unique_functions B1 ->
    ~ Γ \in (name_in_fundefs B1) ->

    (* Injectivity  *)
    injective_subdomain (reach' H1 (env_locs rho1 (FV Scope FVs))) b ->
    injective_subdomain' (reach' H1 (env_locs rho1 (FV Scope FVs))) d ->
    Disjoint _ (image b (reach' H1 (env_locs rho1 (FV Scope FVs)))) (image' d (reach' H1 (env_locs rho1 (FV Scope FVs)))) ->

    
    exists b' d',
      (H1, rho1) ⋞ ^ ((name_in_fundefs B1) :|: Scope; k; j; GI; GP; b'; d') (H2', rho2') /\
      FV_inv k j GI GP b' d' rho1 H1 rho2' H2' c ((name_in_fundefs B1) :|: Scope) Γ FVs /\ 
      injective_subdomain (reach' H1 (env_locs rho1 (FV ((name_in_fundefs B1) :|: Scope) FVs))) b' /\
      injective_subdomain' (reach' H1 (env_locs rho1 (FV ((name_in_fundefs B1) :|: Scope) FVs))) d' /\
      Disjoint _ (image b' (reach' H1 (env_locs rho1 (FV ((name_in_fundefs B1) :|: Scope) FVs))))
               (image' d'  (reach' H1 (env_locs rho1 (FV ((name_in_fundefs B1) :|: Scope) FVs)))).
  (* injective_subdomain (reach' H1' (env_locs rho1' (FV (name_in_fundefs B1 :&: fvs :|: Scope) FVs))) b' *)
  Proof with (now eauto with Ensembles_DB).
    intros Hclo.
    revert m rho1 H1 rho2 H2 rho2' H2' Scope b d.
    induction Hclo as [Γ | f xs t e B ];
      intros m rho1 H1 rho2 H2 rho2' H2' Scope b d
             Hwf1 Hlocs1 Hwf2 Hlocs2 Hdis Hrsub Hlr Hfun Hfv Hctx Hun Hnin Hin1 Hin2 Hdinj.
    - inv Hctx. simpl name_in_fundefs. 
      repeat setoid_rewrite Union_Empty_set_neut_l at 1.
      do 2 eexists.
      split; [| split; [| split; [| split] ]]; try eassumption.
    - inv Hctx.
      simpl name_in_fundefs.
      simpl in H12.

      edestruct Hfun as (l1 & lenv & B1' & g & Hget1 & Hget2 & Hget3 & Heq).
      now left.
      
      simpl in H11. rewrite Hget2, Hget3 in H11. inv H11.

      specialize (Heq H2 (HL.subheap_refl H2)). rewrite H12 in Heq.
      assert (Hseq : (f |: name_in_fundefs B)  :|: Scope <-->
                                               name_in_fundefs B :|: (f |: Scope))
        by eauto with Ensembles_DB.
      
      repeat setoid_rewrite Hseq at 1.
      inv Hun.
      eapply IHHclo with (b := b {l1 ~> l}) (d := d{l1 ~> Some lenv});
        [ | | | | | | | | | eassumption | eassumption | | | | ].
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
      + unfold FV_cc. rewrite <- Union_assoc, Union_commut.
        eapply well_formed_reach_alloc'; try eassumption.
        * rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r. eassumption.
        * rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r. eassumption.
        * simpl. rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r.
          eapply Singleton_Included.
          rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
          eapply reach'_extensive. eapply get_In_env_locs. now right. eassumption.
          reflexivity.
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
        eapply reach'_set_monotonic. eapply post_set_monotonic.
        eapply env_locs_monotonic...
        eapply reach'_set_monotonic. unfold FV. 
        eapply env_locs_monotonic.
        rewrite (Union_commut [set f]) at 2. rewrite <- Setminus_Union.
        rewrite (Union_Setminus_Included _ _ [set f]); eauto with typeclass_instances.
        now eauto with Ensembles_DB.
        now eauto with Ensembles_DB.
      + assert (Hsub : f |: Scope \subset f |: (Scope \\ [set f])).
        { intros x Hin.
          destruct (var_dec x f); subst; eauto.
          inv Hin; eauto. right; constructor; eauto.
          intros Hc; inv Hc; eauto. }
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
              eapply cc_approx_env_P_antimon; [ eassumption |]...
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
            - intros Hc; inv Hc; eauto. }
      + eapply Fun_inv_set_r. eapply Fun_inv_subheap. eapply Fun_inv_rename_ext.
        intros x Hin. eapply Hfun. now right.
        
        eapply f_eq_subdomain_extend_not_In_S_r.
        intros Hc. eapply Hdis. now left.
        constructor. rewrite env_locs_Singleton; eauto. reflexivity.
        eapply reach'_set_monotonic; [| eassumption ].
        eapply env_locs_monotonic. simpl. rewrite !Setminus_Union_distr.
        rewrite (Setminus_Disjoint (name_in_fundefs B) [set f]).
        now eauto with Ensembles_DB. eapply Disjoint_Singleton_r.
        eassumption. reflexivity. 

        eapply f_eq_subdomain_extend_not_In_S_r.
        intros Hc. eapply Hdis. now left.
        constructor. rewrite env_locs_Singleton; eauto. reflexivity.
        eapply reach'_set_monotonic; [| eassumption ].
        eapply env_locs_monotonic. simpl. rewrite !Setminus_Union_distr.
        rewrite (Setminus_Disjoint (name_in_fundefs B) [set f]).
        now eauto with Ensembles_DB. eapply Disjoint_Singleton_r.
        eassumption. reflexivity. 
        
        eapply HL.alloc_subheap. eassumption.

        eassumption. intros Hc. eapply Hnin. subst. now left.
      + eapply FV_inv_set_not_in_FVs_r.
        eapply FV_inv_Scope_mon with (Scope := Scope); try eauto with Ensembles_DB.
        
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
        * eapply FV_inv_rename_ext. eassumption.
          
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
      + assert (Hfveq : FV (f |: Scope) FVs \subset f |: FV Scope FVs).
        { unfold FV... }
        eapply injective_subdomain_antimon; [| eapply reach'_set_monotonic; eapply env_locs_monotonic; eassumption ].
        eapply injective_subdomain_extend'. rewrite env_locs_Union.
        rewrite env_locs_Singleton; eauto. simpl. 
        rewrite reach'_Union. rewrite reach_unfold.
        rewrite <- Union_assoc. rewrite (Union_Same_set (reach' _ _)).
        rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set.
        rewrite Union_Empty_set_neut_l.
        eapply injective_subdomain_antimon; [ eassumption |]...
        eapply Included_trans; [| eassumption ]. simpl.
        rewrite env_locs_Union.
        rewrite env_locs_Singleton; eauto. simpl. 
        rewrite post_Union, reach'_Union...
        
        admit.
      + assert (Hfveq : FV (f |: Scope) FVs \subset f |: FV Scope FVs).
        { unfold FV... }
        eapply injective_subdomain'_antimon; [| eapply reach'_set_monotonic; eapply env_locs_monotonic; eassumption ].
        (* eapply injective_subdomain'_extend. rewrite env_locs_Union. *)
        (* rewrite env_locs_Singleton; eauto. simpl.  *)
        (* rewrite reach'_Union. rewrite reach_unfold. *)
        (* rewrite <- Union_assoc. rewrite (Union_Same_set (reach' _ _)). *)
        (* rewrite Setminus_Union_distr. rewrite Setminus_Same_set_Empty_set. *)
        (* rewrite Union_Empty_set_neut_l. *)
        (* eapply injective_subdomain_antimon; [ eassumption |]... *)
        (* eapply Included_trans; [| eassumption ]. simpl. *)
        (* rewrite env_locs_Union. *)
        (* rewrite env_locs_Singleton; eauto. simpl.  *)
        (* rewrite post_Union, reach'_Union... *)
        admit.
        (* admit. *)
      + eapply Disjoint_Included_l.
        eapply image_extend_Included'.
        eapply Disjoint_Included_r
        with (s2 := image' d (reach' H1 (env_locs rho1 (FV (f |: Scope) FVs)) \\ [set l1]) :|: [set lenv]).
        admit.

        eapply Union_Disjoint_l.
        eapply Union_Disjoint_r.
        admit. (* assumption *)

        eapply Disjoint_Singleton_r.
        eapply image_extend_Included'.
        
        rewrite image_extend_not_admit.
        intros Hc. eapply Hdis. right. eassumption.
        constructor. rewrite env_locs_Singleton; eauto. reflexivity.
        simpl. rewrite !env_locs_Union, !reach'_Union. 
        eapply reach'_set_monotonic; [| eassumption ]. 
        eapply env_locs_monotonic. simpl. unfold FV...
        reflexivity.
        
        rewrite reach_unfold.
        
        erewrite alloc_fresh; eauto.
        
        
        post _Single
        re 
        eapply Setminus_Included_Included_Union.
        unfold FV. rewrite rec
        eapply Included_trans.
        u
        eapply reach'_set_monotonic. eauto.
        
      + assert (Hsub : f |: Scope \subset f |: (Scope \\ [set f])).
        { intros x Hin.
          destruct (var_dec x f); subst; eauto.
          inv Hin; eauto. right; constructor; eauto.
          intros Hc; inv Hc; eauto. }
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
              eapply cc_approx_env_P_antimon; [ eassumption |]...
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
            - intros Hc; inv Hc; eauto. }
      + inv Hun; eassumption.
      + intros Hc. eapply Hnin; right; eauto.
    - assert (Hseq : (f |: name_in_fundefs B) :&: fvs :|: Scope <-->
                     name_in_fundefs B :&: fvs :|: Scope). 
      { rewrite Intersection_Union_distr. rewrite Intersection_Disjoint.
        rewrite Union_Empty_set_neut_l. reflexivity. eapply Disjoint_Singleton_l. eassumption. }
      setoid_rewrite Hseq.
      eapply IHHclo; try eassumption.
      + eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic. simpl. eapply env_locs_monotonic...
      + eapply Included_trans; [| eassumption ].
        simpl. eapply env_locs_monotonic...
      + intros f' Hf. eapply Disjoint_Included_r; [ | eapply Hdis; right; eassumption ].
        simpl. eapply reach'_set_monotonic. eapply env_locs_monotonic...
      + intros x Hin. eapply Hinv. now right.
      + now inv Hun. 
      + intros Hc. eapply Hnin. now right.
  Qed. 
  
(*
  Lemma Closure_conversion_fundefs_correct
    (k : nat)
    (* The IH *)
    (IHk : forall m : nat,
             m < k ->
             forall (H1 H2 : heap block) (rho1 rho2 : env)
               (e1 e2 : exp) (C : exp_ctx) (Scope Funs : Ensemble var)
               (H : ToMSet Funs) (FVs : list var) (β : Inj)
               (c : cTag) (Γ : var),
               (forall j : nat,
                  (H1, rho1) ⋞ ^ (Scope; m; j; PreG Funs; fun _ : nat => Post 0;
                                  β) (H2, rho2)) ->
               (forall j : nat,
                  Fun_inv m j (PreG Funs) (fun _ : nat => Post 0) β rho1 H1 rho2 H2
                          Scope Funs) ->
               (forall j : nat,
                  FV_inv m j (PreG Funs) (fun _ : nat => Post 0) β rho1 H1 rho2 H2 c
                         Scope Funs Γ FVs) ->
               injective_subdomain (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) β ->
               well_formed (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) H1 ->
               env_locs rho1 (FV Scope Funs FVs) \subset dom H1 ->
               well_formed (reach' H2 (env_locs rho2 (FV_cc Scope Funs Γ))) H2 ->
               env_locs rho2 (FV_cc Scope Funs Γ) \subset dom H2 ->
               ~ In var (bound_var e1) Γ ->
               binding_in_map (FV Scope Funs FVs) rho1 ->
               fundefs_names_unique e1 ->
               Disjoint var (Funs \\ Scope) (bound_var e1) ->
               Closure_conversion Size.Util.clo_tag Scope Funs c Γ FVs e1 e2 C ->
               forall j : nat,
                 (e1, rho1, H1) ⪯ ^ (m; j; Pre; PreG Funs;
                                     Post 0; fun _ : nat => Post 0) (C |[ e2 ]|, rho2, H2)) :
    forall  B1 B1' B1'' B2 B2'
       (H1 H1' H2 : heap block) (rho1 rho1' rho2 : env) b
       (e1 e2 : exp) (C Cf: exp_ctx) (Scope Funs : Ensemble var)
       (H : ToMSet Funs) (FVs FVs': list var)
       (c : cTag) (Γ Γ' : var) l l' fvset,
      well_formed (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) H1 ->
      env_locs rho1 (FV Scope Funs FVs) \subset dom H1  ->
      well_formed (reach' H2 (env_locs rho2 (FV_cc Scope Funs Γ))) H2 ->
      env_locs rho2 (env_locs rho2 (FV_cc Scope Funs Γ)) \subset dom H2  ->
      injective_subdomain (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) b ->
      
      (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; PreG Funs; fun _ : nat => Post 0; b) (H2, (M.set Γ' (Loc l') rho2))) ->
      (forall j, Fun_inv k j (PreG Funs) (fun _ : nat => Post 0) b rho1 H1 (M.set Γ' (Loc l') rho2) H2 Scope Funs) ->
      (forall j, FV_inv k j (PreG Funs) (fun _ : nat => Post 0) b rho1 H1 (M.set Γ' (Loc l') rho2) H2 c Scope Funs Γ FVs) ->
      
      (* Free variables invariant for new fundefs *)
      (forall j, FV_inv k j (PreG Funs) (fun i => Post 0) b rho1 H1 (M.set Γ' (Loc l') rho2) H2 c
                   (Empty_set _) (Empty_set _) Γ' FVs') -> (* no scope, no funs yet *)
      FromList FVs' <--> occurs_free_fundefs B1' -> 

      fundefs_names_unique_fundefs B1 ->
      fundefs_names_unique_fundefs B1' ->
      
      Closure_conversion_fundefs Size.Util.clo_tag B1'' c FVs B1 B2 ->
      name_in_fundefs B1 \subset name_in_fundefs B1'' ->
      (* for the inner def funs *)
      Closure_conversion_fundefs Size.Util.clo_tag B1' c FVs B1' B2' ->    

      make_closures Size.Util.clo_tag B1 fvset Γ' Cf ->
      fvset \subset (Scope :|: Funs) ->
            
      get l H1 = Some (Env (restrict_env (fundefs_fv B1') rho1)) -> 
      
      def_closures B1 B1' rho1 H1 l = (H1', rho1') ->
      
      (forall j, (e1, rho1', H1') ⪯ ^ (k; j; Pre; PreG Funs;
                                  Post 0; fun _ : nat => Post 0)
          (Cf |[ C |[ e2 ]| ]|, def_funs B2 B2' (M.set Γ' (Loc l') rho2), H2)). 
  Proof.
    induction B1;
    intros B1' B1'' B2 B2' H1 H1' H2 rho1 rho1' rho2 b e1 e2 C Cf
           Scope Funs H FVs FVs' c Γ Γ'  l1 l2 fvset 
           Hwf1 Hlocs1 Hwf2 Hlocs2 Hinj Henv Hfuns Hfvs Hfvs' Hfveq
           Hun1 Hun2 Hccf1 Hname Hccf2 Hclo Hfvsub Hgetl Hdef j.
    - inv Hccf1. Focus 2. inv Hclo. simpl def_funs. admit. admit.
    - inv Hclo. simpl (Hole_c |[ C |[ e2 ]| ]|). simpl def_funs.
      eapply IHk. 
      
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
    injective_subdomain' (reach' H1 (env_locs rho1 (FV Scope FVs))) δ ->
    Disjoint _ (image β (reach' H1 (env_locs rho1 (FV Scope FVs)))) (image' δ (reach' H1 (env_locs rho1 (FV Scope FVs)))) ->

    (* the reachable parts of the heap are in bijection *)
    (* image β (reach' H1 (env_locs rho1 (FV Scope FVs))) :|: image' δ (reach' H1 (env_locs rho1 (FV Scope FVs))) <--> *)
    (* reach' H2 (env_locs rho2 (FV_cc Scope Γ)) *)
    
    (* FV Scope FVs <--> occurs_free e1 -> *)
    (* FV_cc Scope Γ <--> occurs_free (C |[ e2 ]|) -> *)
    
    
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
            - intros H11 rc1 rc2 henv Hdef. 
              
              eassumption. 
      admit. 
      
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
      inv Hcc.
      admit.
  