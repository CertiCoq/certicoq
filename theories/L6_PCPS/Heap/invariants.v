From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics.

From L6.Heap Require Import heap heap_defs heap_equiv space_sem
     cc_log_rel closure_conversion closure_conversion_util bounds.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega Permutation.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.


Module Invariants (H : Heap).

  Module Size := Size H.

  Import H Size.Util.C.LR.Sem.Equiv Size.Util.C.LR.Sem.Equiv.Defs
         Size.Util.C.LR.Sem Size.Util.C.LR Size.Util.C Size.Util Size.

  (** Invariant about the free variables *) 
  Definition FV_inv (k j : nat) (IP : GIInv) (P : GInv) (b : Inj) (d : EInj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) : Prop :=
    well_formed (reach' H2 (env_locs rho2 [set Γ])) H2 /\ (* True when the environment is created *)
    exists (vs : list value) (l : loc),
      M.get Γ rho2 = Some (Loc l) /\
      get l H2 = Some (Constr c vs) /\
      Forall2_P (Scope :|: Funs)
                (fun (x : var) (v2 : value)  =>
                   exists v1, M.get x rho1 = Some v1 /\
                         Res (v1, H1) ≺ ^ ( k ; j ; IP ; P ; b; d) Res (v2, H2)) FVs vs.

  (** Invariant about the functions currently in scope not yet packed as closures *)
  Definition Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs fenv FVs :=
    forall f, ~ f \in Scope -> f \in Funs ->
         exists l1 lenv B1 g1 rhoc B2 g2,
           M.get f rho1 = Some (Loc l1) /\

           (* Funs locations are fresh, and there are no references to them  *)
           ~ l1 \in (reach' H1 ((env_locs rho1 (FV Scope Funs FVs \\ [set f])) :|: post H1 [set l1])) /\

           M.get f rho2 = Some (FunPtr B2 g2) /\
           get l1 H1 = Some (Clos (FunPtr B1 g1) rhoc) /\

           M.get (fenv f) rho2 = Some (Loc lenv) /\

           (* Environments are related (before allocation) *)
           (rhoc, H1) << ^ (k; j; GI; GP; b; d; occurs_free_fundefs B1) (lenv, H2) /\

           (* We can alloc a related function *)
           let '(l2, H2') := alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc lenv]) H2 in
           Res (Loc l1, H1) ≺ ^ (k; j; GI; GP; b{l1 ~> l2}; d{l1 ~> Some lenv}) Res (Loc l2, H2'). 


    (** Version without the logical relation. Useful when we're only interested in other invariants. *)
  
  (** Invariant about the free variables *) 
  Definition FV_inv_weak (rho1 : env) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) : Prop :=
    exists (vs : list value) (l : loc),
      M.get Γ rho2 = Some (Loc l) /\
      get l H2 = Some (Constr c vs) /\
      Forall2_P (Scope :|: Funs)
                (fun (x : var) (v2 : value)  =>
                   exists v1, M.get x rho1 = Some v1) FVs vs.
  
  Definition Fun_inv_weak rho1 rho2 Scope Funs fenv :=
    forall f, ~ f \in Scope -> f \in Funs ->
         exists l1 lenv B g,
           M.get f rho1 = Some (Loc l1) /\
           M.get f rho2 = Some (FunPtr B g) /\
           M.get (fenv f) rho2 = Some (Loc lenv). 
  
  (** * Lemmas about [FV_inv] *)  

  Lemma FV_inv_cc_approx_clos  (k j : nat) (IP : GIInv) (P : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Γ : var) (FVs : list var) S1 S2 l : 
    FV_inv k j IP P b d rho1 H1 rho2 H2 c S1 S2 Γ FVs ->
    Disjoint _ (S1 :|: S2) (FromList FVs) ->
    NoDup FVs ->
    M.get Γ rho2 = Some (Loc l) ->
    (rho1, H1) << ^ (k; j; IP; P; b; d; (FromList FVs)) (l, H2).
  Proof with (now eauto with Ensembles_DB).
    intros (Hwf & vs & l' & Hget1 & Hget2 & Hall) HD Hnd Hget1'. subst_exp.
    clear Hget1. eexists c, vs. setoid_rewrite Hget2. clear Hget2. 
    induction Hall.
    - eexists []. split. rewrite !FromList_nil. reflexivity.
      split. now constructor. split. reflexivity.
      constructor.
      
    - inv Hnd.
      edestruct H as [v1 [Hget1 Hres1]]. intros Hc.
      eapply HD. constructor; eauto. now left.

      edestruct IHHall as (FLs & Heq & Hnd' & Hget' & Hal').

      eapply Disjoint_Included_r; [| eassumption ]. rewrite FromList_cons...
      
      eassumption. 
      eexists (x :: FLs). split. rewrite !FromList_cons, Heq. reflexivity.
      split. constructor; eauto. intros Hc. eapply H4; eapply Heq. eassumption. 
      split. reflexivity.
      econstructor.

      destruct v1 as [| l1 ]; try contradiction. 
      eexists; split. eassumption. rewrite cc_approx_val_eq. eassumption.
      
      eassumption.
  Qed.
  
  Lemma FV_inv_j_monotonic (k j' j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    j' <= j ->
    FV_inv k j' GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs.
  Proof.
    intros Hfv Hlt. 
    destruct Hfv as (Hwf & v & vs & Hget1 & Hget2 & Hall).
    split.
    
    eassumption. repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros x1 x2 Hin1 Hin3 Hnp [v' [Hget Hres]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.

  Lemma FV_inv_monotonic (k k' j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    k' <= k ->
    FV_inv k' j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs.
  Proof.
    intros Hfv Hlt. 
    destruct Hfv as (Hwf & v & vs & Hget1 & Hget2 & Hall).
    split. eassumption. repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros x1 x2 Hin1 Hin3 Hnp [v' [Hget Hres]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.
      
  Lemma FV_inv_weak_in_FV_inv k j P1 P2 rho1 H1 rho2 H2 β d c Scope Funs Γ FVs :
    FV_inv k j P1 P2 β d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    FV_inv_weak rho1 rho2 H2 c Scope Funs  Γ FVs.
  Proof.
    intros (Hwf & x1 & x2  & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros ? ? ? ? ? [? [? ? ]]. eexists; eauto.
  Qed.

  Lemma Fun_inv_weak_in_Fun_inv k j P1 P2 rho1 H1 rho2 H2 β d
        Scope Funs fenv FVs :
    Fun_inv k j P1 P2 β d rho1 H1 rho2 H2 Scope Funs fenv FVs ->
    Fun_inv_weak rho1 rho2 Scope Funs fenv.
  Proof.
    intros Hfun x Hin Hnin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq); try eassumption.
    repeat eexists; eauto.
  Qed.

  Lemma FV_inv_dom1 k P1 P2 rho1 H1 rho2 H2 b d c
        Scope Funs Γ FVs :
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    env_locs rho1 (FromList FVs \\ (Scope :|: Funs)) \subset dom H1.
  Proof.
    intros Hres l [x1 [Hgetx1 Heq1]].
    destruct (M.get x1 rho1) as [ [|] | ] eqn:Hgety; try inv Heq1.
    edestruct (Hres 0) as (Hwf & vs1 & loc_env & Hget1 & Hget2 & Hall).
    edestruct (@Forall2_P_exists loc) with (x := x1) as [v2 [Hin'' Hv]]; try eassumption.
    
    now eapply Hgetx1.
    now eapply Hgetx1.

    destruct Hv as [v1' [Hgety' Hv']]. repeat subst_exp.

    eapply cc_approx_val_dom1. eassumption. reflexivity.
  Qed.

  Lemma FV_inv_dom2 k P1 P2 rho1 H1 rho2 H2 b d c
        Scope Funs Γ FVs :
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    env_locs rho2 [set Γ] \subset dom H2.
  Proof.
    intros Hres l [x2 [Hgetx2 Heq1]].
    destruct (M.get x2 rho2) as [ [|] | ] eqn:Hgety; try inv Heq1.
    inv Hgetx2.
    edestruct (Hres 0) as (Hwf & vs1 & loc_env & Hget1 & Hget2 & Hall).
    repeat subst_exp. eexists; eauto.
  Qed.

  Lemma FV_inv_reach1 k P1 P2 rho1 H1 rho2 H2 b d c
        Scope Funs Γ FVs :
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    well_formed (reach' H1 (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) H1.
  Proof.
    intros Hres l1 b1 [n [_ Hp]].
    edestruct post_n_exists_Singleton as [lr [Hin Hp']].
    eassumption.
    destruct Hin as [x1 [Hin1 Heq1]].
    
    destruct (M.get x1 rho1) as [ [|] | ] eqn:Hgety; try inv Heq1.

    edestruct (Hres (1 + n)) as (Hwf & vs1 & loc_env & Hget1 & Hget2 & Hall).
    edestruct (@Forall2_P_exists loc) with (x := x1) as [v2 [Hin Hv]]; try eassumption.
    now eapply Hin1.
    now eapply Hin1.    
    destruct Hv as [v1' [Hgety' Hv1]]. repeat subst_exp.
    eapply cc_approx_val_post_n_cc with (v1 := Loc lr) in Hp'.   
    intros Hget.
    
    eapply cc_approx_val_well_formed_post1 with (v1 := Loc l1) (j := 0).
    eassumption.
    reflexivity.
    eassumption.

    eapply cc_approx_val_j_monotonic. eassumption. omega.
  Qed.
   
  Lemma FV_inv_reach2 k j P1 P2 rho1 H1 rho2 H2 b d c
        Γ FVs :
    FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c (Empty_set _) (Empty_set _) Γ FVs ->
    well_formed (reach' H2 (env_locs rho2 [set Γ])) H2.
  Proof.
    intros (Henv & _). eassumption.
  Qed.


  

  Lemma FV_inv_image_reach k P1 P2 rho1 H1 rho2 H2 b d c
        Scope Funs Γ FVs :
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    image b (reach' H1 (env_locs rho1 (FromList FVs \\ (Scope :|: Funs))))
    :|: image' d (reach' H1 (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) \subset
    reach' H2 (post H2 (env_locs rho2 [set Γ])).
  Proof.
    intros Hres l' [l'' [l [Hin Heq]] | l'' [l [Hin Heq]]].
    + destruct Hin as [n [_ Hp]].
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.

      edestruct (Hres n) as (Hwf & vs1 & loc_env & Hget1 & Hget2 & Hall).
    
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

      edestruct (@Forall2_P_exists loc) with (x := y) as [v2' [Hin2' Hv']];
        [| | now apply Hall' |]; try eassumption.
      
      destruct Hv' as [v1' [Hgety' Hv']]. repeat subst_exp.

      assert (Heq1 : v2' = Loc (b l1)).
      { destruct v2'; try contradiction.
        destruct Hv' as [Heqv _]. subst. reflexivity. }

      assert (Heq2 : l2' = b l1).
      { destruct Hv as [Heqv _]. subst. reflexivity. }
      subst. repeat subst_exp. eassumption.

    + destruct Hin as [n [_ Hp]].
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      
      edestruct (Hres n) as (Hwf & vs1 & loc_env & Hget1 & Hget2 & Hall).
    
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
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) x v  :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    ~ x \in (FromList FVs \\ (Scope :|: Funs)) ->
    FV_inv k j GII GI b d (M.set x v rho1) H1 rho2 H2 c Scope Funs Γ FVs.
  Proof.
    intros (Hwf & x1 & x2 & Hget1 & Hget2 & Hall).
    split; eauto. repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros y1 v2 Hin Hnin Hp [v1 [Hget Hall1]].
    eexists; split; eauto.
    rewrite M.gso; eauto.
    intros Hc; subst. eapply H; constructor; eauto. 
  Qed.

  Lemma FV_inv_set_not_in_FVs_r (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) x v  :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    x <> Γ ->
    FV_inv k j GII GI b d rho1 H1 (M.set x v rho2) H2 c Scope Funs Γ FVs.
  Proof.
    intros (Hwf & x1 & x2 & Hget1 & Hget2 & Hall) Hnin.
    split; eauto.
    rewrite env_locs_set_not_In; eauto. now intros Hc; inv Hc; eauto.
    rewrite M.gso; eauto.
  Qed. 
  
  Lemma FV_inv_set_not_in_FVs (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) x y v v'  :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    ~ x \in (FromList FVs \\ (Scope :|: Funs)) ->
    y <> Γ ->
    FV_inv k j GII GI b d (M.set x v rho1) H1 (M.set y v' rho2) H2 c Scope Funs Γ FVs.
  Proof.
    intros. eapply FV_inv_set_not_in_FVs_r; eauto.
    eapply FV_inv_set_not_in_FVs_l; eauto.
  Qed.
  

  (** [FV_inv] is heap monotonic  *)
  Lemma FV_inv_heap_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 H1' : heap block) (rho2 : env) (H2 H2' : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    (forall j, FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ) ->
    FV_inv k j GII GI b d rho1 H1' rho2 H2' c Scope Funs Γ FVs.
  Proof.
    intros Hs1 Hs2.
    intros Henv. edestruct (Henv 0) as (Hwf & x1 & x2 & Hget1 & Hget2 & Hall).
    split.
    - rewrite <- reach'_subheap.
      eapply well_formed_subheap.
      eassumption.
      eapply reachable_in_dom.
      eassumption.
      rewrite env_locs_Singleton; eauto. eapply Singleton_Included.
      eexists; eassumption.
      eassumption. eassumption.
      rewrite env_locs_Singleton; eauto. eapply Singleton_Included.
      eexists; eassumption.
      eassumption.
    - repeat eexists; eauto.
      eapply Forall2_P_monotonic_strong; [| eassumption ].
      intros y1 v2 Hin1 Hin2 Hp [v1 [Hget3 Hrel]].
      eexists; split; eauto. 
      eapply cc_approx_val_heap_monotonic; try eassumption.
      intros j'. 
      edestruct (Henv j') as (Hwf' & x1' & x2' & Hget1' & Hget2' & Hall').
      repeat subst_exp. 
      edestruct (Forall2_P_exists _ _ _ _ _ Hin1 Hp Hall') as [v1' [Hin' [v2' [Hget2' Hp']]]]. repeat subst_exp.
      destruct v2'; [| contradiction ]. 
      eapply cc_approx_val_loc_eq in Hrel. subst.
      assert (Hrel := Hp'). 
      eapply cc_approx_val_loc_eq in Hrel. subst.
      eassumption. 
  Qed.
  
  (** [FV_inv] under rename extension  *)
  Lemma FV_inv_rename_ext (k j : nat) (GII : GIInv) (GI : GInv) (b b' : Inj) (d d' : EInj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env) 
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) b' b ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) d' d ->
    FV_inv k j GII GI b' d' rho1 H1 rho2 H2 c Scope Funs Γ FVs.
  Proof.
    intros (Hwf & x1 & x2 & Hget1 & Hget2 & Hall) Hfeq.
    split. eassumption. repeat eexists; eauto.
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
        (c : cTag) (Scope Scope' Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    Scope \subset Scope' -> 
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope' Funs Γ FVs.
  Proof.
    intros (Hwf & x1 & x2 & Hget1 & Hget2 & Hall) Hfeq.
    split. eassumption. repeat eexists; eauto.
    eapply Forall2_P_monotonic. eassumption.
    now eauto with Ensembles_DB. 
  Qed.

  Lemma FV_inv_Funs_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env) 
        (c : cTag) (Scope Funs Funs' : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    Funs \subset Funs' -> 
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs' Γ FVs.
  Proof.
    intros (Hwf & x1 & x2 & Hget1 & Hget2 & Hall) Hfeq.
    split. eassumption. repeat eexists; eauto.
    eapply Forall2_P_monotonic. eassumption.
    now eauto with Ensembles_DB. 
  Qed.

  Lemma FV_inv_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) (d : EInj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env) 
        (c : cTag) (Scope Scope' Funs Funs' : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    Scope :|: Funs \subset Scope' :|: Funs' -> 
    FV_inv k j GII GI b d rho1 H1 rho2 H2 c Scope' Funs' Γ FVs.
  Proof.
    intros (Hwf & x1 & x2 & Hget1 & Hget2 & Hall) Hfeq.
    split. eassumption. repeat eexists; eauto.
    eapply Forall2_P_monotonic. eassumption.
    now eauto with Ensembles_DB. 
  Qed.

  Instance Proper_FV_inv_Funs k j GI GP b d rho1 H1 rho2 H2 c Scope :
    Proper (Same_set _ ==> eq ==> eq ==> iff)
           (FV_inv k j GI GP b d rho1 H1 rho2 H2 c Scope). 
  Proof.
    intros S1 S2 Hseq x1 x2 Heq1 y1 y2 Heq2; subst.
    split; intros (Hwf & vs & l & Hget1 & Hget2 & Hall1).
    split. eassumption. do 2 eexists.
    split. eassumption.
    split. eassumption.
    eapply Forall2_P_monotonic; eauto. rewrite Hseq. reflexivity.
    split. eassumption. do 2 eexists.
    split. eassumption.
    split. eassumption.
    eapply Forall2_P_monotonic; eauto. rewrite Hseq. reflexivity.
  Qed.


  Lemma Fun_inv_image_reach k P1 P2 rho1 H1 rho2 H2 b d
        Scope Funs fenv FVs :
    (forall j, Fun_inv k j P1 P2 b d rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    image b (reach' H1 (post H1 (env_locs rho1 (Funs \\ Scope))))
    :|: image' d (reach' H1 (post H1 (env_locs rho1 (Funs \\ Scope)))) \subset
    reach' H2 (env_locs rho2 (image fenv (Funs \\ Scope))).
  Proof.
    intros Hres l' [l'' [l [Hin Heq]] | l'' [l [Hin Heq]]].
    + destruct Hin as [n [_ Hp]]. 
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      edestruct Hin as [l2 [b1 [Henv [Hgetl1 Hinl1]]]].
      edestruct Henv as [x1 [Hinx Hm]].
      destruct (M.get x1 rho1) as [[l3|] | ] eqn:Hgetx; inv Hm.

      inv Hinx. 
      edestruct (Hres n) as (l1' & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis' (* & Hsub *)
                                 & Hget2 & Hget3 & Hget4 & Henv' & Heq').
      eassumption. eassumption.
      repeat subst_exp.
      simpl in Hinl1. 

      edestruct Hinl1 as [y1 [Hinx1 Hm]].
      destruct (M.get y1 rhoc) as [[l3|] | ] eqn:Hgety; inv Hm.
      edestruct Henv' as (c & vs & FVs' & Hseq & Hnd & Hget & Hall).
      
      edestruct (@Forall2_exists loc) as [v2 [Hin'' Hv]]; try eassumption.
      eapply Hseq. eassumption.

      edestruct Hv as [l2' [Hgetl1' Hcc]]. repeat subst_exp.
      rewrite cc_approx_val_eq in Hcc. eapply cc_approx_val_loc_eq in Hcc. subst.

      assert (Hccj : forall j,  Res (Loc l2', H1) ≺ ^ (k; j; P1; P2; b; d) Res (Loc (b l2'), H2)).
      { intros j.
        edestruct (Hres j) as
            (l1'' & lenv' & B1' & g1' & rhoc' & B2' & g2' & Hget1' & Hdis'' (* & Hsub *)
                  & Hget2' & Hget3' & Hget4' & Henv'' & Heq''). eassumption. eassumption.
        repeat subst_exp.
        edestruct Henv'' as (c' & vs' & FVs'' & Hseq' & Hnd' & Hget' & Hall').
        repeat subst_exp. 
        edestruct (@Forall2_exists loc) as [v3 [Hin3 Hv']]; try eassumption.
        eapply Hseq'. eassumption.
        edestruct Hv' as [l3 [Hgetl3 Hcc']]. repeat subst_exp.
        rewrite cc_approx_val_eq in Hcc'.
      
        assert (Hcc := Hcc').
        eapply cc_approx_val_loc_eq in Hcc. subst. eassumption. }

      assert (Hccj' : forall j, Res (Loc l, H1) ≺ ^ (k; j; P1; P2; b; d) Res (Loc (b l), H2)).
      { intros j. eapply cc_approx_val_post_n_cc; try eassumption.
        eapply Hccj. eassumption. }

      rewrite reach_unfold. right. 
      eapply reach'_set_monotonic; [| eapply cc_approx_val_image_eq; [ eapply Hccj |] ].
      eapply Singleton_Included. do 2 eexists. split.
      eexists. split. eexists. split; eauto. now constructor; eauto.
      rewrite Hget4. reflexivity. split. eassumption.
      eapply In_Union_list. eapply in_map. eassumption. 
      reflexivity.

      left. eexists. split; [| reflexivity ].
      eexists; split; eauto. constructor; eauto.
    + destruct Hin as [n [_ Hp]]. 
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      edestruct Hin as [l2 [b1 [Henv [Hgetl1 Hinl1]]]].
      edestruct Henv as [x1 [Hinx Hm]].
      destruct (M.get x1 rho1) as [[l3|] | ] eqn:Hgetx; inv Hm.

      inv Hinx. 
      edestruct (Hres n) as (l1' & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis' (* & Hsub *)
                                 & Hget2 & Hget3 & Hget4 & Henv' & Heq').
      eassumption. eassumption.
      repeat subst_exp.
      simpl in Hinl1. 

      edestruct Hinl1 as [y1 [Hinx1 Hm]].
      destruct (M.get y1 rhoc) as [[l3|] | ] eqn:Hgety; inv Hm.
      edestruct Henv' as (c & vs & FVs' & Hseq & Hnd & Hget & Hall).
      
      edestruct (@Forall2_exists loc) as [v2 [Hin'' Hv]]; try eassumption.
      eapply Hseq. eassumption.

      edestruct Hv as [l2' [Hgetl1' Hcc]]. repeat subst_exp.
      rewrite cc_approx_val_eq in Hcc. eapply cc_approx_val_loc_eq in Hcc. subst.

      assert (Hccj : forall j,  Res (Loc l2', H1) ≺ ^ (k; j; P1; P2; b; d) Res (Loc (b l2'), H2)).
      { intros j.
        edestruct (Hres j) as
            (l1'' & lenv' & B1' & g1' & rhoc' & B2' & g2' & Hget1' & Hdis'' (* & Hsub *)
                  & Hget2' & Hget3' & Hget4' & Henv'' & Heq''). eassumption. eassumption.
        repeat subst_exp.
        edestruct Henv'' as (c' & vs' & FVs'' & Hseq' & Hnd' & Hget' & Hall').
        repeat subst_exp. 
        edestruct (@Forall2_exists loc) as [v3 [Hin3 Hv']]; try eassumption.
        eapply Hseq'. eassumption.
        edestruct Hv' as [l3 [Hgetl3 Hcc']]. repeat subst_exp.
        rewrite cc_approx_val_eq in Hcc'.
      
        assert (Hcc := Hcc').
        eapply cc_approx_val_loc_eq in Hcc. subst. eassumption. }

      assert (Hccj' : forall j, Res (Loc l, H1) ≺ ^ (k; j; P1; P2; b; d) Res (Loc (b l), H2)).
      { intros j. eapply cc_approx_val_post_n_cc; try eassumption.
        eapply Hccj. eassumption. }

      rewrite reach_unfold. right. 
      eapply reach'_set_monotonic; [| eapply cc_approx_val_image_eq; [ eapply Hccj |] ].
      eapply Singleton_Included. do 2 eexists. split.
      eexists. split. eexists. split; eauto. now constructor; eauto.
      rewrite Hget4. reflexivity. split. eassumption.
      eapply In_Union_list. eapply in_map. eassumption. 
      reflexivity.
      right. 
      eexists. split; [| eassumption ].
      eexists; split; eauto. constructor; eauto.
  Qed.


  Lemma FV_image_reach k P1 P2 rho1 H1 rho2 H2 b d c
        Scope Funs Γ fenv FVs :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b; d) (H2, rho2)) ->
    (forall j, Fun_inv k j P1 P2 b d rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    image b (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope))
    :|: image' d (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)) \subset
    reach' H2 (env_locs rho2 (Scope :|: image fenv (Funs \\ Scope) :|: [set Γ])).
  Proof with (now eauto with Ensembles_DB).
    intros Hcc Hfun Henv l' [l Hin | l Hin].
    - unfold FV in Hin.
      rewrite !env_locs_Union, !reach'_Union, !Setminus_Union_distr, !image_Union in Hin.
      inv Hin. inv H. 
      
      + eapply reach'_set_monotonic; [| eapply cc_approx_env_image_reach_included; try eassumption ].
        eapply env_locs_monotonic... left. eapply image_monotonic; [| eassumption ]...

      + rewrite !env_locs_Union, !reach'_Union. left. right.
        eapply Fun_inv_image_reach. eassumption. left.
        eapply image_monotonic; [| eassumption ].
        rewrite reach_unfold...

      + rewrite !env_locs_Union, !reach'_Union. right.
        rewrite reach_unfold. right.
        eapply FV_inv_image_reach. eassumption. left.
        eapply image_monotonic; [| eassumption ]...

    - unfold FV in Hin.
      rewrite !env_locs_Union, !reach'_Union, !Setminus_Union_distr, !image'_Union in Hin.
      inv Hin. inv H.
      
      + eapply reach'_set_monotonic; [| eapply cc_approx_env_image_reach_included; try eassumption ].
        eapply env_locs_monotonic... right. eapply image'_monotonic; [| eassumption ]...

      + rewrite !env_locs_Union, !reach'_Union. left. right.
        eapply Fun_inv_image_reach. eassumption. right.
        eapply image'_monotonic; [| eassumption ].
        rewrite reach_unfold...

      + rewrite !env_locs_Union, !reach'_Union. right.
        rewrite reach_unfold. right.
        eapply FV_inv_image_reach. eassumption. right.
        eapply image'_monotonic; [| eassumption ]...
  Qed.


  Lemma def_closures_FV_inv Scope Funs FVs Γ k j GIP GP b d B1 B2 envc c rho1 H1 rho1' H1' rho2 H2 :
    (forall j, FV_inv k j GIP GP b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    def_closures B1 B2 rho1 H1 envc = (H1', rho1') ->
    FV_inv k j GIP GP b d rho1' H1' rho2 H2 c (name_in_fundefs B1 :|: Scope) Funs Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    revert H1 rho1 H1' rho1' j.
    induction B1; intros H1 rho1 H1' rho1' j Hfv Hdef.
    - simpl in Hdef.
      destruct (def_closures B1 B2 rho1 H1) as (H1'', rho1'') eqn:Hdef'.
      destruct (alloc (Clos _ _) H1'') as [la H1a] eqn:Hal.
      inv Hdef.

      eapply FV_inv_set_not_in_FVs_l.
      eapply FV_inv_Scope_mon.
      eapply FV_inv_heap_mon; [ | | ].
      * eapply HL.alloc_subheap. eassumption.
      * eapply HL.subheap_refl.
      * intros j'.
        eapply IHB1 in Hdef'.
        eassumption.
        eassumption.
      * simpl...
      * intros Hc; inv Hc. eapply H0; left; left. now left.
    - inv Hdef. eapply FV_inv_Scope_mon; [ eauto |]...
  Qed.

  Lemma def_funs_FV_inv Scope Funs Γ FVs c k j GIP GP b d B1 B2 rho1 H1 rho2 H2 :
    FV_inv k j GIP GP b d rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    ~ Γ \in name_in_fundefs B1 ->
    FV_inv k j GIP GP b d rho1 H1 (def_funs B1 B2 rho2) H2 c (name_in_fundefs B1 :|: Scope) Funs Γ FVs.
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

  
  (** * Lemmas about [Fun_inv] *)

  Lemma Fun_inv_set_r k j GI GP b d rho1 H1 rho2 H2 Scope Funs fenv FVs f v :
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs fenv FVs ->
    ~ f \in (Funs \\ Scope) -> ~ f \in (image fenv (Funs \\ Scope)) ->
    Fun_inv k j GI GP b d rho1 H1 (M.set f v rho2) H2 Scope Funs fenv FVs.
  Proof.
    intros Hfun Hnin1 Hnin2 x Hnin Hin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                      & Hget2 & Hget3 & Hget4 & Henv & Heq).
    eassumption. eassumption.  
    do 7 eexists. repeat split; try eassumption. rewrite M.gso. eassumption.
    
    intros Hc. subst. eapply Hnin1; eauto. now constructor; eauto.

    rewrite M.gso; try eassumption. 
    intros Hc; subst. eapply Hnin2. eexists; split; constructor; eauto. 
  Qed.
  
  Lemma Fun_inv_Scope_monotonic k j GI GP b d rho1 H1 rho2 H2 Scope S Funs Γ FVs {_ : Decidable S}:
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs Γ FVs ->
    FV (S :|: Scope) Funs FVs <--> FV Scope Funs FVs ->
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 (S :|: Scope) Funs Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hfun Heq y Hin Hnin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                      & Hget2 & Hget3 & Hget4 & Henv & Heq').
    now eauto. eassumption.
    do 7 eexists. repeat split; try eassumption.

    intros Hc. eapply Hsub. rewrite <- Heq. eassumption.

    (* eapply Included_trans. eassumption. eapply reach'_set_monotonic. *)
    (* eapply env_locs_monotonic. *)
    (* rewrite <- (Union_assoc S Scope Funs).  *)
    (* rewrite (Union_commut S (Scope :|: Funs)). *)
    (* rewrite <- (Setminus_Union _ _ S). *)
    (* rewrite (Union_Setminus_Included (S :|: Scope) _ S); tci... *)
  Qed.

  Lemma Fun_inv_Scope_monotonic' k j GI GP b d rho1 H1 rho2 H2 Scope S Funs Γ FVs {_ : Decidable S}:
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs Γ FVs ->
    FV (S :|: Scope) (Funs \\ S) FVs <--> FV Scope Funs FVs ->
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 (S :|: Scope) (Funs \\ S) Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hfun Heq y Hin Hnin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                      & Hget2 & Hget3 & Hget4 & Henv & Heq').
    now eauto. inv Hnin. eassumption.
    do 7 eexists. repeat split; try eassumption.
    
    intros Hc. eapply Hsub. rewrite <- Heq. eassumption.

    (* eapply Included_trans. eassumption. eapply reach'_set_monotonic. *)
    (* eapply env_locs_monotonic. *)
    (* rewrite (Union_Setminus_Included (S:|: Scope) Funs S); tci. *)
    (* rewrite <- (Union_assoc S Scope Funs).  *)
    (* rewrite (Union_commut S (Scope :|: Funs)). *)
    (* rewrite <- (Setminus_Union _ _ S). *)
    (* rewrite (Union_Setminus_Included (S :|: Scope) _ S); tci... *)
    (* now eauto with Ensembles_DB.  *)
  Qed.



  Lemma Fun_inv_dom1 k GI GP rho1 H1 rho2 H2 b d
        Scope Funs Γ FVs :
    (forall j, Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
    env_locs rho1 (Funs \\ Scope) \subset dom H1.
  Proof.
    intros Hres l [x1 [Hgetx1 Heq1]].
    destruct (M.get x1 rho1) as [ [|] | ] eqn:Hgety; try inv Heq1.
    edestruct (Hres 0) as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    now eapply Hgetx1. now eapply Hgetx1.
    edestruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc lenv]) H2) as [l2 H2'] eqn:Ha. 
    repeat subst_exp.
    eapply cc_approx_val_dom1. eassumption. reflexivity. 
  Qed.
  
  Lemma Fun_inv_dom2 k GI GP rho1 H1 rho2 H2 b d
        Scope Funs Γ FVs :
    (forall j, Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
    env_locs rho2 (Funs \\ Scope) \subset dom H2.
  Proof.
    intros Hres l [x2 [Hgetx1 Heq1]].
    destruct (M.get x2 rho2) as [ [|] | ] eqn:Hgety; try inv Heq1.
    edestruct (Hres 0) as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    now eapply Hgetx1. now eapply Hgetx1.
    repeat subst_exp.
  Qed.
  
  Lemma Fun_inv_reach1 k GI GP rho1 H1 rho2 H2 b d
        Scope Funs Γ FVs :
    (forall j, Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
    well_formed (reach' H1 (env_locs rho1 (Funs \\ Scope))) H1.
  Proof.
    intros Hres l b1 [n [_ Hp]] Hget.
    edestruct post_n_exists_Singleton as [lr [Hin' Hp']].
    eassumption.
    destruct Hin' as [x1 [Hin1 Heq1]].
    destruct (M.get x1 rho1) as [ [|] | ] eqn:Hgety; try inv Heq1.
    edestruct (Hres (1 + n))
      as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
         & Hget2 & Hget3 & Hget4 & Henv & Heq).
    now eapply Hin1. now eapply Hin1. repeat subst_exp.
    edestruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc lenv]) H2) as [l2 H2'] eqn:Ha. 
    eapply cc_approx_val_well_formed_post1 with (v1 := Loc l) (j := 0) ; [| reflexivity | eassumption ].

    eapply cc_approx_val_post_n_cc with (v1 := Loc l1) ; [| eassumption ].
    eapply cc_approx_val_j_monotonic. eassumption. omega.
  Qed.

  Lemma Fun_inv_reach2 k GI GP rho1 H1 rho2 H2 b d
        Scope Funs Γ FVs :
    (forall j, Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
    well_formed (reach' H2 (env_locs rho2 (Funs \\ Scope))) H2.
  Proof.
    intros Hres l b1 [n [_ Hp]] Hget.
    edestruct post_n_exists_Singleton as [lr [Hin' Hp']].
    eassumption.
    destruct Hin' as [x1 [Hin1 Heq1]].
    destruct (M.get x1 rho2) as [ [|] | ] eqn:Hgety; try inv Heq1.
    edestruct (Hres (1 + n))
      as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
         & Hget2 & Hget3 & Hget4 & Henv & Heq).
    now eapply Hin1. now eapply Hin1. repeat subst_exp.
  Qed.

  Lemma Fun_inv_dom2_funs k GI GP rho1 H1 rho2 H2 b d
        Scope Funs fenv FVs :
    (forall j, Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    env_locs rho2 (image fenv (Funs \\ Scope)) \subset dom H2.
  Proof.
    intros Hres l [x2 [Hgetx1 Heq1]].
    destruct (M.get x2 rho2) as [ [|] | ] eqn:Hgety; try inv Heq1.
    edestruct Hgetx1 as [f1 [Hin Heq]]; subst. 
    edestruct (Hres 1) as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    now eapply Hin. now eapply Hin.
    repeat subst_exp. 
    eapply cc_approx_clos_dom2. eassumption. 
  Qed.

  Lemma Fun_inv_reach2_funs k GI GP rho1 H1 rho2 H2 b d
        Scope Funs fenv FVs :
    (forall j, Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    well_formed (reach' H2 (env_locs rho2 (image fenv (Funs \\ Scope)))) H2.
  Proof.
    intros Hres l b1 [n [_ Hp]] Hget.
    edestruct post_n_exists_Singleton as [lr [Hin' Hp']].
    eassumption.
    destruct Hin' as [x1 [[f1 [Hin1 Heq2]] Heq1]]; subst.
    destruct (M.get (fenv f1) rho2) as [ [|] | ] eqn:Hgety; try inv Heq1.
    edestruct (Hres 0) as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    now eapply Hin1.
    now eapply Hin1. 
    
    eapply cc_approx_clos_well_formed_reac2 with (l2 := lr); (* TODO typo *)
      [ | | eassumption ].
    
    intros j.
    edestruct (Hres j) as (l1' & lenv' & B1' & g1' & rhoc' & B2' & g2' & Hget1' &
                           Hsub' (* & Hdis' *) & Hget2' & Hget3' & Hget4' & Henv' & Heq').
    now eapply Hin1.
    now eapply Hin1. 
    repeat subst_exp. eassumption. 
    eexists. split. now constructor. eassumption.
  Qed.
  

  Lemma Fun_inv_subheap k j GI GP b d rho1 H1 H1' rho2 H2 H2' Scope Funs fenv FVs :
    well_formed (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) H1 ->
    env_locs rho1 (FV Scope Funs FVs) \subset dom H1 ->
    
    image b (reach' H1 (post H1 (env_locs rho1 (Funs \\ Scope)))) :|:
    image' d (reach' H1 (post H1 (env_locs rho1 (Funs \\ Scope)))) \subset dom H2 ->
    
    (forall j, Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    Fun_inv k j GI GP b d rho1 H1' rho2 H2' Scope Funs fenv FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hwf1 Henv1  Him Hfun Hsub1 Hsub2 x Hin Hnin.
    edestruct (Hfun j) as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq);
      try eassumption.
    do 7 eexists; repeat split; try eassumption.
    
    - intros Hc. eapply Hdis. rewrite reach'_subheap; [ | | | eassumption ].

      rewrite well_formed_post_subheap_same. eassumption.

      eapply well_formed_antimon; [| now apply Hwf1 ].

      eapply reach'_set_monotonic. eapply get_In_env_locs with (v := Loc l1); [| eassumption ].
      left. right. constructor; eauto.

      eapply Singleton_Included. now eexists; eauto.

      eassumption.

      eapply well_formed_antimon; [| now apply Hwf1 ].
      rewrite reach'_Union. eapply Union_Included.
      eapply reach'_set_monotonic. eapply env_locs_monotonic...
      
      rewrite (reach'_idempotent H1 (env_locs rho1 (FV Scope Funs FVs))). eapply reach'_set_monotonic.
      eapply Included_trans; [|  eapply Included_post_reach' ]. eapply post_set_monotonic.
      eapply get_In_env_locs with (v := Loc l1); [| eassumption ].
      left. right. constructor; eauto.

      eapply Included_trans; [| eapply reachable_in_dom; try eassumption ].
      eapply Union_Included. eapply Included_trans; [| eapply reach'_extensive ].
      eapply env_locs_monotonic...

      eapply Included_trans; [|  eapply Included_post_reach' ]. eapply post_set_monotonic.
      eapply get_In_env_locs with (v := Loc l1); [| eassumption ].
      left. right. constructor; eauto.

    (* - rewrite <- well_formed_post_subheap_same; [| | | eassumption ]. *)
    (*   eapply Included_trans. eassumption. eapply reach'_heap_monotonic. eassumption. *)
    (*   eapply well_formed_antimon; [| now apply Hwf1 ].  *)
    (*   eapply reach'_set_monotonic. eapply get_In_env_locs with (v := Loc l1); try eassumption. *)
    (*   left. right. constructor; eassumption. *)
    (*   eapply Included_trans; [| eassumption ]. *)
    (*   eapply get_In_env_locs with (v := Loc l1); try eassumption. *)
    (*   left. right. constructor; eassumption.  *)

    - eapply Hsub1. eassumption.
    - eapply cc_approx_clos_heap_monotonic; try eassumption.
      intros j'.
      edestruct (Hfun j') as (l1' & lenv' & B1' & g1' & rhoc' & B2' & g2' & Hget1' & Hdis' (* & Hsub' *) & Hget2'
                             & Hget3' & Hget4' & Henv' & Heq');
        try eassumption.
      repeat subst_exp. eassumption.

    - destruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc lenv]) H2)
        as [l2 H4] eqn:Ha.
      destruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc lenv]) H2')
        as [l2' H4'] eqn:Ha'.
      
      eapply cc_approx_val_rename_ext
      with (β' := ((id {l2 ~> l2'}) ∘ (b {l1 ~> l2}) ∘ id))
             (δ' := (lift (id {l2 ~> l2'}) ∘ (d {l1 ~> Some lenv}) ∘ id)).
      + eapply cc_approx_val_res_eq.
        eassumption. eapply res_equiv_subheap; try eassumption.
        eapply Included_trans; [| eapply reach'_extensive ].
        eapply get_In_env_locs; try eassumption. left; right.
        constructor; eassumption. 
        
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
          
          eapply reach'_closed.
          eapply Fun_inv_reach2_funs. eassumption. 
          eapply Fun_inv_dom2_funs. eassumption. 
          eapply reach'_closed.
          eapply Fun_inv_reach2_funs. eassumption. 
          eapply Fun_inv_dom2_funs. eassumption. 
          
          eapply Included_trans; [| eapply reach'_extensive ].
          eapply get_In_env_locs; [| eassumption ].
          now eexists; split; eauto. 
          
          eapply Included_trans; [| eapply reach'_extensive ].
          eapply get_In_env_locs; eauto.
          now eexists; split; eauto. 
          
          intros Hc1.
          rewrite <- env_locs_Singleton with (v := Loc lenv) in Hc1; try eassumption. 
          rewrite <- well_formed_reach_alloc_same in Hc1;
          [| | | eassumption ].
        
        eapply reachable_in_dom in Hc1; try eassumption. destruct Hc1 as [b' Hget].
        erewrite alloc_fresh in Hget; eauto. congruence.
        
        eapply well_formed_antimon; [| eapply Fun_inv_reach2_funs; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eapply Singleton_Included. eexists; split; now eauto. 
        eapply Included_trans; [| eapply Fun_inv_dom2_funs; eassumption ].
        eapply env_locs_monotonic.
        eapply Singleton_Included. eexists; split; now eauto.

        eapply well_formed_antimon; [| eapply Fun_inv_reach2_funs; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eapply Singleton_Included. eexists; split; now eauto. 
        eapply Included_trans; [| eapply Fun_inv_dom2_funs; eassumption ].
        eapply env_locs_monotonic.
        eapply Singleton_Included. eexists; split; now eauto.
        
      * eapply injective_subdomain_extend'. now firstorder.
        rewrite image_id.
        rewrite reach_unfold. rewrite Setminus_Union_distr.
        rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        simpl. rewrite post_Singleton; [| erewrite gas; eauto ]. simpl.
        rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r.
        intros Hc. destruct Hc as [Hc1 Hc2].
        
        rewrite <- env_locs_Singleton with (v := Loc lenv) in Hc1; try eassumption. 
        
        rewrite <- well_formed_reach_alloc_same in Hc1;
          [| | | eassumption ].
        
        eapply reachable_in_dom in Hc1; try eassumption. destruct Hc1 as [b' Hget].
        eapply Hsub2 in Hget.  
        erewrite alloc_fresh in Hget; eauto. congruence.
        
        eapply well_formed_antimon; [| eapply Fun_inv_reach2_funs; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eapply Singleton_Included. eexists; split; now eauto. 
        eapply Included_trans; [| eapply Fun_inv_dom2_funs; eassumption ].
        eapply env_locs_monotonic.
        eapply Singleton_Included. eexists; split; now eauto.

        eapply well_formed_antimon; [| eapply Fun_inv_reach2_funs; eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eapply Singleton_Included. eexists; split; now eauto. 
        eapply Included_trans; [| eapply Fun_inv_dom2_funs; eassumption ].
        eapply env_locs_monotonic.
        eapply Singleton_Included. eexists; split; now eauto.
      + rewrite Combinators.compose_id_right. 
        rewrite compose_extend. rewrite extend_gss.
        eapply f_eq_subdomain_antimon.
        eapply Included_Union_Setminus with (s2 := [set l1]). 
        now tci.
        rewrite Union_commut. eapply f_eq_subdomain_extend.
        symmetry. eapply compose_id_extend.
      
        intros Hc.
        rewrite reach_unfold, Setminus_Union_distr,
        Setminus_Same_set_Empty_set, Union_Empty_set_neut_l in Hc.
        
        assert (Hsub' : (post H1 (val_loc (Loc l1))) \subset
                        reach' H1 (env_locs rho1 (Funs \\ Scope))).
        { rewrite (reach_unfold H1 (env_locs rho1 (Funs \\ Scope))).
          eapply Included_Union_preserv_r.
          eapply Included_trans; [| eapply reach'_extensive ].
          eapply post_set_monotonic.
          eapply get_In_env_locs. constructor; eauto. eassumption. }
        
        assert (Hin2 : l2 \in dom H2).
        { eapply Him. left. 
          eapply image_monotonic; [| eassumption ].
          eapply Included_trans. eapply Setminus_Included.
          
          
          rewrite <- well_formed_post_subheap_same, <- well_formed_reach_subheap_same;
            try eassumption.
          
          eapply reach'_set_monotonic. eapply post_set_monotonic.
          eapply get_In_env_locs; try eassumption. now constructor; eauto.
          
          eapply well_formed_antimon; [| eassumption ].
          rewrite (reach'_idempotent H1 (env_locs rho1 (FV Scope Funs FVs))).
          eapply reach'_set_monotonic.  
          eapply Included_trans. eassumption.
          eapply reach'_set_monotonic. eapply env_locs_monotonic...
          eapply Included_trans; [| eapply reachable_in_dom; eassumption ].
          eapply Included_trans. eassumption.
          eapply reach'_set_monotonic. eapply env_locs_monotonic...
          
          eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply get_In_env_locs; try eassumption.
          now left; right; constructor; eassumption. 
          
          eapply Included_trans; [| eassumption ]. 
          
          eapply get_In_env_locs; try eassumption.
          now left; right; constructor; eassumption.
          
        }
      
        destruct Hin2 as [b' Hget].
        erewrite alloc_fresh in Hget; eauto. congruence. 
        
      + rewrite Combinators.compose_id_right.
        rewrite compose_extend. simpl extend. rewrite extend_gso.
        
        eapply f_eq_subdomain_antimon.
        eapply Included_Union_Setminus with (s2 := (val_loc (Loc l1))). 
        now tci.
        rewrite Union_commut. eapply f_eq_subdomain_extend.
      symmetry. eapply compose_lift_id_extend.
      
      intros Hc.
      rewrite reach_unfold, Setminus_Union_distr,
      Setminus_Same_set_Empty_set, Union_Empty_set_neut_l in Hc.
      
      assert (Hsub' : post H1 (val_loc (Loc l1)) \subset
                      reach' H1 (env_locs rho1 (Funs \\ Scope))).
      { eapply Included_trans; [| eapply Included_post_reach' ]. 
        eapply post_set_monotonic.
        eapply get_In_env_locs; try eassumption. constructor; eauto. }
      
      assert (Hin2 : l2 \in dom H2).
      { eapply Him. right. 
        eapply image_monotonic; [| eassumption ].
        eapply Included_trans. eapply Setminus_Included.
        
        rewrite <- well_formed_post_subheap_same, <- well_formed_reach_subheap_same;
          try eassumption.

        eapply reach'_set_monotonic. eapply post_set_monotonic.
        eapply get_In_env_locs; try eassumption. constructor; eauto.

        eapply well_formed_antimon; [| eassumption ].
        rewrite (reach'_idempotent H1 (env_locs rho1 (FV Scope Funs FVs))).
        eapply reach'_set_monotonic. eapply Included_trans. eassumption.

        eapply reach'_set_monotonic. eapply env_locs_monotonic...

        eapply Included_trans; [| eapply reachable_in_dom; eassumption ].
        eapply Included_trans. eassumption.
        eapply reach'_set_monotonic. eapply env_locs_monotonic...
        
        eapply well_formed_antimon; [| eassumption ].
        eapply reach'_set_monotonic.
        eapply get_In_env_locs; try eassumption.
        now left; right; constructor; eassumption.
        
        eapply Included_trans; [| eassumption ]. 
        
        eapply get_In_env_locs; try eassumption.
        now left; right; constructor; eassumption.
      }
     
      destruct Hin2 as [b' Hget].
      erewrite alloc_fresh in Hget; eauto. congruence.

      intros Hc. subst. 
       
      assert (Hd : l2 \in dom H2).
      { eapply reachable_in_dom.
        eapply Fun_inv_reach2_funs; eassumption.
        eapply Fun_inv_dom2_funs; eassumption.        
        eapply reach'_extensive. eapply get_In_env_locs; eauto.
        eexists; split; eauto. constructor; eauto. reflexivity. }

      destruct Hd as [b' Hget].
      erewrite alloc_fresh in Hget; eauto. congruence.
  Qed.
  
  Lemma Fun_inv_rename_ext k j GI GP b b' d d' rho1 H1 rho2 H2 Funs Scope Γ FVs :
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs Γ FVs ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (Funs \\ Scope))) b b' ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (Funs \\ Scope))) d d' ->
    Fun_inv k j GI GP b' d' rho1 H1 rho2 H2 Scope Funs Γ FVs.
  Proof.
    intros Hfun Heq1 Heq2 x Hin Hnin.
    edestruct Hfun
      as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *)
         & Hget2 & Hget3 & Hget4 & Henv & Heq);
      try eassumption.
    
    do 7 eexists; repeat split; try eassumption.    
    
    - eapply cc_approx_clos_rename_ext; try eassumption.

      + eapply f_eq_subdomain_antimon; [ | eassumption ].
        eapply Included_trans; [| eapply reach'_set_monotonic; eapply get_In_env_locs; try eassumption ]. 
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. simpl. 
        rewrite post_Singleton; eauto.
        simpl. reflexivity.
        now constructor; eauto.

      + eapply f_eq_subdomain_antimon; [ | eassumption ].
        eapply Included_trans; [| eapply reach'_set_monotonic; eapply get_In_env_locs; try eassumption ]. 
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. simpl. 
        rewrite post_Singleton; eauto.
        simpl. reflexivity.
        now constructor; eauto.

    - destruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc lenv]) H2) as [l2 H2'].

      assert (Hseq : l1 |: (reach' H1 (val_loc (Loc l1))) <--> reach' H1 (val_loc (Loc l1))).
      { split. eapply Union_Included. eapply Singleton_Included. eapply reach'_extensive.
        reflexivity. reflexivity.
        eapply Included_Union_preserv_r. reflexivity. }
      eapply cc_approx_val_rename_ext. eassumption.
      
      rewrite <- Hseq.  eapply f_eq_subdomain_extend. symmetry.
      eapply f_eq_subdomain_antimon; [ | eassumption ]. eapply reach'_set_monotonic.
      eapply get_In_env_locs. constructor; eauto. eassumption.
      
      rewrite <- Hseq.  eapply f_eq_subdomain_extend. symmetry.
      eapply f_eq_subdomain_antimon; [ | eassumption ]. eapply reach'_set_monotonic.
      eapply get_In_env_locs. constructor; eauto. eassumption.
  Qed.
  

  Instance Proper_Fun_inv_Funs k j GI GP b d rho1 H1 rho2 H2 Scope :
    Proper (Same_set _ ==> eq ==> eq ==> iff)
           (Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope). 
  Proof.
    intros S1 S2 Hseq x1 x2 Heq1 f1 f2 Heq3; subst.
    split; intros Hfv f Hin Hnin.
    - edestruct (Hfv f)
        as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *)
           & Hget2 & Hget3 & Hget4 & Henv & Heq);
      try eassumption.
      rewrite Hseq. eassumption.
      do 7 eexists; repeat split; try eassumption.
      rewrite <- Hseq. eassumption.
      (* rewrite <- Hseq. eassumption. *)
    - edestruct (Hfv f)
        as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *)
               & Hget2 & Hget3 & Hget4 & Henv & Heq);
      try eassumption.
      rewrite <- Hseq. eassumption.
      do 7 eexists; repeat split; try eassumption.
      rewrite Hseq. eassumption.
      (* rewrite Hseq. eassumption. *)
  Qed.
  
  Instance Proper_Fun_inv_Scope k j GI GP b d rho1 H1 rho2 H2 :
    Proper (Same_set _ ==> eq ==> eq ==> eq ==> iff)
           (Fun_inv k j GI GP b d rho1 H1 rho2 H2). 
  Proof.
    intros S1 S2 Hseq x1 x2 Heq1 y1 y2 Heq2 f1 f2 Heq3; subst.
    split; intros Hfv f Hin Hnin.
    edestruct (Hfv f) as
        (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *) &
         Hget2 & Hget3 & Hget4 & Henv & Heq); try eassumption.
    rewrite Hseq. eassumption.
    do 7 eexists; repeat split; try eassumption.
    rewrite <- Hseq. eassumption.
    (* rewrite <- !Hseq at 1. eassumption. *)
    edestruct (Hfv f) as
        (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *) &
            Hget2 & Hget3 & Hget4 & Henv & Heq); try eassumption.
    rewrite <- Hseq. eassumption.
    do 7 eexists; repeat split; try eassumption.
    rewrite Hseq. eassumption.
    (* rewrite !Hseq at 1. eassumption. *)
  Qed.
  
  Lemma Fun_inv_locs_Disjoint1 k j GI GP b d rho1 H1 rho2 H2 Funs Scope Γ FVs f :
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs Γ FVs ->
    f \in (Funs \\ Scope) ->
    Disjoint _ (env_locs rho1 [set f])
             (reach' H1 (env_locs rho1 (FV Scope Funs FVs \\ [set f]))).
  Proof.
    intros Hfun [Hin Hnin].
    edestruct Hfun as
        (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis & (* Hsub & *)
            Hget2 & Hget3 & Hget4 & Henv & Heq); try eassumption.
    rewrite env_locs_Singleton; [| eassumption ].
    eapply Disjoint_Singleton_l. intros Hc. eapply Hdis.
    rewrite reach'_Union. now left. 
  Qed.

  Lemma Fun_inv_locs_Disjoint2 k j GI GP b d rho1 H1 rho2 H2 Funs Scope Γ FVs :
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs Γ FVs ->
    Disjoint _ (env_locs rho1 (Funs \\ Scope))
             (reach' H1 (post H1 (env_locs rho1 (Funs \\ Scope)))).
  Proof.
    intros Hfun. constructor. intros l [l' [f [Hin Hm]] Hin'].
    destruct (M.get f rho1) as [[l1|] | ] eqn:Hget; inv Hm.
    inv Hin.
    edestruct Hfun as
        (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis & (* Hsub & *)
            Hget2 & Hget3 & Hget4 & Henv & Heq); try eassumption.
    eapply Hdis. repeat subst_exp.
    rewrite reach'_Union.
    assert (Hseq : Funs \\ Scope <--> Funs \\ Scope \\ [set f] :|: [set f]).
    { rewrite <- Union_Setminus. rewrite Union_commut, Union_Same_set.
      reflexivity. eapply Singleton_Included. constructor; eauto. tci. }

    rewrite Hseq in Hin'. rewrite env_locs_Union, post_Union, reach'_Union in Hin'.
    inv Hin'.
    - left. rewrite reach'_idempotent. eapply reach'_set_monotonic; [| eassumption ].
      eapply Included_trans. eapply Included_post_reach'.
      eapply reach'_set_monotonic. eapply env_locs_monotonic.
      now eauto with Ensembles_DB.
    - right. eapply reach'_set_monotonic; [| eassumption ].
      rewrite env_locs_Singleton; eauto. reflexivity. 
  Qed.
  
  Lemma Fun_inv_post_Included k j GI GP b d rho1 H1 rho2 H2 Funs Scope Γ FVs :
    Fun_inv k j GI GP b d rho1 H1 rho2 H2 Scope Funs Γ FVs ->
    post H1 (env_locs rho1 (Funs \\ Scope)) \subset
    reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope).
  Proof. 
    intros Hfun l Hpost.
    edestruct post_exists_Singleton as [l' [Hin Hpin]]. eassumption. 
    constructor.

    eapply Included_post_reach'. eapply post_set_monotonic; [| eassumption ].
    eapply Singleton_Included. eapply env_locs_monotonic; [| eassumption ].
    now eauto with Ensembles_DB.

    intros Hc. eapply Fun_inv_locs_Disjoint2. eassumption.
    constructor. eassumption. eapply reach'_extensive.
    eapply post_set_monotonic; [| eassumption ].
    eapply Singleton_Included; eassumption. 
  Qed.

  Lemma FV_dom1 k P1 P2 rho1 H1 rho2 H2 b d c
        Scope {Hs : ToMSet Scope} Funs Γ FVs fenv :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b; d) (H2, rho2)) ->
    (forall j, Fun_inv k j P1 P2 b d rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Funs fenv FVs) ->
    env_locs rho1 (FV Scope Funs FVs) \subset dom H1.
  Proof.
    intros Hcc Hfun Henv.
    unfold FV.
    rewrite <- (Union_Setminus_Included Scope Funs) at 1; [| | reflexivity ]; tci. 
    rewrite !env_locs_Union.
    eapply Union_Included. 
    eapply Union_Included.
    
    eapply cc_approx_env_P_dom1. now eapply (Hcc 0). 
    eapply Fun_inv_dom1. eassumption.

    rewrite (Union_Setminus_Included Scope Funs) at 1; [| | reflexivity ]; tci.     
    eapply FV_inv_dom1.
    eassumption.
  Qed.

  Lemma FV_dom2 k P1 P2 rho1 H1 rho2 H2 b d c
        Scope {Hs : ToMSet Scope} Funs Γ FVs fenv :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b; d) (H2, rho2)) ->
    (forall j, Fun_inv k j P1 P2 b d rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    binding_in_map Scope rho1 ->
    env_locs rho2 (FV_cc Scope Funs fenv Γ) \subset dom H2.
  Proof.
    intros Hcc Hfun Henv Hbin.
    unfold FV_cc.
    rewrite !env_locs_Union.
    eapply Union_Included. 
    eapply Union_Included.
    eapply Union_Included.

    eapply cc_approx_env_P_dom2. now eapply (Hcc 0). 
    eassumption.
    
    eapply Fun_inv_dom2. eassumption.
    eapply Fun_inv_dom2_funs. eassumption.

    eapply FV_inv_dom2. eassumption.
  Qed.
  
  Lemma FV_reach1 k P1 P2 rho1 H1 rho2 H2 b d c
        Scope {Hd : Decidable Scope} Funs Γ fenv FVs :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b; d) (H2, rho2)) ->
    (forall j, Fun_inv k j P1 P2 b d rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Funs fenv FVs) ->
    well_formed (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) H1.
  Proof.
    intros Hcc Hfun Henv.
    unfold FV.
    rewrite <- (Union_Setminus_Included Scope Funs) at 1; [| | reflexivity ]; tci. 
    rewrite !env_locs_Union, !reach'_Union. eapply well_formed_Union.
    eapply well_formed_Union.
    
    eapply cc_approx_env_P_well_formed_reach1. eassumption.

    eapply Fun_inv_reach1. eassumption.
    
    rewrite (Union_Setminus_Included Scope Funs) at 1; [| | reflexivity ]; tci.     
    eapply FV_inv_reach1.
    eassumption.
  Qed.

  Lemma FV_reach2 k P1 P2 rho1 H1 rho2 H2 b d c
        Scope {Hd : Decidable Scope} Funs Γ fenv FVs :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b; d) (H2, rho2)) ->
    (forall j, Fun_inv k j P1 P2 b d rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    (forall j, FV_inv k j P1 P2 b d rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    binding_in_map Scope rho1 ->
    well_formed (reach' H2 (env_locs rho2 (FV_cc Scope Funs fenv Γ))) H2.
  Proof.
    intros Hcc Hfun Henv Hbin.
    unfold FV_cc. 
    rewrite !env_locs_Union, !reach'_Union. eapply well_formed_Union.
    eapply well_formed_Union.
    eapply well_formed_Union.
    
    eapply cc_approx_env_P_well_formed_reach2. eassumption.
    eassumption.
    
    eapply Fun_inv_reach2. eassumption.
    
    eapply Fun_inv_reach2_funs. eassumption.
    destruct (Henv 0) as (Hr & _). 
    eassumption.
  Qed.

    (** * Lemmas about [project_var] and [project_vars] *)
  
    
  Lemma project_var_ctx_to_heap_env Scope Scope' Funs Funs' c fenv FVs x C v1 rho1 rho2 H2 Γ:
    project_var Size.Util.clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    Fun_inv_weak rho1 rho2 Scope Funs fenv ->
    FV_inv_weak rho1 rho2 H2 c Scope Funs Γ FVs ->
    M.get x rho1 = Some v1 ->
    exists H2' rho2' s, ctx_to_heap_env_CC C H2 rho2 H2' rho2' s.
  Proof.
    intros Hproj Hfun HFV Hget. inv Hproj.
    - repeat eexists; econstructor; eauto.
    - edestruct Hfun as (l1 & lenv & B & f' & Hget1 & Hget2 & Hget3); try eassumption.
      edestruct (alloc (Constr Size.Util.clo_tag [FunPtr B f'; Loc lenv]) H2) as [l' H2'] eqn:Ha. 
      do 3 eexists.
      econstructor; [ | | now econstructor ].
      + simpl. rewrite Hget2, Hget3. reflexivity.
      + eassumption. 
    - edestruct HFV as (v & vs  & Hget1 & Hget2 & Hall).   
      edestruct Forall2_P_nthN as [v2 [Hnth Hr]]; eauto.
      repeat eexists. intros Hc. now inv Hc; eauto.
      do 3 eexists. econstructor; try eassumption. constructor.
  Qed.
  
  Lemma project_vars_ctx_to_heap_env Scope Scope' {Hs : ToMSet Scope} Funs Funs' c Γ FVs xs C vs1 rho1 rho2 H2 fenv :
    ~ Γ \in FV Scope Funs FVs ->
    Disjoint _ (image fenv (Funs \\ Scope)) (FV Scope Funs FVs) ->
    project_vars Size.Util.clo_tag Scope Funs fenv c Γ FVs xs C Scope' Funs'  ->
    Fun_inv_weak rho1 rho2 Scope Funs fenv ->
    FV_inv_weak rho1 rho2 H2 c Scope Funs Γ FVs ->
    getlist xs rho1 = Some vs1 ->
    exists H2' rho2' s, ctx_to_heap_env_CC C H2 rho2 H2' rho2' s.
  Proof.
    revert Scope Hs Scope' Funs Γ FVs C vs1
           rho1 rho2 H2.
    induction xs;
      intros Scope Hs Scope' Funs Γ FVs C vs1
             rho1 rho2 H2 Hnin Hdis Hvars Hfun HFV Hget.
    - inv Hvars. repeat eexists; econstructor; eauto.
    - inv Hvars. simpl in Hget.
      destruct (M.get a rho1) eqn:Hgeta1; try discriminate.
      destruct (getlist xs rho1) eqn:Hgetlist1; try discriminate. 
      edestruct project_var_ctx_to_heap_env with (rho1 := rho1)
        as [H2' [rho2' [s Hctx1]]]; eauto.
      inv Hget.
      assert (Hs2 := project_var_ToMSet _ _ _ _ _ _ _ _ _ _ H8).  
      edestruct IHxs with (H2 := H2') (rho2 := rho2') as [H2'' [rho2'' [s' Hctx2]]];
        [ eassumption | | | eassumption | | | eassumption | ].
   
      + intros Hd; eapply Hnin. erewrite project_var_FV_eq; eassumption.
      + erewrite <- project_var_FV_eq; try eassumption.
        eapply Disjoint_Included_l; [| eassumption ].
        eapply image_monotonic. eapply Included_Setminus_compat.
        eapply project_var_Funs_l. eassumption.
        eapply project_var_Scope_l. eassumption.   
      + intros f Hnin' Hin.
        edestruct Hfun as (l1 & lenv & B & f' & Hget1 & Hget2 & Hget3); try eassumption.
        intros Hc; eapply Hnin'. eapply project_var_Scope_l; eassumption.
        eapply project_var_Funs_l; eassumption.
        erewrite <- !project_var_get with (rho1 := rho2) (rho2 := rho2'); try eassumption.
        
        now repeat eexists; eauto.
        intros Hc. inv Hc. eapply Hdis.
        erewrite project_var_FV_eq; try eassumption.
        constructor. eexists; split; eauto.
        constructor. 
        eapply project_var_Funs_l; eassumption.
        intros Hc. eapply Hnin'. 
        eapply project_var_Scope_l; eassumption.   
        left. now left.
        
        intros Hc; inv Hc; eauto.
      + edestruct HFV as [v' [vs [Hget [Hget1 Hall]]]]; eauto.
        repeat eexists; eauto.
        * erewrite <- project_var_get; try eassumption.
          intros Hin'. inv Hin'. eapply Hnin.
          erewrite project_var_FV_eq; try eassumption.
          left. now left.
        * erewrite <- (project_var_subheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H8). reflexivity.
          eassumption. eassumption.
        * eapply Forall2_P_monotonic. eassumption.
          rewrite project_var_Scope_Funs_eq with (Funs' := Funs2); [| eassumption ].
          rewrite Union_Setminus_Included. 
          eapply Included_Union_compat; [| reflexivity ].
          eapply project_var_Scope_l. eassumption. now tci. 
          now eauto with Ensembles_DB.
      + exists H2'', rho2'', (s + s'). eapply ctx_to_heap_env_CC_comp_ctx_f_r; eassumption.
  Qed.

End Invariants.
