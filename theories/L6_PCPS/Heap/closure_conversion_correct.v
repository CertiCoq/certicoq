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
  Definition FV_inv (k j : nat) (IP : GIInv) (P : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) : Prop :=
    exists (vs : list value) (l : loc),
      M.get Γ rho2 = Some (Loc l) /\
      get l H2 = Some (Constr c vs) /\
      Forall2_P (Scope :|: Funs)
                (fun (x : var) (v2 : value)  =>
                   exists v1, M.get x rho1 = Some v1 /\
                         Res (v1, H1) ≺ ^ ( k ; j ; IP ; P ; b) Res (v2, H2)) FVs vs.
  
  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv (k j : nat) (IP : GIInv) (P : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) : Prop :=
    (* (exists f, f \in Funs) /\ *)
    forall (f : var),
    ~ f \in Scope ->
    f \in Funs ->
    exists lf1 lf2,
      M.get f rho1 = Some lf1 /\ 
      M.get f rho2 = Some lf2 /\
      Res (lf1, H1) ≺ ^ ( k ; j ; IP ; P ; b) Res (lf2, H2).
  
  (** Versions without the logical relation. Useful when we're only interested in other invariants. *)
  
  (** Invariant about the free variables *) 
  Definition FV_inv_weak (rho1 : env) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) : Prop :=
    exists (vs : list value) (l : loc),
      M.get Γ rho2 = Some (Loc l) /\
      get l H2 = Some (Constr c vs) /\
      Forall2_P (Scope :|: Funs)
                (fun (x : var) (v2 : value)  =>
                   exists v1, M.get x rho1 = Some v1) FVs vs.
  
  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv_weak (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) : Prop :=
    (* (exists f, f \in Funs \\ Scope) /\ *)
    forall (f : var),
      ~ f \in Scope ->
      f \in Funs  ->    
      exists lf1 lf2,
        M.get f rho1 = Some lf1 /\ 
        M.get f rho2 = Some lf2.
  
  (** * Lemmas about [FV_inv] *)

  Require Import Logic.ClassicalFacts.

  Axiom excluded_middle : excluded_middle. (* Get rid of this at some point *)
  
  Lemma FV_inv_image_post (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->    
    image b ((post H1 ^ j) (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) \subset
    (post H2 ^ j) (post H2 (env_locs rho2 ([set Γ]))).
  Proof with (now eauto with Ensembles_DB).
    intros (vs & l & Hget1 & Hget2 & Hall).
    eapply Included_trans; [| eapply post_n_set_monotonic;
                              rewrite env_locs_Singleton; eauto; simpl;
                              rewrite post_Singleton; eauto; reflexivity ].
    clear Hget1 Hget2.
    induction Hall.
    - eapply Included_trans.
      eapply image_monotonic. eapply post_n_set_monotonic.
      rewrite FromList_nil. rewrite Setminus_Empty_set_abs_r.
      rewrite env_locs_Empty_set. reflexivity.
      rewrite post_n_Empty_set, image_Empty_set...
    - rewrite proper_post_n;
      [| rewrite FromList_cons, Setminus_Union_distr, env_locs_Union
         ; try reflexivity ]. 
      destruct (excluded_middle ((Scope :|: Funs) x)).
      + rewrite proper_post_n;
        [| rewrite Setminus_Included_Empty_set, env_locs_Empty_set,
           Union_Empty_set_neut_l; try reflexivity ].
        eapply Included_trans. eassumption.
        eapply post_n_set_monotonic. simpl...
        eapply Singleton_Included. eassumption.
      +rewrite proper_post_n;
        [| rewrite Setminus_Disjoint; try reflexivity ].
       simpl. rewrite !post_n_Union, image_Union.
       eapply Included_Union_compat; eauto.
       destruct (H H0) as [v1 [Hget1 Hres]].
       rewrite proper_post_n; 
        [| rewrite env_locs_Singleton; eauto; reflexivity ].
      eapply cc_approx_val_image_eq. eassumption.
      eapply Disjoint_Singleton_l; eauto.
  Qed.

  Lemma FV_inv_image_post_eq (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    Disjoint _ (FromList FVs) (Scope :|: Funs) ->
    image b ((post H1 ^ j) (env_locs rho1 (FromList FVs))) <-->
    (post H2 ^ j) (post H2 (env_locs rho2 ([set Γ]))).
  Proof with (now eauto with Ensembles_DB).
    intros Hfv Hd. split.
    - eapply Included_trans.
      eapply image_monotonic. eapply post_n_set_monotonic.
      rewrite <- (Setminus_Disjoint (FromList FVs)); try eassumption.
      reflexivity. eapply FV_inv_image_post. eassumption.
    - destruct Hfv as (vs & l & Hget1 & Hget2 & Hall).
      eapply Included_trans; [ eapply post_n_set_monotonic;
                               rewrite env_locs_Singleton; eauto; simpl;
                               rewrite post_Singleton; eauto; reflexivity |].
      clear Hget1 Hget2.
      induction Hall.
      * simpl. rewrite post_n_Empty_set...
      * assert (Hneq : ~ (Scope :|: Funs) x).
        { intros Hc. eapply Hd. constructor; eauto. constructor; eauto. }
        destruct (H Hneq) as [v1 [Hget1 Hres]].
        eapply Included_trans;
        [| eapply image_monotonic; eapply post_n_set_monotonic;
           rewrite FromList_cons, env_locs_Union, env_locs_Singleton; eauto; reflexivity ]. 
        simpl. rewrite !post_n_Union, image_Union. 
        eapply Included_Union_compat; eauto.
        eapply cc_approx_val_image_eq. eassumption.
        eapply IHHall.  eapply Disjoint_Included_l; [| eassumption ].
        rewrite FromList_cons...
  Qed.
  
  Lemma FV_inv_j_monotonic (k j' j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    j' <= j ->
    FV_inv k j' GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs.
  Proof.
    intros Hfv Hlt. 
    destruct Hfv as (v & vs & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros x1 x2 Hin1 Hin3 Hnp [v' [Hget Hres]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.

  Lemma FV_inv_monotonic (k k' j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    k' <= k ->
    FV_inv k' j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs.
  Proof.
    intros Hfv Hlt. 
    destruct Hfv as (v & vs & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros x1 x2 Hin1 Hin3 Hnp [v' [Hget Hres]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.
    
  Lemma FV_inv_image_reach_n (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->    
    image b (reach_n H1 j (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) \subset
    (reach_n H2 j (post H2 (env_locs rho2 ([set Γ])))).
  Proof.
    intros Hfv. 
    intros l' [l [[m [Hm Hr]] Hin]].
    eapply FV_inv_j_monotonic in Hfv; eauto.
    eexists m. split; eauto. eapply FV_inv_image_post. eassumption.
    eexists; split; eauto.

  Qed.

  Lemma FV_inv_image_reach (k : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    (forall j, FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->    
    image b (reach' H1 (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) \subset
    (reach' H2 (post H2 (env_locs rho2 ([set Γ])))).
  Proof.
    intros Hfv.
    intros l' [l [[m [Hm Hr]] Heq]].
    eexists m. split; eauto. eapply FV_inv_image_post. eauto.
    eexists; split; eauto.
  Qed.

  Lemma FV_inv_image_reach_n_eq (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    Disjoint _ (FromList FVs) (Scope :|: Funs) ->
    image b (reach_n H1 j (env_locs rho1 (FromList FVs))) <-->
    reach_n H2 j (post H2 (env_locs rho2 ([set Γ]))).
  Proof.
    intros Hfv. split.
    - intros l' [l [[m [Hm Hr]] Hin]].
      eapply FV_inv_j_monotonic in Hfv; eauto.
      eexists m. split; eauto. eapply FV_inv_image_post_eq. eassumption.
      eassumption. eexists; split; eauto.
    - intros l' [m [Hm Hr]].
      eapply FV_inv_j_monotonic in Hfv; eauto.
      eapply FV_inv_image_post_eq in Hr; eauto.
      destruct Hr as [l [Heql Hin]]. eexists; split; eauto.
      eexists; split; eauto.
  Qed.

  Lemma FV_inv_image_reach_eq (k : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    (forall j, FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    Disjoint _ (FromList FVs) (Scope :|: Funs) ->
    image b (reach' H1 (env_locs rho1 (FromList FVs))) <-->
    (reach' H2 (post H2 (env_locs rho2 ([set Γ])))).
  Proof.
    intros Hfv. split.
    - intros l' [l [[m [Hm Hr]] Heq]].
      eexists m. split; eauto. eapply FV_inv_image_post_eq; eauto.
      eexists; split; eauto.
    - intros l' [m [Hm Hr]].
      eapply FV_inv_image_post_eq in Hr; eauto.
      destruct Hr as [l [Heql Hin]]. eexists; split; eauto.
      eexists; split; eauto.
  Qed.
  
  Lemma FV_inv_weak_in_FV_inv k j P1 P2 rho1 H1 rho2 H2 β c Scope Funs Γ FVs :
    FV_inv k j P1 P2 β rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    FV_inv_weak rho1 rho2 H2 c Scope Funs Γ FVs.
  Proof.
    intros (x1 & x2  & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    now firstorder.
  Qed.

  Lemma FV_inv_set_not_in_FVs_l (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) x v  :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    ~ x \in (FromList FVs \\ (Scope :|: Funs)) ->
    FV_inv k j GII GI b (M.set x v rho1) H1 rho2 H2 c Scope Funs Γ FVs.
  Proof.
    intros (x1 & x2 & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros y1 v2 Hin Hnin Hp [v1 [Hget Hall1]].
    eexists; split; eauto.
    rewrite M.gso; eauto.
    intros Hc; subst. eapply H; constructor; eauto. 
  Qed.

  Lemma FV_inv_set_not_in_FVs_r (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) x v  :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    x <> Γ ->
    FV_inv k j GII GI b rho1 H1 (M.set x v rho2) H2 c Scope Funs Γ FVs.
  Proof.
    intros (x1 & x2 & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    rewrite M.gso; eauto.
  Qed. 
  
  Lemma FV_inv_set_not_in_FVs (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) x y v v'  :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    ~ x \in (FromList FVs \\ (Scope :|: Funs)) ->
    y <> Γ ->
    FV_inv k j GII GI b (M.set x v rho1) H1 (M.set y v' rho2) H2 c Scope Funs Γ FVs.
  Proof.
    intros. eapply FV_inv_set_not_in_FVs_r; eauto.
    eapply FV_inv_set_not_in_FVs_l; eauto.
  Qed.
  

  (** [FV_inv] is heap monotonic  *)
  Lemma FV_inv_heap_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 H1' : heap block) (rho2 : env) (H2 H2' : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    well_formed (reach' H1 (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) H1 ->
    well_formed (reach' H2 (env_locs rho2 [set Γ])) H2 ->
    env_locs rho1 (FromList FVs \\ (Scope :|: Funs)) \subset dom H1 ->
    env_locs rho2 [set Γ] \subset dom H2 ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    FV_inv k j GII GI b rho1 H1' rho2 H2' c Scope Funs Γ FVs.
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
  Lemma FV_inv_rename_ext (k j : nat) (GII : GIInv) (GI : GInv) (b b' : Inj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env) 
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (FromList FVs \\ (Funs :|: Scope)))) b' b ->
    FV_inv k j GII GI b' rho1 H1 rho2 H2 c Scope Funs Γ FVs.
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
    constructor; eauto. rewrite Union_commut. eassumption.
  Qed.


  (** [FV_inv] monotonic *)
  Lemma FV_inv_Scope_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env) 
        (c : cTag) (Scope Scope' Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    Scope \subset Scope' -> 
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope' Funs Γ FVs.
  Proof.
    intros (x1 & x2 & Hget1 & Hget2 & Hall) Hfeq.
    repeat eexists; eauto. eapply Forall2_P_monotonic. eassumption.
    now eauto with Ensembles_DB. 
  Qed.

  Lemma FV_inv_Funs_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env) 
        (c : cTag) (Scope Funs Funs' : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    Funs \subset Funs' -> 
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs' Γ FVs.
  Proof.
    intros (x1 & x2 & Hget1 & Hget2 & Hall) Hfeq.
    repeat eexists; eauto. eapply Forall2_P_monotonic. eassumption.
    now eauto with Ensembles_DB. 
  Qed.
  
  (** * Lemmas about [Fun_inv] *)

  Lemma Fun_inv_image_post (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs ->
    image b ((post H1 ^ j) (env_locs rho1 (Funs \\ Scope))) <-->
          (post H2 ^ j) (env_locs rho2 (Funs \\ Scope)).
  Proof.
    intros Hfun. split.
    - intros l [l' [Hin Heq]]. subst.
      edestruct post_n_exists_Singleton as [l'' [Hpost' Hin']]; eauto.
      edestruct Hpost' as [f [Hinf Hgetf]]. inv Hinf.
      edestruct Hfun as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
      rewrite Hget1 in Hgetf.
      eapply cc_approx_val_image_eq in Hrel.
      eapply post_n_set_monotonic.
      eapply env_locs_monotonic.
      eapply Singleton_Included. constructor; eauto.
      eapply post_n_set_monotonic. eapply env_locs_Singleton; eauto.
      eapply Hrel. eexists; split;  eauto.
      eapply post_n_set_monotonic; eauto. eapply Singleton_Included. eassumption.
    - intros l Hpost.
      edestruct post_n_exists_Singleton as [l'' [Hpost' Hin']]; eauto.
      edestruct Hpost' as [f' [Hin Hgetf]]; subst.
      inv Hin.
      edestruct Hfun as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
       eapply cc_approx_val_image_eq in Hrel.
      rewrite Hget2 in Hgetf. destruct lf2; inv Hgetf. eapply Hrel in Hin'.
      eapply image_monotonic; eauto.
      eapply post_n_set_monotonic. eexists; split; eauto. constructor; eauto.
      rewrite Hget1; eauto.
  Qed.
  
  Lemma Fun_inv_j_monotonic (k j' j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (Scope Funs : Ensemble var) :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs  ->
    j' <= j ->
    Fun_inv k j' GII GI b rho1 H1 rho2 H2 Scope Funs .
  Proof.
    intros Hfv Hlt f Hin' Hin''.
    edestruct Hfv as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
    repeat eexists; eauto.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.
  
  Lemma Fun_inv_monotonic (k k' j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (Scope Funs : Ensemble var) :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs ->
    k' <= k ->
    Fun_inv k' j GII GI b rho1 H1 rho2 H2 Scope Funs.
  Proof.
    intros Hfv Hlt f Hin' Hin''.
    edestruct Hfv as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
    repeat eexists; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.

  Lemma Fun_inv_set_not_in_Funs_l (k  j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (Scope Funs : Ensemble var) x v :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs  ->
    ~ x \in (Funs \\ Scope) ->
    Fun_inv k j GII GI b (M.set x v rho1) H1 rho2 H2 Scope Funs.
  Proof.
    intros Hfv Hlt f Hnin Hin.
    edestruct Hfv as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
    repeat eexists; eauto.
    rewrite M.gso; eauto. intros Hc; inv Hc; eauto.
    eapply Hlt; constructor; eauto.
  Qed.
  
  Lemma Fun_inv_set_not_in_Funs_r (k  j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (Scope Funs : Ensemble var) x v :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs ->
    ~ x \in (Funs \\ Scope) ->
    Fun_inv k j GII GI b rho1 H1 (M.set x v rho2) H2 Scope Funs.
  Proof.
    intros Hfv Hlt f Hnin Hin.
    edestruct Hfv as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
    repeat eexists; eauto.
    rewrite M.gso; eauto. intros Hc; inv Hc; eauto.
    eapply Hlt. constructor; eauto.
  Qed.

  Lemma Fun_inv_set_not_in_Funs (k  j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (Scope Funs : Ensemble var) x y v v' :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs  ->
    ~ x \in (Funs \\ Scope) ->
    ~ y \in (Funs \\ Scope) ->
    Fun_inv k j GII GI b (M.set x v rho1) H1 (M.set y v' rho2) H2 Scope Funs.
  Proof.
    intros Hfv Hnin Hnin'.
    eapply Fun_inv_set_not_in_Funs_r; eauto.
    eapply Fun_inv_set_not_in_Funs_l; eauto.
  Qed.
  
  Lemma Fun_inv_image_reach (k : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) :
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs) ->
    image b (reach' H1 (env_locs rho1 (Funs \\ Scope))) <-->
    reach' H2 (env_locs rho2 (Funs \\ Scope)).
  Proof.
    intros Hfv. split.
    - intros l' [l [[m [Hm Hr]] Hin]].
      eexists m. split; eauto. eapply Fun_inv_image_post. eauto.
      eexists; split; eauto.
    - intros l' [m [Hm Hr]].
      eapply Fun_inv_j_monotonic in Hfv; eauto.
      eapply Fun_inv_image_post in Hr; eauto.
      destruct Hr as [l [Heql Hin]]. eexists; split; eauto.
      eexists; split; eauto.
  Qed.
  
  Lemma Fun_inv_image_reach_n
        (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (Scope Funs : Ensemble var) :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs ->
    image b (reach_n H1 j (env_locs rho1 (Funs \\ Scope))) <-->
    (reach_n H2 j) (env_locs rho2 (Funs \\ Scope)).
  Proof.
    intros Hfv. split.
    - intros l' [l [[m [Hm Hr]] Hin]].
      eapply Fun_inv_j_monotonic in Hfv; eauto.
      eexists m. split; eauto. eapply Fun_inv_image_post. eassumption.
      eexists; split; eauto.
    - intros l' [m [Hm Hr]].
      eapply Fun_inv_j_monotonic in Hfv; eauto.
      eapply Fun_inv_image_post in Hr; eauto.
      destruct Hr as [l [Heql Hin]]. eexists; split; eauto.
      eexists; split; eauto.
  Qed.
  
  Lemma Fun_inv_weak_in_Fun_inv k j P1 P2 rho1 H1 rho2 H2 β Scope Funs :
    Fun_inv k j P1 P2 β rho1 H1 rho2 H2 Scope Funs ->
    Fun_inv_weak rho1 H1 rho2 H2 Scope Funs.
  Proof.
    now firstorder. 
  Qed.

  (** [Fun_inv] is heap monotonic  *)
  Lemma Fun_inv_heap_mon (k  j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 H1' : heap block) (rho2 : env) (H2 H2' : heap block)
        (Scope Funs : Ensemble var) :
    well_formed (reach' H1 (env_locs rho1 (Funs \\ Scope))) H1 ->
    well_formed (reach' H2 (env_locs rho2 (Funs \\ Scope))) H2 ->
    env_locs rho1 (Funs \\ Scope) \subset dom H1 ->
    env_locs rho2 (Funs \\ Scope) \subset dom H2 ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs ->
    Fun_inv k j GII GI b rho1 H1' rho2 H2' Scope Funs.
  Proof.
    intros Hw1 Hw2 He1 He2 Hs1 Hs2 Hfv x Hnin Hin.
    edestruct Hfv as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
    repeat eexists; eauto.
    eapply cc_approx_val_heap_monotonic; try eassumption.
    eapply well_formed_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply get_In_env_locs; eauto.
    now constructor; eauto.
    eapply well_formed_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply get_In_env_locs; eauto.
    constructor; eauto.
    eapply Included_trans; [| eassumption ]. eapply get_In_env_locs; eauto.
    now constructor; eauto.
    eapply Included_trans; [| eassumption ]. eapply get_In_env_locs; eauto.
    now constructor; eauto.
  Qed.
  

  (** [Fun_inv] under renaming extension  *)
  Lemma Fun_inv_rename_ext (k  j : nat) (GII : GIInv) (GI : GInv) (b b' : Inj)
        (rho1 : env) (H1  : heap block) (rho2 : env) (H2 : heap block)
        (Scope Funs : Ensemble var) :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs  ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (Funs \\ Scope))) b' b ->
    Fun_inv k j GII GI b' rho1 H1 rho2 H2 Scope Funs.
  Proof.
    intros Hfv Hfeq f Hnin Hin.
    edestruct Hfv as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
    repeat eexists; eauto.
    eapply cc_approx_val_rename_ext; try eassumption.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic.
    eapply get_In_env_locs; eauto. constructor; eauto.
  Qed.
  
  (** [Fun_inv] monotonic *)
  Lemma Fun_inv_Scope_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env) 
        (Scope Scope' Funs : Ensemble var) :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs ->
    Scope \subset Scope' -> 
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope' Funs.
  Proof.
    now firstorder.
  Qed.
  
  
  (* Lemma ctx_to_heap_env_size_heap C rho1 rho2 H1 H2 c : *)
  (*   ctx_to_heap_env C H1 rho1 H2 rho2 c -> *)
  (*   size_heap H2 = size_heap H1 + cost_alloc_ctx C. *)
  (* Proof. *)
  (*   intros Hctx; induction Hctx; eauto. *)
  (*   simpl. rewrite IHHctx. *)
  (*   unfold size_heap. *)
  (*   erewrite (HL.size_with_measure_alloc _ _ _ H H'); *)
  (*     [| reflexivity | eassumption ]. *)
  (*   erewrite getlist_length_eq; [| eassumption ]. *)
  (*   simpl. omega. *)
  (* Qed. *)

  (** Process the evaluation context of the right expression *)

  (** * Lemmas about [project_var] and [project_vars] *)
  
    
  Lemma project_var_ctx_to_heap_env Scope Funs c Γ FVs x x' C S S' v1 rho1 rho2 H1 H2:
    project_var Scope Funs c Γ FVs S x x' C S' ->
    Fun_inv_weak rho1 H1 rho2 H2 Scope Funs  ->
    FV_inv_weak rho1 rho2 H2 c Scope Funs Γ FVs ->
    M.get x rho1 = Some v1 ->
    exists H2' rho2' s, ctx_to_heap_env_CC C H2 rho2 H2' rho2' s.
  Proof.
    intros Hproj HFun HFV Hget. inv Hproj.
    - repeat eexists; econstructor; eauto.
    - edestruct HFun as
          (vf1 & vf4 & Hget1 & Hget2) ; eauto.
      repeat eexists; constructor; eauto.
    - edestruct HFV as (v & vs  & Hget1 & Hget2 & Hall).
      edestruct Forall2_P_nthN as [v2 [Hnth Hr]]; eauto. 
      intros Hc; inv Hc; eauto.
      repeat eexists. econstructor; eauto.
      constructor.
  Qed.
  
  Lemma project_vars_ctx_to_heap_env Scope Funs c Γ FVs xs xs' C S S' vs1 rho1 H1 rho2 H2:
    Disjoint _ S (FV_cc Scope Funs Γ) ->
    
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    Fun_inv_weak rho1 H1 rho2 H2 Scope Funs ->
    FV_inv_weak rho1 rho2 H2 c Scope Funs Γ FVs ->
    getlist xs rho1 = Some vs1 ->
    exists H2' rho2' s, ctx_to_heap_env_CC C H2 rho2 H2' rho2' s.
  Proof.
    intros HD Hvars HFun HFV.
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
      + intros f Hin Hnin.
        edestruct HFun as (vf1 & vf2 & Hgetf1 & Hgetf2); try eassumption.
        repeat eexists; eauto.
        erewrite <- project_var_get; try eassumption.
        intros Hin'. eapply HD. constructor. now eauto.
        left. right.  constructor; eauto.
      + edestruct HFV as [v' [vs [Hget [Hget1 Hall]]]]; eauto.
        repeat eexists; eauto.
        * erewrite <- project_var_get; try eassumption.
          intros Hin'. eapply HD. constructor. now eauto.
          right. reflexivity.
        * erewrite <- (project_var_heap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H9). eassumption.
          eassumption.
      + exists H2'', rho2'', (s + s'). eapply ctx_to_heap_env_CC_comp_ctx_f_r; eassumption.
  Qed.
  

  Lemma project_var_preserves_cc_approx GII GI k j H1 rho1 H2 rho2 H2' rho2' b
        Scope Funs c Γ FVs x x' C S S' m y y' :
    project_var Scope Funs c Γ FVs S x x' C S' ->
    cc_approx_var_env k j GII GI b H1 rho1 H2 rho2 y y' ->
    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->
    ~ y' \in S ->
    cc_approx_var_env k j GII GI b H1 rho1 H2' rho2' y y'.
  Proof.     
    intros Hproj Hcc Hctx Hnin.
    destruct Hproj; inv Hctx; eauto.
    - inv H19. eapply cc_approx_var_env_set_neq_r; eauto.
      intros Hc; subst; eauto.
  Qed.
  
  Lemma project_vars_preserves_cc_approx GII GI k j H1 rho1 H2 rho2 H2' rho2' b
        Scope Funs c Γ FVs xs xs' C S S' m y y' :
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    cc_approx_var_env k j GII GI b H1 rho1 H2 rho2 y y' ->
    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->
    ~ y' \in S ->
    cc_approx_var_env k j GII GI b H1 rho1 H2' rho2' y y'.
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
  Lemma project_var_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b
        Scope Funs c Γ FVs x x' C S S' m :
    project_var Scope Funs c Γ FVs S x x' C S' ->
    
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b) (H2, rho2)) ->
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs) ->
    (forall j, FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->

    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->
    
    binding_in_map Scope rho1 ->
    Disjoint _ S (FV_cc Scope Funs Γ) ->

    ~ In _ S' x' /\
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b) (H2', rho2'))  /\
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2' H2' Scope Funs) /\
    (forall j, FV_inv k j GII GI b rho1 H1 rho2' H2' c Scope Funs Γ FVs) /\
    (forall j, cc_approx_var_env k j GII GI b H1 rho1 H2' rho2' x x').

  Proof with (now eauto with Ensembles_DB).
    intros Hproj Hcc Hfun Henv Hctx Hbin Hd.
    inv Hproj.
    - inv Hctx. split. intros Hc. eapply Hd; eauto. constructor; eauto. left; eauto.
      split; [| split; [| split ]]; eauto.
      intros j; eapply Hcc. eassumption.
    - inv Hctx.
      split; [| split; [| split; [| split ]]]. repeat split.
      + intros Hc. eapply Hd. constructor; eauto.
        left. right. constructor; eauto.
      + intros j. eapply Hcc; eauto.
      + eassumption.
      + eassumption.
      + intros j. edestruct (Hfun j) as (vf1 & vf2 & Hget1 & Hget2 & Hcc'); eauto.
        intros v1 Hget1'. repeat subst_exp. eexists; split; eauto.
    - inv Hctx. inv H19.
      split; [| split; [| split; [| split ]]]. repeat split.
      + intros Hc. inv Hc. eauto.
      + intros j. eapply cc_approx_env_P_set_not_in_P_r. now eauto.
        intros Hc. eapply Hd; eauto. constructor; eauto.
        left; eauto.
      + intros j. eapply Fun_inv_set_not_in_Funs_r; eauto.
        intros Hc; eapply Hd. constructor; eauto.
        constructor; eauto.
      + intros h. 
        edestruct Henv as (v1 & vs1 & Hget1 & Hget2 & Hall).
        repeat eexists; eauto. 
        rewrite M.gso; eauto. intros Heq; subst. eapply Hd. constructor; eauto.
        right. reflexivity.
      + intros j v' Hget.
        edestruct (Henv j) as (v1 & vs1 & Hget1 & Hget2 & Hall).
        eexists. rewrite M.gss. split. reflexivity.
        edestruct (Forall2_P_nthN _ _ _ _ FVs _ N _ Hall H3) as (v2 & Hnth' & vs4 & Hget4 & Hrel).
        intros Hc; inv Hc; eauto. repeat subst_exp. eassumption.
  Qed.
  
  Lemma project_var_setminus_same  Scope Funs c Γ FVs x x' C S S' : 
    project_var Scope Funs c Γ FVs S x x' C S' ->
    project_var Scope (Funs \\ Scope) c Γ FVs S x x' C S'.
  Proof. 
    intros Hvar; destruct Hvar; try now constructor; eauto.
    constructor; eauto. intros Hc; inv Hc; eauto.
  Qed.

  Lemma project_vars_setminus_same  Scope Funs c Γ FVs xs xs' C S S' : 
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    project_vars Scope (Funs \\ Scope) c Γ FVs S xs xs' C S'.
  Proof. 
    intros Hvar; induction Hvar; try now constructor; eauto.
    econstructor; eauto. eapply project_var_setminus_same. eassumption.
  Qed.

  (** Correctness of [project_vars] *)
  Lemma project_vars_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b
        Scope Funs c Γ FVs xs xs' C S S' m :
    project_vars Scope Funs c Γ FVs S xs xs' C S' ->
    
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b) (H2, rho2)) ->
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs) ->
    (forall j, FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->

    ctx_to_heap_env_CC C H2 rho2 H2' rho2' m ->

    binding_in_map Scope rho1 -> 
    Disjoint _ S (FV_cc Scope Funs Γ) ->

    Disjoint _ (FromList xs') S' /\
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b) (H2', rho2'))  /\
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2' H2' Scope Funs) /\
    (forall j, FV_inv k j GII GI b rho1 H1 rho2' H2' c Scope Funs Γ FVs) /\
    (forall j, Forall2 (fun x x' => cc_approx_var_env k j GII GI b H1 rho1 H2' rho2' x x') xs xs').
  Proof with (now eauto with Ensembles_DB).
    intros Hvars. revert m H1 rho1 H2 rho2 H2' rho2'.
    induction Hvars; intros m H1 rho1 H2 rho2 H2' rho2' Hcc Hfun Hfv Hctx Hb Hd. 
    - inv Hctx. split; [| split; [| split ; [| split ]]]; eauto.
      rewrite FromList_nil...
    - rewrite FromList_cons in *. 
      edestruct ctx_to_heap_env_CC_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      subst.
      eassumption. subst.
      edestruct project_var_correct as (Hd' & Hcc' & Hfun' & Hfv' & Hall');
        try eassumption.
      edestruct IHHvars as (Hd'' & Hcc'' & Hfun'' & Hfv'' & Hall'');
      try eassumption.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply project_var_free_set_Included. eassumption.
      split; [| split; [| split ; [| split ]]]; eauto.
      * eapply Union_Disjoint_l. 
        eapply Disjoint_Included_r.
        eapply project_vars_free_set_Included. eassumption.
        eapply Disjoint_Singleton_l.
        eapply project_var_not_In_free_set'. eassumption.
        eapply Disjoint_Included_r; [| eassumption ].
        unfold FV_cc...
        eapply Disjoint_sym. eapply project_vars_not_In_free_set'. eassumption.
        eapply Disjoint_Included_l.
        eapply project_var_free_set_Included. eassumption.
        eapply Disjoint_Included_r; [| eassumption ].
        unfold FV_cc...
      * intros j. constructor; eauto .
        eapply project_vars_preserves_cc_approx; eauto.
  Qed.

  (** [project_var] preserves injectiveness *)
  Lemma project_var_same_set
        Scope Funs c Γ FVs x x' C S S'  :
    project_var Scope Funs c Γ FVs S x x' C S' ->
    x |: (FV Scope Funs FVs) <--> FV Scope Funs FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hvar. rewrite Union_Same_set. reflexivity.
    eapply Singleton_Included. eapply project_var_In_Union.
    eassumption.
  Qed.

  Lemma project_vars_same_set
        Scope Funs c Γ FVs x x' C S S'  :
    project_vars Scope Funs c Γ FVs S x x' C S' ->
    (FromList x) :|: (FV Scope Funs FVs) <--> FV Scope Funs FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hvar. rewrite Union_Same_set. reflexivity.
    eapply project_vars_In_Union.
    eassumption.
  Qed.

  Lemma image_FV GI GP k β H1 rho1 H2 rho2 Scope Funs FVs Γ c :
    (forall j, (H1, rho1) ⋞ ^ (Scope ; k ; j ; GI ; GP ; β) (H2, rho2)) ->
    (forall j, Fun_inv k j GI GP β rho1 H1 rho2 H2 Scope Funs) ->
    (forall j, FV_inv k j GI GP β rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    binding_in_map Scope rho1 ->

    (image β (reach' H1 (env_locs rho1 (FV Scope Funs FVs)))) \subset
    reach' H2 ((env_locs rho2 (Scope :|: (Funs \\ Scope))) :|: (post H2 (env_locs rho2 [set Γ]))).
  Proof.
    intros. unfold FV, FV_cc.
    rewrite !env_locs_Union, !reach'_Union, !image_Union.
    rewrite cc_approx_env_image_reach; try eassumption. 
    rewrite Fun_inv_image_reach; try eassumption.
    eapply Included_Union_compat. reflexivity.
    eapply FV_inv_image_reach; try eassumption.
  Qed.     

  Lemma image_FV_eq GI GP k β H1 rho1 H2 rho2 Scope Funs FVs Γ c :
    (forall j, (H1, rho1) ⋞ ^ (Scope ; k ; j ; GI ; GP ; β) (H2, rho2)) ->
    (forall j, Fun_inv k j GI GP β rho1 H1 rho2 H2 Scope Funs) ->
    (forall j, FV_inv k j GI GP β rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    binding_in_map Scope rho1 ->
    Disjoint var (FromList FVs) (Scope :|: Funs) ->
    (image β (reach' H1 (env_locs rho1 (FV Scope Funs FVs)))) <-->
    reach' H2 ((env_locs rho2 (Scope :|: (Funs \\ Scope))) :|: (post H2 (env_locs rho2 [set Γ]))).
  Proof.
    intros. unfold FV, FV_cc.
    rewrite !env_locs_Union, !reach'_Union, !image_Union.
    rewrite cc_approx_env_image_reach; try eassumption. 
    rewrite Fun_inv_image_reach; try eassumption.
    assert (Hd' := H5). eapply Setminus_Disjoint in H5.
    eapply Same_set_Union_compat. reflexivity.
    eapply Same_set_trans. eapply image_Proper_Same_set. (* ?????? *)
    reflexivity. eapply Proper_reach'. reflexivity.
    eapply Proper_env_locs. reflexivity. eassumption.
    rewrite FV_inv_image_reach_eq; try eassumption. reflexivity.
  Qed.     
  
  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct (k : nat) (H1 H2 : heap block)
        (rho1 rho2 : env) (e1 e2 : exp) (C : exp_ctx)
        (Scope Funs : Ensemble var) `{ToMSet Funs} (FVs : list var)
        (β : Inj) (c : cTag) (Γ : var) :
    (* [Scope] invariant *)
    (forall j, (H1, rho1) ⋞ ^ (Scope ; k ; j ; PreG Funs; (fun i => Post 0) ; β) (H2, rho2)) ->
    (* [Fun] invariant *)
    (forall j, Fun_inv k j (PreG Funs) (fun i => Post 0) β rho1 H1 rho2 H2 Scope Funs) ->
    (* Free variables invariant *)
    (forall j, FV_inv k j (PreG Funs) (fun i => Post 0) β rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    (* location renaming is injective *)
    (* only needed to prove the lower bound *)
    injective_subdomain (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) β ->
    
    (* well-formedness *)
    well_formed (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) H1 ->
    (env_locs rho1 (FV Scope Funs FVs)) \subset dom H1 ->
    well_formed (reach' H2 (env_locs rho2 (FV_cc Scope Funs Γ))) H2 ->
    (env_locs rho2 (FV_cc Scope Funs Γ)) \subset dom H2 ->

    
    (* [Γ] (the current environment parameter) is not bound in e *)
    ~ In _ (bound_var e1) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (FV Scope Funs FVs) rho1 ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e1 ->
    (* function renaming codomain is not shadowed by other vars *)
    (* Disjoint _ (image σ (Funs \\ Scope)) (bound_var e1) -> *)

    
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion Size.Util.clo_tag Scope Funs c Γ FVs e1 e2 C ->
    
    (forall j, (e1, rho1, H1) ⪯ ^ (k ; j ; Pre ; PreG Funs ; Post 0 ; fun i => Post 0) (C |[ e2 ]|, rho2, H2)).
  Proof with now eauto with Ensembles_DB.
    revert H1 H2 rho1 rho2 e1 e2 C Scope Funs H FVs β c Γ.
    induction k as [k IHk] using lt_wf_rec1.
    intros H1 H2 rho1 rho2 e1 e2 C Scope Funs HMSet FVs β c Γ
           Henv Hfun HFVs Hinjb Hwf1 Hlocs1 Hwf2 Hlocs2 Hnin Hbind Hun Hcc.
    induction e1 using exp_ind'; try clear IHe1.
    - (* case Econstr *)
      assert (Hfv := Closure_conversion_pre_occurs_free_Included _ _ _ _ _ _ _ _ Hcc).
      assert (Hfv' := Closure_conversion_occurs_free_Included _ _ _ _ _ _ _ _ Hcc Hun).
      
      inv Hcc.

      edestruct (binding_in_map_getlist _ rho1 l Hbind) as [vl Hgetl].
      eapply project_vars_In_Union. eassumption.
      
      edestruct project_vars_ctx_to_heap_env as [H2' [rho2' [m Hct]]]; try eassumption.
      specialize (Hfun 0); eapply Fun_inv_weak_in_Fun_inv; eassumption.
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
      
      edestruct project_vars_correct as (Hd' & Henv' & Hfun' & HFVs' & Hvars);
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
        assert (Hfeq : f_eq_subdomain (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) β (β {l1 ~> l2})).
        { eapply f_eq_subdomain_extend_not_In_S_r; [| reflexivity ].
          intros Hc. eapply reachable_in_dom in Hc.
          edestruct Hc as [vc Hgetc]. erewrite alloc_fresh in Hgetc; eauto. congruence.
          eassumption. eassumption. }
        (* Induction hypothesis *)
        { eapply IHk;
          [ | | | | | | | | | | | | eassumption ].
          * simpl in *. omega.
          * { intros j2.  
              eapply cc_approx_env_set_alloc_Constr with (b := β {l1 ~> l2});
                try eassumption.
              - eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic.
                unfold FV...
              - eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic.
                unfold FV_cc.
                now eauto 20 with Ensembles_DB.
              - eapply Included_trans; [| eassumption ].
                eapply env_locs_monotonic. unfold FV...
              - eapply Included_trans; [| eassumption ].
                eapply env_locs_monotonic. unfold FV.
                now eauto 20 with Ensembles_DB.
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
                simpl in *; omega. now eauto with Ensembles_DB.
                eapply f_eq_subdomain_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic...
              - rewrite extend_gss. reflexivity.
              - intros j3 Hlt3. eapply Forall2_monotonic_strong; [| now eapply Hall ].
                intros x1 x2 Hin1 Hin2 Hrel. eapply cc_approx_val_rename_ext. now eapply Hrel.
                assert (Hincl : val_loc x1 \subset env_locs rho1 (FV Scope Funs FVs)).
                { eapply Included_trans; [| now eapply env_locs_monotonic; eauto ].
                  eapply Included_trans; [| eassumption ].
                  simpl. eapply In_Union_list. eapply in_map. eassumption. }
                
                eapply f_eq_subdomain_extend_not_In_S_l; [| reflexivity ].
                
                intros Hc. eapply reachable_in_dom in Hc.
                destruct Hc as [v1 Hgetv1]. erewrite alloc_fresh in Hgetv1; try eassumption.
                congruence.
                
                eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eassumption.

                eapply Included_trans; eassumption. }
          * intros j'.
            { eapply Fun_inv_set_not_in_Funs.
              - eapply Fun_inv_heap_mon; try (now eapply HL.alloc_subheap; eauto).
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
                + eapply Fun_inv_rename_ext.
                  eapply Fun_inv_Scope_mon. eapply Fun_inv_monotonic.
                  eauto. simpl in *; omega. now eauto with Ensembles_DB.
                  symmetry. eapply f_eq_subdomain_antimon; [| eassumption ].
                  eapply reach'_set_monotonic. eapply env_locs_monotonic...
              - intros Hc. inv Hc. eauto.
              - intros Hc. eapply Hc... }
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
              - intros Hc. inv Hc. eauto.
              - intros Hc.
                eapply Hnin. subst; eauto. }
          * assert
              (Hinc :
                 reach' H1'
                        (env_locs (M.set v (Loc l1) rho1)
                                  (FV (v |: Scope) Funs FVs)) \\ [set l1]
                        \subset
                  reach' H1 (env_locs rho1 (FV Scope Funs FVs))
              ).
            { eapply Included_trans. eapply Included_Setminus_compat.
              eapply Included_trans;
                [| eapply reach'_alloc_set with (H' := H1')
                                                (S := FV Scope Funs FVs)];
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
              eapply image_FV in Hc; try eassumption.
              eapply reachable_in_dom in Hc.
              destruct Hc as [vc Hgetc]. erewrite alloc_fresh in Hgetc; eauto. congruence.
              eapply well_formed_antimon; [| eassumption ].
              unfold FV_cc. rewrite !env_locs_Union, !reach'_Union.
              rewrite <- !Union_assoc. eapply Included_Union_preserv_r.
              rewrite !Union_assoc. eapply Included_Union_compat .
              reflexivity.
              rewrite (reach_unfold H2' (env_locs _ _))...
              eapply Union_Included. eapply Included_trans; [| eassumption ].
              eapply env_locs_monotonic. unfold FV_cc...
              eapply Included_trans; [| eapply reachable_in_dom; eauto ].
              rewrite !env_locs_Union, !reach'_Union.
              eapply Included_Union_preserv_r.
              eapply Included_trans. eapply Included_post_reach'.
              eapply reach'_set_monotonic. eapply env_locs_monotonic. unfold FV_cc...
              eapply binding_in_map_antimon; [| eassumption ]... }
          * assert (Hseq : (FV (v |: Scope) Funs FVs) \subset
                                                      (FV Scope Funs FVs) :|: [set v]).
            { unfold FV. eapply Union_Included; [| now eauto with Ensembles_DB ].
              eapply Union_Included; [| now eauto with Ensembles_DB ].
              eapply Union_Included; [| now eauto with Ensembles_DB ]... }
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
          * assert (Hseq : (FV_cc (v |: Scope) Funs Γ) \subset
                           (FV_cc Scope Funs Γ) :|: [set v]).
            { unfold FV_cc. eapply Union_Included; [| now eauto with Ensembles_DB ].
              eapply Union_Included; [| now eauto 20 with Ensembles_DB ].
              eapply Union_Included; [| now eauto with Ensembles_DB ]... }
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