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
  Definition FV_inv (k j : nat) (IP : GIInv) (P : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) : Prop :=
    well_formed (reach' H2 (env_locs rho2 [set Γ])) H2 /\ (* True when the environment is created *)
    key_set rho1 <--> FV Scope Funs FVs /\ 
    exists (vs : list value) (l : loc),
      M.get Γ rho2 = Some (Loc l) /\
      get l H2 = Some (Constr c vs) /\
      Forall2_P (Scope :|: Funs)
                (fun (x : var) (v2 : value)  =>
                   exists v1, M.get x rho1 = Some v1 /\
                         Res (v1, H1) ≺ ^ ( k ; j ; IP ; P ; b) Res (v2, H2)) FVs vs.

  (** Invariant about the functions currently in scope not yet packed as closures *)
  Definition Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs :=
    forall f, ~ f \in Scope -> f \in Funs ->
         exists l1 lenv1 lenv2 B1 g1 B2 g2,
           M.get f rho1 = Some (Loc l1) /\

           (* Funs locations are fresh, and there are no references to them  *)
           ~ l1 \in (reach' H1 ((env_locs rho1 (FV Scope Funs FVs \\ [set f])) :|: post H1 [set l1])) /\

           M.get f rho2 = Some (FunPtr B2 g2) /\
           get l1 H1 = Some (Clos (FunPtr B1 g1) (Loc lenv1)) /\

           M.get (fenv f) rho2 = Some (Loc lenv2) /\

           (* Environments are related (before allocation) *)
           (lenv1, H1) << ^ (k; j; GI; GP; b) (lenv2, H2) /\

           (* We can alloc a related function *)
           let '(l2, H2') := alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc lenv2]) H2 in
           Res (Loc l1, H1) ≺ ^ (k; j; GI; GP; b{l1 ~> l2}) Res (Loc l2, H2'). 

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

  Lemma Forall2_P_Forall2 {A B : Type} S P (ls1 : list A) (ls2 : list B) :  
    Forall2_P S P ls1 ls2 ->
    Disjoint A S (FromList ls1) ->
    Forall2 P ls1 ls2.
  Proof with (now eauto with Ensembles_DB).
    intros Hall Hd. induction Hall.
    - now constructor.
    - constructor.
      + eapply H. intros Hc. eapply Hd. constructor; eauto.
        now left.
      + eapply IHHall.
        eapply Disjoint_Included_r; eauto.
        normalize_sets...
  Qed. 

  Lemma key_set_get S `{_ : ToMSet S} x rho :
    x \in S ->
    M.get x rho = M.get x (restrict_env (@mset S _) rho).
  Proof.
    intros Hin.
    assert (Hset : Restrict_env S rho (restrict_env (@mset S _) rho)). 
    { eapply restrict_env_correct. eapply H. }
    destruct Hset as [Hin' [Hs1 Hs2]].  
    eapply Hin'. eassumption. 
  Qed.

  Lemma key_set_binding_in_map S `{_ : ToMSet S} (rho : env) :
    binding_in_map S rho ->
    key_set (restrict_env (@mset S _) rho) <--> S.
  Proof. 
    intros Hbin.
    split.
    eapply key_set_Restrict_enc. eapply restrict_env_correct. 
    now eapply H.

    intros x Hin. edestruct Hbin as [v Hget]. eassumption.
    unfold In, key_set. rewrite <- key_set_get; [| eassumption ].
    now rewrite Hget.
  Qed. 

  Lemma FV_inv_cc_approx_clos  (k j : nat) (IP : GIInv) (P : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Γ : var) (FVs : list var) l1 l2 : 
    FV_inv k j IP P b rho1 H1 rho2 H2 c (Empty_set _) (Empty_set _) Γ FVs ->
    binding_in_map (FromList FVs) rho1 ->

    NoDup FVs ->

    get l1 H1 = Some (Env rho1) ->
    M.get Γ rho2 = Some (Loc l2) ->

    l2 = b l1 ->
    
    (l1, H1) << ^ (k; j; IP; P; b) (l2, H2).
  Proof with (now eauto with Ensembles_DB).
    intros (Hwf & Hkey & vs & l' & Hget1 & Hget2 & Hall) Hbin Hnd Hget1' Hget2' Hbeq.
    subst_exp.
    clear Hget1. split. reflexivity.
    do 4 eexists.
    split; [| split; [| split; [| split ]]]; try eassumption.
    - rewrite Hkey. unfold FV.
      rewrite !Union_Empty_set_neut_l.
      rewrite !Setminus_Empty_set_neut_r. 
      rewrite !Union_Empty_set_neut_l.
      reflexivity. 
    - eapply Forall2_monotonic_strong; [| eapply Forall2_P_Forall2; try eassumption ].
      intros x1 x2 Hin1 Hin2 [[l1' |] [Hget1 Hcc1]]; try contradiction. 
      eexists; split; eauto.
      rewrite cc_approx_val_eq. eassumption.

      now eauto with Ensembles_DB. 
  Qed.
  
  Lemma FV_inv_j_monotonic (k j' j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    j' <= j ->
    FV_inv k j' GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs.
  Proof.
    intros Hfv Hlt. 
    destruct Hfv as (Hwf & Hkey & v & vs & Hget1 & Hget2 & Hall).
    split. eassumption. 
    split. eassumption. 
    
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
    destruct Hfv as (Hwf & Hkey & v & vs & Hget1 & Hget2 & Hall).
    split. eassumption.
    split. eassumption.

    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros x1 x2 Hin1 Hin3 Hnp [v' [Hget Hres]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.
      
  Lemma FV_inv_weak_in_FV_inv k j P1 P2 rho1 H1 rho2 H2 β c Scope Funs Γ FVs :
    FV_inv k j P1 P2 β rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    FV_inv_weak rho1 rho2 H2 c Scope Funs  Γ FVs.
  Proof.
    intros (Hwf & Hkey & x1 & x2  & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros ? ? ? ? ? [? [? ? ]]. eexists; eauto.
  Qed.

  Lemma Fun_inv_weak_in_Fun_inv k j P1 P2 rho1 H1 rho2 H2 β
        Scope Funs fenv FVs :
    Fun_inv k j P1 P2 β rho1 H1 rho2 H2 Scope Funs fenv FVs ->
    Fun_inv_weak rho1 rho2 Scope Funs fenv.
  Proof.
    intros Hfun x Hin Hnin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq); try eassumption.
    repeat eexists; eauto.
  Qed.

  Lemma FV_inv_dom1 k P1 P2 rho1 H1 rho2 H2 b c
        Scope Funs Γ FVs :
    (forall j, FV_inv k j P1 P2 b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    env_locs rho1 (FromList FVs \\ (Scope :|: Funs)) \subset dom H1.
  Proof.
    intros Hres l [x1 [Hgetx1 Heq1]].
    destruct (M.get x1 rho1) as [ [|] | ] eqn:Hgety; try inv Heq1.
    edestruct (Hres 0) as (Hwf & Hkey & vs1 & loc_env & Hget1 & Hget2 & Hall).
    edestruct (@Forall2_P_exists loc) with (x := x1) as [v2 [Hin'' Hv]]; try eassumption.
    
    now eapply Hgetx1.
    now eapply Hgetx1.

    destruct Hv as [v1' [Hgety' Hv']]. repeat subst_exp.

    eapply cc_approx_val_dom1. eassumption. reflexivity.
  Qed.

  Lemma FV_inv_dom2 k P1 P2 rho1 H1 rho2 H2 b c
        Scope Funs Γ FVs :
    (forall j, FV_inv k j P1 P2 b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    env_locs rho2 [set Γ] \subset dom H2.
  Proof.
    intros Hres l [x2 [Hgetx2 Heq1]].
    destruct (M.get x2 rho2) as [ [|] | ] eqn:Hgety; try inv Heq1.
    inv Hgetx2.
    edestruct (Hres 0) as (Hwf & Hkey & vs1 & loc_env & Hget1 & Hget2 & Hall).
    repeat subst_exp. eexists; eauto.
  Qed.

  Lemma FV_inv_reach1 k P1 P2 rho1 H1 rho2 H2 b c
        Scope Funs Γ FVs :
    (forall j, FV_inv k j P1 P2 b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    well_formed (reach' H1 (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) H1.
  Proof.
    intros Hres l1 b1 [n [_ Hp]].
    edestruct post_n_exists_Singleton as [lr [Hin Hp']].
    eassumption.
    destruct Hin as [x1 [Hin1 Heq1]].
    
    destruct (M.get x1 rho1) as [ [|] | ] eqn:Hgety; try inv Heq1.

    edestruct (Hres (1 + n)) as (Hwf & Hkey & vs1 & loc_env & Hget1 & Hget2 & Hall).
    edestruct (@Forall2_P_exists loc) with (x := x1) as [v2 [Hin Hv]]; try eassumption.
    now eapply Hin1.
    now eapply Hin1.    
    destruct Hv as [v1' [Hgety' Hv1]]. repeat subst_exp.
    eapply cc_approx_val_post_n_cc with (v1 := Loc lr) (j := 1) in Hp';
      [| eapply cc_approx_val_j_monotonic; try eassumption; omega ].
    intros Hget.
    inv Hp'. 
    
    eapply cc_approx_val_well_formed_post1 with (v1 := Loc l1) (j := 0).
    eassumption. reflexivity. eassumption.

    eapply Included_trans; [| eapply cc_approx_clos_post_dom1 ]; try eassumption.
    rewrite post_Singleton; try eassumption. reflexivity. 
  Qed.
   
  Lemma FV_inv_reach2 k j P1 P2 rho1 H1 rho2 H2 b c
        Γ FVs :
    FV_inv k j P1 P2 b rho1 H1 rho2 H2 c (Empty_set _) (Empty_set _) Γ FVs ->
    well_formed (reach' H2 (env_locs rho2 [set Γ])) H2.
  Proof.
    intros (Henv & _). eassumption.
  Qed.
  

  Lemma FV_inv_image_reach k P1 P2 rho1 H1 rho2 H2 b c
        Scope Funs Γ FVs :
    (forall j, FV_inv k j P1 P2 b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    image b (reach' H1 (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) \subset
    reach' H2 (post H2 (env_locs rho2 [set Γ])).
  Proof.
    intros Hres l' [l [Hin Heq]]; subst.
    destruct Hin as [n [_ Hp]].
    edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.

    edestruct (Hres n) as (Hwf & Hkey & vs1 & loc_env & Hget1 & Hget2 & Hall).
    
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
    [| eexists; split; eauto; eexists; split; eauto; now constructor ].

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
  Qed.

  (* TODO move *)
  Lemma FV_Union1_eq Scope Funs FVs S {_ : Decidable S}:
    FV (S :|: Scope) Funs FVs <-->
    S :|: FV Scope Funs FVs.
  Proof.   
    unfold FV. rewrite <- !Union_assoc.
    rewrite (Union_commut S Scope).
    rewrite (Union_commut S (Scope :|: Funs)).
    do 2 rewrite <- Setminus_Union.
    rewrite !Union_assoc.
    rewrite (Union_Setminus_Included _ _ S); tci.
    rewrite (Union_Setminus_Included _ _ S); tci.
    reflexivity. 
    now eauto with Ensembles_DB.
    now eauto with Ensembles_DB.
  Qed.

  Lemma key_set_set {A} x (v : A) rho :
    key_set (M.set x v rho) <--> x |: key_set rho.
  Proof.
    split; intros y; unfold In, key_set; destruct (Coqlib.peq x y); subst;
    try rewrite !M.gss; eauto.
    - intros _. now left.
    - rewrite !M.gso; eauto. intros H.
      right. eassumption.
    - rewrite !M.gso; eauto. intros H.
      inv H. inv H0. now exfalso; eauto. eassumption.
  Qed.


  Lemma FV_inv_set_not_in_FVs_l (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) x v  :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    FV_inv k j GII GI b (M.set x v rho1) H1 rho2 H2 c (x |: Scope) Funs Γ FVs.
  Proof.
    intros (Hwf & Hkey & x1 & x2 & Hget1 & Hget2 & Hall).
    split; eauto. split; eauto.
    rewrite key_set_set, FV_Union1_eq, Hkey. reflexivity. 
    now tci. 

    repeat eexists; eauto.
    
    eapply Forall2_P_monotonic_strong; [| eapply Forall2_P_monotonic;
                                          [ eassumption |] ].
    intros y1 v2 Hin Hnin Hp [v1 [Hget Hall1]].
    eexists; split; eauto.
    rewrite M.gso; eauto.
    intros Hc; subst. eapply Hp; eauto. now left; left.
    now eauto with Ensembles_DB. 
  Qed.
  
  Lemma FV_inv_set_not_in_FVs_r (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) x v  :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    x <> Γ ->
    FV_inv k j GII GI b rho1 H1 (M.set x v rho2) H2 c Scope Funs Γ FVs.
  Proof.
    intros (Hwf & Hkey & x1 & x2 & Hget1 & Hget2 & Hall) Hnin.
    split; eauto.
    rewrite env_locs_set_not_In; eauto. now intros Hc; inv Hc; eauto.
    split. eassumption. 
    rewrite M.gso; eauto.
  Qed. 
  
  Lemma FV_inv_set_not_in_FVs (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) x y v v'  :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    y <> Γ ->
    FV_inv k j GII GI b (M.set x v rho1) H1 (M.set y v' rho2) H2 c (x |: Scope) Funs Γ FVs.
  Proof.
    intros. eapply FV_inv_set_not_in_FVs_r; eauto.
    eapply FV_inv_set_not_in_FVs_l; eauto.
  Qed.
  

  (** [FV_inv] is heap monotonic  *)
  Lemma FV_inv_heap_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 H1' : heap block) (rho2 : env) (H2 H2' : heap block)
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    (forall j, FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ) ->
    FV_inv k j GII GI b rho1 H1' rho2 H2' c Scope Funs Γ FVs.
  Proof.
    intros Hs1 Hs2.
    intros Henv. edestruct (Henv 0) as (Hwf & Hkey & x1 & x2 & Hget1 & Hget2 & Hall).
    split; [| split ].
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
    - eassumption.
    - repeat eexists; eauto.
      eapply Forall2_P_monotonic_strong; [| eassumption ].
      intros y1 v2 Hin1 Hin2 Hp [v1 [Hget3 Hrel]].
      eexists; split; eauto. 
      eapply cc_approx_val_heap_monotonic; try eassumption.
      intros j'. 
      edestruct (Henv j') as (Hwf' & Hkey' & x1' & x2' & Hget1' & Hget2' & Hall').
      repeat subst_exp. 
      edestruct (Forall2_P_exists _ _ _ _ _ Hin1 Hp Hall') as [v1' [Hin' [v2' [Hget2' Hp']]]]. repeat subst_exp.
      destruct v2'; [| contradiction ]. 
      eapply cc_approx_val_loc_eq in Hrel. subst.
      assert (Hrel := Hp'). 
      eapply cc_approx_val_loc_eq in Hrel. subst.
      eassumption. 
  Qed.
  
  (** [FV_inv] under rename extension  *)
  Lemma FV_inv_rename_ext (k j : nat) (GII : GIInv) (GI : GInv) (b b' : Inj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env) 
        (c : cTag) (Scope Funs : Ensemble var) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (FromList FVs \\ (Scope :|: Funs)))) b' b ->
    FV_inv k j GII GI b' rho1 H1 rho2 H2 c Scope Funs Γ FVs.
  Proof.
    intros (Hwf & Hkey & x1 & x2 & Hget1 & Hget2 & Hall) Hfeq.
    split. eassumption. split. eassumption. repeat eexists; eauto.
    eapply Forall2_P_monotonic_strong; [| eassumption ].
    intros y1 v2 Hin1 Hin2 Hp [v1 [Hget3 Hrel]].
    eexists; split; eauto.
    eapply cc_approx_val_rename_ext; try eassumption.
    eapply f_eq_subdomain_antimon; try eassumption.
    eapply reach'_set_monotonic.
    eapply get_In_env_locs; eauto.
    constructor; eauto.
  Qed.
  

  (** [FV_inv] monotonic *)
  (* Lemma FV_inv_Scope_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) *)
  (*       (rho1 : env) (H1 H2 : heap block) (rho2 : env)  *)
  (*       (c : cTag) (Scope Scope' Funs : Ensemble var) (Γ : var) (FVs : list var) : *)
  (*   FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs -> *)
  (*   Scope \subset Scope' ->  *)
  (*   FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope' Funs Γ FVs. *)
  (* Proof. *)
  (*   intros (Hwf & Hkey & x1 & x2 & Hget1 & Hget2 & Hall) Hfeq. *)
  (*   split. eassumption. split. eassumption. repeat eexists; eauto. *)
  (*   eapply Forall2_P_monotonic. eassumption. *)
  (*   now eauto with Ensembles_DB.  *)
  (* Qed. *)

  (* Lemma FV_inv_Funs_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) *)
  (*       (rho1 : env) (H1 H2 : heap block) (rho2 : env)  *)
  (*       (c : cTag) (Scope Funs Funs' : Ensemble var) (Γ : var) (FVs : list var) : *)
  (*   FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs -> *)
  (*   Funs \subset Funs' ->  *)
  (*   FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs' Γ FVs. *)
  (* Proof. *)
  (*   intros (Hwf & Hkey & x1 & x2 & Hget1 & Hget2 & Hall) Hfeq. *)
  (*   split. eassumption. split. eassumption. repeat eexists; eauto. *)
  (*   eapply Forall2_P_monotonic. eassumption. *)
  (*   now eauto with Ensembles_DB.  *)
  (* Qed. *)

  (* Lemma FV_inv_mon (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj) *)
  (*       (rho1 : env) (H1 H2 : heap block) (rho2 : env)  *)
  (*       (c : cTag) (Scope Scope' Funs Funs' : Ensemble var) (Γ : var) (FVs : list var) : *)
  (*   FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs -> *)
  (*   Scope :|: Funs \subset Scope' :|: Funs' ->  *)
  (*   FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope' Funs' Γ FVs. *)
  (* Proof. *)
  (*   intros (Hwf & x1 & x2 & Hget1 & Hget2 & Hall) Hfeq. *)
  (*   split. eassumption. repeat eexists; eauto. *)
  (*   eapply Forall2_P_monotonic. eassumption. *)
  (*   now eauto with Ensembles_DB.  *)
  (* Qed. *)


  Lemma FV_inv_FV_eq (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 H2 : heap block) (rho2 : env)
        (c : cTag) (Scope Scope' Funs Funs' : Ensemble var)
        {_ : ToMSet Scope} {_ : ToMSet Scope'}
        (Γ : var) FVs :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    Scope :|: Funs <--> Scope' :|: Funs' ->
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Scope' Funs' Γ FVs.
  Proof.
    intros (Hwf & Hkey & x1 & x2 & Hget1 & Hget2 & Hall) Hfeq.
    split. eassumption. split.
    unfold FV in *. 
    rewrite <- Hfeq. rewrite (Union_Setminus_Included Scope' Funs'), <- Hfeq.
    rewrite <- (Union_Setminus_Included Scope Funs) at 1.
    eassumption. tci. reflexivity. tci. reflexivity. 
    repeat eexists; eauto.
    eapply Forall2_P_monotonic. eassumption.
    rewrite Hfeq. reflexivity. 
  Qed.


  Instance Proper_FV_inv_Funs k j GI GP b rho1 H1 rho2 H2 c Scope :
    Proper (Same_set _ ==> eq ==> eq ==> iff)
           (FV_inv k j GI GP b rho1 H1 rho2 H2 c Scope). 
  Proof.
    intros S1 S2 Hseq x1 x2 Heq1 y1 y2 Heq2; subst.
    split; intros (Hwf & Hkey & vs & l & Hget1 & Hget2 & Hall1).
    split. eassumption. split. unfold FV. rewrite <- !Hseq at 1. eassumption.
    do 2 eexists.
    split. eassumption.
    split. eassumption.
    eapply Forall2_P_monotonic; eauto. rewrite Hseq. reflexivity.
    split. eassumption. split. unfold FV. rewrite !Hseq at 1. eassumption.
    do 2 eexists.
    split. eassumption.
    split. eassumption.
    eapply Forall2_P_monotonic; eauto. rewrite Hseq. reflexivity.
  Qed.


  Instance Proper_FV_inv_Scope k j GI GP b rho1 H1 rho2 H2 c :
    Proper (Same_set _ ==> eq ==> eq ==> eq ==> iff)
           (FV_inv k j GI GP b rho1 H1 rho2 H2 c). 
  Proof.
    intros S1 S2 Hseq x1 x2 Heq1 y1 y2 Heq2 z1 z2 Heq3; subst.
    split; intros (Hwf & Hkey & vs & l & Hget1 & Hget2 & Hall1).
    split. eassumption. split. unfold FV. rewrite <- !Hseq at 1.    
    eassumption.
    do 2 eexists.
    split. eassumption.
    split. eassumption.
    eapply Forall2_P_monotonic; eauto. rewrite Hseq. reflexivity.
    split. eassumption. split. unfold FV. rewrite !Hseq at 1. eassumption.
    do 2 eexists.
    split. eassumption.
    split. eassumption.
    eapply Forall2_P_monotonic; eauto. rewrite Hseq. reflexivity.
  Qed.


  Lemma Fun_inv_image_reach k P1 P2 rho1 H1 rho2 H2 b
        Scope Funs fenv FVs :
    (forall j, Fun_inv k j P1 P2 b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    image b (reach' H1 (post H1 (env_locs rho1 (Funs \\ Scope)))) \subset
    reach' H2 (env_locs rho2 (image fenv (Funs \\ Scope))).
  Proof.
    intros Hres l' [l [Hin Heq]].
    destruct Hin as [n [_ Hp]]. 
    edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
    edestruct Hin as [l2 [b1 [Henv [Hgetl1 Hinl1]]]].
    edestruct Henv as [x1 [Hinx Hm]].
    destruct (M.get x1 rho1) as [[l3|] | ] eqn:Hgetx; inv Hm.
    
    inv Hinx. 
    edestruct (Hres n) as (l1' & lenv & l2' & g1 & rhoc & B2 & g2 & Hget1 & Hdis' (* & Hsub *)
                               & Hget2 & Hget3 & Hget4 & Henv' & Heq').
    eassumption. eassumption.
    repeat subst_exp.
    simpl in Hinl1. 

    rewrite Union_Empty_set_neut_l in Hinl1. 
    inv Hinl1.
    eapply reach'_set_monotonic; [| eapply cc_approx_clos_image_eq ].
    
    eapply Singleton_Included. eexists (fenv x1). split.

    eexists. split; [| reflexivity ]. now constructor; eauto.
    rewrite Hget4. reflexivity.

    intros j. 

    edestruct (Hres j) as (l1'' & lenv' & l2'' & g1' & rhoc' & B2' & g2' & Hget1' & Hdis'' (* & Hsub *)
                           & Hget2' & Hget3' & Hget4' & Henv'' & Heq'').
    eassumption. eassumption.
    repeat subst_exp. eassumption.

    eexists. split; [| reflexivity ]. eexists; split; try eassumption. now constructor. 
  Qed.


  Lemma FV_image_reach k P1 P2 rho1 H1 rho2 H2 b c
        Scope Funs Γ fenv FVs :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b) (H2, rho2)) ->
    (forall j, Fun_inv k j P1 P2 b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    (forall j, FV_inv k j P1 P2 b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    image b (reach' H1 (env_locs rho1 (FV Scope Funs FVs)) \\ env_locs rho1 (Funs \\ Scope)) \subset
    reach' H2 (env_locs rho2 (Scope :|: image fenv (Funs \\ Scope) :|: [set Γ])).
  Proof with (now eauto with Ensembles_DB).
    intros Hcc Hfun Henv l' [l [Hin Heq]]; subst.
    unfold FV in Hin.
    rewrite !env_locs_Union, !reach'_Union, !Setminus_Union_distr in Hin.
    inv Hin. inv H. 
    
    + eapply reach'_set_monotonic; [| eapply cc_approx_env_image_reach_included; try eassumption ].
      eapply env_locs_monotonic...
      eexists. split; eauto. inv H0. eassumption.

    + rewrite !env_locs_Union, !reach'_Union. left. right.
      eapply Fun_inv_image_reach. eassumption.
      eexists. split; eauto.
      rewrite reach_unfold, Setminus_Union_distr in H0.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l in H0. 
      inv H0; eassumption.

    + rewrite !env_locs_Union, !reach'_Union. right.
      rewrite reach_unfold. right.
      eapply FV_inv_image_reach. eassumption.

      eexists; split; eauto. 
      inv H. eassumption.
  Qed.


  Lemma def_closures_FV_inv Scope Funs FVs Γ k j GIP GP b B1 B2 envc c rho1 H1 rho1' H1' rho2 H2 :
    (forall j, FV_inv k j GIP GP b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
    def_closures B1 B2 rho1 H1 envc = (H1', rho1') ->
    FV_inv k j GIP GP b rho1' H1' rho2 H2 c (name_in_fundefs B1 :|: Scope) Funs Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    revert H1 rho1 H1' rho1' j.
    induction B1; intros H1 rho1 H1' rho1' j Hfv Hdef.
    - simpl in Hdef.
      destruct (def_closures B1 B2 rho1 H1) as (H1'', rho1'') eqn:Hdef'.
      destruct (alloc (Clos _ _) H1'') as [la H1a] eqn:Hal.
      inv Hdef.
      simpl. eapply Proper_FV_inv_Scope. rewrite <- Union_assoc. reflexivity. reflexivity.
      reflexivity. reflexivity. 
      eapply FV_inv_set_not_in_FVs_l.
      eapply FV_inv_heap_mon; [ | | ].
      * eapply HL.alloc_subheap. eassumption.
      * eapply HL.subheap_refl.
      * intros j'.
        eapply IHB1 in Hdef'.
        eassumption.
        eassumption.
    - inv Hdef. simpl.
      eapply Proper_FV_inv_Scope. rewrite Union_Empty_set_neut_l. reflexivity. 
      reflexivity. reflexivity. reflexivity. auto. 
  Qed.

  Lemma def_funs_FV_inv Scope Funs Γ FVs c k j GIP GP b B1 B2 rho1 H1 rho2 H2 :
    FV_inv k j GIP GP b rho1 H1 rho2 H2 c Scope Funs Γ FVs ->
    name_in_fundefs B1 \subset Scope :|: Funs ->
    ~ Γ \in name_in_fundefs B1 ->
    FV_inv k j GIP GP b rho1 H1 (def_funs B1 B2 rho2) H2 c Scope Funs Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    induction B1; intros Hcc Hsub Hnin.
    - simpl def_funs.
      eapply FV_inv_set_not_in_FVs_r.
      eapply IHB1. eassumption.
      eapply Included_trans; [| eassumption ]... 
      intros Hc. eapply Hnin; now right.
      intros Hc; inv Hc. eapply Hnin; now left.
    - simpl. eassumption.
  Qed.

  
  (** * Lemmas about [Fun_inv] *)

  Lemma Fun_inv_set_r k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs f v :
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs ->
    ~ f \in (Funs \\ Scope) -> ~ f \in (image fenv (Funs \\ Scope)) ->
    Fun_inv k j GI GP b rho1 H1 (M.set f v rho2) H2 Scope Funs fenv FVs.
  Proof.
    intros Hfun Hnin1 Hnin2 x Hnin Hin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                      & Hget2 & Hget3 & Hget4 & Henv & Heq).
    eassumption. eassumption.
    destruct Henv as [Hbeq Henv]. subst.
    
    do 7 eexists. repeat split; try eassumption. rewrite M.gso. eassumption.
    
    intros Hc. subst. eapply Hnin1; eauto. now constructor; eauto.

    rewrite M.gso; try eassumption.

    intros Hc; subst. eapply Hnin2. eexists; split; constructor; eauto.
  Qed.

    Lemma Fun_inv_set_l k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs f v :
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs ->
    Disjoint _ (val_loc v) (dom H1) -> 
    (* post H1 (val_loc v) \subset reach' H1 (env_locs rho1 Scope) ->  *)
    Fun_inv k j GI GP b  (M.set f v rho1) H1 rho2 H2 (f |: Scope) Funs fenv FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hfun Hnin1 (* Hin1 *) x Hnin Hin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    intros Hc. eapply Hnin. right. eassumption. eassumption.
    destruct Henv as [Hbeq Henv]. subst.
    
    do 7 eexists. repeat split; try eassumption. rewrite M.gso. eassumption.
    
    intros Hc. subst. eapply Hnin; now eauto.
    repeat subst_exp. 
    
    intros Hc; subst. eapply Hsub.
    rewrite reach'_Union in *. inv Hc; [| now eauto ].
    left. 
    eapply reach'_set_monotonic in H; [| eapply env_locs_set_Inlcuded' ].
    rewrite reach'_Union in H. inv H. 
    - rewrite reach_unfold in H0. inv H0. 
      + exfalso. eapply Hnin1. constructor; eauto. eexists; eauto.
      + rewrite post_Disjoint in H; [| eassumption ].
        rewrite reach'_Empty_set in H.
        now inv H. 
    - eapply reach'_set_monotonic; [| eassumption ].
      eapply env_locs_monotonic. unfold FV.
      rewrite !Setminus_Union_distr.
        
      eapply Included_Union_compat; [| now eauto with Ensembles_DB ].
      eapply Included_Union_compat; [| now eauto with Ensembles_DB ]. 
      rewrite Setminus_Union, (Union_commut [set x]), <- Setminus_Union. 
      rewrite Setminus_Same_set_Empty_set. rewrite Setminus_Empty_set_abs_r... 
  Qed.

  Lemma Fun_inv_Scope_monotonic k j GI GP b rho1 H1 rho2 H2 Scope S Funs Γ FVs {_ : Decidable S}:
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs Γ FVs ->
    FV (S :|: Scope) Funs FVs <--> FV Scope Funs FVs ->
    Fun_inv k j GI GP b rho1 H1 rho2 H2 (S :|: Scope) Funs Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hfun Heq y Hin Hnin. 
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                      & Hget2 & Hget3 & Hget4 & Henv & Heq').
    now eauto. eassumption.
    destruct Henv as [Hbeq Henv]. subst.
    
    do 7 eexists. repeat split; try eassumption.
    
    intros Hc. eapply Hsub. rewrite <- Heq. eassumption.
  Qed.

  Lemma Fun_inv_monotonic k k' j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs :
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs ->
    k' <= k -> 
    Fun_inv k' j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hfun Hleq x Hin Hnin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    eassumption. eassumption.

    do 7 eexists. repeat (split; [ eassumption |]). split.

    eapply cc_approx_clos_monotonic; eassumption.

    destruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc B1]) H2). 

    eapply cc_approx_val_monotonic; eassumption. 
  Qed.


  Lemma Fun_inv_Scope_monotonic' k j GI GP b rho1 H1 rho2 H2 Scope S Funs Γ FVs {_ : Decidable S}:
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs Γ FVs ->
    FV (S :|: Scope) (Funs \\ S) FVs <--> FV Scope Funs FVs ->
    Fun_inv k j GI GP b rho1 H1 rho2 H2 (S :|: Scope) (Funs \\ S) Γ FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hfun Heq y Hin Hnin.
    edestruct Hfun as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                      & Hget2 & Hget3 & Hget4 & Henv & Heq').
    now eauto. inv Hnin. eassumption.
    destruct Henv as [Hbeq Henv]. subst.
    do 7 eexists. repeat split; try eassumption.
    
    intros Hc. eapply Hsub. rewrite <- Heq. eassumption.
  Qed.



  Lemma Fun_inv_dom1 k GI GP rho1 H1 rho2 H2 b
        Scope Funs Γ FVs :
    (forall j, Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
    env_locs rho1 (Funs \\ Scope) \subset dom H1.
  Proof.
    intros Hres l [x1 [Hgetx1 Heq1]].
    destruct (M.get x1 rho1) as [ [|] | ] eqn:Hgety; try inv Heq1.
    edestruct (Hres 0) as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    now eapply Hgetx1. now eapply Hgetx1.
    destruct Henv as [Hbeq Henv]. subst.
    
    edestruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc (b lenv)]) H2) as [l2 H2'] eqn:Ha. 
    repeat subst_exp. 
    eapply cc_approx_val_dom1. eassumption. reflexivity. 
  Qed.
  
  Lemma Fun_inv_dom2 k GI GP rho1 H1 rho2 H2 b
        Scope Funs Γ FVs :
    (forall j, Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
    env_locs rho2 (Funs \\ Scope) \subset dom H2.
  Proof.
    intros Hres l [x2 [Hgetx1 Heq1]].
    destruct (M.get x2 rho2) as [ [|] | ] eqn:Hgety; try inv Heq1.
    edestruct (Hres 0) as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hsub (* & Hdis *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq).
    now eapply Hgetx1. now eapply Hgetx1.
    repeat subst_exp.
  Qed.
  
  Lemma Fun_inv_reach1 k GI GP rho1 H1 rho2 H2 b
        Scope Funs Γ FVs :
    (forall j, Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
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
    destruct Henv as [Hbeq Henv]. subst.

    assert (Hp'' := Hp'). 
    edestruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc (b lenv)]) H2) as [l2 H2'] eqn:Ha.
    eapply cc_approx_val_post_n_cc with (v1 := Loc l1) (j := 1) in Hp';
      [| eapply cc_approx_val_j_monotonic; try eassumption; omega ].

    
    intros Hget1. 
    eapply cc_approx_val_well_formed_post1 with (v1 := Loc l1) (j := n); try eassumption.
    eapply cc_approx_val_j_monotonic. eassumption. omega.
  Qed.


  Lemma Fun_inv_reach2 k GI GP rho1 H1 rho2 H2 b
        Scope Funs Γ FVs :
    (forall j, Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
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

  Lemma Fun_inv_dom2_funs k GI GP rho1 H1 rho2 H2 b
        Scope Funs fenv FVs :
    (forall j, Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
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

  Lemma Fun_inv_reach2_funs k GI GP rho1 H1 rho2 H2 b
        Scope Funs fenv FVs :
    (forall j, Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
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
  

  Lemma Fun_inv_alloc k j GI GP b rho1 H1 H1' rho2 H2 H2' Scope Funs fenv FVs l1 l2 b1 b2 z:
    closed (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) H1 -> 
    alloc b1 H1 = (l1, H1') ->
    alloc b2 H2 = (l2, H2') ->

    locs b1 \subset reach' H1 (env_locs rho1 Scope) ->
                    
    (forall j, Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->

    ~ z \in image fenv (Funs \\ Scope) ->
    Fun_inv k j GI GP b (M.set z (Loc l1) rho1) H1' (M.set z (Loc l2) rho2) H2' (z |: Scope) Funs fenv FVs.
  Proof with (now eauto with Ensembles_DB).
    intros Hwf Ha1 Ha2 Hsub Hfun Hninz x Hin Hnin.
    edestruct (Hfun j) as (l1' & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *)
                          & Hget2 & Hget3 & Hget4 & Henv & Heq);
      try eassumption.
    intros Hc. eapply Hin. now right. 
    assert (Hneq : x <> z). { intros Hc; inv Hc. eauto. } 
    rewrite !M.gso with (i := x) (j := z) in *; eauto. 
    
    do 7 eexists; split; [| split; [| split; [| split; [| split; [| split ] ]]]]; try eassumption.
    - intros Hc. rewrite post_Singleton in Hdis; eauto. simpl in Hdis.

      rewrite Union_Empty_set_neut_l in Hdis. eapply Hdis.
      rewrite post_Singleton in Hc; [| eapply HL.alloc_subheap; eassumption ].
      simpl in Hc. rewrite Union_Empty_set_neut_l in Hc.
      rewrite reach'_Union in *. inv Hc. 
      + eapply reach'_set_monotonic with (S2 := env_locs (M.set z (Loc l1) rho1)
                                                         (FV Scope Funs FVs \\ [set x] :|: [set z])) in H.
        eapply reach'_alloc_set in H; try eassumption. inv H.
        
        * inv H0. erewrite alloc_fresh in Hget3; eauto. congruence.
        * left. eassumption.
        * eapply Included_trans. eassumption.
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          eapply Included_Setminus. eapply Disjoint_Singleton_r.
          now intros Hc'; eauto. now eauto with Ensembles_DB.
        * eapply env_locs_monotonic. eapply Setminus_Included_Included_Union.

          eapply Included_trans. eapply FV_Union1. rewrite <- Union_assoc. 
          rewrite <- (Union_Included_Union_Setminus _ (z |: [set x])). 
          now eauto with Ensembles_DB. tci.
          now eauto with Ensembles_DB.
      + rewrite <- well_formed_reach_subheap_same in H. right. eassumption.
        eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        rewrite (reach'_idempotent H1 (env_locs rho1 (FV Scope Funs FVs))).
        eapply reach'_set_monotonic.
        eapply Singleton_Included. eexists 1. split. now constructor.
        simpl. do 2 eexists. split; eauto. eapply get_In_env_locs with (x := x); eauto.
        left. right. now constructor; eauto.
        reflexivity. split; eauto. now right.
        eapply Singleton_Included. eapply cc_approx_clos_dom1. eassumption.
        eapply HL.alloc_subheap; eauto.
    - eapply HL.alloc_subheap; eauto.
    - rewrite M.gso. eassumption. intros Hc. eapply Hninz. subst.
      eexists; split; eauto. constructor; eauto.
    - eapply cc_approx_clos_heap_monotonic.
      now eapply HL.alloc_subheap; eauto.
      now eapply HL.alloc_subheap; eauto.
      intros j'.
      edestruct (Hfun j') as (l1'' & lenv' & B1' & g1' & rhoc' & B2' & g2' & Hget1' & Hdis' (* & Hsub *)
                                   & Hget2' & Hget3' & Hget4' & Henv' & Heq');
        try eassumption. intros Hc. eapply Hin. now right.
      repeat subst_exp. eassumption. 
    - destruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc B1]) H2)
        as [l4 H4] eqn:Ha.
      destruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc B1]) H2')
        as [l4' H4'] eqn:Ha'.
      
      eapply cc_approx_val_rename_ext
      with (β' := ((id {l4 ~> l4'}) ∘ (b {l1' ~> l4}) ∘ id)).
      + eapply cc_approx_val_res_eq.
        eassumption.
        eapply res_equiv_subheap; try eassumption; [| | now eapply reach'_extensive |].
        eapply well_formed_antimon; [| eapply well_formed'_closed; eassumption ].
        eapply reach'_set_monotonic. eapply get_In_env_locs; eauto. left. right.
        constructor; eauto. 
        eapply Singleton_Included. eapply cc_approx_val_dom1. eassumption.
        reflexivity.
        now eapply HL.alloc_subheap; eauto.
        clear. now firstorder.
        
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
            [| | | now eapply HL.alloc_subheap; eauto
             | eapply HL.subheap_trans; [| now eapply HL.alloc_subheap; eauto ];
               now eapply HL.alloc_subheap; eauto
             | | ].
             
          eapply reach'_closed.
          eapply Fun_inv_reach2_funs. eassumption. 
          eapply Fun_inv_dom2_funs. eassumption. 
          eapply reach'_closed. 
          eapply Fun_inv_reach2_funs. eassumption. 
          eapply Fun_inv_dom2_funs. eassumption. 
          reflexivity.
          
          eapply Included_trans; [| eapply reach'_extensive ].
          eapply get_In_env_locs; [| eassumption ].
          eexists; split; eauto. now constructor; eauto.
          
          eapply Included_trans; [| eapply reach'_extensive ].
          eapply get_In_env_locs; eauto.
          eexists; split; eauto. now constructor; eauto.
          
          intros Hc1.
          rewrite <- env_locs_Singleton with (v := Loc B1) in Hc1; try eassumption. 
          rewrite <- well_formed_reach_alloc_same in Hc1;
          [| | | eassumption ].
          
          eapply reachable_in_dom in Hc1; try eassumption. destruct Hc1 as [b' Hget].
          erewrite alloc_fresh in Hget; eauto. congruence.
          
          eapply well_formed_antimon; [| eapply Fun_inv_reach2_funs; eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          eapply Singleton_Included.
          eexists; split; eauto. now constructor; eauto.
          eapply Included_trans; [| eapply Fun_inv_dom2_funs; eassumption ].
          eapply env_locs_monotonic.
          eapply Singleton_Included.
          eexists; split; eauto. now constructor; eauto.
          
          eapply well_formed_antimon; [| eapply Fun_inv_reach2_funs; eassumption ].
          eapply reach'_set_monotonic. eapply env_locs_monotonic.
          eapply Singleton_Included.
          eexists; split; eauto. now constructor; eauto.
          eapply Included_trans; [| eapply Fun_inv_dom2_funs; eassumption ].
          eapply env_locs_monotonic.
          eapply Singleton_Included.
          eexists; split; eauto. now constructor; eauto.
          
        * eapply injective_subdomain_extend'. now firstorder.
          rewrite image_id.
          rewrite reach_unfold. rewrite Setminus_Union_distr.
          rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
          simpl. rewrite post_Singleton; [| erewrite gas; eauto ]. simpl.
          rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r.
          intros Hc. inv Hc.
          rewrite reach'_alloc in H; [| eassumption |].
          eapply reachable_in_dom in H. destruct H as [v' Hgetv'].
          eapply HL.alloc_subheap in Hgetv'; [| now apply Ha2 ]. 
          erewrite alloc_fresh in Hgetv'; eauto. congruence.

          eapply well_formed_antimon; [| eapply Fun_inv_reach2_funs; eassumption ]. 
          eapply reach'_set_monotonic.
          eapply Singleton_Included. eapply get_In_env_locs; eauto.
          eexists; split; eauto. now constructor; eauto. reflexivity. 
          
          eapply Included_trans; [| eapply Fun_inv_dom2_funs; eassumption ]. 
          eapply Singleton_Included. eapply get_In_env_locs; eauto.
          eexists; split; eauto. now constructor; eauto. reflexivity. 

          eapply Included_trans; [| eapply reach'_extensive ].
          simpl...
      + rewrite Combinators.compose_id_right. 
        rewrite compose_extend. rewrite extend_gss.
        eapply f_eq_subdomain_antimon.
        eapply Included_Union_Setminus with (s2 := [set l1']). 
        now tci.
        rewrite Union_commut. eapply f_eq_subdomain_extend. 
        symmetry. eapply compose_id_extend.
        
        
        rewrite reach_unfold, Setminus_Union_distr,
        Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
         
        assert (Hsub' : (post H1 (val_loc (Loc l1'))) \subset
                        reach' H1 (env_locs rho1 (Funs \\ Scope))).
        { rewrite (reach_unfold H1 (env_locs rho1 (Funs \\ Scope))).
          eapply Included_Union_preserv_r.
          eapply Included_trans; [| eapply reach'_extensive ].
          eapply post_set_monotonic.
          eapply get_In_env_locs. constructor; eauto. eassumption. }
        simpl. rewrite post_Singleton; [| eapply HL.alloc_subheap; eassumption ].
        simpl. rewrite Union_Empty_set_neut_l.
        
        assert (Henvj : forall j, (lenv, H1) << ^ (k; j; GI; GP; b) (B1, H2)). 
        { intros j'.
          edestruct (Hfun j') as (l1'' & lenv' & B1' & g1' & rhoc' & B2' & g2' & Hget1' & Hdis' (* & Hsub *)
                                   & Hget2' & Hget3' & Hget4' & Henv' & Heq');
            try eassumption. intros Hc'. eapply Hin. now right.
          repeat subst_exp. eassumption. }
        
        rewrite <- well_formed_reach_subheap_same; [| | | now eapply HL.alloc_subheap; eauto ] .
        intros Hc.

        eapply image_monotonic in Hc; [| eapply Setminus_Included ].

        rewrite cc_approx_clos_image_eq in Hc; [| try eassumption ].
        eapply reachable_in_dom in Hc.

        destruct Hc as [v1 Hgetv1]. erewrite alloc_fresh in Hgetv1. congruence.
        eassumption.
        eapply cc_approx_clos_well_formed_reac2. eassumption.
        eapply Singleton_Included. eapply cc_approx_clos_dom2. eassumption.
        eapply cc_approx_clos_well_formed_reach1. eassumption.
        eapply Singleton_Included. eapply cc_approx_clos_dom1. eassumption.
  Qed.
  
  Lemma Fun_inv_rename_ext k j GI GP b b' rho1 H1 rho2 H2 Funs Scope Γ FVs :
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs Γ FVs ->
    f_eq_subdomain (reach' H1 (env_locs rho1 (Funs \\ Scope))) b b' ->
    Fun_inv k j GI GP b' rho1 H1 rho2 H2 Scope Funs Γ FVs.
  Proof.
    intros Hfun Heq1 x Hin Hnin.
    edestruct Hfun
      as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *)
         & Hget2 & Hget3 & Hget4 & Henv & Heq);
      try eassumption.
    assert (Henv' := Henv). 
    destruct Henv as [Hbeq Henv]. subst.

    assert (Hbeq : b lenv = b' lenv). 
    { rewrite <- Heq1. reflexivity.
      eapply Included_post_reach'. eapply post_set_monotonic.
      eapply Singleton_Included. eexists. split. 
      now constructor; eauto. rewrite Hget1. reflexivity. 
      rewrite post_Singleton; [| eassumption ]. simpl. right. reflexivity. } 

    do 7 eexists; repeat split; try eassumption.
    
    - rewrite <- Heq1. eassumption.
      eapply Included_post_reach'. eapply post_set_monotonic.
      eapply Singleton_Included. eexists. split. 
      now constructor; eauto. rewrite Hget1. reflexivity. 
      rewrite post_Singleton; [| eassumption ]. simpl. right. reflexivity. 

    - eapply cc_approx_clos_rename_ext; try eassumption. 
      rewrite <- Hbeq. eassumption. 

      eapply f_eq_subdomain_antimon; [ | eassumption ].
      eapply Included_trans; [| eapply reach'_set_monotonic; eapply get_In_env_locs; try eassumption ]. 
      rewrite (reach_unfold H1 (val_loc (Loc l1))).
      eapply Included_Union_preserv_r. simpl. 
      rewrite post_Singleton; eauto.
      simpl. rewrite Union_Empty_set_neut_l. reflexivity.
      now constructor; eauto.

    - rewrite <- Hbeq in *. 
      destruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc (b lenv)]) H2) as [l2 H2'].
      

      assert (Hseq : l1 |: (reach' H1 (val_loc (Loc l1))) <--> reach' H1 (val_loc (Loc l1))).
      { split. eapply Union_Included. eapply Singleton_Included. eapply reach'_extensive.
        reflexivity. reflexivity.
        eapply Included_Union_preserv_r. reflexivity. }
      eapply cc_approx_val_rename_ext. eassumption.
      
      rewrite <- Hseq.  eapply f_eq_subdomain_extend. symmetry.
      eapply f_eq_subdomain_antimon; [ | eassumption ]. eapply reach'_set_monotonic.
      eapply get_In_env_locs. constructor; eauto. eassumption.
  Qed.
  

  Instance Proper_Fun_inv_Funs k j GI GP b rho1 H1 rho2 H2 Scope :
    Proper (Same_set _ ==> eq ==> eq ==> iff)
           (Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope). 
  Proof.
    intros S1 S2 Hseq x1 x2 Heq1 f1 f2 Heq3; subst.
    split; intros Hfv f Hin Hnin.
    - edestruct (Hfv f)
        as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *)
           & Hget2 & Hget3 & Hget4 & Henv & Heq);
      try eassumption.
      rewrite Hseq. eassumption.

      destruct Henv as [Hbeq Henv]. subst.
      
      do 7 eexists; repeat split; try eassumption.
      rewrite <- Hseq. eassumption.
      (* rewrite <- Hseq. eassumption. *)
    - edestruct (Hfv f)
        as (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *)
               & Hget2 & Hget3 & Hget4 & Henv & Heq);
      try eassumption.
      rewrite <- Hseq. eassumption.
      destruct Henv as [Hbeq Henv]. subst.

      do 7 eexists; repeat split; try eassumption.
      rewrite Hseq. eassumption.
      (* rewrite Hseq. eassumption. *)
  Qed.
  
  Instance Proper_Fun_inv_Scope k j GI GP b rho1 H1 rho2 H2 :
    Proper (Same_set _ ==> eq ==> eq ==> eq ==> iff)
           (Fun_inv k j GI GP b rho1 H1 rho2 H2). 
  Proof.
    intros S1 S2 Hseq x1 x2 Heq1 y1 y2 Heq2 f1 f2 Heq3; subst.
    split; intros Hfv f Hin Hnin. 
    - edestruct (Hfv f) as
          (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *) &
              Hget2 & Hget3 & Hget4 & Henv & Heq); try eassumption.
      rewrite Hseq. eassumption.
      
      destruct Henv as [Hbeq Henv]. subst.
      
      do 7 eexists; repeat split; try eassumption.
      rewrite <- Hseq. eassumption.
    - (* rewrite <- !Hseq at 1. eassumption. *)
      edestruct (Hfv f) as
          (l1 & lenv & B1 & g1 & rhoc & B2 & g2 & Hget1 & Hdis (* & Hsub *) &
              Hget2 & Hget3 & Hget4 & Henv & Heq); try eassumption.
      rewrite <- Hseq. eassumption.
      destruct Henv as [Hbeq Henv]. subst.

      do 7 eexists; repeat split; try eassumption.
      rewrite Hseq. eassumption.
      (* rewrite !Hseq at 1. eassumption. *)
  Qed.
  
  Lemma Fun_inv_locs_Disjoint1 k j GI GP b rho1 H1 rho2 H2 Funs Scope Γ FVs f :
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs Γ FVs ->
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

  Lemma Fun_inv_locs_Disjoint2 k j GI GP b rho1 H1 rho2 H2 Funs Scope Γ FVs :
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs Γ FVs ->
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
  
  Lemma Fun_inv_post_Included k j GI GP b rho1 H1 rho2 H2 Funs Scope Γ FVs :
    Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs Γ FVs ->
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

  Lemma FV_dom1 k P1 P2 rho1 H1 rho2 H2 b c
        Scope {Hs : ToMSet Scope} Funs Γ FVs fenv :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b) (H2, rho2)) ->
    (forall j, Fun_inv k j P1 P2 b rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
    (forall j, FV_inv k j P1 P2 b rho1 H1 rho2 H2 c Scope Funs fenv FVs) ->
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

  Lemma FV_dom2 k P1 P2 rho1 H1 rho2 H2 b c
        Scope {Hs : ToMSet Scope} Funs Γ FVs fenv :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b) (H2, rho2)) ->
    (forall j, Fun_inv k j P1 P2 b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    (forall j, FV_inv k j P1 P2 b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
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
  
  Lemma FV_reach1 k P1 P2 rho1 H1 rho2 H2 b c
        Scope {Hd : Decidable Scope} Funs Γ fenv FVs :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b) (H2, rho2)) ->
    (forall j, Fun_inv k j P1 P2 b rho1 H1 rho2 H2 Scope Funs Γ FVs) ->
    (forall j, FV_inv k j P1 P2 b rho1 H1 rho2 H2 c Scope Funs fenv FVs) ->
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

  Lemma FV_reach2 k P1 P2 rho1 H1 rho2 H2 b c
        Scope {Hd : Decidable Scope} Funs Γ fenv FVs :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; P1; P2; b) (H2, rho2)) ->
    (forall j, Fun_inv k j P1 P2 b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    (forall j, FV_inv k j P1 P2 b rho1 H1 rho2 H2 c Scope Funs Γ FVs) ->
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

    Lemma Fun_inv_subheap k j GI GP b rho1 H1 H1' rho2 H2 H2' Scope Funs fenv FVs :
    well_formed (reach' H1 (env_locs rho1 (FV Scope Funs FVs))) H1 ->
    env_locs rho1 (FV Scope Funs FVs) \subset dom H1 ->
    
    image b (reach' H1 (post H1 (env_locs rho1 (Funs \\ Scope)))) \subset dom H2 ->
    
    (forall j, Fun_inv k j GI GP b rho1 H1 rho2 H2 Scope Funs fenv FVs) ->
    H1 ⊑ H1' ->
    H2 ⊑ H2' ->
    Fun_inv k j GI GP b rho1 H1' rho2 H2' Scope Funs fenv FVs.
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
    - eapply Hsub1. eassumption.
    - destruct Henv as [Hbeq _]; subst. eassumption.
    - eapply cc_approx_clos_heap_monotonic; try eassumption.
      destruct Henv as [Hbeq _]; subst.
      intros j'.
      edestruct (Hfun j') as (l1' & lenv' & B1' & g1' & rhoc' & B2' & g2' & Hget1' & Hdis' (* & Hsub' *) & Hget2'
                             & Hget3' & Hget4' & Henv' & Heq');
        try eassumption.
      repeat subst_exp. eassumption.

    - destruct Henv as [Hbeq Henv]; subst. 
      destruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc (b lenv)]) H2)
        as [l2 H4] eqn:Ha.
      destruct (alloc (Constr Size.Util.clo_tag [FunPtr B2 g2; Loc (b lenv)]) H2')
        as [l2' H4'] eqn:Ha'.
      
      eapply cc_approx_val_rename_ext
      with (β' := ((id {l2 ~> l2'}) ∘ (b {l1 ~> l2}) ∘ id)).
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
          rewrite <- env_locs_Singleton with (v := Loc (b lenv)) in Hc1; try eassumption. 
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
        
        rewrite <- env_locs_Singleton with (v := Loc (b lenv)) in Hc1; try eassumption. 
        
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
        { eapply Him. 
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
        
  Qed.

End Invariants.
