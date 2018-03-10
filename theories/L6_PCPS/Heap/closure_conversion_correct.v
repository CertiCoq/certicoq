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
  
  Import H Size.Compat.LR.Sem.Equiv Size.Compat.LR.Sem.Equiv.Defs Size.Compat.LR.Sem Size.Compat.LR
         Size.Compat Size.
  
  Variable clo_tag : cTag.
  
  (** Invariant about the free variables *) 
  Definition FV_inv (k j : nat) (IP : GIInv) (P : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Γ : var) (FVs : list var) : Prop :=
    exists (v : value) (vs : list value) (l : loc),
      M.get Γ rho2 = Some (Loc l) /\
      get l H2 = Some (Constr c vs) /\
      Forall2 (fun x v' => 
                 exists v, M.get x rho1 = Some v /\
                      Res (v, H1) ≺ ^ ( k ; j ; IP ; P ; b) Res (v', H2)) FVs vs.
  
  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv (k j : nat) (IP : GIInv) (P : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) (σ : var -> var)  : Prop :=
    (* (exists f, f \in Funs) /\ *)
    forall (f : var),
     In var Funs f ->
      exists lf1 lf2,
        M.get f rho1 = Some lf1 /\ 
        M.get (σ f) rho2 = Some lf2 /\
        Res (lf1, H1) ≺ ^ ( k ; j ; IP ; P ; b) Res (lf2, H2).
  
  (** Versions without the logical relation. Useful when we're only interested in other invariants. *)
  
  (** Invariant about the free variables *) 
  Definition FV_inv_weak (rho1 : env) (rho2 : env) (H2 : heap block)
             (c : cTag) (Γ : var) (FVs : list var) : Prop :=
    exists (v : value) (vs : list value) (l : loc),
      M.get Γ rho2 = Some (Loc l) /\
      get l H2 = Some (Constr c vs) /\
      Forall2 (fun x v' => exists v, M.get x rho1 = Some v) FVs vs.
  
  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv_weak (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) (σ : var -> var) : Prop :=
    (* (exists f, f \in Funs \\ Scope) /\ *)
    forall (f : var),
      In var Funs f ->
      exists lf1 lf2,
        M.get f rho1 = Some lf1 /\ 
        M.get (σ f) rho2 = Some lf2.
  
  (** * Lemmas about [V_inv] *)

  Lemma FV_inv_image_post (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Γ FVs ->    
    image b ((post H1 ^ j) (env_locs rho1 (FromList FVs))) <-->
    (post H2 ^ j) (post H2 (env_locs rho2 ([set Γ]))).
  Proof.
    intros Hfv. destruct Hfv as (v & vs & l & Hget1 & Hget2 & Hall).
    rewrite (proper_post_n H2); [| now rewrite env_locs_Singleton; eauto; apply post_Singleton; eauto ].
    simpl. clear Hget1 Hget2. induction Hall.
    - simpl. rewrite post_n_Empty_set.
      eapply Same_set_trans; [| eapply image_Empty_set with (g := b) ].
      rewrite proper_post_n; [| rewrite FromList_nil, env_locs_Empty_set; reflexivity ].
      rewrite post_n_Empty_set. reflexivity.
    - rewrite proper_post_n; [| rewrite FromList_cons, env_locs_Union; reflexivity ].
      simpl. rewrite !post_n_Union, image_Union.
      eapply Same_set_Union_compat; [| now eauto ].
      destruct H as [v' [Hget' Hres]].
      rewrite proper_post_n; [| now eapply env_locs_Singleton; eauto ].
      eapply cc_approx_val_image_eq. eassumption.
  Qed.

  Lemma FV_inv_j_monotonic (k j' j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (c : cTag) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Γ FVs ->
    j' <= j ->
    FV_inv k j' GII GI b rho1 H1 rho2 H2 c Γ FVs.
  Proof.
    intros Hfv Hlt. 
    destruct Hfv as (v & vs & l & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_monotonic; [| eassumption ].
    intros x1 x2 [v' [Hget Hres]]. eexists; split; eauto.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.

    
  Lemma FV_inv_image_reach_n (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Γ : var) (FVs : list var) :
    FV_inv k j GII GI b rho1 H1 rho2 H2 c Γ FVs ->    
    image b (reach_n H1 j (env_locs rho1 (FromList FVs))) <-->
    (reach_n H2 j (post H2 (env_locs rho2 ([set Γ])))).
  Proof.
    intros Hfv. split.
    - intros l' [l [[m [Hm Hr]] Hin]].
      eapply FV_inv_j_monotonic in Hfv; eauto.
      eexists m. split; eauto. eapply FV_inv_image_post. eassumption.
      eexists; split; eauto.
    - intros l' [m [Hm Hr]].
      eapply FV_inv_j_monotonic in Hfv; eauto.
      eapply FV_inv_image_post in Hr; eauto.
      destruct Hr as [l [Heql Hin]]. eexists; split; eauto.
      eexists; split; eauto.
  Qed.

  Lemma FV_inv_image_reach (k : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (c : cTag) (Γ : var) (FVs : list var) :
    (forall j, FV_inv k j GII GI b rho1 H1 rho2 H2 c Γ FVs) ->    
    image b (reach' H1 (env_locs rho1 (FromList FVs))) <-->
    (reach' H2 (post H2 (env_locs rho2 ([set Γ])))).
  Proof.
    intros Hfv. split.
    - intros l' [l [[m [Hm Hr]] Heq]].
      eexists m. split; eauto. eapply FV_inv_image_post. eauto.
      eexists; split; eauto.
    - intros l' [m [Hm Hr]].
      eapply FV_inv_image_post in Hr; eauto.
      destruct Hr as [l [Heql Hin]]. eexists; split; eauto.
      eexists; split; eauto.
  Qed.

  (** * Lemmas about [FV_inv] *)
  Lemma FV_inv_weak_in_FV_inv k j P1 P2 rho1 H1 rho2 H2 β c Γ FVs :
    FV_inv k j P1 P2 β rho1 H1 rho2 H2 c Γ FVs ->
    FV_inv_weak rho1 rho2 H2 c Γ FVs.
  Proof.
    intros (x1 & x2 & l & Hget1 & Hget2 & Hall).
    repeat eexists; eauto.
    eapply Forall2_monotonic; [| eassumption ].
    now firstorder.
  Qed.

  (** * Lemmas about [Fun_inv] *)

  Lemma Fun_inv_image_post (k j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) (σ : var -> var) :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs σ ->
    image b ((post H1 ^ j) (env_locs rho1 Funs)) <-->
          (post H2 ^ j) (env_locs rho2 (image σ Funs)).
  Proof.
    intros Hfun. split.
    - intros l [l' [Hin Heq]]. subst.
      edestruct post_n_exists_Singleton as [l'' [Hpost' Hin']]; eauto.
      edestruct Hpost' as [f [Hinf Hgetf]].
      edestruct Hfun as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto. 
      rewrite Hget1 in Hgetf.
      eapply cc_approx_val_image_eq in Hrel.
      eapply post_n_set_monotonic.
      eapply env_locs_monotonic.
      eapply Singleton_Included. eexists; split; eauto.
      eapply post_n_set_monotonic. eapply env_locs_Singleton; eauto.
      eapply Hrel. eexists; split;  eauto.
      eapply post_n_set_monotonic; eauto. eapply Singleton_Included. eassumption.
    - intros l Hpost.
      edestruct post_n_exists_Singleton as [l'' [Hpost' Hin']]; eauto.
      edestruct Hpost' as [f' [[f'' [Hinf' Heq]] Hgetf]]; subst.
      edestruct Hfun as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
      eapply cc_approx_val_image_eq in Hrel.
      rewrite Hget2 in Hgetf. destruct lf2; inv Hgetf. eapply Hrel in Hin'.
      eapply image_monotonic; eauto.
      eapply post_n_set_monotonic. eexists; split; eauto.
      rewrite Hget1; eauto.
  Qed.

  Lemma Fun_inv_j_monotonic (k j' j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (Scope Funs : Ensemble var) (σ : var -> var) :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs σ  ->
    j' <= j ->
    Fun_inv k j' GII GI b rho1 H1 rho2 H2 Scope Funs σ .
  Proof.
    intros Hfv Hlt f Hin'.
    edestruct Hfv as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
    repeat eexists; eauto.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.

  Lemma Fun_inv_set_not_in_Funs_r (k  j : nat) (GII : GIInv) (GI : GInv) (b : Inj)
        (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
        (Scope Funs : Ensemble var) (σ : var -> var) x v :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs σ  ->
    ~ x \in (image σ Funs) ->
    Fun_inv k j GII GI b rho1 H1 (M.set x v rho2) H2 Scope Funs σ .
  Proof.
    intros Hfv Hlt f Hin'.
    edestruct Hfv as (lf1 & lf2 & Hget1 & Hget2 & Hrel); eauto.
    repeat eexists; eauto.
    rewrite M.gso; eauto. intros Hc; inv Hc; eauto.
    eapply Hlt; eexists; split; eauto.
  Qed.
  
  Lemma Fun_inv_image_reach (k : nat) (GII : GIInv) (GI : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) (σ : var -> var) :
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs σ) ->
    image b (reach' H1 (env_locs rho1 Funs)) <-->
    reach' H2 (env_locs rho2 (image σ Funs)).
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
        (Scope Funs : Ensemble var) (σ : var -> var) :
    Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs σ ->
    image b (reach_n H1 j (env_locs rho1 Funs)) <-->
    (reach_n H2 j) (env_locs rho2 (image σ Funs)).
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

  Lemma Fun_inv_weak_in_Fun_inv k j P1 P2 rho1 H1 rho2 H2 β Scope Funs σ :
    Fun_inv k j P1 P2 β rho1 H1 rho2 H2 Scope Funs σ  ->
    Fun_inv_weak rho1 H1 rho2 H2 Scope Funs σ.
  Proof.
    now firstorder. 
  Qed.


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
    project_var Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    ctx_to_heap_env C1 H1 rho1 H2 rho2 m ->
    ~ In _ S1 y ->
    M.get y rho1 = M.get y rho2. 
  Proof.
    intros Hvar Hctx Hin. inv Hvar.
    - inv Hctx. reflexivity.
    - inv Hctx. reflexivity.
    - inv Hctx. inv H19.
      destruct (var_dec y x'); subst.
      contradiction.
      now rewrite M.gso.
  Qed.    
  
  Lemma project_vars_get Scope Funs σ c Γ FVs S1 xs xs' C1 S2 rho1 H1 rho2 H2 m y:
    project_vars Scope Funs σ c Γ FVs S1 xs xs' C1 S2 ->
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
    project_var Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
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
    project_vars Scope Funs σ c Γ FVs S1 xs xs' C1 S2 ->
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
  
  Lemma project_var_ctx_to_heap_env Scope Funs σ c Γ FVs x x' C S S' v1 rho1 rho2 H1 H2:
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    Fun_inv_weak rho1 H1 rho2 H2 Scope Funs σ  ->
    FV_inv_weak rho1 rho2 H2 c Γ FVs ->
    M.get x rho1 = Some v1 ->
    exists H2' rho2' s, ctx_to_heap_env C H2 rho2 H2' rho2' s.
  Proof.
    intros Hproj HFun HFV Hget. inv Hproj.
    - repeat eexists; econstructor; eauto.
    - edestruct HFun as
          (vf1 & vf4 & Hget1 & Hget2) ; eauto.
      repeat eexists; constructor; eauto.
    - edestruct HFV as (v & vs & l & Hget1 & Hget2 & Hall).
      edestruct (Forall2_nthN _ FVs vs N x Hall) as [v' [Hnth [v'' Hget'']]]; eauto.
      repeat eexists. econstructor; eauto. constructor. 
  Qed.
  
  Lemma project_vars_ctx_to_heap_env Scope Funs σ c Γ FVs xs xs' C S S' vs1 rho1 H1 rho2 H2:
    Disjoint _ S (Union var Scope
                        (Union var (image σ Funs)
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
    
    project_vars Scope Funs σ c Γ FVs S xs xs' C S' ->
    Fun_inv_weak rho1 H1 rho2 H2 Scope Funs σ ->
    FV_inv_weak rho1 rho2 H2 c Γ FVs ->
    getlist xs rho1 = Some vs1 ->
    exists H2' rho2' s, ctx_to_heap_env C H2 rho2 H2' rho2' s.
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
      + intros f Hin.
        edestruct HFun as (vf1 & vf2 & Hgetf1 & Hgetf2); try eassumption.
        repeat eexists; eauto.
        erewrite <- project_var_get; try eassumption.
        intros Hin'. eapply HD. constructor. now eauto.
        right. left. eexists. split; eauto.
      + edestruct HFV as [v' [vs [l' [Hget [Hget1 Hall]]]]]; eauto.
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
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    env_locs rho (occurs_free (C |[ e ]|)) \subset dom H ->
    env_locs rho' (occurs_free e) \subset dom  H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl in *; eauto.
    - simpl in *; eauto.
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
  
  Lemma project_var_env_locs' Scope Funs σ c Γ FVs x x' C S S' k rho H rho' H':
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    well_formed (reach' H (env_locs rho (Scope :|: (image σ Funs) :|: [set Γ]))) H ->
    env_locs rho (Scope :|: (image σ Funs) :|: [set Γ]) \subset dom H ->
    env_locs rho' (x' |: Scope :|: (image σ Funs) :|: [set Γ]) \subset dom  H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - rewrite (Union_Same_set [set x']). eassumption.
      eapply Singleton_Included; eauto.
    - rewrite (Union_commut [set (σ x)]).
      rewrite <- (Union_assoc Scope). rewrite (Union_Same_set [set _]). eassumption.
      eapply Singleton_Included; eauto. eexists; split; eauto.
    - inv H18.
      eapply Included_trans. eapply env_locs_set_Inlcuded'.
      simpl. eapply Union_Included.
      + eapply Included_trans; [| eapply reachable_in_dom; eauto ].
        rewrite !env_locs_Union, !reach'_Union.
        eapply Included_Union_preserv_r. 
        erewrite (reach_unfold H' (env_locs rho ([set _ ]))).
        eapply Included_Union_preserv_r. 
        eapply Included_trans; [| eapply reach'_extensive ].
        rewrite env_locs_Singleton; eauto.
        simpl. rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
      + eapply Included_trans; [| eassumption ]. simpl.
        eapply env_locs_monotonic. now eauto 20 with Ensembles_DB.
  Qed.

  (** [project_var] preserves well-formedness *)
  Lemma project_var_well_formed Scope Funs σ c Γ FVs x x' C S S' e k rho H rho' H':
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    (env_locs rho (occurs_free (C |[ e ]|))) \subset dom H ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    well_formed (reach' H' (env_locs rho' (occurs_free e))) H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl; eauto.
    - simpl; eauto.
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

  Lemma project_var_reachable Scope Funs σ c Γ FVs x x' C S S' e k rho H rho' H':
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    reach' H' (env_locs rho' (occurs_free e)) \subset
           reach' H (env_locs rho (occurs_free (C |[ e ]|))).
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx. inv Hvar; inv Hctx; try reflexivity.
    - simpl. normalize_occurs_free. inv H18.
      eapply Included_trans.
      eapply reach'_set_monotonic. eapply env_locs_set_Inlcuded'. 
      rewrite !env_locs_Union, !reach'_Union, env_locs_Singleton; eauto.
      eapply Included_Union_compat; try reflexivity.
      rewrite (reach_unfold H' (val_loc (Loc l))).
      eapply Included_Union_preserv_r. 
      eapply reach'_set_monotonic.
      simpl. rewrite post_Singleton; eauto.
      simpl. eapply In_Union_list. eapply in_map.
      eapply nthN_In. eassumption.
  Qed.

  Lemma project_vars_reachable Scope Funs σ c Γ FVs xs xs' C S S' e k rho H rho' H':
    project_vars Scope Funs σ c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    reach' H' (env_locs rho' (occurs_free e)) \subset
           reach' H (env_locs rho (occurs_free (C |[ e ]|))).
  Proof with (now eauto with Ensembles_DB).
    intros Hvar. revert rho H rho' H' k e. 
    induction Hvar; intros rho1 H1 rho2 H2 k e Hctx.
    - inv Hctx. reflexivity.
    - edestruct ctx_to_heap_env_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      eapply Included_trans. eapply IHHvar; eauto.
      eapply Included_trans. eapply project_var_reachable; eauto.
      rewrite app_ctx_f_fuse. reflexivity. 
  Qed.

  (** [project_var] preserves well-formedness *)
  Lemma project_var_well_formed' Scope Funs σ c Γ FVs x x' C S S' k rho H rho' H':
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    (env_locs rho (Scope :|: (image σ Funs) :|: [set Γ])) \subset dom H ->
    well_formed (reach' H (env_locs rho (Scope :|: (image σ Funs) :|: [set Γ]))) H ->
    well_formed (reach' H' (env_locs rho' (x' |: Scope :|: (image σ Funs) :|: [set Γ]))) H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx Hlocs Hwf. inv Hvar; inv Hctx.
    - simpl; eauto. rewrite (Union_Same_set [set x']). eassumption.
      eapply Singleton_Included...
    - rewrite (Union_commut [set (σ x)]).
      rewrite <- (Union_assoc Scope). rewrite (Union_Same_set [set _]). eassumption.
      eapply Singleton_Included; eauto. eexists; split; eauto.
    - inv H18.
      eapply well_formed_antimon; [| eapply well_formed_reach_set; try eassumption ].
      + eapply reach'_set_monotonic. eapply env_locs_monotonic.
        now eauto 20 with Ensembles_DB.
      + simpl. eapply well_formed_antimon; try eassumption.
        rewrite !env_locs_Union, !reach'_Union.
        eapply Included_Union_preserv_r. 
        erewrite (reach_unfold H' (env_locs rho ([set _ ]))).
        eapply Included_Union_preserv_r. 
        eapply reach'_set_monotonic.
        rewrite env_locs_Singleton; eauto.
        simpl. rewrite post_Singleton; eauto.
        simpl. eapply In_Union_list. eapply in_map.
        eapply nthN_In. eassumption.
  Qed.

  Lemma project_var_env_locs_subset Scope Funs σ c Γ FVs xs xs' C S S' S1 k rho H rho' H':
    project_var Scope Funs σ c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    Disjoint _ S1 S ->
    env_locs rho' S1 <--> env_locs rho S1.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar Hctx HD. destruct Hvar; inv Hctx; try reflexivity.
    - inv H18. rewrite env_locs_set_not_In. reflexivity. 
      intros Hc; eapply HD; eauto.
  Qed.

   Lemma project_vars_env_locs_subset Scope Funs σ c Γ FVs xs xs' C S S' S1 k rho H rho' H':
    project_vars Scope Funs σ c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    Disjoint _ S1 S ->
    env_locs rho' S1 <--> env_locs rho S1.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho H rho' H' k. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx Hd.
    - inv Hctx. reflexivity.
    - edestruct ctx_to_heap_env_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst. rewrite IHHvar; eauto.
      rewrite project_var_env_locs_subset; eauto.
      reflexivity. eapply Disjoint_Included_r; try eassumption.
      eapply project_var_free_set_Included; eauto.
  Qed.

  Lemma project_var_not_In_free_set' Scope Funs σ c Γ FVs x x' C S S'  :
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    Disjoint _ S (Scope :|: (image σ Funs)) ->
    ~ In _ S' x'.
  Proof.
    intros Hproj Hd. inv Hproj; intros Hc.
    - eapply Hd. eauto.
    - eapply Hd; eauto. constructor; eauto. right.
      eexists; eauto.
    - inv Hc. exfalso. eauto.    
  Qed.

  Lemma project_var_heap Scope Funs σ c Γ FVs x x' S S' C H rho H' rho' k :
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    H = H'. 
  Proof.
    intros Hvar Hctx; inv Hvar; inv Hctx; eauto.
    inv H18; eauto.
  Qed.

  Lemma project_vars_heap Scope Funs σ c Γ FVs x x' S S' C H rho H' rho' k :
    project_vars Scope Funs σ c Γ FVs S x x' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    H = H'. 
  Proof.
    intros Hvar. revert rho H rho' H' k. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx.
    - inv Hctx; eauto.
    - edestruct ctx_to_heap_env_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      eapply project_var_heap in Hctx2; eauto.
      subst. eapply IHHvar; eauto.
  Qed.

  Lemma project_vars_env_locs Scope Funs σ c Γ FVs xs xs' C S S' e k rho H rho' H':
    project_vars Scope Funs σ c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    (env_locs rho (occurs_free (C |[ e ]|))) \subset dom H ->
    well_formed (reach' H (env_locs rho (occurs_free (C |[ e ]|)))) H ->
    (env_locs rho' (occurs_free e)) \subset dom H'.
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
    
  Lemma project_vars_env_locs' Scope Funs σ c Γ FVs xs xs' C S S' k rho H rho' H':
    project_vars Scope Funs σ c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    Disjoint _ S (Scope :|: (image σ Funs)) ->
    well_formed (reach' H (env_locs rho (Scope :|: (image σ Funs) :|: [set Γ]))) H ->
    env_locs rho (Scope :|: (image σ Funs) :|: [set Γ]) \subset dom H ->
    env_locs rho' (FromList xs' :|: Scope :|: (image σ Funs) :|: [set Γ]) \subset dom  H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho H rho' H' k. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx Hd Hlocs Hwf.
    - inv Hctx. rewrite FromList_nil, Union_Empty_set_neut_l. simpl in *; eauto.
    - edestruct ctx_to_heap_env_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      rewrite FromList_cons.
      rewrite <- !Union_assoc. rewrite env_locs_Union.
      eapply Union_Included.
      erewrite <- project_vars_heap with (H := H3) (H' := H2); eauto .
      eapply project_vars_env_locs_subset in Hvar; eauto.
      rewrite Hvar. eapply Included_trans; [| eapply project_var_env_locs'; eauto ].
      eapply env_locs_monotonic...
      eapply Disjoint_Singleton_l. eapply project_var_not_In_free_set'. eassumption.
      eapply Disjoint_Included_r; [| eassumption ]...
      rewrite !Union_assoc. eapply IHHvar; eauto.
      eapply Disjoint_Included_l. eapply project_var_free_set_Included. eassumption.
      eassumption.
      eapply well_formed_antimon; [| eapply project_var_well_formed'; eauto ].
      eapply reach'_set_monotonic. eapply env_locs_monotonic...
      eapply Included_trans; [| eapply project_var_env_locs'; eauto ].
      eapply env_locs_monotonic...
  Qed.
  
  Lemma project_vars_well_formed Scope Funs σ c Γ FVs xs xs' C S S' e k rho H rho' H':
    project_vars Scope Funs σ c Γ FVs S xs xs' C S' ->
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
  
  Lemma project_vars_well_formed' Scope Funs σ c Γ FVs xs xs' C S S' k rho H rho' H':
    project_vars Scope Funs σ c Γ FVs S xs xs' C S' ->
    ctx_to_heap_env C H rho H' rho' k ->
    Disjoint _ S (Scope :|: (image σ Funs)) ->
    (env_locs rho (Scope :|: (image σ Funs) :|: [set Γ])) \subset dom H ->
    well_formed (reach' H (env_locs rho (Scope :|: (image σ Funs) :|: [set Γ]))) H ->
    well_formed (reach' H' (env_locs rho' (FromList xs' :|: Scope :|: (image σ Funs) :|: [set Γ]))) H'.
  Proof with (now eauto with Ensembles_DB). 
    intros Hvar. revert rho H rho' H' k. 
    induction Hvar; intros rho1 H1 rho2 H2 k Hctx HD Hlocs Hwf.
    - inv Hctx. simpl in *; eauto.
      rewrite FromList_nil, Union_Empty_set_neut_l. simpl in *; eauto.
    - edestruct ctx_to_heap_env_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      eassumption. subst.
      rewrite FromList_cons.
      rewrite <- !Union_assoc. rewrite env_locs_Union, reach'_Union.
      eapply well_formed_Union.
      erewrite <- project_vars_heap with (H := H3) (H' := H2); eauto .
      eapply project_vars_env_locs_subset in Hvar; eauto.
      rewrite Hvar.
      eapply well_formed_antimon; [| eapply project_var_well_formed' ]; eauto.
      eapply reach'_set_monotonic. eapply env_locs_monotonic...
      eapply Disjoint_Singleton_l. eapply project_var_not_In_free_set'.
      eassumption.
      eapply Disjoint_Included_r; [| eassumption ]...
      rewrite !Union_assoc. eapply IHHvar; eauto.
      eapply Disjoint_Included_l. eapply project_var_free_set_Included. eassumption.
      eassumption.
      eapply Included_trans; [| eapply project_var_env_locs'; eauto ].
      eapply env_locs_monotonic...
      eapply well_formed_antimon; [| eapply project_var_well_formed'; eauto ].
      eapply reach'_set_monotonic. eapply env_locs_monotonic...
  Qed.

  (** TODO move *)

  Lemma cc_approx_val_image_reach_eq GIP GP (k : nat) (β : Inj)  (H1 H2 : heap block)
        (v1 v2 : value) :
    (forall j, (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β) (Res (v2, H2))) ->
    image β (reach' H1 (val_loc v1)) <--> (reach' H2 (val_loc v2)).
  Proof.
    intros Hres. split.
    - intros l' [l [[m [Hm Hr]] Hin]].
      eapply cc_approx_val_image_eq in Hres. eexists m.
      split; eauto. eapply Hres. eexists. split; eauto.
    - intros l' [m [Hm Hr]].
      eapply cc_approx_val_image_eq in Hres. eapply Hres in Hr.
      destruct Hr as [l [Heql Hin]]. eexists; split; eauto.
      eexists; split; eauto.
  Qed.
  
  Lemma cc_approx_env_image_reach_eq GIP GP
        (k : nat) (β : Inj)
        (H1 H2 : heap block) (rho1 rho2 : env) (x y : var) (v : value) :
    (forall j, cc_approx_var_env k j GIP GP β H1 rho1 H2 rho2 x y) ->
    M.get x rho1 = Some v -> 
    image β (reach' H1 (env_locs rho1 [set x])) <-->
    reach' H2 (env_locs rho2 [set y]).
  Proof.
    intros Hcc Hget.
    edestruct (Hcc 0) as [v' [Hget' Hv]]; eauto.
    rewrite !env_locs_Singleton; eauto. 
    rewrite cc_approx_val_image_reach_eq. reflexivity.
    intros j; eauto.
    edestruct (Hcc j) as [v'' [Hget'' Hv']]; eauto.
    repeat subst_exp. eassumption.
  Qed.

  Lemma cc_approx_env_image_eq GIP GP S (k j : nat) (β : Inj)
        (H1 H2 : heap block) (rho1 rho2 : env) :
    (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; β) (H2, rho2) ->
    binding_in_map S rho1 ->
    image β ((post H1 ^ j) (env_locs rho1 S)) <--> (post H2 ^ j) (env_locs rho2 S).
  Proof.
    intros Henv Hbin. split.
    - intros l1 [l2 [Hin Hbeq]].
      edestruct post_n_exists_Singleton as [l' [Henv' Hp]]. eassumption.
      destruct Henv' as [x [Hgetx Hinx]].
      destruct (M.get x rho1) eqn:Hget1; try now inv Hinx.
      destruct v; inv Hinx; try contradiction.
      assert (Hget2 := Hget1).
      eapply cc_approx_var_env_image_eq in Hget1; eauto.
      eapply post_n_set_monotonic; [| eapply Hget1 ].
      eapply env_locs_monotonic. now eapply Singleton_Included; eauto.
      eexists; split; eauto.
      eapply proper_post_n. eapply env_locs_Singleton. now eauto.
      eassumption. 
    - intros l Hp.
      edestruct post_n_exists_Singleton as [l' [Henv' Hp']]. eassumption.
      destruct Henv' as [x [Hgetx Hinx]].
      destruct (M.get x rho2) eqn:Hget1; try now inv Hinx.
      destruct v; inv Hinx; try contradiction.
      eapply image_monotonic. eapply post_n_set_monotonic.
      eapply env_locs_monotonic. eapply Singleton_Included. eassumption.
      edestruct Hbin as [v Hget]; eauto.
      edestruct Henv as [l'' [Hget' Hres]]; eauto. 
      eapply cc_approx_var_env_image_eq; eauto.
      eapply proper_post_n. now eapply env_locs_Singleton; eauto.
      subst_exp. eassumption.
  Qed.

  Lemma cc_approx_env_image_reach_n GIP GP S (k j : nat) (β : Inj)
        (H1 H2 : heap block) (rho1 rho2 : env) :
    (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; β) (H2, rho2) ->
    binding_in_map S rho1 ->
    image β ((reach_n H1 j) (env_locs rho1 S)) <--> (reach_n H2 j) (env_locs rho2 S).
  Proof.
    intros Hres HB. split.
    - intros l' [l [[m [Hm Hr]] Hin]].
      eapply cc_approx_env_P_j_monotonic in Hres; eauto. 
      eapply cc_approx_env_image_eq in Hres. eexists m.
      split; eauto. eapply Hres. eexists. split; eauto.
      eassumption.
    - intros l' [m [Hm Hr]].
      eapply cc_approx_env_P_j_monotonic in Hres; eauto. 
      eapply cc_approx_env_image_eq in Hres. eapply Hres in Hr.
      destruct Hr as [l [Heql Hin]]. eexists; split; eauto.
      eexists; split; eauto. eassumption.
  Qed.

  Lemma cc_approx_env_image_reach GIP GP S (k : nat) (β : Inj)
        (H1 H2 : heap block) (rho1 rho2 : env) :
    (forall j, (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; β) (H2, rho2)) ->
    binding_in_map S rho1 ->
    image β (reach' H1 (env_locs rho1 S)) <--> reach' H2 (env_locs rho2 S).
  Proof.
    intros Hres HB. split.
    - intros l' [l [[m [Hm Hr]] Hin]].
      eapply cc_approx_env_P_j_monotonic in Hres; eauto. 
      eapply cc_approx_env_image_eq in Hres. eexists m.
      split; eauto. eapply Hres. eexists. split; eauto.
      eassumption.
    - intros l' [m [Hm Hr]].
      eapply cc_approx_env_P_j_monotonic in Hres; eauto. 
      eapply cc_approx_env_image_eq in Hres. eapply Hres in Hr.
      destruct Hr as [l [Heql Hin]]. eexists; split; eauto.
      eexists; split; eauto. eassumption.
  Qed.

  (* TODO move *)

  Lemma cc_approx_var_env_set_neq_r GIP GP b :
    forall (k j : nat)  (rho1 rho2 : env) (H1 H2 : heap block)
      (y1 x2 y2 : var) ( v2 : value),
      cc_approx_var_env k j GIP GP b H1 rho1 H2 rho2 y1 y2 ->
      y2 <> x2 ->
      cc_approx_var_env k j GIP GP b H1 rho1 H2 (M.set x2 v2 rho2) y1 y2.
  Proof. 
    intros k j rho1 rho2 H1 H2 x2 y1 y2 v2 Hval Hneq x' Hget.
    rewrite M.gso in *; eauto.
  Qed.


  Lemma project_var_preserves_cc_approx GII GI k j H1 rho1 H2 rho2 H2' rho2' b
        Scope Funs σ c Γ FVs x x' C S S' m y y' :
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    cc_approx_var_env k j GII GI b H1 rho1 H2 rho2 y y' ->
    ctx_to_heap_env C H2 rho2 H2' rho2' m ->
    ~ y' \in S ->
    cc_approx_var_env k j GII GI b H1 rho1 H2' rho2' y y'.
  Proof.     
    intros Hproj Hcc Hctx Hnin.
    destruct Hproj; inv Hctx; eauto.
    - inv H19. eapply cc_approx_var_env_set_neq_r; eauto.
      intros Hc; subst; eauto.
  Qed.

  Lemma project_vars_preserves_cc_approx GII GI k j H1 rho1 H2 rho2 H2' rho2' b
        Scope Funs σ c Γ FVs xs xs' C S S' m y y' :
    project_vars Scope Funs σ c Γ FVs S xs xs' C S' ->
    cc_approx_var_env k j GII GI b H1 rho1 H2 rho2 y y' ->
    ctx_to_heap_env C H2 rho2 H2' rho2' m ->
    ~ y' \in S ->
    cc_approx_var_env k j GII GI b H1 rho1 H2' rho2' y y'.
  Proof.     
    intros Hvars. revert m H1 rho1 H2 rho2 H2' rho2'.
    induction Hvars; intros m H1 rho1 H2 rho2 H2' rho2' Hcc Hctx Hnin.
    - inv Hctx. eassumption.
    - edestruct ctx_to_heap_env_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]]; eauto.
      subst.
      eapply IHHvars; [| eassumption | ].
      eapply project_var_preserves_cc_approx; try eassumption.
      intros Hc.
      eapply Hnin. eapply project_var_free_set_Included; eauto.
  Qed.  

  (** Correctness of [project_var] *)
  Lemma project_var_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b
        Scope Funs σ c Γ FVs x x' C S S' m :
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b) (H2, rho2)) ->
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs σ) ->
    (forall j, FV_inv k j GII GI b rho1 H1 rho2 H2 c Γ FVs) ->

    ctx_to_heap_env C H2 rho2 H2' rho2' m ->

    injective_subdomain (reach' H1 (env_locs rho1 (Scope :|: FromList FVs :|: Funs))) b ->
    
    binding_in_map Scope rho1 ->
    Disjoint _ S (Scope :|: (image σ Funs) :|: (FromList FVs) :|: [set Γ]) ->

    ~ In _ S' x' /\
    injective_subdomain (reach' H1 (env_locs rho1 (x |: Scope :|: FromList FVs :|: Funs))) b /\
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b) (H2', rho2'))  /\
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2' H2' Scope Funs σ) /\
    (forall j, FV_inv k j GII GI b rho1 H1 rho2' H2' c Γ FVs) /\
    (forall j, cc_approx_var_env k j GII GI b H1 rho1 H2' rho2' x x').
  Proof with (now eauto with Ensembles_DB).
    intros Hproj Hcc Hfun Henv Hctx Hinj Hbin Hd.
    inv Hproj.
    - inv Hctx. split. intros Hc. eapply Hd; eauto.
      split; [| split; [| split ; [| split ]]]; eauto.
      rewrite (Union_Same_set [set x'])... intros j; eapply Hcc. eassumption.
    - inv Hctx.
      split; [| split; [| split; [| split; [| split ]]]]. repeat split.
      + intros Hc. eapply Hd. constructor; eauto.
        left. left. right. eexists; split; eauto.
      + rewrite <- !Union_assoc, (Union_commut [set x]), <- !Union_assoc, (Union_commut _ [set x]).
        rewrite (Union_Same_set [set x]). rewrite !Union_assoc.  eassumption.
        eapply Singleton_Included; eauto.
      + intros j. eapply Hcc; eauto.
      + eassumption.
      + eassumption.
      + intros j. edestruct (Hfun j) as (vf1 & vf2 & Hget1 & Hget2 & Hcc'); eauto.
        intros v1 Hget1'. repeat subst_exp. eexists; split; eauto.
    - inv Hctx. inv H19.
      split; [| split; [| split; [| split; [| split ]]]]. repeat split.
      + intros Hc. inv Hc. eauto.
      + rewrite (Union_commut [set x]), <- (Union_assoc _ _ (FromList FVs)).
        rewrite (Union_Same_set [set x]). eassumption.
        eapply Singleton_Included; eauto. eapply nthN_In; eauto.
      + intros j. eapply cc_approx_env_P_set_not_in_P_r. now eauto.
        intros Hc. eapply Hd; eauto.
      + intros j. eapply Fun_inv_set_not_in_Funs_r; eauto.
        intros Hc; eapply Hd. constructor; eauto.
      + intros h. 
        edestruct Henv as (v1 & vs1 & l' & Hget1 & Hget2 & Hall).
        repeat eexists; eauto. 
        rewrite M.gso; eauto. intros Heq; subst. eapply Hd. constructor; eauto.
      + intros j v' Hget.
        edestruct (Henv j) as (v1 & vs1 & l' & Hget1 & Hget2 & Hall).
        eexists. rewrite M.gss. split. reflexivity.
        edestruct (Forall2_nthN _ FVs vs1 N _ Hall H3) as (v2 & Hnth' & vs4 & Hget4 & Hrel).
        repeat subst_exp. eassumption.
  Qed.

  Lemma project_var_setminus_same  Scope Funs σ c Γ FVs x x' C S S' : 
    project_var Scope Funs σ c Γ FVs S x x' C S' ->
    project_var Scope (Funs \\ Scope) σ c Γ FVs S x x' C S'.
  Proof. 
    intros Hvar; destruct Hvar; try now constructor; eauto.
    constructor; eauto. intros Hc; inv Hc; eauto.
  Qed.

  Lemma project_vars_setminus_same  Scope Funs σ c Γ FVs xs xs' C S S' : 
    project_vars Scope Funs σ c Γ FVs S xs xs' C S' ->
    project_vars Scope (Funs \\ Scope) σ c Γ FVs S xs xs' C S'.
  Proof. 
    intros Hvar; induction Hvar; try now constructor; eauto.
    econstructor; eauto. eapply project_var_setminus_same. eassumption.
  Qed.

  (** Correctness of [project_vars] *)
  Lemma project_vars_correct GII GI k  H1 rho1 H2 rho2 H2' rho2' b
        Scope Funs σ c Γ FVs xs xs' C S S' m :
    project_vars Scope Funs σ c Γ FVs S xs xs' C S' ->
    
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b) (H2, rho2)) ->
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2 H2 Scope Funs σ) ->
    (forall j, FV_inv k j GII GI b rho1 H1 rho2 H2 c Γ FVs) ->

    ctx_to_heap_env C H2 rho2 H2' rho2' m ->

    injective_subdomain (reach' H1 (env_locs rho1 (Scope :|: FromList FVs :|: Funs))) b ->
    
    binding_in_map Scope rho1 -> 
    Disjoint _ S (Scope :|: (image σ Funs) :|: (FromList FVs) :|: [set Γ]) ->

    Disjoint _ (FromList xs') S' /\
    injective_subdomain (reach' H1 (env_locs rho1 ((FromList xs) :|: Scope :|: FromList FVs :|: Funs))) b /\
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GII; GI; b) (H2', rho2'))  /\
    (forall j, Fun_inv k j GII GI b rho1 H1 rho2' H2' Scope Funs σ) /\
    (forall j, FV_inv k j GII GI b rho1 H1 rho2' H2' c Γ FVs) /\
    (forall j, Forall2 (fun x x' => cc_approx_var_env k j GII GI b H1 rho1 H2' rho2' x x') xs xs').
  Proof with (now eauto with Ensembles_DB).
    intros Hvars. revert m H1 rho1 H2 rho2 H2' rho2'.
    induction Hvars; intros m H1 rho1 H2 rho2 H2' rho2' Hcc Hfun Hfv Hctx Hinj Hb Hd. 
    - inv Hctx. split; [| split; [| split ; [| split ]]]; eauto.
      rewrite FromList_nil...
      rewrite FromList_nil. rewrite Union_Empty_set_neut_l...
    - rewrite FromList_cons in *. 
      edestruct ctx_to_heap_env_comp_ctx_f_l as [rho3 [H3 [m1 [m2 [Hctx2 [Hctx3 Heq]]]]]].
      subst.
      eassumption. subst.
      edestruct project_var_correct as (Hd' & Hinj' & Hcc' & Hfun' & Hfv' & Hall');
        try eassumption.
      edestruct IHHvars as (Hd'' & Hinj'' & Hcc'' & Hfun'' & Hfv'' & Hall'');
      try eassumption.
      eapply Disjoint_Included_l; [| eassumption ].
      eapply project_var_free_set_Included. eassumption.
      split; [| split; [| split ; [| split; [| split ] ]]]; eauto.
      * eapply Union_Disjoint_l. 
        eapply Disjoint_Included_r.
        eapply project_vars_free_set_Included. eassumption.
        eapply Disjoint_Singleton_l.
        eapply project_var_not_In_free_set. eassumption.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite <- !Union_assoc. eapply Included_Union_compat. reflexivity.
        eapply Included_Union_compat. eapply image_monotonic...
        reflexivity.        
        eapply Disjoint_sym. eapply project_vars_not_In_free_set. eassumption.
        eapply Disjoint_Included_l.
        eapply project_var_free_set_Included. eassumption.
        eapply Disjoint_Included_r; [| eassumption ].
        rewrite <- !Union_assoc. eapply Included_Union_compat. reflexivity.
        eapply Included_Union_compat. eapply image_monotonic...
        reflexivity.
      * eapply injective_subdomain_antimon. now apply Hinj.
        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        rewrite FromList_cons. rewrite <- !Union_assoc. eapply Union_Included.
        eapply Singleton_Included. rewrite (Union_commut (FromList FVs)).
        eapply project_var_In_Union. eassumption.
        eapply Union_Included.  rewrite (Union_commut (FromList FVs)).
        eapply project_vars_In_Union. eassumption.
        now eauto with Ensembles_DB.
      * intros j. constructor; eauto .
        eapply project_vars_preserves_cc_approx; eauto.
  Qed.
  

  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct (k : nat) (H1 H2 : heap block)
        (rho1 rho2 : env) (e1 e2 : exp) (C : exp_ctx)
        (Scope Funs : Ensemble var) (FVs : list var)
        (σ : var -> var) (β : Inj) (c : cTag) (Γ : var) :
    (* [Scope] invariant *)
    (forall j, (H1, rho1) ⋞ ^ (Scope ; k ; j ; Pre Hole_c ; Post 0 ; β) (H2, rho2)) ->
    (* [Fun] invariant *)
    (forall j, Fun_inv k j (Pre Hole_c) (Post 0) β rho1 H1 rho2 H2 Scope Funs σ) ->
    (* Free variables invariant *)
    (forall j, FV_inv k j (Pre Hole_c) (Post 0) β rho1 H1 rho2 H2 c Γ FVs) ->
    (* location renaming is injective *)
    (* only needed to prove the lower bound *)
    injective_subdomain (reach' H1 (env_locs rho1 (Scope :|: FromList FVs :|: Funs))) β ->
    
    (* well-formedness *)
    well_formed (reach' H1 (env_locs rho1 (Scope :|: Funs :|: FromList FVs))) H1 ->
    (env_locs rho1 (Scope :|: Funs :|: FromList FVs)) \subset dom H1 ->
    well_formed (reach' H2 (env_locs rho2 (Scope :|: (image σ Funs) :|: [set Γ]))) H2 ->
    (env_locs rho2 (Scope :|:  (image σ Funs) :|: [set Γ])) \subset dom H2 ->

    
    (* [Γ] (the current environment parameter) is not bound in e *)
    ~ In _ (bound_var e1) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (Scope :|: Funs :|: FromList FVs) rho1 ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e1 ->
    (* function renaming is injective in the [Funs] subdomain *)
    injective_subdomain Funs σ ->
    (* function renaming codomain is not shadowed by other vars *)
    Disjoint _ (image σ Funs) (bound_var e1) ->

    
    (* [e'] is the closure conversion of [e] *)
    Closure_conversion clo_tag Scope Funs σ c Γ FVs e1 e2 C ->
    
    (forall j, (e1, rho1, H1) ⪯ ^ (k ; j ; Pre Hole_c k ; Pre Hole_c; PostL 0 k H1 rho1 e1 ; Post 0) (C |[ e2 ]|, rho2, H2)).
  Proof with now eauto with Ensembles_DB.
    revert H1 H2 rho1 rho2 e1 e2 C Scope Funs FVs σ β c Γ.
    induction k as [k IHk] using lt_wf_rec1.
    intros H1 H2 rho1 rho2 e1 e2 C Scope Funs FVs σ β c Γ
           Henv Hfun HFVs Hinjb Hwf1 Hlocs1 Hwf2 Hlocs2 Hnin Hbind Hun Hinj Hd Hcc.
    induction e1 using exp_ind'; try clear IHe1.
    - (* case Econstr *)
      assert (Hfv := Closure_conversion_pre_occurs_free_Included _ _ _ _ _ _ _ _ _ _ Hcc).
      assert (Hfv' := Closure_conversion_occurs_free_Included _ _ _ _ _ _ _ _ _ _ Hcc Hun).
      rewrite !Union_assoc in Hfv'.

      inv Hcc.
      edestruct (binding_in_map_getlist _ rho1 l Hbind) as [vl Hgetl].
      rewrite <- Union_assoc. eapply project_vars_In_Union. eassumption.
      
      edestruct project_vars_ctx_to_heap_env as [H2' [rho2' [m Hct]]]; try eassumption.
      specialize (Hfun 0); eapply Fun_inv_weak_in_Fun_inv; eassumption.
      specialize (HFVs 0); eapply FV_inv_weak_in_FV_inv; eassumption.
      
      intros j.
      (* process right ctx *)
      eapply cc_approx_exp_right_ctx_compat
      with (ILi := fun c => PostL c k H1 rho1 (Econstr v t l e1)) (II := fun C => Pre C k);
        [ now intros; eapply Post_transfer; eauto | now intros; eapply IP_ctx_to_heap_env; eauto
          | | | | | eassumption | ].

      eapply well_formed_antimon. eapply reach'_set_monotonic. now eapply env_locs_monotonic; eauto.
      eassumption.

      eapply well_formed_antimon. eapply reach'_set_monotonic. now eapply env_locs_monotonic; eauto.
      eassumption.

      eapply Included_trans; [| eassumption ]. now eapply env_locs_monotonic; eauto.
      eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic; eauto.
      
      rewrite <- plus_n_O.
      replace (comp_ctx_f Hole_c C) with C by eauto.
      assert (Hwf2' := Hwf2).
      assert (Hlocs2' := Hlocs2). 
      eapply project_vars_well_formed' in Hwf2; try eassumption.
      eapply project_vars_env_locs' in Hlocs2; try eassumption.

      edestruct project_vars_correct as (Hd' & Hinj' & Henv' & Hfun' & HFVs' & Hvars);
        try eassumption.
      eapply binding_in_map_antimon; [| eassumption ]...
      rewrite <- !Union_assoc. eassumption.
      
      (* process Econstr one the right and left *)
      eapply cc_approx_exp_constr_compat 
      with (ILi := fun c => PostL c k H1 rho1 (Econstr v t l e1))
           (r2 := 0)
           (IIL2 := Pre Hole_c (k - cost H1 rho1 (Econstr v t l e1)));
        [ | | | | | | | eassumption | | ]. 
      + admit. (* bounds timeout compat *)
      + admit. (* bounds - pick F *)
      + admit. (* pre - allocation *) (* TODO maybe we need less assumptions *)
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
      + admit. (* bounds -- find F *)
      + (* Inductive case *) 
        intros vs1 vs2 l1 l2 H1' H2'' Hleq Ha1 Ha2 Hr1 Hr2 Hall j1.
        (* monotonicity of the local invariant *)
        eapply cc_approx_exp_rel_mon
        with (LP1 := PostL 0 (k - cost H1 rho1 (Econstr v t l e1)) H1' (M.set v (Loc l1) rho1) e1).
        
        (* Induction hypothesis *)
        { eapply IHk;
          [ | | | | | | | | | | | | now apply Hinj | | eassumption ].  
          * simpl in *. omega.
          * { intros j2.  
              eapply cc_approx_env_set_alloc_Constr with (b := β {l1 ~> l2});
                try eassumption.
              - eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic...
              - eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic.
                now eauto 20 with Ensembles_DB.
              - eapply Included_trans; [| eassumption ].
                eapply env_locs_monotonic...
              - eapply Included_trans; [| eassumption ].
                eapply env_locs_monotonic.
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
                eapply f_eq_subdomain_extend_not_In_S_r; [| reflexivity ].
                intros Hc. eapply reachable_in_dom in Hc.
                edestruct Hc as [vc Hgetc]. erewrite alloc_fresh in Hgetc; eauto. congruence.
                eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic. eapply env_locs_monotonic...
                eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic...
              - rewrite extend_gss. reflexivity.
              - intros j3 Hlt3. eapply Forall2_monotonic_strong; [| now eapply Hall ].
                intros x1 x2 Hin1 Hin2 Hrel. eapply cc_approx_val_rename_ext. now eapply Hrel.
                assert (Hincl : val_loc x1 \subset env_locs rho1 (Scope :|: Funs :|: FromList FVs)).
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
          * admit. (* fun inv env_set_alloc *)
          * admit. (* FV inv env set alloc *)
          * assert
              (Hinc :
                 reach' H1'
                        (env_locs (M.set v (Loc l1) rho1)
                                  (v |: Scope :|: FromList FVs :|: Funs)) \\ [set l1]
                        \subset
                  reach' H1 (env_locs rho1 (Scope :|: FromList FVs :|: Funs))
              ).
            { eapply Included_trans. eapply Included_Setminus_compat.
              eapply Included_trans;
                [| eapply reach'_alloc_set with (H' := H1')
                                                (S := Scope :|: FromList FVs :|: Funs)];
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
            { eapply injective_subdomain_antimon. eassumption.
              eapply Included_trans. eassumption.
              eapply reach'_set_monotonic. eapply env_locs_monotonic.
              now eauto 20 with Ensembles_DB. }
            { intros Hc. eapply image_monotonic in Hc; [| eassumption ].
              rewrite !env_locs_Union, !reach'_Union, !image_Union in Hc.
              rewrite cc_approx_env_image_reach in Hc; try eassumption. 
              rewrite FV_inv_image_reach in Hc; try eassumption.
              rewrite Fun_inv_image_reach in Hc; try eassumption.
              rewrite <- !reach'_Union in Hc. eapply reachable_in_dom in Hc.
              destruct Hc as [vc Hgetc]. erewrite alloc_fresh in Hgetc; eauto. congruence.
              eapply well_formed_antimon; [| eassumption ].
              rewrite !env_locs_Union, !reach'_Union.
              rewrite <- !Union_assoc. eapply Included_Union_preserv_r.
              eapply Included_Union_compat. reflexivity. rewrite Union_commut.
              eapply Included_Union_compat. reflexivity.
              rewrite (reach_unfold H2' (env_locs _ _))...
              eapply Union_Included. eapply Union_Included.
              eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic...
              eapply Included_trans; [| eapply reachable_in_dom; eauto ].
              rewrite !env_locs_Union, !reach'_Union.
              eapply Included_Union_preserv_r. eapply Included_post_reach'.
              eapply Included_trans; [| eassumption ]. eapply env_locs_monotonic...
              eapply binding_in_map_antimon; [| eassumption ]... }
          * assert (Hseq : v |: Scope :|: Funs :|: FromList FVs <-->
                             (Scope :|: Funs :|: FromList FVs) :|: [set v]).
            { rewrite (Union_commut _ [set v]). rewrite <- !Union_assoc. reflexivity. }
            rewrite Hseq. eapply well_formed_reach_alloc'; try eassumption.
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
          * assert (Hseq : v |: Scope :|: image σ Funs :|: [set Γ] <-->
                             (Scope :|: image σ Funs :|: [set Γ]) :|: [set v]).
            { rewrite (Union_commut _ [set v]). rewrite <- !Union_assoc. reflexivity. }
            rewrite Hseq. eapply well_formed_reach_alloc; eauto.
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