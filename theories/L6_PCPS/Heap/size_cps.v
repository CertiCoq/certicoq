From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions.

From L6.Heap Require Import heap heap_defs cc_log_rel
     closure_conversion closure_conversion_util compat.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega.

Require Import compcert.lib.Maps.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module Size (H : Heap).

  (* This is stupid. Find out how to use modules correctly. *)
  Module Util := CCUtil H.
  
  Import H Util.C.LR.Sem.Equiv Util.C.LR.Sem.Equiv.Defs Util.C.LR.Sem
         Util.C.LR Util.C Util.


  (** * Size of CPS terms, values and environments, needed to express the upper bound on
         the execution cost of certain transformations *)
  
  (** The size of CPS expressions. Right now we only count the number of
   * variables in a program (free or not), the number of functions and
   * the number of function definition blocks *)
  (* TODO -- max per function block *)
  Fixpoint exp_num_vars (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => length ys + exp_num_vars e
      | Ecase x l =>
        1 + (fix sizeOf_l l :=
               match l with
                 | [] => 0
                 | (t, e) :: l => exp_num_vars e + sizeOf_l l
               end) l
      | Eproj x _ _ y e => 1 + exp_num_vars e
      | Efun B e => 1 + fundefs_num_vars B + 3 * numOf_fundefs B + exp_num_vars e
      | Eapp x _ ys => 1 + length ys
      | Eprim x _ ys e => length ys + exp_num_vars e
      | Ehalt x => 1
    end
  with fundefs_num_vars (B : fundefs) : nat := 
         match B with
           | Fcons _ _ xs e B =>
             1 + exp_num_vars e + fundefs_num_vars B
           | Fnil => 0
         end.

  Fixpoint exp_max_vars (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => exp_max_vars e
      | Ecase x l =>
        1 + (fix sizeOf_l l :=
               match l with
                 | [] => 0
                 | (t, e) :: l => exp_max_vars e
               end) l
      | Eproj x _ _ y e => exp_max_vars e
      | Efun B e => max (1 + fundefs_num_vars B + 3 * numOf_fundefs B) (exp_max_vars e)
      | Eapp x _ ys => 0
      | Eprim x _ ys e => exp_max_vars e
      | Ehalt x => 0
    end.
  
  Fixpoint exp_num_vars_out (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => length ys
      | Ecase x l => 1
      | Eproj x _ _ y e => 1  
      | Efun B e => 1 + fundefs_num_vars B + 3 * numOf_fundefs B
      | Eapp x _ ys => 1 + length ys
      | Eprim x _ ys e => length ys 
      | Ehalt x => 1
    end.

  Fixpoint exp_max_vars_out (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => 0
      | Ecase x l => 0
      | Eproj x _ _ y e => 0
      | Efun B e => 1 + fundefs_num_vars B 
      | Eapp x _ ys => 0
      | Eprim x _ ys e => 0 
      | Ehalt x => 0
    end.

  (** The cost of evaluating a CC evaluation context *)
  Fixpoint cost_exp_ctx (c : exp_ctx) : nat :=
    match c with
      | Hole_c => 0
      | Econstr_c _ _ ys c => 1 + length ys + cost_exp_ctx c
      | Eproj_c _ _ _ _ c => 1 + cost_exp_ctx c
      | Efun1_c B c => 1 + cost_exp_ctx c 
      | Eprim_c _ _ ys c => length ys + cost_exp_ctx c
      | Ecase_c _ l1 _ c l2 => 0
      | Efun2_c B e => 0
    end.

  Definition max_vars_value (v : value) : nat :=
    match v with
      | Loc _ => 0
      | FunPtr B _ => fundefs_num_vars B
    end.

  Definition max_vars_block (b : block) : nat :=
    match b with
      | Constr _ vs => max_list_nat_with_measure max_vars_value 0 vs
      | Clos v1 v2 => max (max_vars_value v1) (max_vars_value v2)
      | Env x => 0
    end.
  
  Definition max_vars_heap (H : heap block) :=
    max_with_measure max_vars_block H.
  
  Definition max_heap_exp (H : heap block) (e : exp) :=
    max (max_vars_heap H) (exp_max_vars e).

  Lemma max_heap_with_measure_get {A} (H1 : heap A) l f b : 
    get l H1 = Some b ->
    f b <= max_with_measure f H1. 
  Proof.
    intros Hget. unfold max_with_measure. 
    eapply heap_elements_complete in Hget.
    generalize (heap_elements H1), Hget. clear Hget.
    intros ls Hin. induction ls.
    + inv Hin.
    + simpl.
      inv Hin.
      * simpl. eapply fold_left_extensive.
        intros [l1 x1] x2. eapply Max.le_max_l. 
      * eapply le_trans. eapply IHls. eassumption.
        eapply fold_left_monotonic; [| omega ].
        intros x1 x2 [l1 y1] Hleq. simpl.
        eapply NPeano.Nat.max_le_compat_r. eassumption.
  Qed.
    
  Lemma max_vars_heap_alloc_constr H1 H1' b l :
    alloc b H1 = (l, H1') ->
    max_vars_block b = 0 ->
    max_vars_heap H1 = max_vars_heap H1'.
  Proof.
    intros Hall Hsub. unfold max_vars_heap.
    erewrite (HL.max_with_measure_alloc _ _ _ _ H1'); [| reflexivity | eassumption ].
    rewrite Hsub. rewrite Max.max_0_r. reflexivity.
  Qed.
  
    
  (** * Postcondition *)

  (** Enforces that the resource consumption of the target is within certain bounds *)
  Definition Post
             k (* time units already spent *)
             (p1 p2 : heap block * env * exp * nat * nat) :=
    match p1, p2 with
      | (H1, rho1, e1, c1, m1), (H2, rho2, e2, c2, m2) =>
        c1 <= c2 + k <=  c1 * (1 + max_heap_exp H1 e1) + (exp_num_vars e1) /\
        m1 <= m2 <= m1 * (1 + max_heap_exp H1 e1)
    end.


  (** * Precondition *)

  (** Enforces that the initial heaps have related sizes *)
  Definition Pre
             (p1 p2 : heap block * env * exp) :=
    (* let m := cost_alloc_ctx C in  *)
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        size_heap H1 <=
        size_heap H2 <= (size_heap H1) * (1 + max_heap_exp H1 e1)
    end.
  
  Definition PreG
             (Funs : Ensemble var)
             `{ToMSet Funs}
             (p1 p2 : heap block * env * exp) :=
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        let funs := PS.cardinal (PS.inter (@mset Funs _) (exp_fv e1)) in
        size_heap H1 <=
        size_heap H2 + funs <= (size_heap H1) * (1 + max_heap_exp H1 e1)
    end.
  (** Compat lemmas *)

  Lemma PostBase H1 H2 rho1 rho2 e1 e2 k :
    k <= exp_num_vars e1 ->
    InvCostBase (Post k) Pre H1 H2 rho1 rho2 e1 e2.
  Proof.
    unfold InvCostBase, Post, Pre.
    intros Hleq1 H1' H2' rho1' rho2' c b1 b2  Heq1 Hinj1 Heq2 Hinj2 [Hs1 Hs2].
    split.
    + split. omega. eapply plus_le_compat.
      rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
      eapply le_plus_l. omega.
    + split. omega. omega.
  Qed.

  Lemma cc_approx_val_max_vars_value k j IP P b v1 H1 v2 H2 :
    (Res (v1, H1)) ≺ ^ (k; j; IP; P; b) (Res (v2, H2)) -> 
    max_vars_value v1 = 0.
  Proof.
    intros Heq. destruct v1; try contradiction. reflexivity.
  Qed.

  Lemma cc_approx_val_max_vars_value_list k j IP P b vs1 H1 vs2 H2 :
    Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k; j; IP; P; b) (Res (v2, H2))) vs1 vs2 -> 
    max_list_nat_with_measure max_vars_value 0 vs1 = 0.
  Proof.
    intros Heq. induction Heq; eauto.
    simpl.
    erewrite cc_approx_val_max_vars_value; [| eassumption ].
    eassumption.
  Qed.


  Lemma PostConstrCompat i j IP P b H1 H2 rho1 rho2 x1 x2 c ys1 ys2 e1 e2 k :
    Forall2 (fun y1 y2 => cc_approx_var_env i j IP P b H1 rho1 H2 rho2 y1 y2) ys1 ys2 -> 
    k <= length ys1 ->
    InvCtxCompat (Post k) (Post 0)
                 H1 H2 rho1 rho2 (Econstr_c x1 c ys1 Hole_c) (Econstr_c x2 c ys2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold InvCtxCompat, Post.
    intros Hall Hleq H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1 c2 c1' c2'
           m1 m2 b1 b2 Heq1 Hinj1 Heq2 Hinj2 [[Hc1 Hc2] [Hm1 Hm2]] Hctx1 Hctx2.
    assert (Hlen := Forall2_length _ _ _ Hall). 
    inv Hctx1. inv Hctx2. inv H13. inv H16.
    rewrite !plus_O_n in *. simpl (cost_ctx _) in *.
    rewrite !Hlen in *.
    eapply Forall2_monotonic_strong
      with (R' := fun y1 y2 : var =>
                    cc_approx_var_env i j IP P (b2 ∘ b ∘ b1) H1' rho1' H2' rho2' y1 y2) in Hall.
    {  edestruct cc_approx_var_env_getlist as [vs2' [Hget2' Hcc]]; try eassumption.
       split.
      - split. omega.
        simpl exp_num_vars. rewrite (plus_comm (length ys1)), plus_assoc. 
        eapply plus_le_compat; [| simpl; omega ].
        simpl (max_heap_exp _ _) in *.
        rewrite <- !plus_n_O in *.
        eapply le_trans. 
        eapply plus_le_compat_r. eassumption.
        rewrite !(plus_comm _ (exp_num_vars e1)).
        rewrite <- !plus_assoc.
        eapply plus_le_compat. reflexivity.
        rewrite NPeano.Nat.mul_add_distr_r.
        eapply plus_le_compat;
          [| rewrite NPeano.Nat.mul_add_distr_l, NPeano.Nat.mul_1_r;
             eapply le_plus_l ].
        eapply mult_le_compat_l. eapply plus_le_compat_l.
        unfold max_heap_exp.
        eapply Nat.max_le_compat; [| simpl; omega ]. 
        erewrite <- max_vars_heap_alloc_constr; try eassumption. reflexivity.
        simpl.       
        eapply cc_approx_val_max_vars_value_list. eassumption.
      - split; eauto. 
        eapply le_trans. eassumption.
        eapply mult_le_compat_l. eapply plus_le_compat_l.
        unfold max_heap_exp.
        eapply Nat.max_le_compat; [| simpl; omega ]. 
        erewrite <- max_vars_heap_alloc_constr; try eassumption. reflexivity.
        simpl.       
        eapply cc_approx_val_max_vars_value_list. eassumption. }
    intros y1 y2 Hin1 Hin2 Hcc.
    eapply cc_approx_var_env_heap_env_equiv; try eassumption.
    simpl; normalize_occurs_free...
    simpl; normalize_occurs_free...
  Qed.

  Lemma PreConstrCompat i j IP P b H1 H2 rho1 rho2 x1 x2 c ys1 ys2 e1 e2 :
    Forall2 (fun y1 y2 => cc_approx_var_env i j IP P b H1 rho1 H2 rho2 y1 y2) ys1 ys2 -> 
    IInvCtxCompat Pre Pre
                 H1 H2 rho1 rho2 (Econstr_c x1 c ys1 Hole_c) (Econstr_c x2 c ys2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold IInvCtxCompat, Pre.
    intros Hall H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1' c2'
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 [Hm1 Hm2] Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H13. inv H16.
    assert (Hlen := Forall2_length _ _ _ Hall).
    eapply Forall2_monotonic_strong
      with (R' := fun y1 y2 : var =>
                    cc_approx_var_env i j IP P (b2 ∘ b ∘ b1) H1' rho1' H2' rho2' y1 y2) in Hall.
    { edestruct cc_approx_var_env_getlist as [vs2' [Hget2' Hcc]]; try eassumption.
      split.
      - simpl. simpl in Hm1.
        unfold size_heap in *.
        erewrite HL.size_with_measure_alloc; [| reflexivity | eassumption ].
        erewrite (HL.size_with_measure_alloc _ _ _ _ H2''); [| reflexivity | eassumption ].
        simpl.
        erewrite <- (getlist_length_eq _ vs); eauto.
        erewrite <- (getlist_length_eq _ vs0); eauto.
        eapply plus_le_compat. omega.
        replace (@length M.elt ys1) with (@length var ys1) by reflexivity.
        replace (@length M.elt ys2) with (@length var ys2) by reflexivity.
        omega. 
      - unfold size_heap in *.
        erewrite (HL.size_with_measure_alloc _ _ _ _ H1''); [| reflexivity | eassumption ].
        erewrite (HL.size_with_measure_alloc _ _ _ _ H2''); [| reflexivity | eassumption ].
        simpl size_val in *. 
        rewrite NPeano.Nat.mul_add_distr_r. eapply plus_le_compat.
        eapply le_trans. eassumption.
        eapply mult_le_compat_l.
        unfold max_heap_exp. eapply plus_le_compat_l. simpl.
        unfold max_heap_exp.
        eapply Nat.max_le_compat; [| simpl; omega ]. 
        erewrite max_vars_heap_alloc_constr; try eassumption. reflexivity.
        simpl.       
        eapply cc_approx_val_max_vars_value_list. eassumption.
        erewrite <- (getlist_length_eq _ vs); eauto.
        erewrite <- (getlist_length_eq _ vs0); eauto.
        replace (@length M.elt ys1) with (@length var ys1) by reflexivity.
        replace (@length M.elt ys2) with (@length var ys2) by reflexivity.
        rewrite Hlen. rewrite NPeano.Nat.mul_add_distr_l.
        eapply le_plus_trans. omega. }
    intros y1 y2 Hin1 Hin2 Hcc.
    eapply cc_approx_var_env_heap_env_equiv; try eassumption.
    simpl; normalize_occurs_free...
    simpl; normalize_occurs_free...
  Qed.

  
  Lemma PostProjCompat H1 H2 rho1 rho2 x1 x2 c n y1 y2 e1 e2 k :
    k <= 1 ->
    InvCtxCompat (Post k) (Post 0)
                 H1 H2 rho1 rho2 (Eproj_c x1 c n y1 Hole_c) (Eproj_c x2 c n y2 Hole_c) e1 e2.
  Proof.
    unfold InvCtxCompat, Post.
    intros Hleq H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1 c2 c1' c2'
           m1 m2 b1 b2 Heq1 Hinj1 Heq2 Hinj2 [[Hc1 Hc2] [Hm1 Hm2]] Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H15. inv H19.
    split.
    - split. simpl. omega.
      simpl exp_num_vars. simpl cost_ctx.
      rewrite !plus_O_n. rewrite <- !plus_n_O in *.
      simpl (max_heap_exp _ _) in *. 
      rewrite NPeano.Nat.mul_add_distr_r. 
      replace  (c1 * (1 + max_heap_exp H1'' (Eproj x1 c n y1 e1)) +
                1 * (1 + max_heap_exp H1'' (Eproj x1 c n y1 e1)) + 
                S (exp_num_vars e1))
      with ((c1 * (1 + max_heap_exp H1'' (Eproj x1 c n y1 e1)) + (exp_num_vars e1)) + 
            (1 * (1 + max_heap_exp H1'' (Eproj x1 c n y1 e1)) + 1)) by ring.
      rewrite <- (plus_assoc). eapply plus_le_compat; [| simpl; omega ].
      eapply le_trans. eassumption.
      eapply plus_le_compat; [| reflexivity ].
      eapply mult_le_compat_l. eapply plus_le_compat_l.
      unfold max_heap_exp.
      eapply Nat.max_le_compat. reflexivity. simpl. omega.
    - split; eauto. 
  Qed.
  
  Lemma PreProjCompat H1 H2 rho1 rho2 x1 x2 c n y1 y2 e1 e2  :
    IInvCtxCompat Pre Pre
                  H1 H2 rho1 rho2 (Eproj_c x1 c n y1 Hole_c) (Eproj_c x2 c n y2 Hole_c) e1 e2.
  Proof.
    unfold IInvCtxCompat, Pre.
    intros H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1' c2'
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 [Hm1 Hm2] Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H15. inv H19.
    split.
    - simpl. simpl in Hm1. omega.
    - eapply le_trans. eassumption. 
      eapply mult_le_compat_l.
      eapply plus_le_compat_l.
      eapply Nat.max_le_compat. reflexivity. simpl; omega.
  Qed.

  (* Cost for projecting vars *)
  Lemma project_var_cost 
        Scope Funs c Γ FVs S1 x x' C1 S2 :
    project_var Scope Funs c Γ FVs S1 x x' C1 S2 ->
    cost_ctx_full C1 <= 1.
  Proof.
    intros Hvar; inv Hvar; eauto.
  Qed.

    
  Lemma project_vars_cost 
        Scope Funs c Γ FVs S1 x x' C1 S2 :
    project_vars Scope Funs c Γ FVs S1 x x' C1 S2 ->
    cost_ctx_full C1 <= length x.
  Proof.
    intros Hvar. induction Hvar; eauto.
    rewrite cost_ctx_full_ctx_comp_ctx_f. simpl.
    eapply project_var_cost in H. omega.
  Qed.
  
  Lemma project_var_cost_alloc
        Scope Funs c Γ FVs S1 x x' C1 S2 :
    project_var Scope Funs c Γ FVs S1 x x' C1 S2 ->
    cost_alloc_ctx C1 = 0.
  Proof.
    intros Hvar; inv Hvar; eauto.
  Qed.
  
  Lemma project_vars_cost_alloc
        Scope Funs c Γ FVs S1 x x' C1 S2 :
    project_vars Scope Funs c Γ FVs S1 x x' C1 S2 ->
    cost_alloc_ctx C1 = 0.
  Proof.
    intros Hvar. induction Hvar; eauto.
    simpl. rewrite cost_alloc_ctx_comp_ctx_f.
    erewrite project_var_cost_alloc; eauto.
  Qed.

  Lemma PreCtxCompat_var_r H1 H2 rho1 rho2 C e1 e2
        Scope Funs c Γ FVs S x x' S':
    project_var Scope Funs c Γ FVs S x x' C S' ->
    IInvCtxCompat_r Pre Pre H1 H2 rho1 rho2 C e1 e2.
  Proof.
    intros Hvar.
    unfold IInvCtxCompat_r, Pre.
    intros H1' H2' H2'' rho1' rho2' rho2'' c1'
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx.
    eapply project_var_heap in Hctx; eauto. subst. eauto.
  Qed.

  Lemma PostCtxCompat_var_r H1 H2 rho1 rho2 C e1 e2
        Scope Funs c Γ FVs S x x' S':
    project_var Scope Funs c Γ FVs S x x' C S' ->
    InvCtxCompat_r (Post 0) (Post (cost_ctx_full C)) H1 H2 rho1 rho2 C e1 e2.
  Proof.
    unfold InvCtxCompat_r, Pre.
    intros Hvar H1' H2' H2'' rho1' rho2' rho2'' c' c1 c2 m1 m2 
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx'.
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx').
    subst. 
    assert (Heq := project_var_cost _ _ _ _ _ _ _ _ _ _ Hvar).  
    eapply project_var_heap in Hctx'; eauto. subst.
    unfold Post in *. omega.
  Qed.

  Lemma PreCtxCompat_vars_r H1 H2 rho1 rho2 C e1 e2
        Scope Funs c Γ FVs S x x' S':
    project_vars Scope Funs c Γ FVs S x x' C S' ->
    IInvCtxCompat_r Pre Pre H1 H2 rho1 rho2 C e1 e2.
  Proof.
    intros Hvar.
    unfold IInvCtxCompat_r, Pre.
    intros H1' H2' H2'' rho1' rho2' rho2'' c1'
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx.
    eapply project_vars_heap in Hctx; eauto. subst. eauto.
  Qed.

  Lemma PostCtxCompat_vars_r H1 H2 rho1 rho2 C e1 e2
        Scope Funs c Γ FVs S x x' S':
    project_vars Scope Funs c Γ FVs S x x' C S' ->
    InvCtxCompat_r (Post 0) (Post (cost_ctx_full C)) H1 H2 rho1 rho2 C e1 e2.
  Proof.
    unfold InvCtxCompat_r, Pre.
    intros Hvar H1' H2' H2'' rho1' rho2' rho2'' c' c1 c2 m1 m2 
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx'.
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx').
    subst. 
    assert (Heq := project_vars_cost _ _ _ _ _ _ _ _ _ _ Hvar).  
    eapply project_vars_heap in Hctx'; eauto. subst.
    unfold Post in *. omega.
  Qed.
    
  (* Lemma sizeOf_env_setlist k H rho rho' xs vs : *)
  (*   setlist xs vs rho = Some rho' -> *)
  (*   sizeOf_env k H rho' = *)
  (*   max (max_list_nat_with_measure (sizeOf_val k H) 0 vs) (sizeOf_env k H rho). *)
  (* Proof. *)
  (*   revert vs rho rho'. induction xs; intros vs rho rho' Hset. *)
  (*   - destruct vs; try discriminate. inv Hset. *)
  (*     reflexivity. *)
  (*   - destruct vs; try discriminate. *)
  (*     simpl in Hset. destruct (setlist xs vs rho) eqn:Hset'; try discriminate. *)
  (*     inv Hset. rewrite sizeOf_env_set; simpl. *)
  (*     rewrite max_list_nat_acc_spec. *)
  (*     rewrite <- Max.max_assoc. eapply NPeano.Nat.max_compat. reflexivity. *)
  (*     eauto. *)
  (* Qed. *)

  (* Lemma sizeOf_env_get k H rho x v : *)
  (*   rho ! x = Some v -> *)
  (*   sizeOf_val k H v <= sizeOf_env k H rho. *)
  (* Proof. *)
  (*   intros Hget.  *)
  (*   unfold sizeOf_env. rewrite <- sizeOf_val_eq. *)
  (*   eapply max_ptree_with_measure_spec1. *)
  (*   eassumption. *)
  (* Qed. *)

  (* (** Lemmas about [size_of_exp] *) *)

  (* Lemma sizeOf_exp_grt_1 e : *)
  (*   1 <= sizeOf_exp e. *)
  (* Proof. *)
  (*   induction e using exp_ind'; simpl; eauto; omega. *)
  (* Qed. *)

  (* (** Lemmas about [sizeOf_exp_ctx] *) *)
  (* Lemma sizeOf_exp_ctx_comp_ctx_mut : *)
  (*   (forall C1 C2, *)
  (*      sizeOf_exp_ctx (comp_ctx_f C1 C2) = sizeOf_exp_ctx C1 + sizeOf_exp_ctx C2) /\ *)
  (*   (forall B e, *)
  (*      sizeOf_fundefs_ctx (comp_f_ctx_f B e) = sizeOf_fundefs_ctx B + sizeOf_exp_ctx e). *)
  (* Proof. *)
  (*   exp_fundefs_ctx_induction IHe IHB;  *)
  (*   try (intros C; simpl; eauto; rewrite IHe; omega); *)
  (*   try (intros C; simpl; eauto; rewrite IHB; omega). *)
  (*   (* probably tactic misses an intro pattern *) *)
  (*   intros l' C. simpl. rewrite IHe; omega. *)
  (* Qed. *)

  (* Corollary sizeOf_exp_ctx_comp_ctx : *)
  (*   forall C1 C2, *)
  (*     sizeOf_exp_ctx (comp_ctx_f C1 C2) = sizeOf_exp_ctx C1 + sizeOf_exp_ctx C2. *)
  (* Proof. *)
  (*   eapply sizeOf_exp_ctx_comp_ctx_mut; eauto. *)
  (* Qed. *)

  (* Corollary sizeOf_fundefs_ctx_comp_f_ctx : *)
  (*   forall B e, *)
  (*     sizeOf_fundefs_ctx (comp_f_ctx_f B e) = sizeOf_fundefs_ctx B + sizeOf_exp_ctx e. *)
  (* Proof. *)
  (*   eapply sizeOf_exp_ctx_comp_ctx_mut; eauto. *)
  (* Qed. *)
  
  (* (** Lemmas about [max_exp_env] *) *)

  (* Lemma max_exp_env_grt_1 k H rho e : *)
  (*   1 <= max_exp_env k H rho e. *)
  (* Proof. *)
  (*   unfold max_exp_env. *)
  (*   eapply le_trans. now apply sizeOf_exp_grt_1. *)
  (*   eapply Max.le_max_l. *)
  (* Qed. *)

  (* Lemma max_exp_env_Econstr k H x t ys e rho : *)
  (*   max_exp_env k H rho e <= max_exp_env k H rho (Econstr x t ys e). *)
  (* Proof. *)
  (*   eapply NPeano.Nat.max_le_compat_r. *)
  (*   simpl. omega. *)
  (* Qed. *)
  
  (* Lemma max_exp_env_Eproj k x t N y e H rho : *)
  (*   max_exp_env k H rho e <= max_exp_env k H rho (Eproj x t N y e). *)
  (* Proof. *)
  (*   eapply NPeano.Nat.max_le_compat_r. *)
  (*   simpl. omega. *)
  (* Qed. *)

  (* Lemma max_exp_env_Ecase_cons_hd k x c e l H rho : *)
  (*   max_exp_env k H rho e <= max_exp_env k H rho (Ecase x ((c, e) :: l)). *)
  (* Proof. *)
  (*   eapply NPeano.Nat.max_le_compat_r. *)
  (*   simpl. omega. *)
  (* Qed. *)
  
  (* Lemma max_exp_env_Ecase_cons_tl k x c e l H rho : *)
  (*   max_exp_env k H rho  (Ecase x l) <= max_exp_env k H rho (Ecase x ((c, e) :: l)). *)
  (* Proof. *)
  (*   eapply NPeano.Nat.max_le_compat_r. *)
  (*   simpl. omega. *)
  (* Qed. *)

  (* Lemma max_exp_env_Eprim k H rho x f ys e : *)
  (*   max_exp_env k H rho e <= max_exp_env k H rho (Eprim x f ys e). *)
  (* Proof. *)
  (*   eapply NPeano.Nat.max_le_compat_r. *)
  (*   simpl. omega. *)
  (* Qed. *)

  (** Number of function definitions *)
  Fixpoint numOf_fundefs (B : fundefs) : nat := 
    match B with
      | Fcons _ _ xs e B =>
        1 + numOf_fundefs B
      | Fnil => 0
    end.

  (** Number of function definitions in an expression *)
  Fixpoint numOf_fundefs_in_exp (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => numOf_fundefs_in_exp e
      | Ecase x l =>
        1  + (fix num l :=
                match l with
                  | [] => 0
                  | (t, e) :: l => numOf_fundefs_in_exp e + num l
                end) l
      | Eproj x _ _ y e => 1 + numOf_fundefs_in_exp e
      | Efun B e => numOf_fundefs_in_fundefs B + numOf_fundefs_in_exp e
      | Eapp x _ ys => 0
      | Eprim x _ ys e => numOf_fundefs_in_exp e
      | Ehalt x => 0
    end
  with numOf_fundefs_in_fundefs (B : fundefs) : nat :=
         match B with
           | Fcons _ _ xs e B =>
             1 + numOf_fundefs_in_exp e + numOf_fundefs_in_fundefs B
           | Fnil => 0
         end.

  (* Lemma numOf_fundefs_le_sizeOf_fundefs B : *)
  (*   numOf_fundefs B <= sizeOf_fundefs B. *)
  (* Proof. *)
  (*   induction B; eauto; simpl; omega. *)
  (* Qed. *)


  (* Lemma max_exp_env_Efun k B e rho : *)
  (*   max_exp_env k He (def_funs B B rho rho) <= max_exp_env k (Efun B e) rho. *)
  (* Proof. *)
  (*   unfold max_exp_env. eapply le_trans. *)
  (*   - eapply NPeano.Nat.max_le_compat_l. *)
  (*     now apply sizeOf_env_def_funs. *)
  (*   - rewrite (Max.max_comm (sizeOf_env _ _)), Max.max_assoc. *)
  (*     eapply NPeano.Nat.max_le_compat_r. *)
  (*     eapply Nat.max_lub; simpl; omega. *)
  (* Qed. *)

  
  (* Lemma make_closures_cost ct B S Γ C g : *)
  (*   make_closures ct B S Γ C g S -> *)
  (*   sizeOf_exp_ctx C = 3 * (numOf_fundefs B). *)
  (* Proof. *)
  (*   intros Hvar. induction Hvar; eauto. *)
  (*   simpl. omega. *)
  (* Qed. *)

  (* Lemma make_closures_cost_alloc ct B S Γ C g : *)
  (*   make_closures ct B S Γ C g S -> *)
  (*   cost_alloc_ctx C = 3 * (numOf_fundefs B). *)
  (* Proof. *)
  (*   intros Hvar. induction Hvar; eauto. *)
  (*   simpl. omega. *)
  (* Qed. *)

  (* Lemma ctx_to_heap_env_cost C H1 rho1 H2 rho2 m : *)
  (*   ctx_to_heap_env C H1 rho1 H2 rho2 m -> *)
  (*   m = sizeOf_exp_ctx C. *)
  (* Proof. *)
  (*   intros Hctx; induction Hctx; eauto. *)
  (*   simpl. omega. *)
  (*   simpl. omega. *)
  (*   simpl. omega. *)
  (* Qed.  *)
  
  (*   Lemma IP_ctx_to_heap_env *)
  (*       i (H1 H2 H2' : heap block) (rho1 rho2 rho2' : env) *)
  (*       (e1 e2 : exp) (C C' : exp_ctx) (c : nat) :  *)
  (*   Pre C' i (H1, rho1, e1) (H2, rho2, C |[ e2 ]|) -> *)
  (*   ctx_to_heap_env C H2 rho2 H2' rho2' c -> *)
  (*   Pre (comp_ctx_f C' C) i (H1, rho1, e1) (H2', rho2', e2). *)
  (* Proof. *)
  (*   intros [HP1 Hp2] Hctx. unfold Pre in *. *)
  (*   erewrite (ctx_to_heap_env_size_heap C rho2 rho2' H2 H2'); [| eassumption ]. *)
  (*   rewrite cost_alloc_ctx_comp_ctx_f in *. split. omega. *)
  (*   assert (Hgrt1 := max_exp_env_grt_1 i H1 rho1 e1). *)
  (*   eapply le_trans. eapply plus_le_compat_r. eassumption. *)
  (*   rewrite plus_assoc. *)
  (*   rewrite <- (mult_assoc _ (size_heap H1 + cost_alloc_ctx C' + cost_alloc_ctx C)). *)
  (*   rewrite Nat.mul_add_distr_r. rewrite Nat.mul_add_distr_l. *)
  (*   rewrite Nat.mul_add_distr_l.  rewrite <- !plus_assoc. eapply plus_le_compat. *)
  (*   rewrite <- Nat.mul_add_distr_l. rewrite <- mult_assoc. omega. *)
  (*   rewrite plus_comm. eapply plus_le_compat_r. *)
  (*   eapply le_trans; *)
  (*     [| eapply mult_le_compat_l; eapply mult_le_compat_l; eassumption ]. *)
  (*   omega.  *)
  (* Qed. *)
  

End Size.