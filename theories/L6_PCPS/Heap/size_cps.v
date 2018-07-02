From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions.

From L6.Heap Require Import heap heap_defs cc_log_rel
     closure_conversion closure_conversion_util compat.

From Coq Require Import ZArith.Znumtheory Arith Arith.Wf_nat Relations.Relations
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega Permutation.

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
         the execution cost of certain transformations
   *)
  
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

  Fixpoint exp_num_fundefs (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => exp_num_fundefs e
      | Ecase x l => 1 + (fix sizeOf_l l :=
                           match l with
                             | [] => 0
                             | (t, e) :: l => exp_num_fundefs e
                           end) l
      | Eproj x _ _ y e => exp_num_fundefs e
      | Efun B e =>  2 * fundefs_num_vars B 
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
      | FunPtr B _ => 1 + fundefs_num_vars B + 3
    end.

  Definition max_vars_block (b : block) : nat :=
    match b with
      | Constr _ vs => max_list_nat_with_measure max_vars_value 0 vs
      | Clos v1 rho => max_vars_value v1 (* ?? *)
    end.

  Definition max_vars_heap (H : heap block) :=
    max_with_measure max_vars_block H.

  Definition numOf_fundefs_value (v : value) : nat :=
    match v with
      | Loc _ => 0
      | FunPtr B _ => 1 + numOf_fundefs B
    end.
  
  Definition numOf_fundefs_block (b : block) : nat :=
    match b with
      | Constr _ vs => max_list_nat_with_measure numOf_fundefs_value 0 vs
      | Clos v1 rho => numOf_fundefs_value v1 
    end.
  
  
  Definition numOf_fundefs_heap (H : heap block) :=
    max_with_measure numOf_fundefs_block H.
  
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

  Lemma max_vars_heap_get H1 l b :
    get l H1 = Some b ->
    max_vars_block b <= max_vars_heap H1. 
  Proof.
    eapply max_heap_with_measure_get.
  Qed.

  Lemma max_vars_heap_alloc_constr H1 H1' l b :
    alloc b H1 = (l, H1') ->
    max_vars_block b = 0 ->
    max_vars_heap H1 = max_vars_heap H1'.
  Proof.
    intros Hall Hsub. unfold max_vars_heap.
    erewrite (HL.max_with_measure_alloc _ _ _ _ H1'); [| reflexivity | eassumption ].
    rewrite Hsub. rewrite Max.max_0_r. reflexivity.
  Qed.

  Lemma max_vars_heap_def_closures_le H1 H1' rho1 rho1' B B0 rho :
    def_closures B B0 rho1 H1 rho = (H1', rho1') ->
    max_vars_heap H1 <= max_vars_heap H1'.
  Proof.
    revert H1' rho1'. induction B; intros H1' rho1' Hclo.
    - simpl in Hclo.
      destruct (def_closures B B0 rho1 H1 rho) as [H2 rho2] eqn:Hclo'.
      destruct (alloc (Clos (FunPtr B0 v) rho) H2) as [l' rho3] eqn:Hal. inv Hclo.
      eapply le_trans. eapply IHB; try eassumption. reflexivity.
      unfold max_vars_heap.  
      erewrite (HL.max_with_measure_alloc _ _ _ _ H1'); [| reflexivity | eassumption ].
      eapply Max.le_max_l.
    - inv Hclo; eauto.
  Qed.
      
  Lemma max_vars_heap_def_closures H1 H1' rho1 rho1' B B0 f rho :
    def_closures B B0 rho1 H1 rho = (H1', rho1') ->
    max_vars_block (Clos (FunPtr B0 f) rho) <=  max_vars_heap H1 ->
    max_vars_heap H1 = max_vars_heap H1'.
  Proof.
    revert H1' rho1'. induction B; intros H1' rho1' Hclo Hmax.
    - simpl in Hclo.
      destruct (def_closures B B0 rho1 H1 rho) as [H2 rho2] eqn:Hclo'.
      destruct (alloc (Clos (FunPtr B0 v) rho) H2) as [l' rho3] eqn:Hal. inv Hclo.
      erewrite (IHB H2); try eassumption; try reflexivity.
      unfold max_vars_heap.
      erewrite (HL.max_with_measure_alloc _ _ _ _ H1'); [| reflexivity | eassumption ].
      rewrite Max.max_l. reflexivity. eapply le_trans. eassumption.
      eapply max_vars_heap_def_closures_le. eassumption.
    - inv Hclo. reflexivity.
  Qed.

  Lemma max_heap_GC H1 H2 S `{ToMSet S}: 
    live S H1 H2 ->
    max_vars_heap H2 <= max_vars_heap H1.
  Proof.
  Admitted.

  (** * Postcondition *)

  (** Enforces that the resource consumption of the target is within certain bounds *)
  Definition Post
             k (* time units already spent *)
             (Funs : Ensemble var)
             `{ToMSet Funs}
             (p1 p2 : heap block * env * exp * nat * nat) :=
    match p1, p2 with
      | (H1, rho1, e1, c1, m1), (H2, rho2, e2, c2, m2) =>
        let funs := PS.cardinal (@mset Funs _) in
        c1 <= c2 + k <=  c1 * (4 + max_heap_exp H1 e1) + (exp_num_vars e1) /\
        m1 <= m2 + max_heap_exp H1 e1 +  3 * funs <= m1 * (1 + max_heap_exp H1 e1) + max_heap_exp H1 e1
    end.


  (** * Precondition *)

  (** Enforces that the initial heaps have related sizes *)  
  Definition PreG
             (Funs : Ensemble var)
             `{ToMSet Funs}
             (p1 p2 : heap block * env * exp) :=
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        let funs := PS.cardinal (@mset Funs _) in
        size_heap H1 <=
        size_heap H2 + 3 * funs <= (size_heap H1) * (1 + max_heap_exp H1 e1)
    end.
  

  (** Compat lemmas *)

  Lemma PostBase H1 H2 rho1 rho2 e1 e2 k Funs {_ : ToMSet Funs} :
    k <= exp_num_vars e1 ->
    InvCostBase (Post k Funs) (PreG Funs) H1 H2 rho1 rho2 e1 e2.
  Proof.
    unfold InvCostBase, Post, PreG.
    intros Hleq1 H1' H2' rho1' rho2' c b1 b2  Heq1 Hinj1 Heq2 Hinj2 [Hs1 Hs2].
    split.
    + split. omega. eapply plus_le_compat.
      rewrite !Nat.mul_add_distr_l. rewrite mult_comm. simpl.
      rewrite <- plus_assoc. eapply le_plus_l. omega.
    + split. omega. omega.
  Qed.

  Lemma cc_approx_val_max_vars_value k j IP P b d v1 H1 v2 H2 :
    (Res (v1, H1)) ≺ ^ (k; j; IP; P; b; d) (Res (v2, H2)) -> 
    max_vars_value v1 = 0.
  Proof.
    intros Heq. destruct v1; try contradiction. reflexivity.
  Qed.
  
  Lemma cc_approx_val_max_vars_value_list k j IP P b d vs1 H1 vs2 H2 :
    Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k; j; IP; P; b; d) (Res (v2, H2))) vs1 vs2 -> 
    max_list_nat_with_measure max_vars_value 0 vs1 = 0.
  Proof.
    intros Heq. induction Heq; eauto.
    simpl.
    erewrite cc_approx_val_max_vars_value; [| eassumption ].
    eassumption.
  Qed.
  

  Lemma PostConstrCompat i j IP P Funs {_ : ToMSet Funs}
        b d H1 H2 rho1 rho2 x1 x2 c ys1 ys2 e1 e2 k :
    Forall2 (fun y1 y2 => cc_approx_var_env i j IP P b d H1 rho1 H2 rho2 y1 y2) ys1 ys2 -> 
    k <= length ys1 ->
    InvCtxCompat (Post k Funs) (Post 0 Funs)
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
                    cc_approx_var_env i j IP P (b2 ∘ b ∘ b1) (lift b2 ∘ d ∘ b1)
                                      H1' rho1' H2' rho2' y1 y2) in Hall.
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
        eapply plus_le_compat.
        eapply mult_le_compat_l. eapply plus_le_compat_l.
        unfold max_heap_exp.
        eapply Nat.max_le_compat; [| simpl; omega ]. 
        erewrite <- max_vars_heap_alloc_constr; try eassumption. reflexivity.
        simpl.       
        eapply cc_approx_val_max_vars_value_list. eassumption.
        rewrite NPeano.Nat.mul_add_distr_l.
        eapply le_plus_trans. rewrite mult_comm. simpl. omega.
      - split; eauto.
        
        eapply le_trans. eassumption.
        rewrite <- !plus_assoc. eapply plus_le_compat_l.
        eapply plus_le_compat_r.
        unfold max_heap_exp.
        eapply Nat.max_le_compat; [| simpl; omega ]. 
        erewrite <- max_vars_heap_alloc_constr; try eassumption. reflexivity.
        simpl. 
        eapply cc_approx_val_max_vars_value_list. eassumption.
        
        eapply le_trans.
        unfold max_heap_exp. simpl. 
        erewrite max_vars_heap_alloc_constr; try eassumption. simpl.
        eapply cc_approx_val_max_vars_value_list. eassumption.
        eapply plus_le_compat.
        eapply mult_le_compat_l.
        eapply plus_le_compat_l.
        unfold max_heap_exp.
        eapply Nat.max_le_compat; [| simpl; omega ]. 
        erewrite <- max_vars_heap_alloc_constr; try eassumption. reflexivity.
        simpl.       
        eapply cc_approx_val_max_vars_value_list. eassumption.
        eapply Nat.max_le_compat; [| simpl; omega ]. 
        erewrite <- max_vars_heap_alloc_constr; try eassumption. reflexivity.
        simpl.       
        eapply cc_approx_val_max_vars_value_list. eassumption.
    }
    intros y1 y2 Hin1 Hin2 Hcc.
    eapply cc_approx_var_env_heap_env_equiv; try eassumption.
    simpl; normalize_occurs_free...
    simpl; normalize_occurs_free...
  Qed.
  
  Lemma PreConstrCompat i j IP P Funs {_ : ToMSet Funs}
        b d H1 H2 rho1 rho2 x1 x2 c ys1 ys2 e1 e2 :
    Forall2 (fun y1 y2 => cc_approx_var_env i j IP P b d H1 rho1 H2 rho2 y1 y2) ys1 ys2 -> 
    IInvCtxCompat (PreG Funs) (PreG Funs)
                 H1 H2 rho1 rho2 (Econstr_c x1 c ys1 Hole_c) (Econstr_c x2 c ys2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold IInvCtxCompat, PreG.
    intros Hall H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1' c2'
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 [Hm1 Hm2] Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H13. inv H16.
    assert (Hlen := Forall2_length _ _ _ Hall).
    eapply Forall2_monotonic_strong
      with (R' := fun y1 y2 : var =>
                    cc_approx_var_env i j IP P (b2 ∘ b ∘ b1) (lift b2 ∘ d ∘ b1) H1' rho1' H2' rho2' y1 y2) in Hall.
    { edestruct cc_approx_var_env_getlist as [vs2' [Hget2' Hcc]]; try eassumption.
      split.
      - simpl in Hm1.
        unfold size_heap in *.
        erewrite HL.size_with_measure_alloc; [| reflexivity | eassumption ].
        erewrite (HL.size_with_measure_alloc _ _ _ _ H2''); [| reflexivity | eassumption ].
        simpl size_val.
        erewrite <- (getlist_length_eq _ vs); eauto.
        erewrite <- (getlist_length_eq _ vs0); eauto.
        rewrite <- plus_assoc, (plus_comm (S (length _))), plus_assoc.
        eapply plus_le_compat. omega.
        replace (@length M.elt ys1) with (@length var ys1) by reflexivity.
        replace (@length M.elt ys2) with (@length var ys2) by reflexivity.
        omega. 
      - unfold size_heap in *.
        erewrite (HL.size_with_measure_alloc _ _ _ _ H1''); [| reflexivity | eassumption ].
        erewrite (HL.size_with_measure_alloc _ _ _ _ H2''); [| reflexivity | eassumption ].
        simpl size_val in *. 
        rewrite NPeano.Nat.mul_add_distr_r.
        rewrite <- plus_assoc, (plus_comm (S (length _))), plus_assoc.
        eapply plus_le_compat.
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

  
  Lemma PostProjCompat Funs {_ : ToMSet Funs} H1 H2 rho1 rho2 x1 x2 c n y1 y2 e1 e2 k :
    k <= 1 ->
    InvCtxCompat (Post k Funs) (Post 0 Funs)
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
      rewrite <- (plus_assoc).
      eapply le_trans.
      eapply plus_le_compat; [| reflexivity ]. eassumption.
      rewrite <- !plus_assoc. 
      eapply plus_le_compat. eapply mult_le_compat_l. eapply plus_le_compat_l.
      unfold max_heap_exp.
      eapply Nat.max_le_compat. reflexivity. simpl. omega.
      rewrite Nat.mul_1_l. eapply le_trans. eapply plus_le_compat_l.
      eapply plus_le_compat_l. eassumption. omega.
    - split; eauto. 
  Qed.
  
  Lemma PreProjCompat Funs {_ : ToMSet Funs} H1 H2 rho1 rho2 x1 x2 c n y1 y2 e1 e2  :
    IInvCtxCompat (PreG Funs) (PreG Funs)
                  H1 H2 rho1 rho2 (Eproj_c x1 c n y1 Hole_c) (Eproj_c x2 c n y2 Hole_c) e1 e2.
  Proof.
    unfold IInvCtxCompat, PreG.
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
        Scope Scope' Funs c Γ FVs x C1 :
    project_var Util.clo_tag Scope Funs c Γ FVs x C1 Scope' ->
    cost_ctx_full C1 <= 3.
  Proof.
    intros Hvar; inv Hvar; eauto.
  Qed.

  Instance ToMSet_Intersection (S1 : Ensemble positive) `{ToMSet S1}
           (S2 : Ensemble positive) `{ToMSet S2} : ToMSet (S1 :&: S2).
  Proof.
    destruct H as [m1 Hm1]; destruct H0 as [m2 Hm2].
    eexists (PS.inter m1 m2).
    split.
    - intros x H. destruct H as [y Hs1 Hs2].  
      eapply FromSet_complete. reflexivity.
      eapply PS.inter_spec. split.
      eapply FromSet_sound. eapply Hm1; eauto. eassumption. 
      eapply FromSet_sound. eapply Hm2; eauto. eassumption. 
    - intros x H.
      eapply FromSet_sound in H; [| reflexivity ].
      eapply PS.inter_spec in H. inv H. constructor.
      eapply FromSet_complete. eapply Hm1; eauto. eassumption. 
      eapply FromSet_complete. eapply Hm2; eauto. eassumption. 
  Qed.


  Lemma project_var_cost_alloc_eq
        Scope {_ : ToMSet Scope} Scope' {_ : ToMSet Scope'} Funs `{ToMSet (Proj1 Funs)}
        c Γ FVs x C1 :
    project_var Util.clo_tag Scope Funs c Γ FVs x C1 Scope' ->
    cost_alloc_ctx_CC C1 = 3 * PS.cardinal (@mset (Proj1 Funs :&: (Scope' \\ Scope)) _).
  Proof.
    intros Hvar; inv Hvar; eauto.
    - rewrite (Proper_carinal _ PS.empty).
      reflexivity.
      eapply Same_set_From_set.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set, Intersection_Empty_set_abs_r.
      rewrite FromSet_empty. reflexivity.
    - simpl cost_ctx_full.
      rewrite (Proper_carinal _ (PS.singleton x)).
      reflexivity.
      eapply Same_set_From_set.
      rewrite FromSet_singleton.
      rewrite <- mset_eq. rewrite Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite Setminus_Disjoint, Intersection_commut, Intersection_Same_set.
      reflexivity.
      eapply Singleton_Included.
      eapply prod_Proj1. eassumption. 
      eapply Disjoint_Singleton_l; eassumption.
    - rewrite (Proper_carinal _ PS.empty).
      simpl. reflexivity.
      eapply Same_set_From_set.
      rewrite FromSet_empty.
      rewrite <- mset_eq.
      rewrite Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite Setminus_Disjoint, Intersection_Disjoint.
      reflexivity.
      eapply Disjoint_Singleton_r. eassumption. 
      eapply Disjoint_Singleton_l. eassumption. 
  Qed.

  Definition disjoint (s1 s2 : PS.t) : Prop :=
    PS.Equal (PS.inter s1 s2) PS.empty.

  Lemma disjoint_spec (s1 s2 : PS.t) x :
    disjoint s1 s2 ->
    PS.In x s1->
    ~ PS.In x s2.
  Proof.
    intros Hd Hin1 Hin2.
    assert (Hin3 : PS.In x (PS.inter s1 s2)).
    { eapply PS.inter_spec; eauto. }
    unfold disjoint in Hd. rewrite Hd in Hin3.
    inv Hin3.
  Qed.

  Lemma disjoint_spec' (s1 s2 : PS.t) x :
    disjoint s1 s2 ->
    PS.In x s2 ->
    ~ PS.In x s1.
  Proof.
    intros Hd Hin1 Hin2.
    assert (Hin3 : PS.In x (PS.inter s1 s2)).
    { eapply PS.inter_spec; eauto. }
    unfold disjoint in Hd. rewrite Hd in Hin3.
    inv Hin3.
  Qed.

  Lemma FromSet_intersection (s1 s2 : PS.t) : 
    FromSet (PS.inter s1 s2) <--> FromSet s1 :&: FromSet s2. 
  Proof.
    split; intros x Hin.
    eapply FromSet_sound in Hin; [| reflexivity ].
    eapply PS.inter_spec in Hin. destruct Hin as [Hin1 Hin2].
    constructor; (eapply FromSet_complete; [ reflexivity | eassumption ]). 
    inv Hin.
    eapply FromSet_complete. reflexivity.
    eapply PS.inter_spec.
    split; (eapply FromSet_sound; [ reflexivity | eassumption ]).
  Qed. 
    
  Lemma FromSet_disjoint (s1 s2 : PS.t) : 
    disjoint s1 s2 <-> Disjoint _ (FromSet s1) (FromSet s2). 
  Proof.
    split; intros Hd.
    - constructor. intros x Hin.
      eapply FromSet_intersection in Hin.
      unfold disjoint in Hd. rewrite Hd in Hin.
      eapply FromSet_empty in Hin. inv Hin.
    - inv Hd. unfold disjoint. intros y.
      specialize (H y). split; intros Hin; [| now inv Hin ].
      exfalso. eapply H.
      eapply FromSet_intersection.
      eapply FromSet_complete; [| eassumption ].
      reflexivity.
  Qed.

  Lemma PS_union_elements s1 s2 :
    disjoint s1 s2 -> 
    Permutation (PS.elements s1 ++ PS.elements s2) (PS.elements (PS.union s1 s2)).
  Proof.
    intros Hnin. 
    eapply NoDup_Permutation.
    - eapply NoDup_app.
      eapply NoDupA_NoDup. now eapply PS.elements_spec2w.
      eapply NoDupA_NoDup. now eapply PS.elements_spec2w.
      eapply FromSet_disjoint. eassumption.      
    - eapply NoDupA_NoDup. eapply PS.elements_spec2w.
    - intros y. split.
      + intros Hin.
        eapply InA_In.
        eapply PS.elements_spec1. eapply PS.union_spec. 
        eapply Coqlib.in_app in Hin. 
        inv Hin.
        * left. eapply PS.elements_spec1.
          eapply In_InA. eauto with typeclass_instances.
          eassumption.
        * right. eapply PS.elements_spec1.
          eapply In_InA. eauto with typeclass_instances.
          eassumption.
      + intros HIn.
        eapply In_InA in HIn. 
        eapply PS.elements_spec1 in HIn. 
        eapply PS.union_spec in HIn.
        eapply Coqlib.in_app.
        inv HIn.
        * left. eapply InA_In. eapply PS.elements_spec1.
          eassumption. 
        * right. eapply InA_In. eapply PS.elements_spec1.
          eassumption.
        * eauto with typeclass_instances.
  Qed. 
  
  Lemma PS_cardinal_union s1 s2 :
    disjoint s1 s2 -> 
    PS.cardinal s1 + PS.cardinal s2 = PS.cardinal (PS.union s1 s2).
  Proof.
    intros Hd.
    rewrite !PS.cardinal_spec.
    erewrite (@Permutation_length _ (PS.elements (PS.union s1 s2))).
    rewrite <- app_length. reflexivity.
    symmetry. eapply PS_union_elements. eassumption.
  Qed.

  Lemma Same_set_Intersection_compat {A : Type} (s1 s2 s3 s4 : Ensemble A):
    s1 <--> s2 -> s3 <--> s4 -> s1 :&: s3 <--> s2 :&: s4.
  Proof.
    intros H1 H2; split; eapply Included_Intersection_compat;
    (try now apply H1); try now apply H2.
  Qed.  

  Lemma Disjoint_Intersection_r {A} (s1 s2 s3 : Ensemble A) :
    Disjoint _ s2 s3 -> 
    Disjoint _ (s1 :&: s2) (s1 :&: s3).
  Proof with (now eauto with Ensembles_DB).
    intros Hd. 
    eapply Disjoint_Included; [| | eassumption ];
    now eapply Included_Intersection_r.
  Qed. 

  Lemma Setminus_compose {A} (s1 s2 s3 : Ensemble A) `{Decidable _ s2} :
    s1 \subset s2 ->
    s2 \subset s3 ->
    s2 \\ s1 :|: (s3 \\ s2) <--> s3 \\ s1.
  Proof.
    intros H1 H2; split; intros x Hin.
    - inv Hin.
      + inv H0. constructor; eauto.
      + inv H0. constructor; eauto.
    - inv Hin. destruct H as [Hdec].
      destruct (Hdec x).
      + left. constructor; eauto.
      + right. constructor; eauto.
  Qed.

  
  Lemma project_var_ToMSet Scope1 Scope2 `{ToMSet Scope1} Funs
        c Γ FVs y C1 :
    project_var Util.clo_tag Scope1 Funs c Γ FVs y C1 Scope2 ->
    ToMSet Scope2.
  Proof.
    intros Hvar.
    assert (Hd1 := H).  eapply Decidable_ToMSet in Hd1. 
    destruct Hd1 as [Hdec1].
    destruct (Hdec1 y).
    - assert (Scope1 <--> Scope2).
      { inv Hvar; eauto; try reflexivity.
        now exfalso; eauto. now exfalso; eauto. }
      eapply ToMSet_Same_set; eassumption.
    - assert (y |: Scope1 <--> Scope2).
      { inv Hvar; try reflexivity.
        exfalso; eauto. }
      eapply ToMSet_Same_set; try eassumption.
      eauto with typeclass_instances.
  Qed. 
    
  Lemma project_vars_cost_alloc_eq
        Scope `{ToMSet Scope} Scope' `{ToMSet Scope'} Funs `{ToMSet (Proj1 Funs)}
        c Γ FVs xs C1 :
    project_vars Util.clo_tag Scope Funs c Γ FVs xs C1 Scope' ->
    cost_alloc_ctx_CC C1 = 3 * PS.cardinal (@mset (Proj1 Funs :&: (Scope' \\ Scope)) _).
  Proof with (now eauto with Ensembles_DB).
    intros Hvar; induction Hvar; eauto.
    - rewrite (Proper_carinal _ PS.empty).
      reflexivity.
      eapply Same_set_From_set.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set, Intersection_Empty_set_abs_r.
      rewrite FromSet_empty. reflexivity.
    - assert (Hvar' := H2). assert (Hvar'' := H2).
      eapply project_var_ToMSet in Hvar''; eauto. 
      rewrite cost_alloc_ctx_CC_comp_ctx_f. 
      eapply (@project_var_cost_alloc_eq Scope1 H Scope2 Hvar'' Funs H1) in H2.
      erewrite H2. erewrite IHHvar; eauto.
      rewrite <- NPeano.Nat.mul_add_distr_l.
      eapply Nat_as_OT.mul_cancel_l. omega.
      rewrite PS_cardinal_union. 
      eapply Proper_carinal.  
      eapply Same_set_From_set. setoid_rewrite <- mset_eq.
      rewrite FromSet_union.
      do 2 setoid_rewrite <- mset_eq at 1.
      rewrite !(Intersection_commut _ (Proj1 Funs)).
      rewrite <- Intersection_Union_distr.
      eapply Same_set_Intersection_compat; [| reflexivity ].
      eapply Setminus_compose. now eauto with typeclass_instances. 
      eapply project_var_Scope_l. eassumption.
      eapply project_vars_Scope_l. eassumption.
      eapply FromSet_disjoint.
      do 2 setoid_rewrite <- mset_eq at 1.
      eapply Disjoint_Intersection_r.
      eapply Disjoint_Setminus_r...
  Qed.          
      
  Lemma project_vars_cost 
       Scope Scope' Funs c Γ FVs xs C1 :
    project_vars Util.clo_tag Scope Funs c Γ FVs xs C1 Scope' ->
    cost_ctx_full C1 <= 3 * length xs.
  Proof.
    intros Hvar. induction Hvar; simpl; eauto.
    rewrite cost_ctx_full_ctx_comp_ctx_f.
    eapply project_var_cost in H. omega.
  Qed.
  
  Lemma project_var_cost_alloc
        Scope Scope' Funs c Γ FVs x C1 :
    project_var Util.clo_tag Scope Funs c Γ FVs x C1 Scope' ->
    cost_alloc_ctx C1 <= 3.
  Proof.
    intros Hvar; inv Hvar; eauto.
  Qed.
  
  Lemma project_vars_cost_alloc
        Scope Scope' Funs c Γ FVs xs C1 :
    project_vars Util.clo_tag Scope Funs c Γ FVs xs C1 Scope' ->
    cost_alloc_ctx C1 <= 3 * length xs.
  Proof.
    intros Hvar. induction Hvar; eauto.
    simpl. rewrite cost_alloc_ctx_comp_ctx_f.
    eapply project_var_cost_alloc in H. omega. 
  Qed.

  Lemma Same_set_Intersection_Setminus {A: Type} (S1 S2 S3 : Ensemble A)
        {_ : Decidable S3}:
    S2 \subset S3 ->
    S1 :&: (S3 \\ S2) :|: (S1 \\ S3) <--> S1 \\ S2.
  Proof.
    intros Hsub; split; intros x Hin; inv Hin.
    - inv H. inv H1. constructor; eauto.
    - inv H; constructor; eauto.
    - destruct X as [Hdec]. destruct (Hdec x).
      + left. constructor; eauto.
        constructor; eauto.
      + right. constructor; eauto.
  Qed.

  Lemma PreCtxCompat_var_r H1 H2 rho1 rho2 C e1 e2
        Scope `{ToMSet Scope} Scope' `{ToMSet Scope'} Funs {_ : ToMSet (Proj1 Funs)}
        c Γ FVs x :
    project_var Util.clo_tag Scope Funs c Γ FVs x C Scope' ->
    IInvCtxCompat_r (PreG (Proj1 Funs \\ Scope)) (PreG (Proj1 Funs \\ Scope')) H1 H2 rho1 rho2 C e1 e2.
  Proof.
    intros Hvar.
    unfold IInvCtxCompat_r, PreG.
    intros H1' H2' H2'' rho1' rho2' rho2'' c1'
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx.
    erewrite (ctx_to_heap_env_CC_size_heap _ _ _ H2' H2''); [| eassumption ].
    erewrite (project_var_cost_alloc_eq Scope Scope'); [| eassumption ].
    rewrite <- plus_assoc, <- NPeano.Nat.mul_add_distr_l.
    rewrite PS_cardinal_union. 
    rewrite Proper_carinal. eassumption. 
    eapply Same_set_From_set. setoid_rewrite <- mset_eq.
    rewrite FromSet_union. rewrite <- !mset_eq at 1.
    eapply Same_set_Intersection_Setminus. eapply Decidable_ToMSet. eassumption.
    eapply project_var_Scope_l. eassumption.
    eapply FromSet_disjoint.
    do 2 setoid_rewrite <- mset_eq at 1.
    eapply Disjoint_Setminus_r.
    eapply Included_trans. eapply Included_Intersection_r.
    now eauto with Ensembles_DB.
  Qed.

  
  Lemma PostCtxCompat_var_r Funs {Hf : ToMSet (Proj1 Funs)} H1 H2 rho1 rho2 C e1 e2
        Scope Scope' c Γ FVs x :
    project_var Util.clo_tag Scope Funs c Γ FVs x C Scope' ->
    InvCtxCompat_r (Post 0 (Proj1 Funs))
                   (Post (cost_ctx_full C) (Proj1 Funs)) H1 H2 rho1 rho2 C e1 e2.
  Proof.
    unfold InvCtxCompat_r, Post.
    intros Hvar H1' H2' H2'' rho1' rho2' rho2'' c' c1 c2 m1 m2 
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx'.
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx').
    subst.  
    assert (Heq := project_var_cost _ _ _ _ _ _ _ _ Hvar).  
    unfold Post in *. omega.
  Qed.
  
  Lemma PreCtxCompat_vars_r  H1 H2 rho1 rho2 C e1 e2
        Scope `{ToMSet Scope} Scope' `{ToMSet Scope'} Funs `{ToMSet (Proj1 Funs)}
        c Γ FVs xs :
    project_vars Util.clo_tag Scope Funs c Γ FVs xs C Scope' ->
    IInvCtxCompat_r (PreG (Proj1 Funs \\ Scope)) (PreG (Proj1 Funs \\ Scope')) H1 H2 rho1 rho2 C e1 e2.
  Proof.
    intros Hvar.
    unfold IInvCtxCompat_r, PreG.
    intros H1' H2' H2'' rho1' rho2' rho2'' c1'
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx. subst. eauto. 
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx).
    subst.  
    assert (Heq := project_vars_cost _ _ _ _ _ _ _ _ Hvar).  
    erewrite (ctx_to_heap_env_CC_size_heap _ _ _ H2' H2''); [| eassumption ].
    erewrite (project_vars_cost_alloc_eq Scope Scope'); [| eassumption ].
    rewrite <- plus_assoc, <- NPeano.Nat.mul_add_distr_l.
    rewrite PS_cardinal_union. 
    rewrite Proper_carinal. eassumption. 
    eapply Same_set_From_set. setoid_rewrite <- mset_eq.
    rewrite FromSet_union. rewrite <- !mset_eq at 1.
    eapply Same_set_Intersection_Setminus. eapply Decidable_ToMSet. eassumption.
    eapply project_vars_Scope_l. eassumption.
    eapply FromSet_disjoint.
    do 2 setoid_rewrite <- mset_eq at 1.
    eapply Disjoint_Setminus_r.
    eapply Included_trans. eapply Included_Intersection_r.
    now eauto with Ensembles_DB.
  Qed.

  Lemma PostCtxCompat_vars_r H1 H2 rho1 rho2 C e1 e2
        Scope Scope' Funs `{ToMSet (Proj1 Funs)} c Γ FVs xs :
    project_vars Util.clo_tag Scope Funs c Γ FVs xs C Scope' ->
    InvCtxCompat_r (Post 0 (Proj1 Funs)) (Post (cost_ctx_full C) (Proj1 Funs)) H1 H2 rho1 rho2 C e1 e2.
  Proof.
    unfold InvCtxCompat_r, PreG.
    intros Hvar H1' H2' H2'' rho1' rho2' rho2'' c' c1 c2 m1 m2 
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx'.
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx').
    subst.
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx').
    subst.  
    assert (Heq := project_vars_cost _ _ _ _ _ _ _ _ Hvar).  
    unfold Post in *. omega.
  Qed.

  Lemma PostGC k : (InvGC (fun i => Post k)).
  Proof.
    unfold InvGC, Post. 
    intros H1 H1' H2 H2' rho1 rho2 e1 e2 Funs Hf c1 c2 m1 m2 _ (* TODO remove *)
           [[Hm1 Hm2] [Hc1 Hc2]] Hl1 Hl2.
    eapply max_heap_GC in Hl1.
    split.
    - split. omega.
      eapply le_trans. eassumption.
      eapply plus_le_compat_r.
      eapply mult_le_compat_l.
      eapply plus_le_compat_l.
      unfold max_heap_exp.
      eapply NPeano.Nat.max_le_compat_r. eassumption.
    - split.
      + eapply le_trans. eassumption.
        eapply plus_le_compat.
        eapply plus_le_compat_l.
        eapply NPeano.Nat.max_le_compat_r. eassumption.
        reflexivity.
      + rewrite <- plus_assoc, (plus_comm (max_heap_exp _ _)), plus_assoc.
        eapply plus_le_compat_r. eapply Nat.add_le_mono_r.
        rewrite <- plus_assoc, (plus_comm (3 * PS.cardinal mset)), plus_assoc.
        eapply le_trans. eassumption.
        eapply plus_le_compat_r. eapply mult_le_compat_l.
        eapply plus_le_compat_l.
        unfold max_heap_exp.
        eapply NPeano.Nat.max_le_compat_r. eassumption.
  Qed.
  
  Lemma fun_in_fundefs_exp_num_vars B f tau xs e: 
    fun_in_fundefs B (f, tau, xs, e) ->
    exp_num_vars e <= fundefs_num_vars B.
  Proof.
    induction B; intros Hin; inv Hin.
    - inv H. simpl. omega.
    - eapply le_trans. eapply IHB. eassumption.
      simpl. omega. 
  Qed.

  Opaque max. 

  Lemma exp_max_vars_exp_num_vars e :
    exp_max_vars e <= exp_num_vars e.
  Proof.
    revert e. eapply exp_ind'; intros; try (simpl; omega).
    simpl. 
    eapply NPeano.Nat.max_lub.
    omega. omega. 
  Qed.

  Lemma numOf_fundefs_fundefs_num_vars_le B1 :
    numOf_fundefs B1 <= fundefs_num_vars B1.
  Proof.
    induction B1; eauto. simpl. omega.
  Qed.
  
  Lemma PostAppCompat i j IP P Funs {_ : ToMSet Funs}
        b d H1 H2 rho1 rho2 f1 t xs1 f2 xs2 f2' Γ k :
    Forall2 (fun y1 y2 => cc_approx_var_env i j IP P b d H1 rho1 H2 rho2 y1 y2) (f1 :: xs1) (f2 :: xs2) -> 
    k <= S (length xs1) ->
    ~ Γ \in FromList xs2 ->
    ~ f2' \in FromList xs2 ->
    IInvAppCompat Util.clo_tag (fun i => Post 0) (Post k Funs) (PreG Funs)
                  H1 H2 rho1 rho2 f1 t xs1 f2 xs2 f2' Γ.
  Proof.
    unfold IInvAppCompat, PreG, Post.
    intros Hall Hk Hnin1 Hnin2 _ H1' H1'' H2'
           rhoc1 rhoc2 rhoc3 rho1' rho2' rho2''
           b1 b2 B1 f1' ct1 xs1' e1 l1 vs1 B
           f3 c ct2 xs2' e2 l2 env_loc2 vs2 c1 c2 m1 m2
           Heq1 Hinj1 Heq2 Hinj2
           [[Hc1 Hc2] [Hm1 Hm2]] [Hh1 Hh2]
           Hgetf1 Hgetl1 Hfind1 Hgetxs1 Hclo Hset1
           Hgetf2 Hgetxs2 Hset2 Hgetl2 Hfind2.
    eapply Forall2_monotonic_strong
      with (R' := fun y1 y2 : var =>
                    cc_approx_var_env i j IP P (b2 ∘ b ∘ b1) _
                                      H1' rho1' H2' rho2' y1 y2) in Hall.
    assert (Hlen := Forall2_length _ _ _ Hall). inversion Hlen as [Hlen']. 
    { rewrite <- !plus_n_O in *. 
      rewrite !Hlen' in *.
      split.
      - split.
        + simpl. omega.
        + simpl cost in *.
          rewrite <- !plus_assoc. eapply le_trans.
          eapply plus_le_compat_r. eassumption.
          simpl exp_num_vars.
          replace (c1 * (4 + max_heap_exp H1'' e1) + exp_num_vars e1 +
                   (1 + (1 + (S (S (length xs2)) + k))))
          with ((c1 * (4 + max_heap_exp H1'' e1) + (exp_num_vars e1 + 4 + length xs2)) + k) by ring.
          replace ((c1 + S (length xs1)) * (4 + max_heap_exp H1' (Eapp f1 t xs1)) +
                   S (length xs1))
          with ((c1 * (4 + max_heap_exp H1' (Eapp f1 t xs1)) +
                 (max_heap_exp H1' (Eapp f1 t xs1) + 4 + length xs1) +
                 S (length xs1)) +
                (3 * (length xs1) + (length xs1) * (max_heap_exp H1' (Eapp f1 t xs1)))) by ring.
          eapply le_trans; [| eapply le_plus_l ].
          eapply plus_le_compat.
          eapply plus_le_compat. 

          eapply mult_le_compat_l.
          eapply plus_le_compat_l.
          eapply le_trans; [| eapply Max.le_max_l].
          eapply Max.max_lub.
          erewrite <- max_vars_heap_def_closures; try eassumption. reflexivity.
          eapply max_vars_heap_get. eassumption.
          eapply le_trans; [| eapply max_vars_heap_get; now apply Hgetl1 ].
          simpl.
          eapply le_trans.
          eapply exp_max_vars_exp_num_vars.
          eapply le_trans. 
          eapply fun_in_fundefs_exp_num_vars.
          eapply find_def_correct. eassumption.
          simpl. omega.
          rewrite Hlen'.
          eapply plus_le_compat_r. eapply plus_le_compat_r. 
          eapply le_trans; [| eapply Max.le_max_l].
          eapply le_trans; [| eapply max_vars_heap_get; now apply Hgetl1 ].
          eapply le_trans. 
          eapply fun_in_fundefs_exp_num_vars.
          eapply find_def_correct. eassumption.
          simpl. omega.
          omega.
      - erewrite def_closures_size; try eassumption.
        unfold mset in *.
        destruct (ToMSet_name_in_fundefs B1) as [funsB HeqB].
        split.
        + rewrite <- !Max.plus_max_distr_r.
          eapply NPeano.Nat.max_le_compat.
          * eapply le_trans. eassumption.
            unfold mset at 1. 
            
            eapply plus_le_compat_r. eapply plus_le_compat_r. eapply plus_le_compat_l.
          eapply Max.max_lub.
          eapply le_trans; [| eapply Max.le_max_l ]. 
          erewrite <- max_vars_heap_def_closures; try eassumption. reflexivity.
          eapply max_vars_heap_get. eassumption.
          eapply le_trans; [| eapply Max.le_max_l].
          eapply le_trans; [| eapply max_vars_heap_get; now apply Hgetl1 ].
          eapply le_trans.
          eapply exp_max_vars_exp_num_vars.
          eapply le_trans. 
          eapply fun_in_fundefs_exp_num_vars.
          eapply find_def_correct. eassumption.
          simpl. omega.
          rewrite <- !plus_assoc, (plus_comm (max_heap_exp _ _)), !plus_assoc. 
          eapply plus_le_compat. eassumption.
          eapply le_trans; [| eapply Max.le_max_l].
          eapply le_trans; [| eapply max_vars_heap_get; now apply Hgetl1 ].
          simpl.
          eapply le_trans. eapply  numOf_fundefs_fundefs_num_vars_le.
          omega. 
        + rewrite <- !plus_assoc, (plus_comm (max_heap_exp _ _)), !plus_assoc. 
          eapply plus_le_compat_r. rewrite <- !NPeano.Nat.mul_max_distr_r.
          rewrite <- !Max.plus_max_distr_r.
          eapply NPeano.Nat.max_le_compat.
          eapply le_trans. eapply Nat.add_le_mono_r in Hm2. eassumption.
          eapply mult_le_compat_l.
          eapply plus_le_compat_l.
          eapply le_trans; [| eapply Max.le_max_l].
          eapply Max.max_lub.
          erewrite <- max_vars_heap_def_closures; try eassumption. reflexivity.
          eapply max_vars_heap_get. eassumption.
          eapply le_trans; [| eapply max_vars_heap_get; now apply Hgetl1 ].
          eapply le_trans.
          eapply exp_max_vars_exp_num_vars.
          eapply le_trans. 
          eapply fun_in_fundefs_exp_num_vars.
          eapply find_def_correct. eassumption.
          simpl. omega.
          eapply le_trans. eassumption.
          eapply mult_le_compat_r.
          erewrite (def_closures_size _ _ _ H1' _ H1''); try eassumption.
          omega. }
    { intros y1 y2 Hin1 Hin2 Hcc.
      eapply cc_approx_var_env_heap_env_equiv; try eassumption.
      now inv Hin1; eauto.
      unfold AppClo. repeat normalize_occurs_free.
      inv Hin2; eauto. 
      right. constructor. right. constructor.
      left. rewrite FromList_cons. right. eassumption.
      intros Hc. eapply Hnin1. inv Hc; eauto.
      intros Hc. eapply Hnin2. inv Hc; eauto.  }
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
  

  Lemma occurs_free_cardinality_mut :
    (forall e FVs,
       FromList FVs \subset occurs_free e ->
       NoDup FVs ->
       length FVs <= exp_num_vars e) /\
    (forall B FVs,
       FromList FVs \subset occurs_free_fundefs B ->
       NoDup FVs ->
       length FVs <= fundefs_num_vars B).
  Proof.
    exp_defs_induction IHe IHl IHb; intros FVs Heq Hnd;
    try repeat normalize_occurs_free_in_ctx; simpl.
    - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
      eassumption.
      rewrite <- HP in Hnd.
      eapply Permutation_length in HP. rewrite <- HP.
      rewrite app_length.
      eapply (Included_trans (FromList l2) (Setminus var (occurs_free e) [set v])) in Hin2;
        [| now apply Setminus_Included ].
      eapply Same_set_FromList_length in Hin1.
      eapply IHe in Hin2. omega.
      eapply NoDup_cons_r; eauto. 
      eapply NoDup_cons_l; eauto.
    - rewrite <- (Union_Empty_set_neut_r [set v]) in Heq.
      rewrite <- FromList_nil, <- FromList_cons in Heq.
      eapply Same_set_FromList_length in Heq; eauto.
    - rewrite Union_commut, <- Union_assoc, (Union_commut (occurs_free (Ecase v l))),
      (Union_Same_set [set v]) in Heq.
      edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
      eassumption.
      rewrite <- HP in Hnd.
      eapply Permutation_length in HP. rewrite <- HP.
      rewrite !app_length.
      eapply IHe in Hin1. eapply IHl in Hin2. simpl in *. omega.
      eapply NoDup_cons_r; eauto. 
      eapply NoDup_cons_l; eauto.
      eapply Singleton_Included. eauto.
    - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
      eassumption.
      rewrite <- HP in Hnd.
      eapply Permutation_length in HP. rewrite <- HP.
      rewrite app_length.
      eapply (Included_trans (FromList l2) (Setminus var (occurs_free e) [set v])) in Hin2;
        [| now apply Setminus_Included ].
      rewrite <- (Union_Empty_set_neut_r [set v0]) in Hin1.
      rewrite <- FromList_nil, <- FromList_cons in Hin1.
      eapply Same_set_FromList_length in Hin1.
      eapply IHe in Hin2. simpl in *. omega.
      eapply NoDup_cons_r; eauto. 
      eapply NoDup_cons_l; eauto.
    - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
      eassumption.
      rewrite <- HP in Hnd.
      eapply Permutation_length in HP. rewrite <- HP.
      rewrite app_length.
      eapply (Included_trans (FromList l2) (Setminus var (occurs_free e) _)) in Hin2;
        [| now apply Setminus_Included ].
      eapply IHb in Hin1. eapply IHe in Hin2. omega.
      eapply NoDup_cons_r; eauto. 
      eapply NoDup_cons_l; eauto.
    - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
      eassumption. rewrite <- HP in Hnd.
      eapply Same_set_FromList_length in Hin1; eauto.
      eapply Permutation_length in HP. rewrite <- HP.
      rewrite app_length.
      rewrite <- (Union_Empty_set_neut_r [set v]) in Hin2.
      rewrite <- FromList_nil, <- FromList_cons in Hin2.
      eapply Same_set_FromList_length in Hin2.
      simpl in *. omega.
      eapply NoDup_cons_r; eauto. 
      eapply NoDup_cons_l; eauto.
    - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
      eassumption.
      rewrite <- HP in Hnd.
      eapply Permutation_length in HP. rewrite <- HP.
      rewrite app_length.
      eapply (Included_trans (FromList l2) (Setminus var (occurs_free e) [set v])) in Hin2;
        [| now apply Setminus_Included ].
      eapply Same_set_FromList_length in Hin1.
      eapply IHe in Hin2. omega.
      eapply NoDup_cons_r; eauto. 
      eapply NoDup_cons_l; eauto.
    - rewrite occurs_free_Ehalt in Heq.
      rewrite <- (Union_Empty_set_neut_r [set v]) in Heq.
      rewrite <- FromList_nil, <- FromList_cons in Heq.
      eapply Same_set_FromList_length in Heq; eauto.
    - edestruct (@FromList_Union_split var) as [l1 [l2 [HP [Hin1 Hin2]]]].
      eassumption. rewrite <- HP in Hnd.
      eapply Permutation_length in HP. rewrite <- HP.
      rewrite app_length.
      eapply (Included_trans (FromList l2) (Setminus var _ [set v])) in Hin2;
        [| now apply Setminus_Included ].
      eapply (Included_trans (FromList l1) (Setminus var _ _)) in Hin1;
        [| now apply Setminus_Included ]. 
      eapply IHe in Hin1. eapply IHb in Hin2. omega.
      eapply NoDup_cons_r; eauto. 
      eapply NoDup_cons_l; eauto.
    - rewrite <- FromList_nil in Heq.
      apply Same_set_FromList_length in Heq; eauto.
  Qed.


  Corollary occurs_free_cardinality :
    (forall e FVs,
       FromList FVs \subset occurs_free e ->
       NoDup FVs ->
       length FVs <= exp_num_vars e).
  Proof.
    eapply occurs_free_cardinality_mut.
  Qed.

  Corollary occurs_free_fundefs_cardinality :
    (forall B FVs,
       FromList FVs \subset occurs_free_fundefs B ->
       NoDup FVs ->
       length FVs <= fundefs_num_vars B).
  Proof.
    eapply occurs_free_cardinality_mut.
  Qed.

End Size.