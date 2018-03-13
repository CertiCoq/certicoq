From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions.

From L6.Heap Require Import heap heap_defs cc_log_rel
     closure_conversion closure_conversion_util.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega.

Require Import compcert.lib.Maps.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module Defs := HeapDefs .

Module Size (H : Heap).

  (* This is stupid. Find out how to use modules correctly. *)
  Module LR := CC_log_rel H.

  Import H LR LR.Sem LR.Sem.Equiv LR.Sem.Equiv.Defs.

  (** * Size of CPS terms, values and environments, needed to express the upper bound on the execution cost of certain transformations *)
  
  (** The size of CPS expressions. Right now we only count the number of
   * variables in a program (free or not), the number of functions and
   * the number of function definition blocks *)
  (* TODO -- max per function block *)
  Fixpoint sizeOf_exp (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => length ys + sizeOf_exp e
      | Ecase x l =>
        1 + (fix sizeOf_l l :=
               match l with
                 | [] => 0
                 | (t, e) :: l => sizeOf_exp e + sizeOf_l l
               end) l
      | Eproj x _ _ y e => 1 + sizeOf_exp e
      | Efun B e => 1 + sizeOf_fundefs B + sizeOf_exp e
      | Eapp x _ ys => 1 + length ys
      | Eprim x _ ys e => length ys + sizeOf_exp e
      | Ehalt x => 1
    end
  with sizeOf_fundefs (B : fundefs) : nat := 
         match B with
           | Fcons _ _ xs e B =>
             1 + sizeOf_exp e + sizeOf_fundefs B
           | Fnil => 0
         end.

  (** The size of evaluation contexts *)
  Fixpoint sizeOf_exp_ctx (c : exp_ctx) : nat :=
    match c with
      | Hole_c => 0
      | Econstr_c _ _ ys c => 1 + length ys + sizeOf_exp_ctx c
      | Eproj_c _ _ _ _ c => 1 + sizeOf_exp_ctx c
      | Eprim_c _ _ ys c => length ys + sizeOf_exp_ctx c
      | Ecase_c _ l1 _ c l2  =>
        1 + sizeOf_exp_ctx c
        + fold_left (fun s p => s + sizeOf_exp (snd p)) l1 0
        + fold_left (fun s p => s + sizeOf_exp (snd p)) l2 0 
      | Efun1_c B c => sizeOf_fundefs B + sizeOf_exp_ctx c
      | Efun2_c B e => sizeOf_fundefs_ctx B + sizeOf_exp e
    end
  with sizeOf_fundefs_ctx (B : fundefs_ctx) : nat :=
         match B with
           | Fcons1_c _ _ xs c B =>
             1 + length xs + sizeOf_exp_ctx c + sizeOf_fundefs B
           | Fcons2_c _ _ xs e B =>
             1 + length xs + sizeOf_exp e + sizeOf_fundefs_ctx B
         end.

  (* Compute the maximum of a tree given a measure function *)
  (* TODO move? *)
  Definition max_ptree_with_measure {A} (f : A -> nat) (i : nat) (rho : M.t A) :=
    M.fold (fun c _ v => max c (f v)) rho i.

  Lemma Mfold_monotonic {A} f1 f2 (rho : M.t A) n1 n2 :
    (forall x1 x1' x2 x3, x1 <= x1' -> f1 x1 x2 x3 <= f2 x1' x2 x3) ->
    n1 <= n2 ->
    M.fold f1 rho n1 <= M.fold f2 rho n2.
  Proof.
    rewrite !M.fold_spec.
    intros. eapply fold_left_monotonic; eauto.
  Qed.

  Lemma max_ptree_with_measure_spec1 {A} (f : A -> nat) i rho x v :
    M.get x rho = Some v ->
    f v <= max_ptree_with_measure f i rho. 
  Proof.
    intros Hget. unfold max_ptree_with_measure.
    rewrite M.fold_spec.
    assert (List.In (x, v) (M.elements rho))
      by (eapply PTree.elements_correct; eauto).
    revert H. generalize (M.elements rho).
    intros l Hin. induction l. now inv Hin.
    inv Hin.
    - simpl. eapply le_trans. now apply Max.le_max_r.
      eapply fold_left_extensive.
      intros [y u] n; simpl. now apply Max.le_max_l.
    - simpl. eapply le_trans. now eapply IHl; eauto. 
      eapply fold_left_monotonic.
      intros. now eapply NPeano.Nat.max_le_compat_r; eauto.
      now apply Max.le_max_l.
  Qed.

  Lemma max_list_nat_acc_spec {A} (xs : list A) f acc :
    max_list_nat_with_measure f acc xs =
    max acc (max_list_nat_with_measure f 0 xs).
  Proof.
    rewrite <- (Max.max_0_r acc) at 1. generalize 0.
    revert acc. induction xs; intros acc n; simpl; eauto.
    rewrite <- Max.max_assoc. eauto.
  Qed.

  (** Stratified size for values *)
  Fixpoint sizeOf_val' (i : nat) (H : heap block) (v : value)  : nat :=
    match i with
      | 0 => 0
      | S i' =>
        match v with
          | Loc l =>
            let sizeOf_env rho := max_ptree_with_measure (sizeOf_val' i' H) 0 rho in
            match get l H with
              | Some (Constr _ vs) => max_list_nat_with_measure (sizeOf_val' i' H) 0 vs
              | Some (Clos v1 v2) => max (sizeOf_val' i' H v1) (sizeOf_val' i' H v2)
              | Some (Env rho) => sizeOf_env rho
              | None => 0
            end
          | FunPtr B f => sizeOf_fundefs B
        end
    end.

  (** Size of environments.
    * The size of an environment is the size of the maximum value stored in it *)
  Definition sizeOf_env i (H : heap block) rho :=
    max_ptree_with_measure (sizeOf_val' i H) 0 rho.

  (** Maximum of an expression and an environment. *)
  Definition max_exp_env (k : nat) (H : heap block) (rho : env) (e : exp) :=
    max (sizeOf_exp e) (sizeOf_env k H rho).
  
  (** Equivalent definition *)
  Definition sizeOf_val (i : nat) (H : heap block) (v : value) : nat :=
    match i with
      | 0 => 0
      | S i' =>
        match v with
          | Loc l =>
            match get l H with
              | Some (Constr _ vs) => max_list_nat_with_measure (sizeOf_val' i' H) 0 vs
              | Some (Clos v1 v2) => max (sizeOf_val' i' H v1) (sizeOf_val' i' H v2)
              | Some (Env rho) => sizeOf_env i' H rho
              | None => 0
            end
          | FunPtr B f => sizeOf_fundefs B
        end
    end.
  
  Lemma sizeOf_val_eq i H v :
    sizeOf_val' i H v = sizeOf_val i H v.
  Proof.
    destruct i; eauto.
  Qed.
  
  Opaque sizeOf_val'.

  (** Monotonicity properties *)

  (* TODO move *)
  Lemma max_list_nat_monotonic (A : Type) (f1 f2 : A -> nat) (l : list A) (n1 n2 : nat) :
    (forall (x1 : A), f1 x1 <= f2 x1) ->
    n1 <= n2 ->
    max_list_nat_with_measure f1 n1 l <= max_list_nat_with_measure f2 n2 l.
  Proof.
    unfold max_list_nat_with_measure.
    intros. eapply fold_left_monotonic; eauto.
    intros. eapply NPeano.Nat.max_le_compat; eauto.
  Qed.

  Lemma sizeOf_val_monotic i i' H v :
    i <= i' ->
    sizeOf_val i H v <= sizeOf_val i' H v.
  Proof.
    revert i' v. induction i as [i IHi] using lt_wf_rec1; intros i' v.
    destruct i; try (simpl; omega). intros Hlt.
    destruct i'; simpl; try omega.
    destruct v; simpl; eauto. destruct (get l H); eauto.
    destruct b; eauto.
    - eapply max_list_nat_monotonic; eauto. intros.
      rewrite !sizeOf_val_eq. eapply IHi; omega.
    - eapply NPeano.Nat.max_le_compat; eauto.
      rewrite !sizeOf_val_eq. eapply IHi; omega.
      rewrite !sizeOf_val_eq. eapply IHi; omega.
    - unfold sizeOf_env. eapply Mfold_monotonic; eauto.
      intros. eapply NPeano.Nat.max_le_compat; eauto.
      rewrite !sizeOf_val_eq; eapply IHi; omega.
  Qed.

  Lemma sizeOf_env_monotonic i i' H rho :
    i <= i' ->
    sizeOf_env i H rho <= sizeOf_env i' H rho.
  Proof.
    intros Hi. unfold sizeOf_env.
    eapply Mfold_monotonic; eauto.
    intros. eapply NPeano.Nat.max_le_compat; eauto.
    rewrite !sizeOf_val_eq. now eapply sizeOf_val_monotic.
  Qed.

  (** Lemmas about [size_of_env] *)
  Lemma sizeOf_env_O H rho :
    sizeOf_env 0 H rho = 0.
  Proof.
    unfold sizeOf_env, max_ptree_with_measure.
    rewrite M.fold_spec. generalize (M.elements rho).
    induction l; eauto.
  Qed.
  

  Lemma sizeOf_env_set k H rho x v :
    sizeOf_env k H (M.set x v rho) = max (sizeOf_val k H v) (sizeOf_env k H rho).
  Proof.
    (* Obvious but seems painful, admitting for now *)
  Admitted.


  Lemma sizeOf_env_setlist k H rho rho' xs vs :
    setlist xs vs rho = Some rho' ->
    sizeOf_env k H rho' =
    max (max_list_nat_with_measure (sizeOf_val k H) 0 vs) (sizeOf_env k H rho).
  Proof.
    revert vs rho rho'. induction xs; intros vs rho rho' Hset.
    - destruct vs; try discriminate. inv Hset.
      reflexivity.
    - destruct vs; try discriminate.
      simpl in Hset. destruct (setlist xs vs rho) eqn:Hset'; try discriminate.
      inv Hset. rewrite sizeOf_env_set; simpl.
      rewrite max_list_nat_acc_spec.
      rewrite <- Max.max_assoc. eapply NPeano.Nat.max_compat. reflexivity.
      eauto.
  Qed.

  Lemma sizeOf_env_get k H rho x v :
    rho ! x = Some v ->
    sizeOf_val k H v <= sizeOf_env k H rho.
  Proof.
    intros Hget. 
    unfold sizeOf_env. rewrite <- sizeOf_val_eq.
    eapply max_ptree_with_measure_spec1.
    eassumption.
  Qed.

  (** Lemmas about [size_of_exp] *)

  Lemma sizeOf_exp_grt_1 e :
    1 <= sizeOf_exp e.
  Proof.
    induction e using exp_ind'; simpl; eauto; omega.
  Qed.

  (** Lemmas about [sizeOf_exp_ctx] *)
  Lemma sizeOf_exp_ctx_comp_ctx_mut :
    (forall C1 C2,
       sizeOf_exp_ctx (comp_ctx_f C1 C2) = sizeOf_exp_ctx C1 + sizeOf_exp_ctx C2) /\
    (forall B e,
       sizeOf_fundefs_ctx (comp_f_ctx_f B e) = sizeOf_fundefs_ctx B + sizeOf_exp_ctx e).
  Proof.
    exp_fundefs_ctx_induction IHe IHB; 
    try (intros C; simpl; eauto; rewrite IHe; omega);
    try (intros C; simpl; eauto; rewrite IHB; omega).
    (* probably tactic misses an intro pattern *)
    intros l' C. simpl. rewrite IHe; omega.
  Qed.

  Corollary sizeOf_exp_ctx_comp_ctx :
    forall C1 C2,
      sizeOf_exp_ctx (comp_ctx_f C1 C2) = sizeOf_exp_ctx C1 + sizeOf_exp_ctx C2.
  Proof.
    eapply sizeOf_exp_ctx_comp_ctx_mut; eauto.
  Qed.

  Corollary sizeOf_fundefs_ctx_comp_f_ctx :
    forall B e,
      sizeOf_fundefs_ctx (comp_f_ctx_f B e) = sizeOf_fundefs_ctx B + sizeOf_exp_ctx e.
  Proof.
    eapply sizeOf_exp_ctx_comp_ctx_mut; eauto.
  Qed.
  
  (** Lemmas about [max_exp_env] *)

  Lemma max_exp_env_grt_1 k H rho e :
    1 <= max_exp_env k H rho e.
  Proof.
    unfold max_exp_env.
    eapply le_trans. now apply sizeOf_exp_grt_1.
    eapply Max.le_max_l.
  Qed.

  Lemma max_exp_env_Econstr k H x t ys e rho :
    max_exp_env k H rho e <= max_exp_env k H rho (Econstr x t ys e).
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.
  
  Lemma max_exp_env_Eproj k x t N y e H rho :
    max_exp_env k H rho e <= max_exp_env k H rho (Eproj x t N y e).
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Ecase_cons_hd k x c e l H rho :
    max_exp_env k H rho e <= max_exp_env k H rho (Ecase x ((c, e) :: l)).
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.
  
  Lemma max_exp_env_Ecase_cons_tl k x c e l H rho :
    max_exp_env k H rho  (Ecase x l) <= max_exp_env k H rho (Ecase x ((c, e) :: l)).
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Eprim k H rho x f ys e :
    max_exp_env k H rho e <= max_exp_env k H rho (Eprim x f ys e).
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

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

  Lemma numOf_fundefs_le_sizeOf_fundefs B :
    numOf_fundefs B <= sizeOf_fundefs B.
  Proof.
    induction B; eauto; simpl; omega.
  Qed.


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

    (* Concrete bounds for closure conversion *)

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

  Lemma Post_timeout i (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp)
        C (k c  : nat) :
    Pre C i (H1, rho1, e1) (H2, rho2, e2) ->
    k <= 7 * sizeOf_exp e1 ->
    cost_alloc_ctx C = 0 ->
    PostL k i H1 rho1 e1 (c, size_heap H1) (c, size_heap H2).
  Proof. 
    unfold Pre, Post. intros [H1' H2'] Ht Hm.
    split. split. omega.
    assert (Hgrt := max_exp_env_grt_1 i H1 rho1 e1).
    eapply plus_le_compat; try omega.
    replace c with (1 * c * 1) at 1 by omega. 
    eapply mult_le_compat. omega. eassumption.
    rewrite Hm in *. split. omega.
    rewrite <- plus_n_O in H2'. eassumption.
  Qed.

  (* Cost for projecting vars *)
  Lemma project_var_cost 
        Scope Funs σ c Γ FVs S1 x x' C1 S2 :
    project_var Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    sizeOf_exp_ctx C1 <= 1.
  Proof.
    intros Hvar; inv Hvar; eauto.
  Qed.
  
  Lemma project_vars_cost 
        Scope Funs σ c Γ FVs S1 x x' C1 S2 :
    project_vars Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    sizeOf_exp_ctx C1 <= length x.
  Proof.
    intros Hvar. induction Hvar; eauto.
    rewrite sizeOf_exp_ctx_comp_ctx.
    simpl. replace (S (length ys)) with (1 + length ys) by omega.
    eapply plus_le_compat.
    eapply project_var_cost; eauto.
    eauto.
  Qed.

  Lemma project_var_cost_alloc
        Scope Funs σ c Γ FVs S1 x x' C1 S2 :
    project_var Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    cost_alloc_ctx C1 = 0.
  Proof.
    intros Hvar; inv Hvar; eauto.
  Qed.
  
  Lemma project_vars_cost_alloc
        Scope Funs σ c Γ FVs S1 x x' C1 S2 :
    project_vars Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    cost_alloc_ctx C1 = 0.
  Proof.
    intros Hvar. induction Hvar; eauto.
    simpl. rewrite cost_alloc_ctx_comp_ctx_f.
    erewrite project_var_cost_alloc; eauto.
  Qed.

  Lemma make_closures_cost ct B S Γ C g :
    make_closures ct B S Γ C g S ->
    sizeOf_exp_ctx C = 3 * (numOf_fundefs B).
  Proof.
    intros Hvar. induction Hvar; eauto.
    simpl. omega.
  Qed.

  Lemma make_closures_cost_alloc ct B S Γ C g :
    make_closures ct B S Γ C g S ->
    cost_alloc_ctx C = 3 * (numOf_fundefs B).
  Proof.
    intros Hvar. induction Hvar; eauto.
    simpl. omega.
  Qed.

  (* Lemma ctx_to_heap_env_cost C H1 rho1 H2 rho2 m : *)
  (*   ctx_to_heap_env C H1 rho1 H2 rho2 m -> *)
  (*   m = sizeOf_exp_ctx C. *)
  (* Proof. *)
  (*   intros Hctx; induction Hctx; eauto. *)
  (*   simpl. omega. *)
  (*   simpl. omega. *)
  (*   simpl. omega. *)
  (* Qed.  *)
  
End Size.