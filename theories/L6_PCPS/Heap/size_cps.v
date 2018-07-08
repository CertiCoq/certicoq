From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics.

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


  (** The cost of constructing environments when evaluating e *)
  Fixpoint cost_env_exp (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => cost_env_exp e
      | Ecase x l =>
        1 + (fix sizeOf_l l :=
               match l with
                 | [] => 0
                 | (t, e) :: l => max (cost_env_exp e) (sizeOf_l l)
               end) l
      | Eproj x _ _ y e => cost_env_exp e
      | Efun B e => 1 + PS.cardinal (fundefs_fv B) 
      | Eapp x _ ys => 0
      | Eprim x _ ys e => cost_env_exp e
      | Ehalt x => 0
    end.

  (** The cost of evaluating e *)
  Fixpoint cost_env_app_exp (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => max (3 * length ys) (cost_env_app_exp e)
      | Ecase x l =>
        max 3 ((fix sizeOf_l l :=
                  match l with
                    | [] => 0
                    | (t, e) :: l => max (cost_env_app_exp e) (sizeOf_l l)
                  end) l)
      | Eproj x _ _ y e => max 3 (cost_env_app_exp e)
      | Efun B e => max (1 + PS.cardinal (fundefs_fv B)) (cost_env_app_exp e)
      | Eapp x _ ys => 3 + 3 * length ys
      | Eprim x _ ys e => max (length ys) (cost_env_app_exp e)
      | Ehalt x => 1
    end.

  Definition cost_env_app_exp_out (e : exp) : nat :=
    match e with
      | Econstr x _ ys e => 3 * length ys
      | Ecase x l => 3
      | Eproj x _ _ y e => 3
      | Efun B e => 1 + PS.cardinal (fundefs_fv B)
      | Eapp x _ ys => 3 * length ys
      | Eprim x _ ys e => length ys
      | Ehalt x => 1
    end.

  (** The extra cost incurred by evaluating an expression up to the next call *)
  Definition cost_mem_exp
             (Funs : Ensemble var) {_ : ToMSet Funs}
             (e : exp) :=
    let funs := PS.cardinal (@mset Funs  _) in
    3 * funs + cost_env_exp e.
  
  
  (** The cost incurred by evaluation a function in the heap *) 
  Definition cost_mem_fundefs (Funs : Ensemble var) {fv : ToMSet Funs} :=
    fix aux (B : fundefs) : nat :=
    match B with
      | Fcons _ _ xs e B => max (cost_mem_exp (Funs \\ (FromList xs)) e) (aux B)
      | Fnil => 0
    end.
  
  (** The extra cost incurred by evaluating an expression up to the next call *)
  Definition cost_time_exp (e : exp) := cost_env_app_exp e.  
  
  (** The cost incurred by evaluation a function in the heap *) 
  Fixpoint cost_time_fundefs (B : fundefs) : nat :=
    match B with
      | Fcons _ _ xs e B => max (cost_time_exp e) (cost_time_fundefs B)
      | Fnil => 0
    end.
  
  
  Definition cost_value (c : fundefs -> nat) (v : value) : nat :=
    match v with
      | Loc _ => 0
      | FunPtr B _ => (* cost_fundefs (name_in_fundefs B) *)c B
    end.

  Definition cost_block (c : fundefs -> nat) (b : block) : nat :=
    match b with
      | Constr _ vs => 0
      | Clos v1 rho => cost_value c v1 
    end.
  
  (** The maximum cost of evaluating any function in the heap *)
  Definition cost_heap (c : fundefs -> nat) (H : heap block) :=
    max_with_measure (cost_block c) H.
  
  (** memory cost of heap *)
  Definition cost_mem_heap := cost_heap (fun B => cost_mem_fundefs (name_in_fundefs B) B).

  (** time cost of heap *)
  Definition cost_time_heap := cost_heap cost_time_fundefs.
  


  (** The size of a closure after closure conversion including the closure environment *)
  Fixpoint size_fundefs (f : fundefs) : nat :=
    (* Clos (FunPtr B f) rho ~ Constr f_clo [(Funtr B' f); Loc l]  *) 
    3 + (* 3 words for each closure constructor *)
    (* l ~> Contr env [l1; .... ; l_fvno] *)
    PS.cardinal (fundefs_fv f) (* over-approximating the environment associated to each B by a factor of |B| *).
  
  (** The heap overheap of closure conversion -- remove functions not yet projected *)
  Definition size_cc_heap (Funs : Ensemble loc) {_ : ToMSet Funs} (H : heap block) :=
    size_with_measure_minus (cost_block size_fundefs) Funs H.

  
  (** * Postcondition *)

  (** Enforces that the resource consumption of the target is within certain bounds *)
  Definition Post
             (k : nat) (* This varies locally in the proof *)
             (sizeH : nat) (* This varies globally *)
             (Funs : Ensemble var)
             `{ToMSet Funs}
             (p1 p2 : heap block * env * exp * nat * nat) :=
    match p1, p2 with
      | (H1, rho1, e1, c1, m1), (H2, rho2, e2, c2, m2) =>
        (* time bound *)
        c1 + k <= c2 + k <= c1 * (1 + max (cost_time_exp e1) (cost_time_heap H1)) /\
        (* memory bound *)
        m2 <= m1 + max (cost_mem_exp Funs e1) (cost_mem_heap H1) + sizeH
    end.

  Definition PostG
             (Scope : Ensemble loc)
             `{ToMSet Scope}
             (Funs : Ensemble var)
             `{ToMSet Funs}
             (p1 p2 : heap block * env * exp * nat * nat) :=
     match p1, p2 with
       | (H1, rho1, e1, c1, m1), (H2, rho2, e2, c2, m2) =>
         Post 0 (size_cc_heap (env_locs rho1 Funs) H1) (Funs \\ Scope) p1 p2
     end.

  (** * Precondition *)
  
  (** Enforces that the initial heaps have related sizes *)  
  Definition Pre
             (sizeH : nat)
             (p1 p2 : heap block * env * exp) :=
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        (* Sizes of the initial heaps *)
        size_heap H2 <= size_heap H1 + sizeH
    end.


  Definition PreG
             (Funs : Ensemble var)
             `{ToMSet Funs}
             (p1 p2 : heap block * env * exp) :=
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        (* Sizes of the initial heaps *)
        size_heap H2 <= size_heap H1 + (size_cc_heap (env_locs rho1 Funs) H1)
    end.

  
  (* TODO move *)

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

  Lemma size_with_measure_get {A} (H1 : heap A) l f b : 
    get l H1 = Some b ->
    f b <= size_with_measure f H1. 
  Proof.
    intros Hget. unfold size_with_measure. 
    eapply heap_elements_complete in Hget.
    generalize (heap_elements H1), Hget. clear Hget.
    intros ls Hin. induction ls.
    + inv Hin.
    + simpl.
      inv Hin.
      * simpl. eapply fold_left_extensive.
        intros [l1 x1] x2. omega.
      * eapply le_trans. eapply IHls. eassumption.
        eapply fold_left_monotonic; [| omega ].
        intros x1 x2 [l1 y1] Hleq. simpl.
        omega.
  Qed.
  
  (* end move *)

  Lemma cost_heap_block_get H1 c l b :
    get l H1 = Some b ->
    cost_block c b <= cost_heap c H1. 
  Proof.
    eapply max_heap_with_measure_get.
  Qed.
  
  Lemma cost_heap_alloc H1 H1' c l b :
    alloc b H1 = (l, H1') ->
    cost_heap c H1' = max (cost_block c b) (cost_heap c H1).
  Proof.
    intros Hal. unfold cost_heap.
    erewrite (HL.max_with_measure_alloc _ _ _ _ H1'); eauto.
    rewrite Max.max_comm. eapply NPeano.Nat.max_compat; omega.
  Qed.

  Lemma cost_time_heap_alloc H1 H1' l b :
    alloc b H1 = (l, H1') ->
    cost_time_heap H1' = max (cost_block cost_time_fundefs b)
                             (cost_time_heap H1).
  Proof.
    intros. eapply cost_heap_alloc. eassumption.
  Qed.

  Lemma cost_mem_heap_alloc H1 H1' l b :
    alloc b H1 = (l, H1') ->
    cost_mem_heap H1' = max (cost_block (fun B => cost_mem_fundefs (name_in_fundefs B) B) b)
                             (cost_mem_heap H1).
  Proof.
    intros. eapply cost_heap_alloc. eassumption.
  Qed.
  
  Lemma cost_heap_def_closures H1 H1' rho1 rho1' c B B0 rho :
    def_closures B B0 rho1 H1 rho = (H1', rho1') ->
    cost_heap c H1' = match B with
                        | Fnil => cost_heap c H1
                        |  _ => max (c B0) (cost_heap c H1)
                      end.
  Proof.
    revert H1' rho1'. induction B; intros H1' rho1' Hclo.
    - simpl in Hclo.
      destruct (def_closures B B0 rho1 H1 rho) as [H2 rho2] eqn:Hclo'.
      destruct (alloc (Clos (FunPtr B0 v) rho) H2) as [l' rho3] eqn:Hal. inv Hclo.
      erewrite cost_heap_alloc; [| eassumption ].
      simpl. destruct B.
      + erewrite (IHB H2); [| reflexivity ].
        rewrite Max.max_assoc, Max.max_idempotent. reflexivity.
      + erewrite (IHB H2); reflexivity.
    - inv Hclo; eauto.
  Qed.

  Lemma cost_mem_heap_def_closures H1 H1' rho1 rho1' B rho :
    def_closures B B rho1 H1 rho = (H1', rho1') ->
    cost_mem_heap H1' = max (cost_mem_fundefs (name_in_fundefs B) B) (cost_mem_heap H1).
  Proof.
    intros Hdef. unfold cost_mem_heap. erewrite cost_heap_def_closures; [| eassumption ].
    destruct B; eauto.
  Qed.

  Lemma cost_time_heap_def_closures H1 H1' rho1 rho1' B rho :
    def_closures B B rho1 H1 rho = (H1', rho1') ->
    cost_time_heap H1' = max (cost_time_fundefs B) (cost_time_heap H1).
  Proof.
    intros Hdef. unfold cost_time_heap. erewrite cost_heap_def_closures; [| eassumption ].
    destruct B; eauto.
  Qed.


  (* Lemma size_cc_heap_block_get H1 l S b : *)
  (*   get l H1 = Some b -> *)
  (*   ~  *)
  (*   cost_block size_fundefs b <= size_cc_heap S H1.  *)
  (* Proof. *)
  (*   eapply size_with_measure_get. *)
  (* Qed. *)

  (** Proper instances for invriants *)
  Lemma size_cc_heap_Same_Set_compat
        (Funs : Ensemble var) { Hf : ToMSet Funs}
        (Funs' : Ensemble var) { Hf' : ToMSet Funs'} H1 :
    (Funs <--> Funs') ->
    size_cc_heap Funs H1 = size_cc_heap Funs' H1.
  Proof.
    unfold size_cc_heap.
    eapply HL.size_with_measure_minus_Same_set.
  Qed.

  
  Lemma PostSame_Set_compat
        (Funs : Ensemble var) { Hf : ToMSet Funs}
        (Funs' : Ensemble var) { Hf' : ToMSet Funs'} c1 c2 k m :
    Funs <--> Funs' ->
    Post k m Funs' c1 c2 -> 
    Post k m Funs c1 c2.
  Proof.
    destruct c1 as [[[[H1 rho1] e1] c1] m1].
    destruct c2 as [[[[H2 rho2] e2] c2] m2]. simpl.
    intros Heq1 [Hc Hm]. split. eassumption.
    eapply le_trans. eassumption.
    eapply plus_le_compat. eapply plus_le_compat_l.
    eapply NPeano.Nat.max_le_compat; [| reflexivity ].
    unfold cost_mem_exp. eapply plus_le_compat_r.
    eapply mult_le_compat. reflexivity.
    rewrite Proper_carinal. reflexivity.
    eapply Same_set_From_set. rewrite <- !mset_eq at 1.
    rewrite Heq1. reflexivity.
    reflexivity.
  Qed.

  Lemma size_cc_heap_alloc S {_ : ToMSet S} H1 H1' l b :
    alloc b H1 = (l, H1') ->
    ~ l \in S -> 
    size_cc_heap S H1' = cost_block size_fundefs b + size_cc_heap S H1.
  Proof.
    intros Hal Hnin. unfold size_cc_heap.
    erewrite (HL.size_with_measure_minus_alloc _ _ _ _ _ H1'); eauto.
    omega.
  Qed.

  Lemma size_cc_heap_alloc_In S {_ : ToMSet S} H1 H1' l b :
    alloc b H1 = (l, H1') ->
    l \in S -> 
    size_cc_heap S H1' =  size_cc_heap S H1.
  Proof.
    intros Hal Hnin. unfold size_cc_heap.
    erewrite (HL.size_with_measure_minus_alloc_not_In _ _ _ _ _ H1'); eauto.
  Qed.

  (* Lemma size_cc_heap_def_closures H1 H1' rho1 rho1' B B0 rho : *)
  (*   def_closures B B0 rho1 H1 rho = (H1', rho1') -> *)
  (*   size_cc_heap S H1' = size_cc_heap S H1. *)
  (*   (PS.cardinal (fundefs_names B))*(size_fundefs B0) (* because of overapproximation  of env *) *)
  (*                      + size_cc_heap H1. *)
  (* Proof. *)
  (*   revert H1' rho1'. induction B; intros H1' rho1' Hun Hclo. *)
  (*   - simpl in Hclo. *)
  (*     destruct (def_closures B B0 rho1 H1 rho) as [H2 rho2] eqn:Hclo'. *)
  (*     destruct (alloc (Clos (FunPtr B0 v) rho) H2) as [l' rho3] eqn:Hal. inv Hclo. *)
  (*     erewrite size_cc_heap_alloc; [| eassumption ]. *)
  (*     inv Hun. simpl. rewrite <- PS_cardinal_add. *)
  (*     + erewrite (IHB H2);[ | eassumption | reflexivity ]. *)
  (*       rewrite NPeano.Nat.mul_add_distr_r. omega. *)
  (*     + intros Hin. eapply H7. eapply fundefs_names_correct. eassumption. *)
  (*   - simpl in *. inv Hclo; eauto. *)
  (* Qed. *)

  Lemma size_cc_heap_def_closures S {Hs : ToMSet S} H1 H1' rho1 rho1' B B0 rho :
    unique_functions B ->
    def_closures B B0 rho1 H1 rho = (H1', rho1') ->
    (env_locs rho1' (name_in_fundefs B)) \subset S ->
    size_cc_heap S H1' = size_cc_heap S H1.
  Proof.
    revert H1 H1' rho1'. induction B; intros H1 H1' rho1' Hun Hclo Hsub.
    - simpl in Hclo.
      destruct (def_closures B B0 rho1 H1 rho) as [H2 rho2] eqn:Hclo'.
      destruct (alloc (Clos (FunPtr B0 v) rho) H2) as [l' H3] eqn:Hal.
      inv Hun.
      inv Hclo. erewrite <- (IHB H1 H2 _ H4 Hclo').
      erewrite <- (size_cc_heap_alloc_In _ H2 H1'); [ reflexivity | eassumption |  ].
      eapply Hsub.
      
      eapply env_locs_set_In. now left. now left.

      eapply Included_trans; [| eassumption ]. 
      rewrite env_locs_set_In; [| now left ].
      eapply Included_Union_preserv_r. simpl.
      rewrite Setminus_Union_distr. rewrite env_locs_Union.
      eapply Included_Union_preserv_r. rewrite Setminus_Disjoint.
      reflexivity. eapply Disjoint_Singleton_r. eassumption.
    - inv Hclo. reflexivity.
  Qed.

  Lemma size_cc_heap_def_closures_Union S {_ : ToMSet S} H1 H1' rho1 rho1' B B0 rho :
    unique_functions B ->
    def_closures B B0 rho1 H1 rho = (H1', rho1') ->
    size_cc_heap (env_locs rho1' (name_in_fundefs B) :|: S) H1' = size_cc_heap S H1.
  Proof.
    revert H1 H1' rho1'.
    induction B; intros H1 H1' rho1' Hun Hclo.
    - simpl in Hclo.
      destruct (def_closures B B0 rho1 H1 rho) as [H2 rho2] eqn:Hclo'.
      destruct (alloc (Clos (FunPtr B0 v) rho) H2) as [l' H3] eqn:Hal.
      inv Hun.
      inv Hclo.
      erewrite <- (IHB H1 H2 _ H4 Hclo'). 
      erewrite (size_cc_heap_alloc_In _ H2 H1'); [ | eassumption |  ].
      erewrite size_cc_heap_Same_Set_compat with (Funs' := l' |: ((env_locs rho2 (name_in_fundefs B)) :|: S)).
      unfold size_cc_heap. erewrite <- HL.size_with_measure_Disjoint_dom. reflexivity.
      eapply Disjoint_Singleton_l. intros [v' Hc]. erewrite alloc_fresh in Hc; try eassumption.
      congruence. rewrite env_locs_set_In. simpl. rewrite Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set. rewrite Setminus_Disjoint.
      now eauto with Ensembles_DB.
      eapply Disjoint_Singleton_r. eassumption. now left.
      left. rewrite env_locs_set_In. simpl. now left. now left.
    - inv Hclo. simpl.
      erewrite size_cc_heap_Same_Set_compat with (Funs' := S).
      reflexivity. rewrite env_locs_Empty_set, Union_Empty_set_neut_l; reflexivity.
  Qed.


  (* Lemma size_cc_heap_def_closures H1 H1' rho1 rho1' B B0 rho : *)
  (*   unique_functions B -> *)
  (*   def_closures B B0 rho1 H1 rho = (H1', rho1') -> *)
  (*   size_cc_heap H1' = (PS.cardinal (fundefs_names B))*(size_fundefs B0) (* because of overapproximation  of env *) *)
  (*                      + size_cc_heap H1. *)
  (* Proof. *)
  (*   revert H1' rho1'. induction B; intros H1' rho1' Hun Hclo. *)
  (*   - simpl in Hclo. *)
  (*     destruct (def_closures B B0 rho1 H1 rho) as [H2 rho2] eqn:Hclo'. *)
  (*     destruct (alloc (Clos (FunPtr B0 v) rho) H2) as [l' rho3] eqn:Hal. inv Hclo. *)
  (*     erewrite size_cc_heap_alloc; [| eassumption ]. *)
  (*     inv Hun. simpl. rewrite <- PS_cardinal_add. *)
  (*     + erewrite (IHB H2);[ | eassumption | reflexivity ]. *)
  (*       rewrite NPeano.Nat.mul_add_distr_r. omega. *)
  (*     + intros Hin. eapply H7. eapply fundefs_names_correct. eassumption. *)
  (*   - simpl in *. inv Hclo; eauto. *)
  (* Qed. *)
  

  Lemma cost_env_app_exp_out_le e :
    cost_env_app_exp_out e <= cost_env_app_exp e.
  Proof.
    induction e; try eapply Max.le_max_l.
    simpl. omega.
    simpl. omega.
  Qed.

  
  (** * Compat lemmas *)
  
  Lemma PostBase H1 H2 rho1 rho2 e1 e2 k m
        (Funs : Ensemble var) { _ : ToMSet Funs} :
    k <= cost_env_app_exp_out e1 ->
    InvCostBase (Post k m Funs) (Pre m) H1 H2 rho1 rho2 e1 e2.
  Proof.
    unfold InvCostBase, Post, Pre.
    intros Hleq H1' H2' rho1' rho2' c b1 b2  Heq1 Hinj1 Heq2 Hinj2 Hm.
    split.
    + split. omega.
      rewrite NPeano.Nat.mul_add_distr_l, Nat.mul_1_r.
      eapply plus_le_compat_l.
      eapply le_trans. eassumption.
      eapply le_trans. eapply cost_env_app_exp_out_le.
      rewrite <- (Nat.mul_1_l (cost_env_app_exp _)). eapply mult_le_compat.
      admit. eapply Nat.le_max_l. 
    + simpl. eapply le_trans. eassumption. omega.
  Admitted. 
  

  (* TODO move *)
  
  Lemma PS_elements_subset S1 {HS1 : ToMSet S1} S2 {HS2 : ToMSet S2} :
    S1 \subset S2 ->
    (PS.cardinal (@mset S1 _)) <= (PS.cardinal (@mset S2 _)).
  Proof.
    rewrite !PS.cardinal_spec. intros Hin.
    eapply Same_set_FromList_length.
    eapply NoDupA_NoDup. eapply PS.elements_spec2w.
    rewrite <- !FromSet_elements. unfold mset. 
    destruct HS1 as [m1 HS1].
    destruct HS2 as [m2 HS2].
    rewrite <- HS1, <- HS2. eassumption.
  Qed. 
    
  (* Lemma cost_time_exp_Scope_antimon *)
  (*       (Scope : Ensemble var) `{ToMSet Scope} *)
  (*       (Scope' : Ensemble var) `{ToMSet Scope'} *)
  (*       (Funs : Ensemble var) `{ToMSet Funs} *)
  (*       (FVs : Ensemble var) `{ToMSet FVs} e : *)
  (*   Scope' \subset Scope -> *)
  (*   cost_time_exp Scope Funs FVs e <= cost_time_exp Scope' Funs FVs e. *)
  (* Proof with (now eauto with Ensembles_DB). *)
  (*   intros Hleq. unfold cost_time_exp. *)
  (*   eapply plus_le_compat_r. *)
  (*   eapply plus_le_compat. *)
  (*   - eapply mult_le_compat_l. *)
  (*     eapply PS_elements_subset... *)
  (*   - eapply PS_elements_subset... *)
  (* Qed. *)


  Lemma cost_mem_exp_Fun_mon
        (Funs : Ensemble var) `{ToMSet Funs}
        (Funs' : Ensemble var) `{ToMSet Funs'}
        e :
    Funs \subset Funs' ->
    cost_mem_exp Funs e <= cost_mem_exp Funs' e.
  Proof with (now eauto with Ensembles_DB).
    intros Hleq. unfold cost_mem_exp.
    eapply plus_le_compat_r.
    eapply mult_le_compat_l.
    eapply PS_elements_subset. eassumption.
  Qed.


  Lemma cost_mem_exp_inv_exp
        (Funs : Ensemble var) `{ToMSet Funs} e e' :
    cost_env_exp e = cost_env_exp e' ->
    cost_mem_exp Funs e = cost_mem_exp Funs e'.
  Proof with (now eauto with Ensembles_DB).
    intros Heq. unfold cost_mem_exp.
    rewrite Heq. reflexivity.
  Qed.


  Lemma PostConstrCompat i j IP P
        m (Funs : Ensemble var) {Hf : ToMSet Funs}
        b d H1 H2 rho1 rho2 x c ys1 ys2 e1 e2 :
    Forall2 (cc_approx_var_env i j IP P b d H1 rho1 H2 rho2) ys1 ys2 ->
    InvCtxCompat (Post (cost_env_app_exp_out (Econstr x c ys1 e1)) m Funs)
                 (Post 0 m Funs)
                 H1 H2 rho1 rho2 (Econstr_c x c ys1 Hole_c) (Econstr_c x c ys2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold InvCtxCompat, Post.
    intros Hall H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1 c2 c1' c2'
           m1 m2 b1 b2 Heq1 Hinj1 Heq2 Hinj2 [[Hc1 Hc2] Hm] Hctx1 Hctx2.
    assert (Hlen := Forall2_length _ _ _ Hall). 
    inv Hctx1. inv Hctx2. inv H13. inv H16.
    rewrite !plus_O_n in *. simpl cost_ctx in *.
    rewrite !Hlen in *.
    eapply Forall2_monotonic_strong
      with (R' := fun y1 y2 : var =>
                    cc_approx_var_env i j IP P (b2 ∘ b ∘ b1) (lift b2 ∘ d ∘ b1)
                                      H1' rho1' H2' rho2' y1 y2) in Hall.
    { edestruct cc_approx_var_env_getlist as [vs2' [Hget2' Hcc]]; try eassumption.
      split.
      - split.
        + rewrite !(plus_comm _ (S (length _))). rewrite <- !plus_assoc.
          assert (Hleq : c1 <= c2).
          { omega. }
          eapply plus_le_compat_l. eapply le_trans.
          eapply plus_le_compat_r. eassumption. reflexivity.
          (* eapply plus_le_compat_l. *)
          (* simpl. eapply Max.le_max_r. *)
        + rewrite NPeano.Nat.mul_add_distr_r.
          rewrite <- plus_assoc, (plus_comm (S (length _))). 
          eapply plus_le_compat.
          eapply le_trans; [ | eapply le_trans; [ now apply Hc2 |] ].
          omega.
          eapply mult_le_compat_l.
          erewrite cost_time_heap_alloc; [| eassumption ]. simpl cost_block.
          rewrite Max.max_0_l.
          eapply plus_le_compat_l. eapply NPeano.Nat.max_le_compat_r.
          now eapply Max.le_max_r.
          
          rewrite NPeano.Nat.mul_add_distr_l, Nat.mul_1_r.
          rewrite plus_comm. eapply plus_le_compat_l.
          rewrite <- (Nat.mul_1_l (cost_env_app_exp_out _)).
          eapply mult_le_compat. omega.
          eapply le_trans; [| eapply Max.le_max_l ].
          eapply cost_env_app_exp_out_le.
      - eapply le_trans. eassumption.
         
        rewrite <- !plus_assoc.
        eapply plus_le_compat_l. simpl. eapply plus_le_compat_r.
 
        eapply Nat.max_le_compat_l.
        erewrite cost_mem_heap_alloc; [| eassumption ].
        reflexivity.  }
    intros y1 y2 Hin1 Hin2 Hcc.
    eapply cc_approx_var_env_heap_env_equiv; try eassumption.
    simpl; normalize_occurs_free...
    simpl; normalize_occurs_free...
  Qed.
  
  Lemma PreConstrCompat i j IP P
        m b d H1 H2 rho1 rho2 x c ys1 ys2 e1 e2 :
    Forall2 (fun y1 y2 => cc_approx_var_env i j IP P b d H1 rho1 H2 rho2 y1 y2) ys1 ys2 -> 
    IInvCtxCompat (Pre m) (Pre m )
                  H1 H2 rho1 rho2 (Econstr_c x c ys1 Hole_c) (Econstr_c x c ys2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold IInvCtxCompat, Pre.
    intros Hall H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1' c2'
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H13. inv H16.
    assert (Hlen := Forall2_length _ _ _ Hall).
    eapply Forall2_monotonic_strong
      with (R' := fun y1 y2 : var =>
                    cc_approx_var_env i j IP P (b2 ∘ b ∘ b1) (lift b2 ∘ d ∘ b1) H1' rho1' H2' rho2' y1 y2) in Hall.
    { edestruct cc_approx_var_env_getlist as [vs2' [Hget2' Hcc]]; try eassumption.
      unfold size_heap in *.
      erewrite HL.size_with_measure_alloc; [| reflexivity | eassumption ].
      erewrite (HL.size_with_measure_alloc _ _ _ _ H1''); [| reflexivity | eassumption ].
      simpl size_val. rewrite !(plus_comm _ (S (length _))), <- !plus_assoc.
      eapply plus_le_compat.
      repeat subst_exp. eapply Forall2_length in Hcc. omega.
      eassumption. }
    intros y1 y2 Hin1 Hin2 Hcc.
    eapply cc_approx_var_env_heap_env_equiv; try eassumption.
    simpl; normalize_occurs_free...
    simpl; normalize_occurs_free...
  Qed.
  

  Lemma PostProjCompat
        m (Funs : Ensemble var) {Hf : ToMSet Funs}
        H1 H2 rho1 rho2 x c y1 y2 e1 e2 n :
    InvCtxCompat (Post (cost_env_app_exp_out (Eproj x c n y1 e1)) m Funs)
                 (Post 0 m Funs)
                 H1 H2 rho1 rho2 (Eproj_c x c n y1 Hole_c) (Eproj_c x c n y2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold InvCtxCompat, Post.
    intros H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1 c2 c1' c2'
           m1 m2 b d Heq1 Hinj1 Heq2 Hinj2 [[Hc1 Hc2] Hm] Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H15. inv H19.
    split.
    - split.
      + assert (Hleq : c1 <= c2).
        { omega. }
        simpl cost_ctx. eapply le_trans. eapply plus_le_compat_r.
        eapply plus_le_compat_r. eassumption. omega.
      + rewrite !plus_O_n.  
        rewrite NPeano.Nat.mul_add_distr_r.
        rewrite <- plus_assoc, (plus_comm (cost_ctx _)). 
        eapply plus_le_compat.
        eapply le_trans; [ | eapply le_trans; [ now apply Hc2 |] ].
        omega.
        eapply mult_le_compat_l.
        eapply plus_le_compat_l. eapply NPeano.Nat.max_le_compat_r.
        now eapply Max.le_max_r.
        
        rewrite NPeano.Nat.mul_add_distr_l, Nat.mul_1_r.
        rewrite plus_comm. eapply plus_le_compat_l.
        rewrite <- (Nat.mul_1_l (cost_env_app_exp_out _)).
        eapply mult_le_compat. simpl. omega.
        eapply le_trans. eapply cost_env_app_exp_out_le. eapply Max.le_max_l.
    - eassumption.
      (* eapply le_trans. eassumption. reflexivity. *)
      (* rewrite <- !plus_assoc. *)
      (* eapply plus_le_compat_l. simpl.  *)
      (* reflexivity. eapply plus_le_compat_l. *)
      (* eapply Nat.max_le_compat; [| simpl; omega ]. *)
      (* eapply le_trans. *)
      (* eapply (cost_mem_exp_Scope_antimon (x |: Scope) Scope). *)
      (* now eauto with Ensembles_DB. *)
      (* rewrite cost_mem_exp_inv_exp with (e := (Eproj x c n y1 e1)) (e' := e1); [| reflexivity ]. *)
      (* eapply cost_mem_exp_Fun_mon... *)
      (* eapply NPeano.Nat.eq_le_incl. *)
      (* eapply size_cc_heap_Same_Set_compat. rewrite env_locs_set_not_In. *)
      (* rewrite Setminus_Disjoint.  reflexivity. *)
      (* eapply Disjoint_Singleton_r. eassumption. *)
      (* intros Hc; inv Hc; eauto. *)
  Qed.
  
  Lemma PreProjCompat H1 H2 rho1 rho2 x1 x2 c n y1 y2 e1 e2 
    m (Funs : Ensemble var) {Hf : ToMSet Funs} :
    IInvCtxCompat (Pre m) (Pre m)
                  H1 H2 rho1 rho2 (Eproj_c x1 c n y1 Hole_c) (Eproj_c x2 c n y2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold IInvCtxCompat, Pre.
    intros H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1' c2'
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm1 Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H15. inv H19.
    eapply le_trans. eassumption. eapply plus_le_compat_l.
    reflexivity.
    (* unfold size_cc_heap. *)
    (* eapply HL.size_with_measure_minus_Included. *)
    (* rewrite env_locs_set_not_In. eapply env_locs_monotonic... *)
    (* intros Hc; inv Hc; eauto. *)
  Qed.
  

  (* TODO move *)
  

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

  
  Lemma project_var_ToMSet Scope1 Scope2 `{ToMSet Scope1} Funs1 Funs2
        fenv c Γ FVs y C1 :
    project_var Util.clo_tag Scope1 Funs1 fenv c Γ FVs y C1 Scope2 Funs2 ->
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

  Lemma project_var_ToMSet_Funs Scope1 Scope2 Funs1 Funs2 `{ToMSet Funs1}
        fenv c Γ FVs y C1 :
    project_var Util.clo_tag Scope1 Funs1 fenv c Γ FVs y C1 Scope2 Funs2 ->
    ToMSet Funs2.
  Proof.
    intros Hvar.
    assert (Hd1 := H).  eapply Decidable_ToMSet in Hd1. 
    destruct Hd1 as [Hdec1]. 
    destruct (Hdec1 y).
  Admitted. 

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

    
  (* end move *)

  Lemma project_var_cost_alloc_eq Scope Scope'
        Funs `{ToMSet Funs}
        Funs' `{ToMSet Funs'}
        fenv c Γ FVs x C1 :
    project_var Util.clo_tag Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
    cost_alloc_ctx_CC C1 = 3 * PS.cardinal (@mset (Funs \\ Funs') _).
  Proof.
    intros Hvar; inv Hvar; eauto.
    - rewrite (Proper_carinal _ PS.empty).
      reflexivity.
      eapply Same_set_From_set. 
      rewrite <- mset_eq, Setminus_Same_set_Empty_set.
      rewrite FromSet_empty. reflexivity.
    - simpl cost_ctx_full.
      rewrite (Proper_carinal _ (PS.singleton x)).
      reflexivity.
      eapply Same_set_From_set.
      rewrite FromSet_singleton.
      rewrite <- mset_eq. 
      split. eapply Included_trans.
      eapply Setminus_Setminus_Included. tci.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l...
      reflexivity...
      eapply Singleton_Included. constructor; eauto.
      intros Hc. inv Hc. eauto.
    - rewrite (Proper_carinal _ PS.empty).
      simpl. reflexivity.
      eapply Same_set_From_set.
      rewrite FromSet_empty.
      rewrite <- mset_eq. rewrite Setminus_Same_set_Empty_set. reflexivity. 
  Qed.
  

  Lemma project_vars_cost_alloc_eq Scope Scope'
        Funs `{ToMSet Funs}
        Funs' `{ToMSet Funs'}
        fenv c Γ FVs xs C1 :
    project_vars Util.clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    cost_alloc_ctx_CC C1 = 3 * PS.cardinal (@mset (Funs \\ Funs') _).
  Proof with (now eauto with Ensembles_DB).
    intros Hvar; induction Hvar; eauto.
    - rewrite (Proper_carinal _ PS.empty).
      reflexivity.
      eapply Same_set_From_set.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set.
      rewrite FromSet_empty. reflexivity.
    - assert (Hvar' := H1). assert (Hvar'' := H1).
      eapply project_var_ToMSet_Funs in Hvar''; eauto. 
      rewrite cost_alloc_ctx_CC_comp_ctx_f. 
      eapply (@project_var_cost_alloc_eq Scope1 Scope2 Funs1 _ Funs2 Hvar'') in H1.
      rewrite H1. erewrite IHHvar; eauto.
      rewrite <- NPeano.Nat.mul_add_distr_l.
      eapply Nat_as_OT.mul_cancel_l. omega.
      rewrite PS_cardinal_union. 
      eapply Proper_carinal.  
      eapply Same_set_From_set. setoid_rewrite <- mset_eq.
      rewrite FromSet_union.
      do 2 setoid_rewrite <- mset_eq at 1.
      rewrite Union_commut. erewrite Setminus_compose; tci.
      reflexivity. eapply project_vars_Funs_l. eassumption.
      eapply project_var_Funs_l. eassumption.
      eapply FromSet_disjoint.
      do 2 setoid_rewrite <- mset_eq at 1.
      eapply Disjoint_Setminus_l...
  Qed.          

  Lemma project_var_cost_eq
        Scope {_ : ToMSet Scope} Scope' {_ : ToMSet Scope'} Funs `{ToMSet Funs}
        Funs' `{ToMSet Funs'} fenv
        c Γ FVs x C1 :
    project_var Util.clo_tag Scope Funs fenv c Γ FVs x C1 Scope' Funs' ->
    cost_ctx_full C1 = 3 * PS.cardinal (@mset (Funs \\ Funs') _) +
                       PS.cardinal (@mset ((FromList FVs \\ Funs) :&: (Scope' \\ Scope)) _).
  Proof with (now eauto with Ensembles_DB).
    intros Hvar; inv Hvar; eauto.
    - rewrite !(Proper_carinal _ PS.empty).
      rewrite !(Proper_carinal mset PS.empty).
      reflexivity.
      eapply Same_set_From_set.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set, Intersection_Empty_set_abs_r.
      rewrite FromSet_empty. reflexivity.
      eapply Same_set_From_set.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set.
      rewrite FromSet_empty. reflexivity.
    - simpl cost_ctx_full.
      
      rewrite (Proper_carinal _ (PS.singleton x)).
      rewrite !(Proper_carinal mset PS.empty).
      reflexivity.
      eapply Same_set_From_set.
      rewrite <- mset_eq. 
      rewrite Setminus_Union_distr, (Setminus_Disjoint [set x]).
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite Intersection_Disjoint.
      rewrite FromSet_empty. reflexivity.
      eapply Disjoint_Singleton_r. intros Hc; inv Hc; eauto.
      eapply Disjoint_Singleton_l. eassumption. 
      
      eapply Same_set_From_set.
      rewrite <- mset_eq.
      rewrite FromSet_singleton. 
      split. eapply Included_trans. eapply Setminus_Setminus_Included; tci...
      now eauto with Ensembles_DB. 

      eapply Singleton_Included. constructor; eauto.
      intros Hc. inv Hc; eauto. 
    - rewrite (Proper_carinal _ PS.empty).
      rewrite (Proper_carinal mset (PS.singleton x)).
      simpl. reflexivity.
      + eapply Same_set_From_set.
        rewrite <- mset_eq.
        rewrite Setminus_Union_distr, (Setminus_Disjoint [set x]).
        rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
        rewrite Intersection_commut, Intersection_Same_set.
        rewrite FromSet_singleton. reflexivity.
        eapply Singleton_Included.
        constructor. eapply nthN_In. eassumption.
        eassumption.
        eapply Disjoint_Singleton_l. eassumption.
      + eapply Same_set_From_set.
        rewrite <- mset_eq.
        rewrite Setminus_Same_set_Empty_set.
        rewrite FromSet_empty. reflexivity.
  Qed.


  Lemma project_var_Scope_Funs_eq Scope Scope' Funs Funs'
        fenv c Γ FVs xs C1 :
    project_var Util.clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    Funs' <--> Funs \\ (Scope' \\ Scope).
  Proof.
    intros hvar; inv hvar; eauto.
    - rewrite Setminus_Same_set_Empty_set, Setminus_Empty_set_neut_r. reflexivity.
    - rewrite Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite (Setminus_Disjoint _ Scope). reflexivity.
      eapply Disjoint_Singleton_l. eassumption.
    - rewrite Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite (Setminus_Disjoint _ Scope).
      rewrite (Setminus_Disjoint Funs').
      reflexivity.
      eapply Disjoint_Singleton_r. eassumption.
      eapply Disjoint_Singleton_l. eassumption.
  Qed.

  (* 
   Lemma project_vars_Scope_Funs_eq Scope Scope' Funs Funs'
        fenv c Γ FVs xs C1 :
    project_vars Util.clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    Funs' <--> Funs \\ (Scope' \\ Scope).
  Proof.
    intros hvar; induction hvar; eauto.
    - rewrite Setminus_Same_set_Empty_set, Setminus_Empty_set_neut_r. reflexivity.
    - rewrite IHhvar.  
      rewrite <project_var_Scope_Funs_eq at 2. [| eassumption ]. Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite (Setminus_Disjoint _ Scope). reflexivity.
      eapply Disjoint_Singleton_l. eassumption.
    - rewrite Setminus_Union_distr.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite (Setminus_Disjoint _ Scope).
      rewrite (Setminus_Disjoint Funs').
      reflexivity.
      eapply Disjoint_Singleton_r. eassumption.
      eapply Disjoint_Singleton_l. eassumption.
  Qed.
   *)

  Lemma project_vars_cost_eq
        Scope `{ToMSet Scope} Scope' `{ToMSet Scope'} Funs `{ToMSet Funs}
        Funs' `{ToMSet Funs'}
        fenv c Γ FVs xs C1 :
    project_vars Util.clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    cost_ctx_full C1 = 3 * PS.cardinal (@mset (Funs \\ Funs') _) +
                       PS.cardinal (@mset ((FromList FVs \\ Funs) :&: (Scope' \\ Scope)) _).
  Proof with (now eauto with Ensembles_DB).
    intros Hvar; induction Hvar; eauto.
    - rewrite (Proper_carinal _ PS.empty).
      rewrite (Proper_carinal mset PS.empty).
      reflexivity.
      eapply Same_set_From_set.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set, Intersection_Empty_set_abs_r.
      rewrite FromSet_empty. reflexivity.
      eapply Same_set_From_set.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set.
      rewrite FromSet_empty. reflexivity.
    - assert (Hvar' := H3). assert (Hvar'' := H3).
      assert (Hvar''' := H3).
      eapply project_var_ToMSet_Funs in Hvar''; eauto. 
      eapply project_var_ToMSet in Hvar'; eauto. 
      rewrite cost_ctx_full_ctx_comp_ctx_f. 
      eapply (@project_var_cost_eq Scope1 H Scope2 Hvar' Funs1 _ Funs2) in H3.
      rewrite H3. erewrite IHHvar; eauto.
      rewrite <- !plus_assoc, (plus_assoc _  (3 * _)), (plus_comm _ (3 * _)).
      rewrite !plus_assoc. 
      rewrite <- NPeano.Nat.mul_add_distr_l.
      rewrite <- plus_assoc. eapply f_equal2_plus. 
      + eapply Nat_as_OT.mul_cancel_l. omega.
        rewrite PS_cardinal_union. 
        eapply Proper_carinal.  
        eapply Same_set_From_set. setoid_rewrite <- mset_eq.
        rewrite FromSet_union.
        do 2 setoid_rewrite <- mset_eq at 1.
        rewrite Union_commut, Setminus_compose. now eauto with typeclass_instances. 
        tci. eapply project_vars_Funs_l. eassumption.
        eapply project_var_Funs_l. eassumption.
        eapply FromSet_disjoint.
        do 2 setoid_rewrite <- mset_eq at 1.
        eapply Disjoint_Setminus_l...
      + rewrite PS_cardinal_union. 
        eapply Proper_carinal.  
        eapply Same_set_From_set. setoid_rewrite <- mset_eq.
        rewrite FromSet_union.
        do 2 setoid_rewrite <- mset_eq at 1.
        rewrite !(Intersection_commut _ (FromList FVs \\ _)).
        eapply project_var_Scope_Funs_eq in Hvar'''. 
        rewrite Hvar'''.
        admit. (* sets... *)
        (* rewrite <- Intersection_Union_distr. *)
        (* eapply Same_set_Intersection_compat; [| reflexivity ]. *)
        (* eapply Setminus_compose. now eautoo with typeclass_instances.  *)
        (* eapply project_var_Scope_l. eassumption. *)
        (* eapply project_vars_Scope_l. eassumption. *)
        eapply FromSet_disjoint.
        do 2 setoid_rewrite <- mset_eq at 1.
        eapply Disjoint_Included_l.  eapply Included_Intersection_compat.
        eapply Included_Setminus_compat. reflexivity. eapply project_var_Funs_l. eassumption.
        reflexivity. eapply Disjoint_Intersection_r.
        eapply Disjoint_Setminus_r...
  Admitted.          

  (*
  Lemma project_var_size_cc_heap H1 rho1 C
        Scope `{ToMSet Scope} Scope' `{ToMSet Scope'} Funs {_ : ToMSet Funs} Funs' {_ : ToMSet Funs'}
        fenv c Γ FVs x :
    project_var Util.clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    size_cc_heap (env_locs rho1 Funs') H1 =
    size_cc_heap (env_locs rho1 Funs) H1 + 3 * (PS.cardinal (@mset (Funs \\ Funs') _)).
  Proof.
    intros Hvar. inv Hvar; eauto.
    - rewrite (Proper_carinal _ PS.empty).
      simpl. rewrite <- plus_n_O.
      eapply size_cc_heap_Same_Set_compat. reflexivity.
      eapply Same_set_From_set.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set.
      rewrite FromSet_empty. reflexivity.
    - admi;;t.
    - rewrite (Proper_carinal _ PS.empty).
      simpl. rewrite <- plus_n_O.
      eapply size_cc_heap_Same_Set_compat. reflexivity.
      eapply Same_set_From_set.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set.
      rewrite FromSet_empty. reflexivity.
  Admitted.

  Lemma project_vars_size_cc_heap H1 rho1 C
        Scope `{ToMSet Scope} Scope' `{ToMSet Scope'} Funs {_ : ToMSet Funs} Funs' {_ : ToMSet Funs'}
        fenv c Γ FVs x :
    project_vars Util.clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    size_cc_heap (env_locs rho1 Funs') H1 <= size_cc_heap (env_locs rho1 Funs) H1 + 3 * (PS.cardinal (@mset (Funs \\ Funs') _)).
  Proof.
    intros Hvar. induction Hvar; eauto.
    - simpl. eapply le_plus_trans.
      eapply NPeano.Nat.eq_le_incl.
      eapply size_cc_heap_Same_Set_compat. reflexivity.
    - assert (Hs2 : ToMSet Funs2).
      { eapply project_var_ToMSet_Funs; [| eassumption ]. eassumption. } 
      eapply le_trans. apply IHHvar.
      eapply project_var_ToMSet; [| eassumption ]. eassumption.
      eassumption.
      eapply le_trans. eapply plus_le_compat_r.
      eapply project_var_size_cc_heap in H2. eassumption.
      eassumption.
      eapply project_var_ToMSet; [| eassumption ]. eassumption.
      rewrite <- !plus_assoc. eapply plus_le_compat_l.
      rewrite <- NPeano.Nat.mul_add_distr_l.
      eapply mult_le_compat_l. rewrite PS_cardinal_union. 
      eapply NPeano.Nat.eq_le_incl.
      eapply Proper_carinal.  
      eapply Same_set_From_set. setoid_rewrite <- mset_eq.
      rewrite FromSet_union.
      do 2 setoid_rewrite <- mset_eq at 1.
      rewrite Union_commut.
      rewrite Setminus_compose. reflexivity.
      eapply Decidable_ToMSet.
      eapply project_var_ToMSet_Funs; [| eassumption ]. eassumption.
      eapply project_vars_Funs_l. eassumption.
      eapply project_var_Funs_l. eassumption.
      eapply FromSet_disjoint.
      do 2 setoid_rewrite <- mset_eq at 1.
      eapply Disjoint_Setminus_l; now eauto with Ensembles_DB.
  Qed.
   *)
  
  Lemma PreCtxCompat_var_r H1 H2 rho1 rho2 C e1 e2
        Scope Scope' Funs {_ : ToMSet Funs} Funs' {_ : ToMSet Funs'}
        fenv c Γ FVs x m :
    project_var Util.clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    IInvCtxCompat_r (Pre m) (Pre (m + 3 * PS.cardinal (@mset (Funs \\ Funs') _))) H1 H2 rho1 rho2 C e1 e2.
  Proof.
    intros Hvar.
    unfold IInvCtxCompat_r, Pre.
    intros H1' H2' H2'' rho1' rho2' rho2'' c1'
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx.
    erewrite (ctx_to_heap_env_CC_size_heap _ _ _ H2' H2''); [| eassumption ].
    erewrite (project_var_cost_alloc_eq Scope Scope' Funs Funs'); [| eassumption ].
    eapply le_trans. eapply plus_le_compat_r. eassumption.
    rewrite <- plus_assoc. eapply plus_le_compat_l.
    omega.
    (* unfold mset. rewrite <- plus_assoc, <- NPeano.Nat.mul_add_distr_l. *)
    (* rewrite PS_cardinal_union.  *)
    (* rewrite Proper_carinal. eassumption.  *)
    (* eapply Same_set_From_set. setoid_rewrite <- mset_eq. *)
    (* rewrite FromSet_union. rewrite <- !mset_eq at 1. *)
    (* eapply Same_set_Intersection_Setminus. eapply Decidable_ToMSet. eassumption. *)
    (* eapply project_var_Scope_l. eassumption. *)
    (* eapply FromSet_disjoint. *)
    (* do 2 setoid_rewrite <- mset_eq at 1. *)
    (* eapply Disjoint_Setminus_r. *)
    (* eapply Included_trans. eapply Included_Intersection_r. *)
    (* now eauto with Ensembles_DB. *)
  Qed.

  
  Lemma PostCtxCompat_var_r
        Scope {Hs : ToMSet Scope} Scope' {Hs' : ToMSet Scope'} Funs {Hf : ToMSet Funs}
        Funs' {Hf' : ToMSet Funs'} fenv
        H1 H2 rho1 rho2 C e1 e2 c Γ FVs x k m s :
    project_var Util.clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    cost_ctx_full C + m <= k ->
    InvCtxCompat_r (Post m (s + 3 * PS.cardinal (@mset (Funs \\ Funs') _)) (Funs \\ Scope))
                   (Post k s (Funs' \\ Scope')) H1 H2 rho1 rho2 C e1 e2.
  Proof.
    unfold InvCtxCompat_r, Post.
    intros Hvar Hleq H1' H2' H2'' rho1' rho2' rho2'' c' c1 c2 m1 m2 
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 [[Hs1 Hs2] Hm] Hctx'.   
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx').
    subst.  
    assert (Heq := project_var_cost_eq _ _ _ _ _ _ _ _ _ _ Hvar). rewrite !Heq.
    split.
    - split.
      + assert (Hleq' : c1 <= c2) by omega. omega.
      + eapply le_trans; [| eassumption ].
        rewrite <- plus_assoc. eapply plus_le_compat_l.
        rewrite <- Heq. eassumption.
    - eapply le_trans. eassumption.
      rewrite <- !plus_assoc. eapply plus_le_compat_l.
      eapply plus_le_compat.
      eapply NPeano.Nat.max_le_compat_r. 
      eapply cost_mem_exp_Fun_mon.
      eapply Included_Setminus_compat.
      eapply project_var_Funs_l. eassumption.
      eapply project_var_Scope_l. eassumption.
      omega.
  Qed.
 
 Lemma PreCtxCompat_vars_r
       Scope {Hs : ToMSet Scope} Scope' {Hs' : ToMSet Scope'} Funs {Hf : ToMSet Funs}
       Funs' {Hf' : ToMSet Funs'} fenv
       H1 H2 rho1 rho2 C e1 e2 c Γ FVs x m :
   project_vars Util.clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
   IInvCtxCompat_r (Pre m) (Pre (m + 3 * PS.cardinal (@mset (Funs \\ Funs') _))) H1 H2 rho1 rho2 C e1 e2.
  Proof.
    intros Hvar.
    unfold IInvCtxCompat_r, Pre.
    intros H1' H2' H2'' rho1' rho2' rho2'' k
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 Hm Hctx. subst. eauto. 
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx).
    subst.  
    assert (Heq := project_vars_cost_eq _ _ _ _ _ _ _ _ _ _ Hvar).  
    erewrite (ctx_to_heap_env_CC_size_heap _ _ _ H2' H2''); [| eassumption ].
    erewrite (project_vars_cost_alloc_eq Scope Scope' Funs Funs'); [| eassumption ].
    eapply le_trans. eapply plus_le_compat_r. eassumption.
    rewrite <- plus_assoc. reflexivity.
  Qed.

   Lemma PostCtxCompat_vars_r
       Scope {Hs : ToMSet Scope} Scope' {Hs' : ToMSet Scope'} Funs {Hf : ToMSet Funs}
       Funs' {Hf' : ToMSet Funs'} fenv
       H1 H2 rho1 rho2 C e1 e2 c Γ FVs x k m s :
   project_vars Util.clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
   cost_ctx_full C + m <= k ->
   InvCtxCompat_r (Post m (s + 3 * PS.cardinal (@mset (Funs \\ Funs') _)) (Funs \\ Scope))
                  (Post k s (Funs' \\ Scope')) H1 H2 rho1 rho2 C e1 e2.
   Proof.
    unfold InvCtxCompat_r, Pre.
    intros Hvar Hleq H1' H2' H2'' rho1' rho2' rho2'' c' c1 c2 m1 m2 
           b1 b2 Heq1 Hinj1 Heq2 Hinj2 [[Hs1 Hs2] Hm] Hctx'.
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx').
    assert (Heq := project_vars_cost_eq _ _ _ _ _ _ _ _ _ _ Hvar). subst.
    rewrite !Heq.
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx').
    subst.  
    unfold Post in *. split. omega.
    eapply le_trans. eassumption.
    rewrite <- !plus_assoc. eapply plus_le_compat_l.
    eapply plus_le_compat; [| omega ].
    eapply NPeano.Nat.max_le_compat_r.
    eapply cost_mem_exp_Fun_mon.
    eapply Included_Setminus_compat. eapply project_vars_Funs_l. eassumption.
    eapply project_vars_Scope_l. eassumption.
   Qed.

  Lemma cost_heap_GC H1 H2 S `{ToMSet S} c: 
    live S H1 H2 ->
    cost_heap c H2 <= cost_heap c H1.
  Proof.
  Admitted.
  
  Lemma cost_time_heap_GC H1 H2 S `{ToMSet S} : 
    live S H1 H2 ->
    cost_time_heap H2 <= cost_time_heap H1.
  Proof.
    intros. eapply cost_heap_GC.
    eassumption.
  Qed.

  Lemma cost_mem_heap_GC H1 H2 S `{ToMSet S} : 
    live S H1 H2 ->
    cost_mem_heap H2 <= cost_mem_heap H1.
  Proof.
    intros. eapply cost_heap_GC.
    eassumption.
  Qed.

  Lemma size_cc_heap_GC H1 H2 S `{ToMSet S} F `{ToMSet F}:
    live S H1 H2 ->
    size_cc_heap F H2 <= size_cc_heap F H1.
  Proof.
  Admitted.

  Lemma PostGC : (InvGC PostG).
  Proof.
    unfold InvGC, PostG. 
    intros H1 H1' H2 H2' rho1 rho2 e1 e2 Scopes Hs Funs Hf c1 c2 m1 m2
           [[Hc1 Hc2] Hm] Hl1 Hl2.
    split.
    - eapply cost_time_heap_GC in Hl1.
      
      split. omega.
      eapply le_trans. eassumption.
      eapply mult_le_compat_l.
      eapply plus_le_compat_l.
      eapply NPeano.Nat.max_le_compat_l. eassumption.
      
    - eapply le_trans. eassumption.
      eapply plus_le_compat.
      eapply plus_le_compat_l.
      eapply NPeano.Nat.max_le_compat_l.
      eapply cost_mem_heap_GC in Hl1. eassumption.
      eapply size_cc_heap_GC in Hl1. eassumption.
  Qed.
  
  Lemma fun_in_fundefs_cost_mem_fundefs Funs {Hf : ToMSet Funs} B f tau xs e: 
    fun_in_fundefs B (f, tau, xs, e) ->
    cost_mem_exp (Funs \\ (FromList xs)) e <= cost_mem_fundefs Funs B.
  Proof.
    induction B; intros Hin; inv Hin.
    - inv H. simpl. eapply NPeano.Nat.le_max_l.
    - eapply le_trans. eapply IHB. eassumption.
      simpl. eapply NPeano.Nat.le_max_r.
  Qed.

  Lemma fun_in_fundefs_cost_time_fundefs B f tau xs e: 
    fun_in_fundefs B (f, tau, xs, e) ->
    cost_time_exp e <= cost_time_fundefs B.
  Proof.
    induction B; intros Hin; inv Hin.
    - inv H. simpl. eapply NPeano.Nat.le_max_l.
    - eapply le_trans. eapply IHB. eassumption.
      simpl. eapply NPeano.Nat.le_max_r.
  Qed.

  Lemma PostAppCompat i j IP P Scope {Hc : ToMSet Scope} Funs {Hf : ToMSet Funs}
        b d H1 H2 rho1 rho2 f1 t xs1 f2 xs2 f2' Γ k m :
    Forall2 (fun y1 y2 => cc_approx_var_env i j IP P b d H1 rho1 H2 rho2 y1 y2) (f1 :: xs1) (f2 :: xs2) -> 
    k <= S (length xs1) ->
    ~ Γ \in FromList xs2 ->
    ~ f2' \in FromList xs2 ->
    IInvAppCompat Util.clo_tag PostG
                  (Post (cost_env_app_exp_out (Eapp f1 t xs1)) m Funs) (Pre m)
                  H1 H2 rho1 rho2 f1 t xs1 f2 xs2 f2' Γ.
  Proof.
    unfold IInvAppCompat, Pre, Post, PostG.
    intros Hall Hk Hnin1 Hnin2 _ H1' H1'' H2'
           rhoc1 rhoc2 rhoc3 rho1' rho2' rho2''
           b1 b2 B1 f1' ct1 xs1' e1 l1 vs1 B
           f3 c ct2 xs2' e2 l2 env_loc2 vs2 c1 c2 m1 m2
           Heq1 Hinj1 Heq2 Hinj2
           [[Hc1 Hc2] Hm1] Hh1
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
        + eapply le_trans.
          rewrite <- !plus_assoc. eapply plus_le_compat_r.  eassumption.
          rewrite Nat.mul_add_distr_r. eapply plus_le_compat.
          * eapply mult_le_compat_l.
            eapply plus_le_compat_l.
            eapply le_trans; [| now eapply Max.le_max_r ].
            eapply Nat.max_lub. eapply le_trans.
            eapply fun_in_fundefs_cost_time_fundefs.
            eapply find_def_correct. eassumption.
            eapply max_heap_with_measure_get with (f := cost_block cost_time_fundefs) in Hgetl1.
            eassumption.
            erewrite cost_time_heap_def_closures; [| eassumption ].
            eapply Max.max_lub.
            eapply max_heap_with_measure_get with (f := cost_block cost_time_fundefs) in Hgetl1.
            eassumption.
            reflexivity.
          * rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
            rewrite !plus_assoc.
            replace (1 + 1 + (cost (Eapp f2' t (Γ :: xs2)))) with (cost (Eapp f1 t xs1) + 3)
              by (simpl; omega).
            rewrite <- plus_assoc. eapply plus_le_compat_l.
            eapply le_trans; [| eapply mult_le_compat_r with (n := 1)].
            rewrite Nat.mul_1_l.
            eapply le_trans; [| eapply Max.le_max_l ]. reflexivity.
            simpl. omega.
      - erewrite def_closures_size with (H := H1') (H' := H1''); [| eassumption ].
        unfold mset in *. 
        eapply NPeano.Nat.max_lub_iff. split.
        + eapply le_trans. eassumption.
          rewrite <- !Max.plus_max_distr_r.
          erewrite (size_cc_heap_def_closures H1' H1''); [ | admit | eassumption ].
          
(        rewrite <- Max.plus_max_distr_r. eapply NPeano.Nat.max_le_compat. Max.max_le_compat. NPeano.Nat.max_le_compat_l. Max.max_le_compat. destruct (ToMSet_name_in_fundefs B1) as [funsB HeqB]. fold mset in *. 
        split.

        + rewrite <- !Max.plus_max_distr_r.
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