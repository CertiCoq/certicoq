From CertiCoq.L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics map_util.

From CertiCoq.L6.Heap Require Import heap heap_defs 
     cc_log_rel compat closure_conversion closure_conversion_util GC.

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
  
  Import H Util.C.LR.Sem Util.C.LR.Sem.GC Util.C.LR.Sem.GC.Equiv Util.C.LR.Sem.GC.Equiv.Defs Util.C.LR.Sem.GC
         Util.C.LR Util.C Util.


  
  (** * Postcondition *)

  (** Enforces that the resource consumption of the target is within certain bounds *)
  Definition Post
             (k : nat) (* This varies locally in the proof *)
             (fvlen : nat) (* varies globally, accouts for he cost of clo env *)  
             (* (Funs : Ensemble var) *)
             (* `{ToMSet Funs} *)
             (p1 p2 : heap block * env * exp * nat * nat) :=
    match p1, p2 with
      | (H1, rho1, e1, c1, m1), (H2, rho2, e2, c2, m2) =>
        (* time bound *)
        c1 + k <= c2 + k <= c1 * (1 + max (cost_time_exp e1) (cost_time_heap H1))
                          + max (cost_time_exp e1) (cost_time_heap H1) /\
        (* The additive factor should not be necessary in time, but helps the proof *)
        (* memory bound *)
        m2 <= m1 * (1 + max (cost_mem_exp e1) (cost_mem_heap H1))
             + 2 * (max fvlen (1 + max (cost_mem_exp e1) (cost_mem_heap H1)))
    end.

  (** * Precondition *)
  
  (** Enforces that the initial heaps have related sizes *)  
  Definition Pre
             (Funs : Ensemble var)
             `{ToMSet Funs} k
             (p1 p2 : heap block * env * exp) :=
    let funs := 3 * PS.cardinal (@mset Funs _) in
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        (* Sizes of the initial heaps *)
        size_heap H2 + funs <= size_heap H1 + size_cc_heap H1 + k
    end.
  
  Lemma cost_heap_block_get H1 c l b :
    get l H1 = Some b ->
    cost_block c b <= cost_heap c H1. 
  Proof.
    eapply HL.max_with_measure_get.
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
    cost_mem_heap H1' = max (cost_mem_block b)
                             (cost_mem_heap H1).
  Proof.
    intros. unfold cost_mem_heap.
    erewrite (HL.max_with_measure_alloc _ _ _ _ H1'); eauto.
    rewrite Max.max_comm. eapply NPeano.Nat.max_compat; omega.
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

  Lemma cost_mem_heap_def_closures H1 H1' rho1 rho1' B B0 rho :
    def_closures B B0 rho1 H1 rho = (H1', rho1') ->
    cost_mem_heap H1' = match B with
                          | Fnil => cost_mem_heap H1
                          |  _ => max (cost_mem_fundefs B0) (cost_mem_heap H1)
                        end.
  Proof.
    revert H1' rho1'. induction B; intros H1' rho1' Hclo.
    - simpl in Hclo.
      destruct (def_closures B B0 rho1 H1 rho) as [H2 rho2] eqn:Hclo'.
      destruct (alloc (Clos (FunPtr B0 v) rho) H2) as [l' rho3] eqn:Hal. inv Hclo.
      unfold cost_mem_heap in *.
      erewrite (HL.max_with_measure_alloc _ _ _ _ H1'); eauto.
      unfold cost_mem_block at 2. unfold cost_value.
      destruct B.
      + erewrite (IHB H2); [| reflexivity ].
        rewrite (Max.max_l _ (cost_mem_fundefs B0)).
        reflexivity. eapply Max.le_max_l.
      + erewrite (IHB H2); [| reflexivity ].
        rewrite Max.max_comm.
        reflexivity.
    - inv Hclo; eauto.
  Qed.


  Lemma cost_mem_heap_def_closures_cons H1 H1' rho1 rho1' B B0 rho :
    B <> Fnil ->
    def_closures B B0 rho1 H1 rho = (H1', rho1') ->
    cost_mem_heap H1' = max (cost_mem_fundefs B0) (cost_mem_heap H1).
  Proof.
    intros. erewrite cost_mem_heap_def_closures; [| eassumption ].
    destruct B. reflexivity.
    congruence.
  Qed.

  Lemma cost_time_heap_def_closures H1 H1' rho1 rho1' B rho :
    def_closures B B rho1 H1 rho = (H1', rho1') ->
    cost_time_heap H1' = max (cost_time_fundefs B) (cost_time_heap H1).
  Proof.
    intros Hdef. unfold cost_time_heap. erewrite cost_heap_def_closures; [| eassumption ].
    destruct B; eauto.
  Qed.


  (* TODO move *)

  Lemma Same_set_FromList_length' (A : Type) (l1 l2 : list A):
    NoDup l1 -> NoDup l2 -> FromList l1 <--> FromList l2 -> length l1 = length l2.
  Proof.
    intros Hnd Hnd2 Heq. eapply NPeano.Nat.le_antisymm.
    eapply Same_set_FromList_length; eauto. eapply Heq. 
    eapply Same_set_FromList_length; eauto. eapply Heq.
  Qed. 


  (* TODO move *)

  Lemma PS_cardinal_singleton s x :
    FromSet s <--> [set x] ->
    PS.cardinal s = 1. 
  Proof.
    intros Heq.
    replace 1 with (length [x]) by reflexivity.
    rewrite !PS.cardinal_spec. eapply Same_set_FromList_length'.
    eapply NoDupA_NoDup. eapply PS.elements_spec2w.
    constructor; eauto. now constructor.
    rewrite <- !FromSet_elements. rewrite Heq. repeat normalize_sets.
    reflexivity.
  Qed.

  Lemma PS_cardinal_empty s :
    FromSet s <--> Empty_set _ ->
    PS.cardinal s = 0. 
  Proof.
    intros Heq.
    replace 0 with (@length var []) by reflexivity.
    rewrite !PS.cardinal_spec. eapply Same_set_FromList_length'.
    eapply NoDupA_NoDup. eapply PS.elements_spec2w.
    constructor; eauto.
    rewrite <- !FromSet_elements. rewrite Heq. repeat normalize_sets.
    reflexivity.
  Qed. 

  Lemma cardinal_name_in_fundefs B :
    unique_functions B ->
    PS.cardinal (@mset (name_in_fundefs B) _) = numOf_fundefs B.
  Proof.
    intros Hun. induction B.
    - inv Hun.
      simpl.
      rewrite Proper_carinal.  Focus 2.
      eapply Same_set_From_set. 
      rewrite <- (@mset_eq (v |: name_in_fundefs B)) at 1.
      rewrite FromSet_union. eapply Same_set_Union_compat.
      eapply ToMSet_Singleton.
      eapply ToMSet_name_in_fundefs.
      rewrite <- PS_cardinal_union. erewrite PS_cardinal_singleton.
      now rewrite <- IHB; eauto.
      rewrite <- mset_eq. reflexivity. 
      eapply FromSet_disjoint. rewrite <- !mset_eq...
      eapply Disjoint_Singleton_l. eassumption. 
    - simpl. 
      rewrite PS.cardinal_spec. erewrite Same_set_FromList_length' with (l2 := []).
      reflexivity. eapply NoDupA_NoDup. eapply PS.elements_spec2w.
      now constructor. 
      rewrite <- FromSet_elements. rewrite <- mset_eq, FromList_nil. reflexivity. 
  Qed.


  Lemma size_cc_heap_alloc H1 H1' l b :
    alloc b H1 = (l, H1') ->
    size_cc_heap H1' = size_cc_block b + size_cc_heap H1.
  Proof.
    intros Hal. unfold size_cc_heap.
    erewrite (HL.size_with_measure_alloc _ _ _ _ H1'); eauto.
    simpl. omega.
  Qed.
  
  Lemma size_cc_heap_def_closures H1 H1' rho1 rho1' B B0 rho :
    unique_functions B ->
    def_closures B B0 rho1 H1 rho = (H1', rho1') ->
    size_cc_heap H1' = 2 * (numOf_fundefs B) + size_cc_heap H1.
  Proof.
    revert H1 H1' rho1'.
    induction B; intros H1 H1' rho1' Hun Hclo.
    - simpl in Hclo.
      destruct (def_closures B B0 rho1 H1 rho) as [H2 rho2] eqn:Hclo'.
      destruct (alloc (Clos (FunPtr B0 v) rho) H2) as [l' H3] eqn:Hal.
      inv Hun. inv Hclo.
      erewrite (size_cc_heap_alloc H2 H1'); [ | eassumption ].
      erewrite  (IHB H1 H2 _ H4 Hclo'). simpl. omega. 
    - inv Hclo. simpl. reflexivity. 
  Qed.

  Lemma cost_env_app_exp_out_le e :
    cost_env_app_exp_out e <= cost_time_exp e.
  Proof.
    induction e; try eapply Max.le_max_l.
    simpl. omega.
    simpl. omega.
  Qed.

  Lemma size_cc_heap_GC H1 H2 S `{ToMSet S} b : 
    live' S H1 H2 b ->
    size_cc_heap H2 <= size_cc_heap H1.
  Proof.
    intros. eapply live_size_with_measure_leq; [| eassumption | ].
    eassumption.
    intros. eapply block_equiv_size_cc_block. eassumption.
  Qed. 
  
  Lemma cost_time_heap_GC H1 H2 S `{ToMSet S} b : 
    live' S H1 H2 b ->
    cost_time_heap H2 <= cost_time_heap H1.
  Proof.
    intros. eapply live_max_with_measure_leq; [| eassumption | ].
    eassumption.
    intros. eapply block_equiv_cost_time_block. eassumption.
  Qed.
  
  Lemma cost_mem_heap_GC H1 H2 S `{ToMSet S} b : 
    live' S H1 H2 b ->
    cost_mem_heap H2 <= cost_mem_heap H1.
  Proof.
    intros. eapply live_max_with_measure_leq; [| eassumption | ].
    eassumption.
    intros. eapply block_equiv_cost_mem_block. eassumption.
  Qed.

  Lemma fun_in_fundefs_cost_mem_fundefs Funs {Hf : ToMSet Funs} B f tau xs e: 
    fun_in_fundefs B (f, tau, xs, e) ->
    cost_mem_exp e <= cost_mem_fundefs B.
  Proof. 
    induction B; intros Hin; inv Hin.
    - inv H. eapply le_trans.
      eapply NPeano.Nat.le_max_l.
      unfold cost_mem_exp, cost_mem_fundefs.
      rewrite <- Max.max_assoc.
      unfold cost_env_funs.
      reflexivity.
    - eapply le_trans. eapply IHB. eassumption.
      unfold cost_mem_fundefs.
      eapply NPeano.Nat.max_le_compat_l. 
      eapply NPeano.Nat.le_max_r.
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


  Lemma size_cc_heap_leq H1 :
    size_cc_heap H1 <= size_heap H1 * cost_mem_heap H1.
  Proof.
    unfold size_heap, size_cc_heap, cost_mem_heap, cost_heap. 
    unfold size_with_measure, max_with_measure.
    eapply le_trans; [| eapply fold_left_mult ]. simpl.
    eapply fold_left_monotonic; [| reflexivity ].
    intros n1 n2 [l1 b1] Hleq.
    eapply plus_le_compat. eassumption. simpl. 
    destruct b1.
    + simpl. omega.
    + unfold size_cc_block, size_val, cost_mem_block.
      rewrite NPeano.Nat.mul_1_l.
      eapply Max.le_max_l.
    + simpl. omega.
  Qed.

  (** * Compat lemmas *)
  
  Lemma PostBase e1 e2 k
        (Funs : Ensemble var) { _ : ToMSet Funs} A A' :
    k <= cost_env_app_exp_out e1 ->
    A' <= A + (1 + cost_mem_exp e1) ->
    InvCostBase (Post k A) (Pre Funs A') e1 e2.
  Proof.
    unfold InvCostBase, Post, Pre.
    intros Hleq H1' H2' rho1' rho2' c  Hm.
    split.
    + split. omega. 
      rewrite NPeano.Nat.mul_add_distr_l, Nat.mul_1_r.
      rewrite <- !plus_assoc. eapply plus_le_compat_l.
      eapply le_trans; [| eapply le_plus_r ]. 
      eapply le_trans. eassumption. 
      eapply le_trans. eapply cost_env_app_exp_out_le. 
      eapply Nat.le_max_l.
    + eapply le_trans. eapply le_plus_l.
      eapply le_trans. eassumption.
      rewrite NPeano.Nat.mul_add_distr_l.
      rewrite NPeano.Nat.mul_1_r.
      rewrite <- !plus_assoc. eapply plus_le_compat_l. 
      eapply plus_le_compat. eapply le_trans; [| eapply mult_le_compat_l; eapply Max.le_max_r ].
      eapply size_cc_heap_leq.
      eapply le_trans. eassumption. simpl.
      rewrite <- plus_n_O. eapply plus_le_compat.
      eapply Nat.le_max_l.
      eapply le_trans; [| eapply Nat.le_max_r ].
      eapply le_n_S. eapply Nat.le_max_l.
  Qed.
  
  Lemma PostAppCompat i j IP P Funs {Hf : ToMSet Funs}
        b H1 H2 rho1 rho2 f1 t xs1 f2 xs2 f2' Γ k A :
    Forall2 (fun y1 y2 => cc_approx_var_env i j IP P b H1 rho1 H2 rho2 y1 y2) (f1 :: xs1) (f2 :: xs2) -> 
    k <= (cost_env_app_exp_out (Eapp f1 t xs1)) ->
    ~ Γ \in FromList xs2 ->
    ~ f2' \in FromList xs2 ->
    IInvAppCompat Util.clo_tag (Post 0)
                  (Post k A) (Pre Funs A)
                  H1 H2 rho1 rho2 f1 t xs1 f2 xs2 f2' Γ.
  Proof.
    unfold IInvAppCompat, Pre, Post.
    intros Hall Hk Hnin1 Hnin2 _ H1' H1'' Hgc1 H2' Hgc2 env_loc
           rhoc1 rhoc2 rhoc3 rho1' rho2' rho2''
           b1 b2 B1 f1' ct1 xs1' e1 l1 vs1 B
           f3 c ct2 xs2' e2 l2 env_loc2 vs2 c1 c2 m1 m2 d3 d4
           Heq1 Hinj1 Heq2 Hinj2
           [[Hc1 Hc2] Hm1] Hh1
           Hgetf1 Hgetl1 Hgetel Hfind1 Hgetxs1 Hclo Hset1 Gc1
           Hgetf2 Hgetxs2 Hset2 Hgetl2 Hfind2 Gc2. 
    assert (Hlen := Forall2_length _ _ _ Hall). inversion Hlen as [Hlen'].
    assert (Hleq : Init.Nat.max (cost_time_exp e1) (cost_time_heap Hgc1) <=
                   Init.Nat.max (cost_time_exp (Eapp f1 t xs1)) (cost_time_heap H1')). 
    { eapply le_trans; [| now eapply Max.le_max_r ].
      eapply Nat.max_lub. eapply le_trans.
      eapply fun_in_fundefs_cost_time_fundefs.
      eapply find_def_correct. eassumption.
      eapply HL.max_with_measure_get with (f := cost_block cost_time_fundefs) in Hgetl1.
      eassumption.
      eapply le_trans. eapply cost_time_heap_GC; [ | eassumption ]. tci.
      erewrite cost_time_heap_def_closures with (H1 := H1') (H1' := H1''); [| eassumption ].
      eapply Max.max_lub.
      eapply HL.max_with_measure_get with (f := cost_block cost_time_fundefs) in Hgetl1.
      eassumption.
      reflexivity. }

    { rewrite <- !plus_n_O in *. split.
      - split.
        + simpl. omega.
        + eapply le_trans. 
          rewrite <- !plus_assoc. eapply plus_le_compat_r. eassumption.
          rewrite <- plus_assoc. rewrite (plus_comm (Init.Nat.max (cost_time_exp e1) (cost_time_heap Hgc1))). 
          rewrite plus_assoc. eapply plus_le_compat; [| omega ]. 
          rewrite Nat.mul_add_distr_r.
          eapply plus_le_compat.
          * eapply mult_le_compat_l.
            eapply plus_le_compat_l. eassumption.
            
          * rewrite Nat.mul_add_distr_l, Nat.mul_1_r.
            rewrite !plus_assoc. 
            replace (1 + 1 + (cost (Eapp f2' t (Γ :: xs2)))) with (cost (Eapp f1 t xs1) + 3)
              by (simpl; omega). 
            rewrite <- plus_assoc. eapply plus_le_compat_l.
            eapply le_trans; [| eapply mult_le_compat_r with (n := 1)].
            rewrite Nat.mul_1_l.
            eapply le_trans; [| eapply Max.le_max_l ]. unfold cost_time_exp.
            eapply le_trans. eapply plus_le_compat_l. eassumption. 
            reflexivity.
            simpl. omega.
      - erewrite def_closures_size with (H := H1') (H' := H1''); [| eassumption ].
              unfold mset in *. rewrite <- !NPeano.Nat.mul_max_distr_r, <- !NPeano.Nat.add_max_distr_r.
         
        eapply NPeano.Nat.max_le_compat.        
        + eapply le_trans. eassumption. eapply plus_le_compat. 

          eapply mult_le_compat_l. eapply plus_le_compat_l.
          eapply le_trans; [| eapply Max.le_max_r ].
          eapply Max.max_lub. 
          unfold cost_mem_heap. 
          eapply le_trans; [| eapply HL.max_with_measure_get; now apply Hgetl1  ].
          eapply le_trans. 
          eapply fun_in_fundefs_cost_mem_fundefs.
          eassumption.
          eapply find_def_correct. eassumption.
          reflexivity.
          
          eapply le_trans. 
          eapply cost_mem_heap_GC; [| eassumption ]. tci. 
          erewrite (cost_mem_heap_def_closures_cons H1' H1''); [| | eassumption ].
          eapply Max.max_lub.
          eapply le_trans; [| eapply HL.max_with_measure_get; now apply Hgetl1  ].
          reflexivity. reflexivity.
          intros Heq; subst. inv Hfind1.

          eapply mult_le_compat_l. 
          eapply le_trans; [| eapply Max.le_max_r ].
          eapply Max.max_lub.
          eapply plus_le_compat_l.
          eapply le_trans; [| eapply Max.le_max_r ].
          
          eapply le_trans; [| eapply HL.max_with_measure_get; now apply Hgetel ].
          reflexivity.
          eapply plus_le_compat_l.

          eapply Max.max_lub. eapply le_trans; [| eapply Max.le_max_r ].          
          eapply le_trans; [| eapply HL.max_with_measure_get; now apply Hgetl1 ].
          eapply fun_in_fundefs_cost_mem_fundefs; eauto. eapply find_def_correct. eassumption. 

          
          eapply le_trans. 
          eapply cost_mem_heap_GC; [| eassumption ]. tci.
          erewrite (cost_mem_heap_def_closures_cons H1' H1''); [| | eassumption ].
          eapply Max.max_lub.
          eapply le_trans; [| eapply Max.le_max_r ].          
          eapply le_trans; [| eapply HL.max_with_measure_get; now apply Hgetl1  ].
          reflexivity.
          eapply Max.le_max_r. intros Heq; subst. inv Hfind1.
          
        + eapply le_trans. eapply le_plus_l.
          eapply le_trans. eassumption.
          rewrite NPeano.Nat.mul_add_distr_r.
          eapply plus_le_compat. 
          
          rewrite NPeano.Nat.mul_add_distr_l, NPeano.Nat.mul_1_r.
          rewrite <- plus_assoc. eapply plus_le_compat_l.
          
          rewrite NPeano.Nat.mul_add_distr_l, NPeano.Nat.mul_1_r.

          eapply le_trans; [| eapply le_plus_l ].
          
          eapply le_trans; [| eapply mult_le_compat_l; eapply Max.le_max_r ].
          eapply size_cc_heap_leq. 
          eapply le_trans; [| eapply mult_le_compat_l; eapply Nat.le_max_l ]. omega.  
    }
  Qed. 
  
  Lemma PostConstrCompat i j IP P k
        b H1 H2 rho1 rho2 x c ys1 ys2 e1 e2 A :
    k <= cost_env_app_exp_out (Econstr x c ys1 e1) ->
    Forall2 (cc_approx_var_env i j IP P b H1 rho1 H2 rho2) ys1 ys2 ->
    InvCtxCompat (Post k A)
                 (Post 0 A) (Econstr_c x c ys1 Hole_c) (Econstr_c x c ys2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold InvCtxCompat, Post.
    intros Hleqk Hall H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1 c2 c1' c2'
           m1 m2 [[Hc1 Hc2] Hm] Hctx1 Hctx2.
    assert (Hlen := Forall2_length _ _ _ Hall). 
    inv Hctx1. inv Hctx2. inv H13. inv H16.
    rewrite !plus_O_n in *. simpl cost_ctx in *.
    rewrite !Hlen in *.
    split.
    - split.
      + rewrite !(plus_comm _ (S (length _))). rewrite <- !plus_assoc.
        assert (Hleq : c1 <= c2).
        { omega. }
        eapply plus_le_compat_l. eapply le_trans.
        eapply plus_le_compat_r. eassumption. reflexivity.
      + rewrite NPeano.Nat.mul_add_distr_r. 
        rewrite <- plus_assoc, (plus_comm (S (length _))). 
        rewrite <- plus_assoc, (plus_comm (S _ * _)).
        rewrite (plus_assoc (c1 * _)).  
        assert (Hleq :  Init.Nat.max (cost_time_exp e1) (cost_time_heap H1'') <=
                        Init.Nat.max (cost_time_exp (Econstr_c x c ys1 Hole_c |[ e1 ]|))
                                     (cost_time_heap H1')
               ).
        { erewrite (cost_time_heap_alloc H1' H1''); [| eassumption ]. simpl cost_block.
          eapply NPeano.Nat.max_le_compat_r. now eapply Max.le_max_r. }
        
        eapply plus_le_compat.
        eapply le_trans; [ | eapply le_trans; [ now apply Hc2 |] ].
        omega.
        eapply plus_le_compat. 
        eapply mult_le_compat_l. omega. omega. 

        rewrite NPeano.Nat.mul_add_distr_l, Nat.mul_1_r.
        rewrite plus_comm. eapply plus_le_compat_l.
        eapply le_trans. eassumption. 
        rewrite <- (Nat.mul_1_l (cost_env_app_exp_out _)).
        eapply mult_le_compat. omega.
        eapply le_trans; [| eapply Max.le_max_l ].
        eapply cost_env_app_exp_out_le.
    - rewrite <- !plus_n_O in *. eapply le_trans. eassumption.
      eapply plus_le_compat.
      eapply mult_le_compat_l.
      eapply plus_le_compat_l.
      erewrite cost_mem_heap_alloc; [| eassumption ].      
      unfold cost_mem_exp. reflexivity.

      eapply mult_le_compat_l. 
      eapply Nat.max_le_compat_l.
      erewrite cost_mem_heap_alloc; [| eassumption ].      
      eapply plus_le_compat_l. simpl. eapply Nat.max_le_compat_r.
      unfold cost_mem_exp. reflexivity.
  Qed.
  
  Lemma PreConstrCompat i j k IP P
        (Funs Funs' : Ensemble var) {Hf : ToMSet Funs} {Hf' : ToMSet Funs'}
        b H1 H2 rho1 rho2 x c ys1 ys2 e1 e2 :
    Forall2 (fun y1 y2 => cc_approx_var_env i j IP P b H1 rho1 H2 rho2 y1 y2) ys1 ys2 ->
    Funs' \subset Funs ->
    IInvCtxCompat (Pre Funs k) (Pre Funs' k)
                  (Econstr_c x c ys1 Hole_c) (Econstr_c x c ys2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold IInvCtxCompat, Pre.
    intros Hall Hsub H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1' c2'
           Hm Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H13. inv H16.
    
    unfold size_heap in *.
    erewrite HL.size_with_measure_alloc; [| reflexivity | eassumption ].
    erewrite (HL.size_with_measure_alloc _ _ _ _ H1''); [| reflexivity | eassumption ].
    erewrite (size_cc_heap_alloc H1' H1''); [| eassumption ]. simpl size_val. 
    
    rewrite !(plus_comm _ (S (length _))), <- !plus_assoc.
    eapply plus_le_compat.
    repeat subst_exp. eapply Forall2_length in Hall.
    eapply (@getlist_length_eq value) in H11; try eassumption.
    eapply (@getlist_length_eq value) in H14; try eassumption.
    subst. rewrite <- H14, <- H11.
    replace (@length var ys1) with (@length M.elt ys1) in *. rewrite  Hall.
    reflexivity. 
    reflexivity. 
    assert (Hsubleq : 3 * PS.cardinal (@mset Funs' _) <= 3 * PS.cardinal (@mset Funs _)).
    { eapply mult_le_compat_l. eapply PS_elements_subset. eassumption. }
    omega. 
  Qed.
  

  Lemma PostProjCompat k x c y1 y2 e1 e2 n A :
    k <= (cost_env_app_exp_out (Eproj x c n y1 e1)) ->
    InvCtxCompat (Post k A)
                 (Post 0 A)
                 (Eproj_c x c n y1 Hole_c) (Eproj_c x c n y2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold InvCtxCompat, Post.
    intros Hleqk H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1 c2 c1' c2'
           m1 m2 [[Hc1 Hc2] Hm] Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H17. inv H13.
    split; rewrite <- !plus_n_O in *.
    - split.
      + assert (Hleq : c1 <= c2). 
        { omega. } 
        simpl cost_ctx. eapply le_trans. eapply plus_le_compat_r.
        eapply plus_le_compat_r. eassumption. simpl. omega.
      + rewrite !plus_O_n.
        rewrite NPeano.Nat.mul_add_distr_r.
        rewrite <- plus_assoc, (plus_comm (cost_ctx _)). 
        rewrite <- plus_assoc. rewrite (plus_comm ((cost_ctx _) * _)). 
        rewrite (plus_assoc (c1 * _)). eapply plus_le_compat. 
    
        eapply le_trans; [ | eapply le_trans; [ now apply Hc2 |] ].
        omega.
        eapply plus_le_compat.
        
        eapply mult_le_compat_l.
        eapply plus_le_compat_l.
        eapply NPeano.Nat.max_le_compat_r. now eapply Max.le_max_r.
        eapply NPeano.Nat.max_le_compat_r. now eapply Max.le_max_r.
        
        rewrite NPeano.Nat.mul_add_distr_l, Nat.mul_1_r.
        rewrite plus_comm. eapply plus_le_compat_l. eapply le_trans. eassumption. 
        rewrite <- (Nat.mul_1_l (cost_env_app_exp_out _)).
        eapply mult_le_compat. simpl. omega.
        eapply le_trans. eapply cost_env_app_exp_out_le. eapply Max.le_max_l.
    - eassumption.
  Qed.
  
  Lemma PreProjCompat x1 x2 c n y1 y2 e1 e2 k
        (Funs : Ensemble var) {Hf : ToMSet Funs} (Funs' : Ensemble var) {Hf' : ToMSet Funs'} :
    Funs' \subset Funs -> 
    IInvCtxCompat (Pre Funs k) (Pre Funs' k)
                  (Eproj_c x1 c n y1 Hole_c) (Eproj_c x2 c n y2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold IInvCtxCompat, Pre.
    intros Hsub H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1' c2'
           Hm1 Hctx1 Hctx2.
    inv Hctx1. inv Hctx2. inv H13. inv H17.  
    eapply le_trans; [| now apply Hm1 ]. eapply plus_le_compat_l.
    eapply mult_le_compat_l. eapply PS_elements_subset. eassumption. 
  Qed.

  Lemma cost_time_exp_case_hd x1 c1 e1 P1 :
    cost_time_exp e1 <= cost_time_exp (Ecase x1 ((c1, e1) :: P1)).
  Proof.
    eapply le_trans; [| eapply Max.le_max_r ].
    eapply Max.le_max_l. 
  Qed.

  Lemma cost_time_exp_case_tl x1 c1 e1 P1 :
    cost_time_exp (Ecase x1 P1) <= cost_time_exp (Ecase x1 ((c1, e1) :: P1)).
  Proof.
    eapply Nat.max_le_compat_l. 
    eapply Max.le_max_r.
  Qed.

  Lemma cost_mem_exp_case_hd x1 c1 e1 P1 :
    cost_mem_exp e1 <= cost_mem_exp (Ecase x1 ((c1, e1) :: P1)).
  Proof.
    eapply Nat.max_le_compat_l.
    eapply le_trans; [| eapply le_plus_r ].
    eapply Max.le_max_l. 
  Qed.
  
  Lemma cost_mem_exp_case_tl x1 c1 e1 P1 :
    cost_mem_exp (Ecase x1 P1) <= cost_mem_exp (Ecase x1 ((c1, e1) :: P1)).
  Proof.
    eapply Nat.max_le_compat_l. 
    eapply plus_le_compat_l. 
    eapply Max.le_max_r.
  Qed.
  
  Lemma cost_time_exp_case_In x1 c1 e1 P1 :
    List.In (c1, e1) P1 ->
    cost_time_exp e1 <= cost_time_exp (Ecase x1 P1).
  Proof.
    induction P1; intros Hin.
    - now inv Hin.
    - inv Hin.
      + eapply le_trans; [| eapply Max.le_max_r ].
        eapply Max.le_max_l.
      + eapply le_trans. eapply IHP1. eassumption.
        eapply Nat.max_le_compat_l. destruct a as [c' e']. 
        eapply Max.le_max_r.
  Qed.

  Lemma cost_mem_exp_case_In x1 c1 e1 P1 :
    List.In (c1, e1) P1 ->
    cost_mem_exp e1 <= cost_mem_exp (Ecase x1 P1).
  Proof.
    induction P1; intros Hin.
    - now inv Hin.
    - inv Hin.
      + eapply Nat.max_le_compat_l.
        eapply le_trans; [| eapply le_plus_r ].
        eapply Max.le_max_l.
      + eapply le_trans. eapply IHP1. eassumption.
        eapply Nat.max_le_compat_l.
        eapply plus_le_compat_l. destruct a as [c' e'].
        eapply Max.le_max_r.
  Qed.

  Lemma PostCaseCompat k x1 x2 P1 P2 A :
    k <= (cost_env_app_exp_out (Ecase x1 P1)) ->
    InvCaseCompat (Post k A)
                  (fun e1 e2 => Post 0 A) x1 x2 P1 P2.
  Proof with (now eauto with Ensembles_DB).
    unfold InvCaseCompat, Post.
    intros Hleqk H1' H2' rho1' rho2' m1 m2
           c1 c2 c e1 tc1 e2 tc2 Hin1 Hin2 Hleq1 [[Hc1 Hc2] Hm].
    split; rewrite <- !plus_n_O in *.
    - split.
      + simpl. omega.
      + rewrite NPeano.Nat.mul_add_distr_r.
        rewrite <- !plus_assoc. rewrite (plus_comm (c * _)). 
        rewrite (plus_assoc (c1 * _)). eapply plus_le_compat. 
        
        eapply le_trans; [ | eapply le_trans; [ now apply Hc2 |] ].
        omega.
        eapply plus_le_compat.
        
        eapply mult_le_compat_l.
        eapply plus_le_compat_l.
        eapply NPeano.Nat.max_le_compat_r. eapply cost_time_exp_case_In. eassumption.
        eapply NPeano.Nat.max_le_compat_r. eapply cost_time_exp_case_In. eassumption.
        
        rewrite NPeano.Nat.mul_add_distr_l, Nat.mul_1_r.
        eapply plus_le_compat_l. eapply le_trans. eassumption. 

        eapply le_trans; [| eapply mult_le_compat_r; eassumption ]. 
        rewrite NPeano.Nat.mul_1_l.
        eapply le_trans; [| eapply Max.le_max_l ]. eapply Max.le_max_l. 
    - eapply le_trans. eassumption. 
      eapply plus_le_compat.
      eapply mult_le_compat_l. eapply plus_le_compat_l.
      eapply Nat.max_le_compat_r. eapply cost_mem_exp_case_In. eassumption.
      eapply mult_le_compat_l.
      eapply Nat.max_le_compat_l.
      eapply plus_le_compat_l. eapply Nat.max_le_compat_r.
      eapply cost_mem_exp_case_In. eassumption.
  Qed.

  Lemma PreCaseCompat k x1 x2 P1 P2 
        (Funs : Ensemble var) {Hf : ToMSet Funs} (Funs' : exp -> Ensemble var)
        {HFe : forall e, ToMSet (Funs' e)} :
    (forall c e, List.In (c, e) P1 -> Funs' e \subset Funs) -> 
    IInvCaseCompat (Pre Funs k) (fun e1 e2  => Pre (Funs' e1) k) x1 x2 P1 P2.
  Proof with (now eauto with Ensembles_DB).
    unfold IInvCtxCompat, Pre.
    intros Hsub H1'  rho1' H2' rho2 c1 c2 e1 e2 Hin1 Hin2 hleq.
    eapply le_trans; [| eassumption ]. eapply plus_le_compat_l.
    eapply mult_le_compat_l.
    eapply PS_elements_subset. eapply Hsub. eassumption.
  Qed.

  
  Lemma PostFunsCompat B1 B2 e1 e2 k m A  :
    k <= cost_env_app_exp_out (Efun B1 e1) + m ->
    InvCtxCompat (Post k A)
                 (Post m A) (Efun1_c B1 Hole_c) (Efun1_c B2 Hole_c) e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold InvCtxCompat, Post.
    intros Hleq H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1 c2 c1' c2'
           m1 m2 [[Hc1 Hc2] Hm] Hctx1 Hctx2.
    (* simpl *) 
    (* assert (Hlen := Forall2_length _ _ _ Hall).  *)
    inv Hctx1. inv Hctx2. inv H4. inv H9. inv H10.
    (* rewrite <- !plus_O_n in Hc1, Hc2, Hc1. *)
    rewrite !plus_O_n. simpl cost_ctx.
    split.
    - split. 
      + rewrite <- !plus_assoc. eapply plus_le_compat_r.
        omega.
      + rewrite NPeano.Nat.mul_add_distr_r.
        eapply le_trans. eapply plus_le_compat_l. eassumption.
        rewrite <- plus_assoc. rewrite (plus_comm 1).
        rewrite (plus_comm _ m). rewrite <- (plus_assoc m).
        rewrite plus_assoc. 
        
        rewrite <- (plus_assoc (c1 * _)). rewrite (plus_comm (1 * _)). 
        rewrite (plus_assoc (c1 * _)). eapply plus_le_compat. 
        
        assert (Hleqs : Init.Nat.max (cost_time_exp e1) (cost_time_heap H1'') <=
                        Init.Nat.max (cost_time_exp (Efun1_c B1 Hole_c |[ e1 ]|))
                                     (cost_time_heap H1')). 
        { erewrite (cost_time_heap_def_closures H' H1''); [| eassumption ].
          erewrite (cost_time_heap_alloc H1' H'); [| eassumption ].
          simpl cost_block. rewrite Max.max_0_l. 
          Opaque mult plus. simpl (cost_time_exp (Efun1_c B1 Hole_c |[ e1 ]|)). 
          
          rewrite (Max.max_comm _ (cost_time_exp e1)).        
          rewrite <- !Max.max_assoc. eapply Max.le_max_r. } 
        
        eapply le_trans. eassumption. eapply plus_le_compat. 
        eapply mult_le_compat_l.
        eapply plus_le_compat_l. eassumption. eassumption. 
        
        rewrite Nat.mul_1_l. rewrite (plus_comm _ 1).
        eapply plus_le_compat_l.
        eapply le_trans; [| eapply Max.le_max_l ]. 
        simpl.
        eapply le_trans; [| eapply Max.le_max_l ]. omega. 
    - eapply le_trans. eassumption.
      simpl.  

      assert (Hmem :   Init.Nat.max (cost_mem_exp e1) (cost_mem_heap H1'') <=
                       Init.Nat.max (cost_mem_exp (Efun1_c B1 Hole_c |[ e1 ]|))
                                    (cost_mem_heap H1')). 
      { erewrite (cost_mem_heap_def_closures H' H1''); [| eassumption ].
        erewrite (cost_mem_heap_alloc H1' H'); [| eassumption ].      
        simpl (cost_mem_exp (Efun1_c B1 Hole_c |[ e1 ]|)). 
        destruct B1.
        + unfold cost_mem_fundefs. unfold cost_mem_exp.
          simpl (cost_env_exp (Efun (Fcons v f l e B1) e1)).
          eapply Max.max_lub.

          eapply Max.max_lub.
          rewrite <- !Max.max_assoc. now eapply Max.le_max_l.
          rewrite !Max.max_assoc.
          eapply le_trans; [| eapply Max.le_max_l ]. 
          now eapply Max.le_max_r. 

          eapply Max.max_lub.
          rewrite !Max.max_assoc. 
          eapply le_trans; [| eapply Max.le_max_l ]. 
          eapply le_trans; [| eapply Max.le_max_l ].
          rewrite <- !Max.max_assoc.
          eapply NPeano.Nat.max_le_compat_l.
          now eapply Max.le_max_r.

          simpl cost_mem_block. 
          rewrite !Max.max_assoc.
          eapply NPeano.Nat.max_le_compat_r.
          eapply le_trans; [| eapply Max.le_max_l ]. 
          eapply le_trans; [| eapply Max.le_max_l ]. 
          eapply le_trans; [| eapply Max.le_max_l ]. 
          eapply le_trans; [| eapply Max.le_max_r ].
          erewrite Proper_carinal with (x := (fundefs_fv (Fcons v f l e B1)))
                                         (y := @mset (occurs_free_fundefs (Fcons v f l e B1)) _).
          eapply PS_elements_subset.
          eapply Included_trans. eapply key_set_Restrict_env.
          now eapply restrict_env_correct. 
          rewrite <- FromSet_elements. now eapply fundefs_fv_correct. 
          eapply Same_set_From_set. 
          rewrite <- mset_eq. symmetry; now eapply fundefs_fv_correct.
        + inv H0. simpl cost_mem_block. unfold cost_mem_exp. 
          simpl (cost_env_exp (Efun Fnil e1)). 
          
          eapply Max.max_lub. now eapply Max.le_max_l. 
          
          eapply Max.max_lub. rewrite PS_cardinal_empty. omega.

          (* rewrite Proper_carinal with (y := PS.empty). unfold PS.cardinal. simpl. omega. *)
          (* eapply Same_set_From_set.  *)
          rewrite <- mset_eq. split; [| now eauto with Ensembles_DB ]. 
          
          eapply Included_trans. eapply key_set_Restrict_env.
          now eapply restrict_env_correct. 
          eapply Included_trans. eapply fundefs_fv_correct. normalize_occurs_free.
          reflexivity. 
          now eapply Max.le_max_r.
      }
      simpl in *. 
      eapply plus_le_compat;[| eapply mult_le_compat_l; eapply Nat.max_le_compat_l; omega ].
      eapply mult_le_compat_l. 
      eapply plus_le_compat_l. eassumption. 
  Qed.



  Lemma PreSubsetCompat (Funs : Ensemble var) {Hf : ToMSet Funs} (Funs' : Ensemble var) {Hf' : ToMSet Funs'}
        k H1 rho1 e1 H2 rho2 e2  :
    Pre Funs k (H1, rho1, e1) (H2, rho2, e2) ->
    Funs' \subset Funs -> 
    Pre Funs' k (H1, rho1, e1) (H2, rho2, e2). 
  Proof. 
    unfold Pre. intros Hpre Hleq.
    assert (Hsubleq : 3 * PS.cardinal (@mset Funs' _) <= 3 * PS.cardinal (@mset Funs _)).
    { eapply mult_le_compat_l. eapply PS_elements_subset. eassumption. }
    omega.
  Qed.
  
  Lemma PreFunsCompat
        (Scope : Ensemble var) {Hs : ToMSet Scope} 
        (* (Scope' : Ensemble var) {Hs' : ToMSet Scope'}  *)
        (Funs : Ensemble var) {Hf : ToMSet Funs}
        (* (Funs' : Ensemble var) {Hf' : ToMSet Funs'} *)
        (S : Ensemble var) {Hst : ToMSet S}
        (S' : Ensemble var) {Hst' : ToMSet S'}
        B1 B2 e1 e2 k m:
    k <= (1 + (PS.cardinal (@mset (occurs_free_fundefs B1) _))) + m ->
    Funs :&: S' \subset Funs :&: S ->
    Disjoint _ (name_in_fundefs B1) (Scope :|: Funs) ->
    unique_functions B1 ->
    IInvCtxCompat_Funs (Pre (Funs :&: S \\ Scope) k)
                       (Pre ((name_in_fundefs B1 :|: Funs) :&: S'  \\ (Scope \\ name_in_fundefs B1)) m) B1 B2 e1 e2.
  Proof with (now eauto with Ensembles_DB).
    unfold IInvCtxCompat.
    intros Hleq Hsub Hdis Hun H1' H2' H1'' H2'' rho1' rho2' rho1'' rho2'' c1' c2'
           Hm Hbin Hctx1 Hctx2.

    eapply PreSubsetCompat with (Funs := name_in_fundefs B1 :|: (Funs :&: S \\ Scope)); eauto with Ensembles_DB.

 
    inv Hctx1. inv Hctx2. inv H9. inv H10.

    unfold Pre in *. 

    erewrite (size_cc_heap_def_closures H' H1''); [| eassumption | eassumption ].
    rewrite Proper_carinal. Focus 2.
    eapply Same_set_From_set.
    rewrite <- (@mset_eq (name_in_fundefs B1 :|: (Funs :&: S \\ Scope))) at 1.
    rewrite FromSet_union. eapply Same_set_Union_compat.
    eapply ToMSet_name_in_fundefs.
    rewrite <- (@mset_eq (Funs :&: S \\ Scope)) at 1.
    reflexivity. tci.

    rewrite <- PS_cardinal_union. 
    erewrite (size_cc_heap_alloc H1' H'); [| eassumption ]. 
    erewrite (def_closures_size _ _ _ _ _ _ _ H4).
    unfold size_heap in *.
    erewrite (HL.size_with_measure_alloc _ _ _ _ H'); [| reflexivity | eassumption ].
    rewrite (plus_comm (PS.cardinal _ )).
    rewrite NPeano.Nat.mul_add_distr_l. rewrite plus_assoc.
    eapply le_trans. eapply plus_le_compat_r.
    eapply le_trans; [| eapply Hm ].
    
    reflexivity. 
     
    simpl. 
    assert (Heq: PS.cardinal (@mset (@key_set value (restrict_env (fundefs_fv B1) rho1')) _) =
                 PS.cardinal (@mset (occurs_free_fundefs B1) _)).
    { rewrite !PS.cardinal_spec. eapply Same_set_FromList_length'.
      eapply NoDupA_NoDup. eapply PS.elements_spec2w.
      eapply NoDupA_NoDup. eapply PS.elements_spec2w. rewrite <- !FromSet_elements.
      rewrite <- !mset_eq at 1. rewrite key_set_binding_in_map_alt. 
      rewrite <- (fundefs_fv_correct B1). reflexivity.
      rewrite <- (fundefs_fv_correct B1). eassumption. }
    assert (Heq' : 3 * PS.cardinal (@mset (name_in_fundefs B1) (ToMSet_name_in_fundefs B1)) =
                   3 * numOf_fundefs B1).
    { f_equal. eapply cardinal_name_in_fundefs. eassumption. } 
    omega. 
    
    eapply FromSet_disjoint. rewrite <- !mset_eq.
    eapply Disjoint_Included_r; [| eassumption ].
    eapply Included_trans. eapply Setminus_Included.
    eapply Included_trans. eapply Ensembles_util.Included_Intersection_l.
    now eauto with Ensembles_DB.
    eapply Included_trans. 
    eapply Included_Setminus_compat.
    rewrite Intersection_Union_distr. eapply Included_Union_compat.
    eapply Included_Intersection_l. reflexivity. 
    reflexivity.
    rewrite  Setminus_Union_distr... 
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

  Lemma project_var_ToMSet_Funs Scope1 `{ToMSet Scope1} Scope2 Funs1 Funs2 `{ToMSet Funs1}
        fenv c Γ FVs y C1 :
    project_var Util.clo_tag Scope1 Funs1 fenv c Γ FVs y C1 Scope2 Funs2 ->
    ToMSet Funs2.
  Proof.
    intros Hvar.
    assert (Hd1 := H). eapply Decidable_ToMSet in Hd1. 
    destruct Hd1 as [Hdec1]. 
    destruct (Hdec1 y).
    - assert (Funs1 <--> Funs2).
      { inv Hvar; eauto; try reflexivity.
        now exfalso; eauto. }
      tci.
    - destruct (@Dec _ Funs1 _ y).
      + assert (Funs1 \\ [set y] <--> Funs2).
        { inv Hvar; try reflexivity.
          exfalso; eauto. exfalso; eauto. }
        eapply ToMSet_Same_set; try eassumption.
        tci.
      + assert (Funs1 <--> Funs2).
        { inv Hvar; try reflexivity.
          exfalso; eauto. }
        eapply ToMSet_Same_set; try eassumption.
  Qed.   

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
    - simpl cost_ctx_full. erewrite PS_cardinal_singleton. 
      reflexivity.
      rewrite <- mset_eq. 
      split. eapply Included_trans.
      eapply Setminus_Setminus_Included. tci.
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l...
      reflexivity...
      eapply Singleton_Included. constructor; eauto.
      intros Hc. inv Hc. eauto.
    - rewrite PS_cardinal_empty. reflexivity. 
      rewrite <- mset_eq. rewrite Setminus_Same_set_Empty_set. reflexivity. 
  Qed.
  

  Lemma project_vars_cost_alloc_eq Scope `{ToMSet Scope} Scope'
        Funs `{ToMSet Funs}
        Funs' `{ToMSet Funs'}
        fenv c Γ FVs xs C1 :
    project_vars Util.clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    cost_alloc_ctx_CC C1 = 3 * PS.cardinal (@mset (Funs \\ Funs') _).
  Proof with (now eauto with Ensembles_DB).
    intros Hvar; induction Hvar; eauto.
    - rewrite PS_cardinal_empty. reflexivity. 
      rewrite <- mset_eq, Setminus_Same_set_Empty_set.
      reflexivity.
    - assert (Hvar' := H2); assert (Hvar'' := H2).
      eapply (project_var_ToMSet_Funs Scope1 Scope2 Funs1 Funs2) in  Hvar''; eauto. 
      rewrite cost_alloc_ctx_CC_comp_ctx_f. 
      eapply (@project_var_cost_alloc_eq Scope1 Scope2 Funs1 _  Funs2 _) in H2.
      rewrite H2. erewrite IHHvar; eauto.
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
      eapply Disjoint_Setminus_l... tci.
      eapply project_var_ToMSet in Hvar'; tci.
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
    - rewrite !PS_cardinal_empty.
      reflexivity.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set, Intersection_Empty_set_abs_r.
      reflexivity.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set.
      reflexivity.
    - simpl cost_ctx_full.

      erewrite PS_cardinal_singleton. 
      erewrite PS_cardinal_empty. omega.
      rewrite <- mset_eq. 
      rewrite Setminus_Union_distr, (Setminus_Disjoint [set x]).
      rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
      rewrite Intersection_Disjoint.
      reflexivity.
      eapply Disjoint_Singleton_r. intros Hc; inv Hc; eauto.
      eapply Disjoint_Singleton_l. eassumption. 

      rewrite <- mset_eq.
      split. eapply Included_trans. eapply Setminus_Setminus_Included; tci...
      now eauto with Ensembles_DB. 
      
      eapply Singleton_Included. constructor; eauto.
      intros Hc. inv Hc; eauto. 
    - rewrite PS_cardinal_empty.
      erewrite PS_cardinal_singleton.
      simpl. reflexivity.
      + rewrite <- mset_eq.
        rewrite Setminus_Union_distr, (Setminus_Disjoint [set x]).
        rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_r.
        rewrite Intersection_commut, Intersection_Same_set.
        reflexivity.
        eapply Singleton_Included.
        constructor. eapply nthN_In. eassumption.
        eassumption.
        eapply Disjoint_Singleton_l. eassumption.
      + rewrite <- mset_eq.
        rewrite Setminus_Same_set_Empty_set. reflexivity. 
  Qed.

  (* TODO move *) 
  Lemma Intersection_Setmius_Disjoint {A} (S1 S2 S3 : Ensemble A) :
    Disjoint _ S2 S3 ->
    (S1 \\ S2) :&: S3 <--> S1 :&: S3.
  Proof.
    intros Hd. split.
    - intros x Hin. inv Hin. inv H. constructor; eauto.
    - intros x Hin. inv Hin. constructor; eauto.
      constructor. eassumption. intros Hc. eapply Hd; constructor; eauto. 
  Qed.

  Lemma Intersection_Setmius_Setminus_Disjoint {A} (S1 S2 S3 S4 : Ensemble A) :
    Disjoint _ S3 S4 ->
    (S1 \\ (S2 \\ S4)) :&: S3 <--> (S1 \\ S2) :&: S3.
  Proof.
    intros Hd. split.
    - intros x Hin. inv Hin. inv H. constructor; eauto. constructor; eauto.
      intros Hc. eapply H2; eauto. constructor. eassumption.
      intros Hc'. eapply Hd; constructor; eauto.
    - intros x Hin. inv Hin. constructor; eauto. inv H. 
      constructor. eassumption. intros Hc. eapply Hd; constructor; eauto.
      inv Hc. exfalso; eauto.
  Qed.

  Lemma project_vars_cost_eq
        Scope `{ToMSet Scope} Scope' `{ToMSet Scope'} Funs `{ToMSet Funs}
        Funs' `{ToMSet Funs'}
        fenv c Γ FVs xs C1 :
    project_vars Util.clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    cost_ctx_full C1 = 3 * PS.cardinal (@mset (Funs \\ Funs') _) +
                       PS.cardinal (@mset ((FromList FVs \\ Funs) :&: (Scope' \\ Scope)) _).
  Proof with (now eauto with Ensembles_DB).
    intros Hvar; induction Hvar; eauto.
    - rewrite !PS_cardinal_empty.

      reflexivity.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set, Intersection_Empty_set_abs_r.
      reflexivity.
      rewrite <- mset_eq, Setminus_Same_set_Empty_set.
      reflexivity.
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
        assert (Hvar1 := Hvar'''). eapply project_var_Scope_Funs_eq in Hvar'''. 
        rewrite Hvar'''.
        assert (Hseq : (Scope3 \\ Scope2) :&: (FromList FVs \\ (Funs1 \\ (Scope2 \\ Scope1))) <-->
                                          (Scope3 \\ Scope2) :&: (FromList FVs \\ Funs1)).
        { rewrite Intersection_commut. rewrite Intersection_Setmius_Setminus_Disjoint.
          rewrite Intersection_commut. reflexivity. 
          now eauto with Ensembles_DB. }

        rewrite Hseq.
        rewrite <- Intersection_Union_distr.
        eapply Same_set_Intersection_compat; [| reflexivity ].
        eapply Setminus_compose. now eauto with typeclass_instances.
        eapply project_var_Scope_l. eassumption.
        eapply project_vars_Scope_l. eassumption.
        eapply FromSet_disjoint.
        do 2 setoid_rewrite <- mset_eq at 1.
        eapply Disjoint_Included_l.  eapply Included_Intersection_compat.
        eapply Included_Setminus_compat. reflexivity. eapply project_var_Funs_l. eassumption.
        reflexivity. eapply Disjoint_Intersection_r.
        eapply Disjoint_Setminus_r...

        Grab Existential Variables. tci. 
  Qed.          
  

  Lemma project_var_Scope_Funs_subset Scope Scope' Funs Funs'
        fenv c Γ FVs xs C1 :
    project_var Util.clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    Funs \\ Funs' \subset Scope' \\ Scope. 
  Proof.
    intros Hvar. inv Hvar.
    now eauto with Ensembles_DB.
    rewrite Setminus_Union_distr.
    eapply Included_Union_preserv_l.
    rewrite (Setminus_Disjoint [set xs]).
    eapply Setminus_Included_Included_Union.
    rewrite Union_Setminus_Included.
    now eauto with Ensembles_DB. tci. reflexivity. 
    eapply Disjoint_Singleton_l. eassumption. 

    now eauto with Ensembles_DB. 
  Qed.

  Lemma project_vars_Scope_Funs_subset
        Scope Scope' {_ : ToMSet Scope}
        Funs {_ : ToMSet Funs} Funs'
        fenv c Γ FVs xs C1 :
    project_vars Util.clo_tag Scope Funs fenv c Γ FVs xs C1 Scope' Funs' ->
    Funs \\ Funs' \subset Scope' \\ Scope. 
  Proof.
    intros Hvar. induction Hvar.

    now eauto with Ensembles_DB.

    rewrite <- Setminus_compose; [| | eapply project_vars_Funs_l; eassumption
                                 | eapply project_var_Funs_l; eassumption ]; tci. 
    rewrite <- Setminus_compose with (s3 := Scope3);
      [| | eapply project_var_Scope_l; eassumption
       | eapply project_vars_Scope_l; eassumption ]; tci. 

    rewrite (Union_commut (Scope2 \\ _)). 
    eapply Included_Union_compat.
    eapply IHHvar; tci.

    eapply project_var_ToMSet; [| eassumption ]; eauto.
    eapply project_var_ToMSet_Funs; [ | | eassumption ]; eauto.
    
    eapply project_var_Scope_Funs_subset. 
    eassumption.

    eapply Decidable_ToMSet. 
    eapply project_var_ToMSet; [| eassumption ]; eauto.
    eapply Decidable_ToMSet. 
    eapply project_var_ToMSet_Funs; [| | eassumption ]; eauto.
    
  Qed.
  

  Lemma PreCtxCompat_var_r C e1 e2 i
        Scope Scope' {_ : ToMSet Scope} {_ : ToMSet Scope'}
        Funs {_ : ToMSet Funs} Funs' {_ : ToMSet Funs'} S {_ : ToMSet S} 
        fenv c Γ FVs x :
    project_var Util.clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    x \in S ->
    IInvCtxCompat_r (Pre (Funs :&: S \\ Scope) i) (Pre (Funs' :&: S \\ Scope') i) C e1 e2.
  Proof.
    intros Hvar Hin.
    unfold IInvCtxCompat_r, Pre.
    intros H1' H2' H2'' rho1' rho2' rho2'' c1' Hm Hctx.
    erewrite (ctx_to_heap_env_CC_size_heap _ _ _ H2' H2''); [| eassumption ].
    erewrite (project_var_cost_alloc_eq Scope Scope' Funs Funs'); [| eassumption ].
    eapply le_trans with (m := size_heap H2' + (3 * PS.cardinal (@mset (Funs \\ Funs') _) +
                                                3 * PS.cardinal (@mset (Funs' :&: S \\ Scope') _))).
    omega.
     
    rewrite <- NPeano.Nat.mul_add_distr_l.
    rewrite PS_cardinal_union. eapply le_trans; [| eassumption ].
    
    eapply plus_le_compat_l.
    eapply mult_le_compat_l.
    
    rewrite !PS.cardinal_spec. eapply Same_set_FromList_length.
    eapply NoDupA_NoDup. eapply PS.elements_spec2w.

    rewrite <- !FromSet_elements, !FromSet_union. rewrite <- !mset_eq.
    
    eapply Union_Included.

    eapply Included_Setminus.
    eapply Disjoint_Included_l. 
    eapply project_var_Scope_Funs_subset. eassumption.
    now eauto with Ensembles_DB.
    intros z Hc. inv Hc.  constructor. eassumption. 
    eapply project_var_Funs in H; try eassumption.
    inv H. inv H1; eauto. now exfalso; eauto.


    eapply Included_Setminus_compat.
    eapply Included_Intersection_compat. 
    eapply project_var_Funs_l; eassumption.
    reflexivity.
    eapply project_var_Scope_l; eassumption. 

    eapply FromSet_disjoint. rewrite <- !mset_eq...

    eapply Disjoint_Setminus_l.
    eapply Setminus_Included_Included_Union.
    eapply Included_trans. eapply Included_Intersection_l. 
    now eauto with Ensembles_DB. 
  Qed.

  Lemma PreCtxCompat_ctx_to_heap_env (C : exp_ctx) (e1 e2 : exp) k m
        Funs {_ : ToMSet Funs} Funs' {_ : ToMSet Funs'} :
    Funs' \subset Funs ->
    k + cost_alloc_ctx_CC C <=  m ->
    IInvCtxCompat_r (Pre Funs k) (Pre Funs' m) C e1 e2.
  Proof.
    intros Hsub Hleq.
    unfold IInvCtxCompat_r, Pre.
    intros H1' H2' H2'' rho1' rho2' rho2'' c1' Hm Hctx.
    erewrite (ctx_to_heap_env_CC_size_heap _ _ _ H2' H2''); [| eassumption ].
    assert (Hsubleq : 3 * PS.cardinal (@mset Funs' _) <= 3 * PS.cardinal (@mset Funs _)).
    { eapply mult_le_compat_l. eapply PS_elements_subset. eassumption. }
    omega.
  Qed.

  Lemma PostCtxCompat_ctx_r
        C e1 e2 k m A :
    cost_ctx_full C + m <= k ->
    InvCtxCompat_r (Post m A)
                   (Post k A) C e1 e2.
  Proof. 
    unfold InvCtxCompat_r, Post.
    intros Hleq H1' H2' H2'' rho1' rho2' rho2'' c' c1 c2 m1 m2 
           [[Hs1 Hs2] Hm] Hctx'.   
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx'). subst. 
    omega.
  Qed.


  Lemma PreCtxCompat_vars_r
        Scope {Hs : ToMSet Scope} Scope' {Hs' : ToMSet Scope'} Funs {Hf : ToMSet Funs}
        S {HS : ToMSet S}
        Funs' {Hf' : ToMSet Funs'} fenv
        C e1 e2 c Γ FVs x i :
    FromList x \subset S ->
    project_vars Util.clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
    IInvCtxCompat_r (Pre (Funs :&: S \\ Scope) i) (Pre (Funs' :&: S \\ Scope') i) C e1 e2.
  Proof.
    intros Hsub Hvar.
    unfold IInvCtxCompat_r, Pre.
    intros H1' H2' H2'' rho1' rho2' rho2'' k Hm Hctx. subst. eauto. 
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx).
    subst.  
    assert (Heq := project_vars_cost_eq _ _ _ _ _ _ _ _ _ _ Hvar).  
    erewrite (ctx_to_heap_env_CC_size_heap _ _ _ H2' H2''); [| eassumption ].
    erewrite (project_vars_cost_alloc_eq Scope Scope' Funs Funs'); [| eassumption ].
    eapply le_trans; [| eassumption ].

    eapply le_trans with (m := size_heap H2' +
                               (3 * PS.cardinal (@mset (Funs \\ Funs') _) +
                                3 * PS.cardinal (@mset (Funs' :&: S \\ Scope') _))). 
    omega. 
    rewrite  <- NPeano.Nat.mul_add_distr_l.
    rewrite PS_cardinal_union.

    eapply plus_le_compat_l. 
    eapply mult_le_compat_l.
    rewrite !PS.cardinal_spec. eapply Same_set_FromList_length.
    eapply NoDupA_NoDup. eapply PS.elements_spec2w.
    
    rewrite <- !FromSet_elements, !FromSet_union. rewrite <- !mset_eq.

    eapply Union_Included.

    eapply Included_Setminus.
    eapply Disjoint_Included_l. 
    eapply project_vars_Scope_Funs_subset; [| | eassumption]; tci.
    now eauto with Ensembles_DB.
    intros z Hc. inv Hc.  constructor. eassumption. 
    eapply project_vars_Funs in H; try eassumption.
    inv H. eapply Hsub. eassumption. now exfalso; eauto.

    eapply Included_Setminus_compat.
    eapply Included_Intersection_compat. 
    eapply project_vars_Funs_l; eassumption.
    reflexivity.
    eapply project_vars_Scope_l; eassumption. 

    eapply FromSet_disjoint. rewrite <- !mset_eq...

    eapply Disjoint_Setminus_l.
    eapply Setminus_Included_Included_Union.
    eapply Included_trans. eapply Included_Intersection_l. 
    now eauto with Ensembles_DB. 
  Qed.
  
  Lemma PostCtxCompat_vars_r
       Scope {Hs : ToMSet Scope} Scope' {Hs' : ToMSet Scope'} Funs {Hf : ToMSet Funs}
       Funs' {Hf' : ToMSet Funs'} fenv
       C e1 e2 c Γ FVs x k m A :
   project_vars Util.clo_tag Scope Funs fenv c Γ FVs x C Scope' Funs' ->
   cost_ctx_full C + m <= k ->
   InvCtxCompat_r (Post m A)
                  (Post k A) C e1 e2.
   Proof.
    unfold InvCtxCompat_r, Pre.
    intros Hvar Hleq H1' H2' H2'' rho1' rho2' rho2'' c' c1 c2 m1 m2 
           [[Hs1 Hs2] Hm] Hctx'.
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx').
    assert (Heq := project_vars_cost_eq _ _ _ _ _ _ _ _ _ _ Hvar). subst.
    rewrite !Heq.
    assert (Hcost := ctx_to_heap_env_CC_cost _ _ _ _ _ _ Hctx').
    subst.  
    unfold Post in *. split. omega.
    eassumption.
   Qed.


   Lemma cc_approx_val_size k j GIP GP b H1 H2 x y v v' :
    Res (Loc x, H1) ≺ ^ (k; S j; GIP; GP; b) Res (Loc y, H2) ->
    get x H1 = Some v ->
    get y H2 = Some v' ->
    size_val v <= size_val v' <= size_val v + 2.
  Proof.
    intros Hres Hget1 Hget2. simpl in Hres. rewrite Hget1, Hget2 in Hres.
    destruct Hres as [Hbeq Hres]; subst.
    destruct v as [c1 vs1 | [| B1 f1] [ rho_clo |] | ]; try contradiction;
    destruct v' as [c2 vs2 | | ]; try contradiction.
    - destruct Hres as [Heq2 Hall]; subst.
      simpl. specialize (Hall 0 (NPeano.Nat.lt_0_succ _)).
      erewrite (Forall2_length _ _ _ Hall).
      simpl. omega.
    - simpl. split. omega.      
      destruct vs2 as [| [|] [| [|] [|] ]]; try contradiction.
      
      destruct Hres as [Hdeq Hall]. simpl. omega.
  Qed.

  Lemma cc_approx_val_size' k j GIP GP b H1 H2 x y v v' :
    Res (Loc x, H1) ≺ ^ (k; S j; GIP; GP; b) Res (Loc y, H2) ->
    get x H1 = Some v ->
    get y H2 = Some v' ->
    size_val v <= size_val v' <=
    size_val v + size_with_measure_filter (cost_block size_fundefs) [set x] H1.
  Proof.
    intros Hres Hget1 Hget2. simpl in Hres. rewrite Hget1, Hget2 in Hres.
    destruct Hres as [Hbeq Hres]; subst.
    destruct v as [c1 vs1 | [| B1 f1] [ rho_clo |] | ]; try contradiction;
    destruct v' as [c2 vs2 | | ]; try contradiction.
    - destruct Hres as [Heq1 Hall]; subst.
      simpl. specialize (Hall 0 (NPeano.Nat.lt_0_succ _)).
      erewrite (Forall2_length _ _ _ Hall).
      simpl. omega.
    - simpl. split. omega.
      
      destruct vs2 as [| [|] [| [|] [|] ]]; try contradiction.
      
      destruct Hres as [Hdeq Hall]. simpl.
      erewrite !HL.size_with_measure_Same_set with (S' := x |: Empty_set _) (H := H1);
        [| now eauto with Ensembles_DB ].

      erewrite HL.size_with_measure_filter_add_In;
        [| intros Hc; now inv Hc | eassumption ]. simpl.
      unfold size_fundefs. omega.
  Qed.

  
  Lemma size_reachable_leq S1 `{HS1 : ToMSet S1}  S2 `{HS2 : ToMSet S2}
        H1 H2 k GIP GP b :
    (forall j, S1 |- H1 ≼ ^ (k ; j ; GIP ; GP ; b ) H2) ->
    S2 <--> image b S1 ->
    size_with_measure_filter size_val S2 H2 <=
    size_with_measure_filter size_val S1 H1 +
    size_with_measure_filter size_cc_block S1 H1.
  Proof with (now eauto with Ensembles_DB).
    assert (HS1' := HS1).
    revert HS1 S2 HS2.
    set (P := (fun S1 => 
                 forall (HS1 : ToMSet S1) (S2 : Ensemble positive) (HS2 : ToMSet S2),
                   (forall j, S1 |- H1 ≼ ^ (k ; j ; GIP ; GP ; b ) H2) ->
                   S2 <--> image b S1 ->
                   size_with_measure_filter size_val S2 H2 <=
                   size_with_measure_filter size_val S1 H1 +
                   size_with_measure_filter size_cc_block S1 H1)). 
    assert (HP : Proper (Same_set var ==> iff) P).
    { intros S1' S2' Hseq. unfold P.
      split; intros.
      
      assert (HMS1' : ToMSet S1').
      { eapply ToMSet_Same_set. symmetry. eassumption. eassumption. }
      
      erewrite <- !(@HL.size_with_measure_Same_set _ _ _ _ _ _ _ Hseq).
      eapply H; try eassumption; repeat setoid_rewrite Hseq at 1; try eassumption.

      assert (HMS2' : ToMSet S2').
      { eapply ToMSet_Same_set; eassumption. }

      erewrite !(@HL.size_with_measure_Same_set _ _ _ _ _ _ _ Hseq).
      eapply H; try eassumption; repeat setoid_rewrite <- Hseq at 1; try eassumption.   }
    eapply (@Ensemble_ind P HP); [| | eassumption ].
    - intros HS1 S2 HS2 Hcc Heq1.
      rewrite !HL.size_with_measure_filter_Empty_set.
      rewrite image_Empty_set in Heq1.
      erewrite (@HL.size_with_measure_Same_set _ _ _ _ _ _ _ Heq1).
      rewrite HL.size_with_measure_filter_Empty_set. omega.
    - intros x S1' HS Hnin IHS HS1 S2 HS2 Hheap Heq1.
      rewrite !image_Union, !image_Singleton in Heq1.
      
      assert (Hseq : S2 <--> b x |: (S2 \\ [set b x])).
      { eapply Union_Setminus_Same_set; tci.
        rewrite Heq1... }
       
      erewrite (HL.size_with_measure_Same_set _ S2 (b x |: (S2 \\ [set b x])));
        try eassumption.
      assert (Hyp : size_with_measure_filter size_val (S2 \\ [set b x]) H2 <=
                    size_with_measure_filter size_val S1' H1 +
                    size_with_measure_filter size_cc_block S1' H1).
      { destruct (@Dec _ (image b S1') _ (b x)).
        - eapply le_trans. eapply HL.size_with_measure_filter_monotonic.
          eapply Setminus_Included.
          eapply IHS. 
          intros j. eapply cc_approx_heap_antimon; [| eapply Hheap ]...
          rewrite Heq1. rewrite Union_Same_set.
          reflexivity. 
          eapply Singleton_Included. eassumption.
        - eapply IHS. 
          intros j. eapply cc_approx_heap_antimon; [| eapply Hheap ]...
          rewrite Heq1. rewrite Setminus_Union_distr. 
          rewrite Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
          rewrite Setminus_Disjoint. reflexivity. 
          eapply Disjoint_Singleton_r. eassumption.
      }
      erewrite !HL.size_with_measure_filter_Union. 

      assert (Hyp' : size_with_measure_filter size_val [set b x] H2 <=
                     size_with_measure_filter size_val [set x] H1 +
                     size_with_measure_filter size_cc_block [set x] H1).
      { erewrite !HL.size_with_measure_Same_set with (S' := x |: Empty_set _) (H := H1);
        [| now eauto with Ensembles_DB ].
        erewrite !HL.size_with_measure_Same_set with (S' := (b x) |: Empty_set _) (H := H2);
          [| now eauto with Ensembles_DB ].
        erewrite !HL.size_with_measure_Same_set with (f := size_cc_block) (S' := x |: Empty_set _) (H := H1);
        [| now eauto with Ensembles_DB ].
            
        edestruct (Hheap 1) as [Hcc | Henv]. now left.
        - destruct Hcc as [_ Hcc].
          destruct (get x H1) as [ [c vs1 | [fs |] [el|] | env] | ] eqn:Hgetl1; try contradiction.
          + destruct (get (b x) H2 ) as [ [c' vss | fs' [el |] | env'] | ] eqn:Hgetl2; try contradiction.
            
            erewrite HL.size_with_measure_filter_add_In;
              [| intros Hc; now inv Hc | eassumption ]. simpl.
            erewrite HL.size_with_measure_filter_add_In;
              [| intros Hc; now inv Hc | eassumption ] . simpl.
            destruct Hcc as [_ Hcc]. specialize (Hcc 0Nat.lt_0_1). 
            rewrite !HL.size_with_measure_filter_Empty_set. eapply Forall2_length in Hcc.
            omega.
          + destruct ( get (b x) H2 ) as [ [ c' [ | [lf |] [| [lenv |] [|]  ]] | | ] | ] eqn:Hgetl2; try contradiction.
            erewrite HL.size_with_measure_filter_add_In;
              [| intros Hc; now inv Hc | eassumption ]. simpl.
            erewrite HL.size_with_measure_filter_add_In;
              [| intros Hc; now inv Hc | eassumption ]. simpl.
            erewrite HL.size_with_measure_filter_add_In;
              [| intros Hc; now inv Hc | eassumption ] . simpl.
            rewrite !HL.size_with_measure_filter_Empty_set. omega.
        - edestruct Henv as [_ [rho1 [c1 [vs1 [FVs [Hkey [Hnd [Hget1 [Hget2 Hall]]]]]]]]]. 
          erewrite HL.size_with_measure_filter_add_In;
            [| intros Hc; now inv Hc | eassumption ]. simpl.
          erewrite HL.size_with_measure_filter_add_In;
            [| intros Hc; now inv Hc | eassumption ]. simpl.
          erewrite HL.size_with_measure_filter_add_In;
            [| intros Hc; now inv Hc | eassumption ] . simpl.
          rewrite !HL.size_with_measure_filter_Empty_set.
          rewrite <- !plus_n_O. eapply plus_le_compat_l.
          rewrite PS.cardinal_spec.
          eapply Forall2_length in Hall. 
          rewrite <- Hall.
          eapply Same_set_FromList_length. eassumption.
          rewrite <- FromSet_elements, <- mset_eq.
          eapply Hkey. } 

      omega.
      
      
      eapply Disjoint_Singleton_l. eassumption. 
      eapply Disjoint_Singleton_l. eassumption. 
      eapply Disjoint_Setminus_r. reflexivity.

  Qed.


  Lemma cardinal_env_locs S {HS : ToMSet S} rho :
    (forall x, x \in S -> exists l, M.get x rho = Some (Loc l) /\ ~ l \in (env_locs rho (S \\ [set x]))) ->
    PS.cardinal (@mset S _) <= PS.cardinal (@mset (env_locs rho S) _).
  Proof with (now eauto with Ensembles_DB).
    assert (HS' := HS).
    revert HS.
    set (P := fun S1 => 
                forall (HS1 : ToMSet S1),
                  (forall x : positive, In positive S1 x ->
                  exists l, M.get x rho = Some (Loc l) /\ ~ l \in (env_locs rho (S1 \\ [set x]))) ->
                  PS.cardinal (@mset S1 _) <= PS.cardinal (@mset (env_locs rho S1) _)).
    assert (HP : Proper (Same_set var ==> iff) P).
    { intros S1' S2' Hseq. unfold P.
      split; intros. 
      eapply le_trans. eapply (PS_elements_subset S2' S1'). eapply Hseq.
      eapply le_trans; [| eapply (PS_elements_subset (env_locs _ S1') (env_locs _ S2')) ].
      eapply H. setoid_rewrite Hseq. eassumption. eapply env_locs_monotonic. eapply Hseq.

      eapply le_trans. eapply (PS_elements_subset S1' S2'). eapply Hseq.
      eapply le_trans; [| eapply (PS_elements_subset (env_locs _ S2') (env_locs _ S1')) ].
      eapply H. setoid_rewrite <- Hseq. eassumption. eapply env_locs_monotonic. eapply Hseq. }
    
    eapply (@Ensemble_ind P HP); [| | eassumption ]; unfold P; [ intros HS Hyp | intros x S1 HS1 ].
    
    - rewrite !PS_cardinal_empty. reflexivity.
      rewrite <- mset_eq. eapply env_locs_Empty_set.
      rewrite <- mset_eq. reflexivity.

    - intros Hnin IH Hun Hyp.
      rewrite Proper_carinal. 
      Focus 2.
      eapply Same_set_From_set. 
      rewrite <- (@mset_eq (x |: S1)) at 1.
      rewrite FromSet_union. eapply Same_set_Union_compat.
      eapply ToMSet_Singleton. eapply HS1.

      edestruct Hyp as [l [Hgetx Hgf]]. now left. 
      
      eapply le_trans; [| eapply PS_elements_subset with (S1 := l |: (env_locs rho S1)) ]. 
      
      erewrite Proper_carinal with (x := (@mset (l |: (env_locs rho S1)) _ )).
      Focus 2.
      eapply Same_set_From_set. 
      rewrite <- (@mset_eq (l |: _)) at 1.
      rewrite FromSet_union. eapply Same_set_Union_compat.
      eapply ToMSet_Singleton. eapply ToMSet_env_locs.
      
      rewrite <- !PS_cardinal_union.
      erewrite !(PS_cardinal_singleton (@mset [set x] _)).
      erewrite !(PS_cardinal_singleton (@mset [set l] _)).
      
      eapply plus_le_compat_l. eapply le_trans. eapply IH.
      intros. edestruct Hyp as [l1 [Hget Hf]]. right. eassumption.
      eexists; split; eauto. intros H1. eapply Hf. 
      eapply env_locs_monotonic; [| eassumption ]... reflexivity.
      
      rewrite <- mset_eq. reflexivity.
      rewrite <- mset_eq. reflexivity.

      eapply FromSet_disjoint. rewrite <- !mset_eq. 
      eapply Disjoint_Singleton_l. intros Hc. eapply Hgf.
      eapply env_locs_monotonic; [| eassumption ]...
      
      eapply FromSet_disjoint. rewrite <- !mset_eq. 
      eapply Disjoint_Singleton_l. eassumption.

      rewrite env_locs_Union, env_locs_Singleton; eauto. reflexivity. 

      Grab Existential Variables.
      eapply ToMSet_Same_set; eassumption.
      eapply ToMSet_Same_set. symmetry. eassumption. eassumption. 
  Qed.

  Lemma def_closures_env_locs S B B0 H rho H' rho' v x :
    S \subset name_in_fundefs B ->
    x \in S ->
    def_closures B B0 rho H v = (H', rho') ->
    exists l, M.get x rho' = Some (Loc l) /\
         ~ l \in env_locs rho' (S \\ [set x]).
  Proof with (now eauto with Ensembles_DB).
    revert S H' rho'.
    induction B; intros S H' rho' Hin1 Hin2 Hdef.
    - simpl in Hdef.
      destruct (def_closures B B0 rho H v) as [H2 rho2] eqn:Hclo'.
      destruct (alloc (Clos (FunPtr B0 v0) v) H2) as [l' H3] eqn:Hal.
      inv Hdef.

      destruct (var_dec x v0); subst.
      + rewrite M.gss. eexists; split; eauto. intros Hc.
        rewrite env_locs_set_not_In in Hc; [| intros Hc'; inv Hc'; now eauto ].
        eapply env_locs_monotonic in Hc.
        eapply def_closures_env_locs_in_dom with (S := Empty_set _) in Hc; try eassumption.
        eapply HL.alloc_not_In_dom. eassumption. eassumption.

        rewrite env_locs_Empty_set...
        rewrite Union_Empty_set_neut_l.
        eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption.
        simpl...
      + setoid_rewrite M.gso; eauto.
        edestruct IHB  with (S := S \\ [set v0]) as [l0 [Hget0 Hsub0]].
        
        eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption.
        simpl...

        constructor; eauto. intros Hc'; inv Hc'; now eauto.
        reflexivity.

        eexists. split; eauto.
        
        intros Hc. eapply env_locs_set_Inlcuded' in Hc. inv Hc.
        * inv H0. eapply HL.alloc_not_In_dom. eassumption.
          eapply def_closures_env_locs_in_dom with (S := Empty_set _); try eassumption.
          
          rewrite env_locs_Empty_set... 

          eapply get_In_env_locs; try eassumption; [| reflexivity ].
          right. eapply Hin1 in Hin2. inv Hin2. inv H0; contradiction.
          eassumption.
        * rewrite @Setminus_Union in *. rewrite Union_commut in H0; eauto.
    - eapply Hin1 in Hin2. inv Hin2. 
  Qed. 

      
  Lemma size_with_measure_filter_def_closures
        S {HS : ToMSet S} g H1 H1' rho1 rho1' B B0 rho f
        (Hyp : forall B v f rho, g (Clos (FunPtr B v) rho) = g (Clos (FunPtr B f) rho)) : 
    unique_functions B ->
    S \subset env_locs rho1' (name_in_fundefs B) ->
    def_closures B B0 rho1 H1 rho = (H1', rho1') ->
    size_with_measure_filter g S H1' = (g (Clos (FunPtr B0 f) rho)) * (PS.cardinal (@mset S _)).
  Proof.
    revert S HS H1 H1' rho1'.
    induction B; intros S HS H1 H1' rho1' Hun Hin Hclo.
    - simpl in Hclo.
      destruct (def_closures B B0 rho1 H1 rho) as [H2 rho2] eqn:Hclo'.
      destruct (alloc (Clos (FunPtr B0 v) rho) H2) as [l' H3] eqn:Hal.
      
      inv Hun. inv Hclo.

      destruct (@Dec _ S _ l').
      + assert (Hseq : S <--> l' |: (S \\ [set l'])). 
        { rewrite Union_Setminus_Included. rewrite Union_Same_set. reflexivity.
          eapply Singleton_Included; eauto. tci.
          eapply Singleton_Included; eauto. }

        erewrite (@HL.size_with_measure_Same_set _ _ _ _ _ _ _ Hseq).
        erewrite HL.size_with_measure_filter_add_In; [| | eapply gas; eauto ].   

        rewrite Proper_carinal. Focus 2.
        eapply Same_set_From_set with (s2 := @mset (l' |: (S \\ [set l'])) _).
        do 2 rewrite <- mset_eq. eassumption.

        rewrite Proper_carinal. Focus 2.
        eapply Same_set_From_set. 
        rewrite <- (@mset_eq (l' |: (S \\ [set l']))) at 1.
        rewrite FromSet_union. eapply Same_set_Union_compat.
        eapply ToMSet_Singleton.
        eapply ToMSet_Setminus.
        
        rewrite <- PS_cardinal_union.
        simpl. rewrite NPeano.Nat.mul_add_distr_l.
        eapply f_equal2_plus.
        
        rewrite <- (Nat.mul_1_r (g _)). erewrite (Hyp B0 v f).
        f_equal. erewrite PS_cardinal_singleton. reflexivity.
        
        replace 1 with (length [l']) by reflexivity.
        rewrite <- mset_eq. 
        repeat normalize_sets. reflexivity.
        
        erewrite HL.size_with_measure_filter_alloc_in; [| reflexivity | eassumption | ]. 
        eapply IHB; try eassumption.
        
        eapply Setminus_Included_Included_Union. eapply Included_trans. eassumption.

        eapply Included_trans. eapply env_locs_set_Inlcuded'. simpl.
        rewrite Union_commut. eapply Included_Union_compat; [| reflexivity ]. 
        eapply env_locs_monotonic. now eauto with Ensembles_DB.

        intros Hc; inv Hc; eauto. 
        eapply FromSet_disjoint.  rewrite <- !mset_eq. 
        eapply Disjoint_Singleton_l. 
        intros Hc; inv Hc; eauto. 
        intros Hc; inv Hc; eauto. 
      + erewrite HL.size_with_measure_filter_alloc_in; [| reflexivity | eassumption | eassumption ]. 
        eapply IHB; try eassumption.

        rewrite <- (Setminus_Disjoint S [set l']); tci. 
        eapply Setminus_Included_Included_Union.
        eapply Included_trans. eassumption.
        eapply Included_trans. eapply env_locs_set_Inlcuded'. simpl.
        rewrite Union_commut. eapply Included_Union_compat; [| reflexivity ]. 
        eapply env_locs_monotonic. now eauto with Ensembles_DB.
        
        eapply Disjoint_Singleton_r. eassumption. 
    - inv Hclo. simpl. 
      rewrite PS_cardinal_empty. rewrite <- mult_n_O.
      erewrite (HL.size_with_measure_Same_set _ S (Empty_set _)).
      rewrite HL.size_with_measure_filter_Empty_set. reflexivity.
      rewrite env_locs_Empty_set in Hin. now eauto with Ensembles_DB. 
      rewrite <- @mset_eq.
      rewrite env_locs_Empty_set in Hin. now eauto with Ensembles_DB. 
  Qed.

    
  Lemma GC_pre 
        (H1' H1'' Hgc1 H2' Hgc2: heap block)
        env_loc (rho_clo rho_clo1 rho_clo2 rho2'' : env) 
        (B1 : fundefs) (f1' : var) (ct1 : cTag)
        (xs1' : list var) (e1 : exp)
        (vs1 : list value) 
        (B2 : fundefs) (f3 : var) (c ct2 : cTag) (xs2' : list var) 
        (e2 : exp) (env_loc2 : loc) (vs2 : list value) fls b d
        Scope {Hs : ToMSet Scope} β k A : (* existentials *) 
        
        get env_loc H1' = Some (Env rho_clo) ->
        find_def f1' B1 = Some (ct1, xs1', e1) ->
        def_closures B1 B1 rho_clo H1' (Loc env_loc) = (H1'', rho_clo1) ->
        setlist xs1' vs1 rho_clo1 = Some rho_clo2 ->
        live' ((env_locs rho_clo2) (occurs_free e1)) H1'' Hgc1 b ->
        
        Some rho2'' =
        setlist xs2' (Loc env_loc2 :: vs2) (def_funs B2 B2 (M.empty value)) ->
        find_def f3 B2 = Some (ct2, xs2', e2) ->
        live' ((env_locs rho2'') (occurs_free e2)) H2' Hgc2 d ->

        get env_loc2 H2' = Some (Constr c fls) ->
        length fls = PS.cardinal (@mset (key_set rho_clo) _) ->

        (forall j, Scope |- H1' ≼ ^ ( k ; j ; Pre ; Post A ; β ) H2') ->

        Disjoint M.elt (name_in_fundefs B1 :&: occurs_free e1) (FromList xs1') ->
        unique_functions B1 ->

        (** To show size relation  **)

        (* Scope <--> vs :&: FVs *)
        Scope :|: (* reachable from xs or FVs of post name :&: FV(e1) *)
        env_locs rho_clo2 (name_in_fundefs B1 :&: occurs_free e1) (* closures *) \subset
        reach' H1'' ((env_locs rho_clo2) (occurs_free e1)) ->
        
        reach' H2' ((env_locs rho2'') (occurs_free e2)) \subset
        env_loc2 |: image β Scope  (* reachable from xs or Γ *) ->
        
        Pre (name_in_fundefs B1 :&: occurs_free e1) (1 + PS.cardinal (@mset (key_set rho_clo) _))
            (Hgc1, subst_env b rho_clo2, e1) (Hgc2, subst_env d rho2'', e2) .
  Proof with (now eauto with Ensembles_DB). 
    intros (* Hgetf1 Hgetl1 *) Hgetenv1 Hfd1 (* Hgl1 *) Hclo1 Hst1 Hl1
           (* Hgetf2 Hgl2 Hgetl2 *) Hs2 Hdf2 Hl2 Hget Hlen Hreach Hdis Hun Heq1 Heq2. 
    unfold Pre.
    unfold size_heap, size_cc_heap.
    assert (Hdis' : Disjoint loc Scope
                            (env_locs rho_clo2 (name_in_fundefs B1 :&: occurs_free e1))). 
    { eapply Disjoint_Included_r.
      rewrite <- env_locs_setlist_Disjoint; try eassumption.
      eapply env_locs_monotonic. eapply Included_Intersection_l.
      eapply Disjoint_Included_l; [| eapply Disjoint_sym; eapply def_closures_env_locs_Disjoint ; eassumption ].
      eapply cc_approx_heap_dom1 with (j := 0). eapply Hreach. }
    

    assert (Hseq : (env_loc2 |: image β Scope) <--> (env_loc2 |: (image β Scope \\ [set env_loc2]))). 
    { rewrite Union_Setminus_Included. reflexivity. tci. reflexivity. }

    assert (Hsize : size_with_measure_filter size_val (reach' H2' (env_locs rho2'' (occurs_free e2))) H2'
                    + 3 * PS.cardinal (@mset (name_in_fundefs B1 :&: occurs_free e1) _) <=
                    size_with_measure_filter size_val (reach' H1'' (env_locs rho_clo2 (occurs_free e1))) H1''
                    + size_with_measure_filter size_cc_block (reach' H1'' (env_locs rho_clo2 (occurs_free e1))) H1''
                    + (1 + PS.cardinal (@mset (key_set rho_clo) _))). 
    { eapply le_trans. 
      eapply plus_le_compat_r. 
      eapply (@HL.size_with_measure_filter_monotonic _ _ _ _ _ _ ) in Heq2. eassumption.
      assert (Heq1' := Heq1). 
      eapply (@HL.size_with_measure_filter_monotonic _ _ _ _ _ _ ) in Heq1; tci.  
      eapply le_trans; [| eapply plus_le_compat_r; eapply plus_le_compat_l; eassumption ]. 
      eapply (@HL.size_with_measure_filter_monotonic _ _ _ _ _ _ ) in Heq1'. 
      eapply le_trans; [| eapply plus_le_compat_r; eapply plus_le_compat_r; eassumption ]. 
      erewrite !HL.size_with_measure_filter_Union with (S1 := Scope). 
      (* Closure env size *)
      assert (Hsize1 : size_with_measure_filter size_val (env_loc2 |: image β Scope) H2' <=
                       1 + PS.cardinal (@mset (key_set rho_clo) _)
                       + size_with_measure_filter size_val (image β Scope) H2'). 
      { erewrite (HL.size_with_measure_Same_set _ _ _ _ _ Hseq).
        erewrite HL.size_with_measure_filter_add_In; try eassumption.
        eapply plus_le_compat. simpl. omega.
        eapply HL.size_with_measure_filter_monotonic. now eauto with Ensembles_DB.
        intros Hc; inv Hc. eauto. } 
      (* reachable part *)
      assert (Hsize2 : size_with_measure_filter size_val (image β Scope) H2' <=
                       size_with_measure_filter size_val Scope H1'
                       + size_with_measure_filter size_cc_block Scope H1').
      { eapply size_reachable_leq. eassumption. reflexivity. }
      
      assert (Hlem : forall f, size_with_measure_filter f Scope H1' = size_with_measure_filter f Scope H1''). 
      { intros f. eapply HL.size_with_measure_filter_subheap_eq.
        now eapply def_funs_subheap; eauto. 
        eapply cc_approx_heap_dom1 with (j := 0). now eauto.  }
      
      rewrite <- !Hlem.
      (* def_closure *)
      assert (Hclos : 3 * PS.cardinal (@mset (name_in_fundefs B1 :&: occurs_free e1) _) <=
                      size_with_measure_filter size_val (env_locs rho_clo2 (name_in_fundefs B1 :&: occurs_free e1)) H1''
                      + size_with_measure_filter size_cc_block (env_locs rho_clo2 (name_in_fundefs B1 :&: occurs_free e1)) H1'').
      { erewrite size_with_measure_filter_def_closures with (f := f1'); try eassumption.
        erewrite size_with_measure_filter_def_closures with (f := f1'); try eassumption.
        simpl. rewrite <- NPeano.Nat.mul_add_distr_r. eapply mult_le_compat_l.
         
        eapply cardinal_env_locs. intros.
        setoid_rewrite <- env_locs_setlist_Disjoint; try eassumption.
        setoid_rewrite <- setlist_not_In; try eassumption. eapply def_closures_env_locs; try eassumption.

        eapply Included_Intersection_l.
        intros Hc. eapply Hdis. now constructor; eauto.
        eapply Disjoint_Included_l ; [| eassumption ]... 

        intros. reflexivity.

        rewrite <- env_locs_setlist_Disjoint; try eassumption.
        eapply env_locs_monotonic. now eapply Included_Intersection_l. 
        intros. reflexivity.

        rewrite <- env_locs_setlist_Disjoint; try eassumption.
        eapply env_locs_monotonic. now eapply Included_Intersection_l. }
      (* lemma size_with_measure_filter def_closures *)
      omega. eassumption. eassumption. }
    assert (Hl1' := Hl1). 
    eapply live_size_with_measure in Hl1. eapply live_size_with_measure in Hl2.
    eapply live_size_with_measure in Hl1'. 
    rewrite Hl1, Hl1', Hl2. eapply le_trans; [| eassumption ].
    eapply plus_le_compat_l. eapply mult_le_compat_l.
    reflexivity.

    intros. eapply block_equiv_size_cc_block. eassumption. 
    intros. eapply block_equiv_size_val. eassumption. 
    intros. eapply block_equiv_size_val. eassumption.     
  Qed.   
    
End Size.