From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions closure_conversion closure_conversion_util
     closure_conversion_correct.

From L6.Heap Require Import heap heap_defs heap_equiv space_sem cc_log_rel size_cps.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module ClosureConversionCorrect (H : Heap).

  (* Module Sem := SpaceSem H. *)
  Module LogRel := CC_log_rel H.
  Module Size := Size H.

  Import H LogRel.Sem.Equiv LogRel.Sem.Equiv.Defs LogRel.Sem LogRel Size.
  
  Variable clo_tag : cTag.
  

  (** *  Useful definitions and lemmas to express the upper bound. TODO move *)

  Definition max_exp_env (k : nat) (H : heap block) (rho : env) (e : exp) :=
    max (sizeOf_exp e) (sizeOf_env k H rho).

  
  Lemma max_exp_env_grt_1 k e rho :
    1 <= max_exp_env k e rho.
  Proof.
    unfold max_exp_env.
    eapply le_trans. now apply sizeOf_exp_grt_1.
    eapply Max.le_max_l.
  Qed.

  (** Lemmas used to establish the upper bound given the IH *)

  Lemma max_exp_env_Econstr k x t ys e rho :
    max_exp_env k e rho <= max_exp_env k (Econstr x t ys e) rho.
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Eproj k x t N y e rho :
    max_exp_env k e rho <= max_exp_env k (Eproj x t N y e) rho.
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Ecase_cons_hd k x c e l rho :
    max_exp_env k e rho <= max_exp_env k (Ecase x ((c, e) :: l)) rho.
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Ecase_cons_tl k x c e l rho :
    max_exp_env k (Ecase x l) rho <= max_exp_env k (Ecase x ((c, e) :: l)) rho.
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Eprim k x f ys e rho :
    max_exp_env k e rho <= max_exp_env k (Eprim x f ys e) rho.
  Proof.
    eapply NPeano.Nat.max_le_compat_r.
    simpl. omega.
  Qed.

  Lemma max_exp_env_Efun k B e rho :
    max_exp_env k e (def_funs B B rho rho) <= max_exp_env k (Efun B e) rho.
  Proof.
    unfold max_exp_env. eapply le_trans.
    - eapply NPeano.Nat.max_le_compat_l.
      now apply sizeOf_env_def_funs.
    - rewrite (Max.max_comm (sizeOf_env _ _)), Max.max_assoc.
      eapply NPeano.Nat.max_le_compat_r.
      eapply Nat.max_lub; simpl; omega.
  Qed.


  (* XXX maybe move *)
  Fixpoint cost_alloc_ctx (c : exp_ctx) : nat :=
    match c with
      | Econstr_c x t ys c => 1 + length ys + cost_alloc_ctx c
      | Eproj_c x t n y c => cost_alloc_ctx c
      (* not relevant *)
      | Efun1_c B c => cost_alloc_ctx c
      | Eprim_c x p ys c => cost_alloc_ctx c
      | Hole_c => 0
      | Efun2_c f _ => cost_alloc_f_ctx f
      | Ecase_c _ _ _ c _ => cost_alloc_ctx c
    end
  with
  cost_alloc_f_ctx (f : fundefs_ctx) : nat :=
    match f with
      | Fcons1_c _ _ _ c _ => cost_alloc_ctx c
      | Fcons2_c _ _ _ _ f => cost_alloc_f_ctx f
    end.
    
  Lemma cost_alloc_ctx_comp_ctx_f C C' :
    cost_alloc_ctx (comp_ctx_f C C') =
    cost_alloc_ctx C + cost_alloc_ctx C'
  with cost_alloc_comp_f_ctx_f f C' :
    cost_alloc_f_ctx (comp_f_ctx_f f C') =
    cost_alloc_f_ctx f + cost_alloc_ctx C'.
  Proof.
    - destruct C; simpl; try reflexivity;
      try (rewrite cost_alloc_ctx_comp_ctx_f; omega).
      rewrite cost_alloc_comp_f_ctx_f. omega.
    - destruct f; simpl; try reflexivity.
      rewrite cost_alloc_ctx_comp_ctx_f; omega.
      rewrite cost_alloc_comp_f_ctx_f. omega.
  Qed. 
    
  Definition FP i (e1 : exp) (rho1 : env) p1 p2 :=
    match p1, p2 with
      | (c1, m1), (c2, m2) =>
        c1 <= c2 <= 7 * c1 * (max_exp_env i e1 rho1) + 7 * sizeOf_exp e1
    end.
  
  Definition IP C (p1 p2 : heap block * env * exp) :=
    let m := cost_alloc_ctx C in 
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        size_heap H1 + m  <= size_heap H2 <= 2*(size_heap H1 + m)
    end.
  
  Lemma FP_transfer (k c1 c2 c m1 m2 : nat) : 
    FP (k + c) (c1, m1) (c2, m2) -> FP k (c1, m1) (c2 + c, m2).
  Proof.
    simpl. intros H. omega.
  Qed.
  
  (* Lemma ctx_to_heap_env_size_heap C rho1 rho2 H1 H2 c : *)
  (*   ctx_to_heap_env C H1 rho1 H2 rho2 c -> *)
  (*   size_heap H2 = size_heap H1 + cost_alloc_ctx C.  *)
  (* Proof. *)
  (*   intros Hctx; induction Hctx; eauto. *)
  (*   simpl. rewrite IHHctx. *)
  (*   unfold size_heap. *)
  (*   erewrite (HL.size_with_measure_alloc _ _ _ H H'); *)
  (*     [| reflexivity | eassumption ]. *)
  (*   erewrite getlist_length_eq; [| eassumption ].  *)
  (*   simpl. omega. *)
  (* Qed. *)


  (** * Lemmas about [ctx_to_heap_env] *)

  Lemma ctx_to_heap_env_comp_ctx_f_r C1 C2 rho1 H1 m1 rho2 H2 m2 rho3 H3 :
    ctx_to_heap_env C1 H1 rho1 H2 rho2 m1 ->
    ctx_to_heap_env C2 H2 rho2 H3 rho3 m2 ->
    ctx_to_heap_env (comp_ctx_f C1 C2) H1 rho1 H3 rho3 (m1 + m2).
  Proof.
    revert C2 rho1 H1 m1 rho2 H2 m2 rho3 H3.
    induction C1; intros C2 rho1 H1 m1 rho2 H2 m2 rho3 H3 Hctx1 GHctx2; inv Hctx1.
    - eassumption.
    - replace (c0 + costCC_ctx (Econstr_c v c l C1) + m2) with (c0 + m2 + costCC_ctx (Econstr_c v c l C1)) by omega.
      simpl. econstructor; eauto. 
    - replace (c0 + costCC_ctx (Eproj_c v c n v0 C1) + m2) with (c0 + m2 + costCC_ctx (Eproj_c v c n v0 C1)) by omega.
      simpl. econstructor; eauto.
  Qed.

  Lemma ctx_to_heap_env_comp_ctx_l C C1 C2 H rho H' rho' m :
    ctx_to_heap_env C H rho H' rho' m ->
    comp_ctx C1 C2 C ->
    exists rho'' H'' m1 m2,
      ctx_to_heap_env C1 H rho H'' rho'' m1 /\
      ctx_to_heap_env C2 H'' rho'' H' rho' m2 /\
      m = m1 + m2.
  Proof.
    intros Hctx. revert C1 C2.
    induction Hctx; intros C1 C2 Hcomp.
    - inv Hcomp. repeat eexists; constructor.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        constructor. inv H1.
        do 4 eexists. split; [ | split ].  econstructor.
        econstructor; eauto. omega.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        eassumption.
        do 4 eexists. split; [ | split ]. econstructor; eauto.
        eassumption. simpl. omega.
    - inv Hcomp.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        constructor. inv H1.
        do 4 eexists; split; [| split ]. constructor.
        econstructor; eauto. omega.
      + edestruct IHHctx as [rho'' [H''' [m1 [m2 [Hc1 [Hc2 Hadd]]]]]].
        eassumption.
        do 4 eexists; split; [| split ]. econstructor; eauto.
        eassumption. simpl. omega.
  Qed.

  Lemma ctx_to_heap_env_comp_ctx_f_l C1 C2 H rho H' rho' m :
    ctx_to_heap_env (comp_ctx_f C1 C2) H rho H' rho' m ->
    exists rho'' H'' m1 m2,
      ctx_to_heap_env C1 H rho H'' rho'' m1 /\
      ctx_to_heap_env C2 H'' rho'' H' rho' m2 /\
      m = m1 + m2.
  Proof.
    intros. eapply ctx_to_heap_env_comp_ctx_l. eassumption.
    eapply comp_ctx_f_correct. reflexivity.
  Qed.

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

  Lemma ctx_to_heap_env_subheap C H rho H' rho' m :
    ctx_to_heap_env C H rho H' rho' m ->
    H ⊑ H'.
  Proof.
    intros Hc; induction Hc.
    - eapply HL.subheap_refl.
    - eapply HL.subheap_trans.
      eapply HL.alloc_subheap. eassumption. eassumption.
    - eassumption.
  Qed.
  
  Lemma project_var_get Scope Funs σ c Γ FVs S1 x x' C1 S2 rho1 H1 rho2 H2 m y:
    project_var clo_tag Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
    ctx_to_heap_env C1 H1 rho1 H2 rho2 m ->
    ~ In _ S1 y ->
    M.get y rho1 = M.get y rho2. 
  Proof.
    intros Hvar Hctx Hin. inv Hvar.
    - inv Hctx. reflexivity.
    - inv Hctx.
      destruct (var_dec y x'); subst.
      contradiction.
      inv H16. now rewrite M.gso.
    - inv Hctx. inv H19.
      destruct (var_dec y x'); subst.
      contradiction.
      now rewrite M.gso.
  Qed.    
  
  Lemma project_vars_get Scope Funs σ c Γ FVs S1 xs xs' C1 S2 rho1 H1 rho2 H2 m y:
    project_vars clo_tag Scope Funs σ c Γ FVs S1 xs xs' C1 S2 ->
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
    project_var clo_tag Scope Funs σ c Γ FVs S1 x x' C1 S2 ->
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
    project_vars clo_tag Scope Funs σ c Γ FVs S1 xs xs' C1 S2 ->
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
  
  Lemma project_var_ctx_to_heap_env Scope Funs σ c Γ FVs x x' C S S' v1 rho1 rho2 H2:
    project_var clo_tag Scope Funs σ c Γ FVs S x x' C S' ->
    Fun_inv_weak rho1 rho2 Scope Funs σ c Γ ->
    FV_inv_weak rho1 rho2 H2 Scope Funs c Γ FVs ->
    M.get x rho1 = Some v1 ->
    exists H2' rho2' s, ctx_to_heap_env C H2 rho2 H2' rho2' s.
  Proof.
    intros Hproj HFun HFV Hget. inv Hproj.
    - repeat eexists; econstructor; eauto.
    - edestruct HFun as
          [vf [venv [Hnin [Hget1 Hget2]]]]; eauto.
      destruct (alloc (Constr clo_tag [vf; venv]) H2) as [l' H2'] eqn:Hal.
      repeat eexists; econstructor; eauto.
      simpl. rewrite Hget2, Hget1. reflexivity. constructor.
    - edestruct HFV as [vs [l [v' [Hget1 [Hget2 Hnth']]]]]; eauto.
      repeat eexists. econstructor; eauto. constructor. 
  Qed.
  
  Lemma project_vars_ctx_to_heap_env Scope Funs σ c Γ FVs xs xs' C S S' vs1 rho1 rho2 H2:
    Disjoint _ S (Union var Scope
                        (Union var (image σ (Setminus _ Funs Scope))
                               (Union var (FromList FVs) (Singleton var Γ)))) ->
    
    project_vars clo_tag Scope Funs σ c Γ FVs S xs xs' C S' ->
    Fun_inv_weak rho1 rho2 Scope Funs σ c Γ ->
    FV_inv_weak rho1 rho2 H2 Scope Funs c Γ FVs ->
    getlist xs rho1 = Some vs1 ->
    exists H2' rho2' s, ctx_to_heap_env C H2 rho2 H2' rho2' s.
  Proof.
    intros HD Hvars HFun HFV.
    (* assert (HD' := Hvars). *)
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
      + intros f v' Hnin Hin Hget.
        edestruct HFun as
            [vf [venv [Hnin' [Hget1 Hget2]]]]; eauto.
        repeat eexists; eauto.
        * erewrite <- project_var_get; try eassumption.
          intros Hin'. eapply HD. constructor. now eauto.
          right. left. eexists. now eauto.
        * erewrite <- project_var_get; try eassumption.
          intros Hin'. eapply HD. constructor. now eauto.
          right. right. right. reflexivity.
      + intros x N v' Hnin1 Hnin2 Hnth Hget.
        edestruct HFV as [vs [l' [v'' [Hget1 [Hget2 Hnth']]]]]; eauto.
        repeat eexists; eauto.
        * erewrite <- project_var_get; try eassumption.
          intros Hin'. eapply HD. constructor. now eauto.
          right. right. right. reflexivity.
        * erewrite ctx_to_heap_env_subheap. reflexivity.
          eassumption. eassumption.
      + exists H2'', rho2'', (s + s'). eapply ctx_to_heap_env_comp_ctx_f_r; eassumption.
  Qed.

  Lemma IP_ctx_to_heap_env
        (H1 H2 H2' : heap block) (rho1 rho2 rho2' : env)
        (e1 e2 : exp) (C C' : exp_ctx) (c : nat) : 
    IP C' (H1, rho1, e1) (H2, rho2, C |[ e2 ]|) ->
    ctx_to_heap_env C H2 rho2 H2' rho2' c ->
    IP (comp_ctx_f C' C) (H1, rho1, e1) (H2', rho2', e2).
  Proof.
    intros [HP1 Hp2] Hctx. unfold IP in *.
    erewrite (ctx_to_heap_env_size_heap C rho2 rho2' H2 H2'); [| eassumption ].
    rewrite cost_alloc_ctx_comp_ctx_f in *. simpl.
    omega.
  Qed.

  Lemma Fun_inv_weak_in_Fun_inv k P1 P2 rho1 H1 rho2 H2 Scope Funs σ c Γ :
    Fun_inv k P1 P2 rho1 H1 rho2 H2 Scope Funs σ c Γ ->
    Fun_inv_weak rho1 rho2 Scope Funs σ c Γ.
  Proof.
    intros HFun f v' Hnin Hin Hget.
    edestruct HFun as
        [vf [venv [Hnin' [Hget1 [Hget2 _]]]]]; eauto.
  Qed.

  Lemma FV_inv_weak_in_FV_inv k P1 P2 rho1 H1 rho2 H2 Scope Funs c Γ FVs :
    FV_inv k P1 P2 rho1 H1 rho2 H2 Scope Funs c Γ FVs ->
    FV_inv_weak rho1 rho2 H2 Scope Funs c Γ FVs.
  Proof.
    intros HFV x N v' Hnin1 Hnin2 Hnth Hget.
    edestruct HFV as [vs [l' [v'' [Hget1 [Hget2 [Hnth' _]]]]]]; eauto.
    firstorder.
  Qed.

  (** Correctness of [Closure_conversion] *)
  Lemma Closure_conversion_correct (k : nat) (H1 H2 : heap block)
        (rho1 rho2 : env) (e1 e2 : exp) (C : exp_ctx)
        (Scope Funs : Ensemble var) (FVs : list var)
        (σ : var -> var) (c : cTag) (Γ : var) :
    (* [Scope] invariant *)
    (H1, rho1) ⋞ ^ (Scope ; k ; IP Hole_c ; FP 0) (H2, rho2) ->
    (* [Fun] invariant *)
    Fun_inv k (IP Hole_c) (FP 0) rho1 H1 rho2 H2 Scope Funs σ c Γ ->
    (* Free variables invariant *)
    FV_inv k (IP Hole_c) (FP 0) rho1 H1 rho2 H2 Scope Funs c Γ FVs ->

    (* well-formedness *)
    well_formed (reach' H1 (env_locs rho1 (occurs_free e1))) H1 ->
    (env_locs rho1 (occurs_free e1)) \subset dom H1 ->
    well_formed (reach' H2 (env_locs rho2 (occurs_free (C |[ e2 ]|)))) H2 ->
    (env_locs rho2 (occurs_free (C |[ e2 ]|))) \subset dom H2 ->

    (* [Γ] (the current environment parameter) is not bound in e *)
    ~ In _ (bound_var e1) Γ ->
    (* The free variables of e are defined in the environment *)
    binding_in_map (occurs_free e1) rho1 ->
    (* The blocks of functions have unique function names *)
    fundefs_names_unique e1 ->
    (* function renaming is injective in the [Funs] subdomain *)
    injective_subdomain Funs σ ->
    (* function renaming codomain is not shadowed by other vars *)
    Disjoint _ (image σ (Setminus _ Funs Scope)) (bound_var e1) ->

    (* [e'] is the closure conversion of [e] *)
    Closure_conversion clo_tag Scope Funs σ c Γ FVs e1 e2 C ->
    (e1, rho1, H1) ⪯ ^ (k ; IP Hole_c ; IP Hole_c; FP 0 ; FP 0) (C |[ e2 ]|, rho2, H2).
  Proof with now eauto with Ensembles_DB.
    revert H1 H2 rho1 rho2 e1 e2 C Scope Funs FVs σ c Γ.
    induction k as [k IHk] using lt_wf_rec1.
    intros H1 H2 rho1 rho2 e1 e2 C Scope Funs FVs σ c Γ
           Henv Hfun HFVs Hwf1 Hlocs1 Hwf2 Hlos2 Hnin Hbind Hun Hinj Hd Hcc.
    induction e1 using exp_ind'; try clear IHe1.
    - (* case Econstr *)
      inv Hcc.

      edestruct (binding_in_map_getlist _ rho1 l Hbind) as [vl Hgetl].
      normalize_occurs_free...

      edestruct project_vars_ctx_to_heap_env as [H2' [rho2' [m Hct]]]; try eassumption.
      eapply Fun_inv_weak_in_Fun_inv; eassumption.
      eapply FV_inv_weak_in_FV_inv; eassumption.
      
      eapply cc_approx_exp_right_ctx_compat;
        [ exact FP_transfer | exact IP_ctx_to_heap_env | eassumption | eassumption
        | eassumption | eassumption | eassumption | ]. 

      eapply cc_approx_exp_constr_compat.
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