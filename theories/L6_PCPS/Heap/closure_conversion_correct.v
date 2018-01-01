From L6 Require Import cps size_cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions closure_conversion.

From L6.Heap Require Import heap heap_defs heap_equiv space_sem cc_log_rel.

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

  Import H LogRel.Sem.Equiv LogRel.Sem.Equiv.Defs LogRel.Sem LogRel.
  
  Variable clo_tag : cTag.


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
    
  Definition FP c p1 p2 :=
    match p1, p2 with
      | (c1, m1), (c2, m2) =>
        c1 <= c2 + c <= 4*c1 /\
        m1 <= m2 <= 2*m1
    end.
  
  Definition IP C p1 p2 :=
    let m := cost_alloc_ctx C in 
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        size_heap H1 + m  <= size_heap H2 <= 2*(size_heap H1 + m) /\
        (forall m1 m2, size_reachable (env_locs rho1 (occurs_free e1)) H1 m1 ->
                  size_reachable (env_locs rho2 (occurs_free e2)) H2 m2 ->
                  m1 + m <= m2 <= 2*(m1 + m))
    end.
  
  Lemma FP_transfer (k c1 c2 c m1 m2 : nat) : 
    FP (k + c) (c1, m1) (c2, m2) -> FP k (c1, m1) (c2 + c, m2).
  Proof.
    simpl. intros H. omega.
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
    split.
    - omega.
    - 
      + unfold size_heap.
        erewrite (HL.size_with_measure_alloc _ _ _ H H') ; try eassumption. 
          in Hpre by reflexivity.

  
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
           Henv Hnin HFVs Hwf1 Hlocs1 Hwf2 Hlos2 Hun Hinj Hd Hfun Hfv Hcc.
    induction e1 using exp_ind'; try clear IHe1.
    - (* case Econstr *)
      inv Hcc.      
      eapply cc_approx_exp_right_ctx_compat;
        [ exact FP_transfer | | eassumption | eassumption
        | eassumption | eassumption | | ].  
      
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
  Abort.