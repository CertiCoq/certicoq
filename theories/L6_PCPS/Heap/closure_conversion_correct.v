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

  Module Size := Size H.
  
  Import H Size.Compat.LR.Sem.Equiv Size.Compat.LR.Sem.Equiv.Defs Size.Compat.LR.Sem Size.Compat.LR
         Size.Compat Size.
  
  Variable clo_tag : cTag.
  
    
  Definition FP k i (H : heap block) (rho1 : env) (e1 : exp)
             (p1 p2 : nat * nat) :=
    match p1, p2 with
      | (c1, m1), (c2, m2) =>
        c1 <= c2 + k <= 7 * c1 * (max_exp_env i H rho1 e1) + 7 * sizeOf_exp e1 /\
        m1 <= m2 <= 4 * m1 * (max_exp_env i H rho1 e1) + 4 * sizeOf_exp e1
    end.
  
  Definition IP i C (p1 p2 : heap block * env * exp) :=
    let m := cost_alloc_ctx C in 
    match p1, p2 with
      | (H1, rho1, e1), (H2, rho2, e2) =>
        size_heap H1 + m  <= size_heap H2 <=
        4 * (size_heap H1 + m) * (max_exp_env i H1 rho1 e1) + 4 * sizeOf_exp e1
    end.
  
  Lemma FP_transfer i (H1 : heap block) (rho1 : env) (e1 : exp)
        (k c1 c2 c m1 m2 : nat) : 
    FP (k + c) i H1 rho1 e1  (c1, m1) (c2, m2) -> FP k i H1 rho1 e1 (c1, m1) (c2 + c, m2).
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
        i (H1 H2 H2' : heap block) (rho1 rho2 rho2' : env)
        (e1 e2 : exp) (C C' : exp_ctx) (c : nat) : 
    IP i C' (H1, rho1, e1) (H2, rho2, C |[ e2 ]|) ->
    ctx_to_heap_env C H2 rho2 H2' rho2' c ->
    IP i (comp_ctx_f C' C) (H1, rho1, e1) (H2', rho2', e2).
  Proof.
    intros [HP1 Hp2] Hctx. unfold IP in *.
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

  Lemma Fun_inv_weak_in_Fun_inv k P1 P2 rho1 H1 rho2 H2 β Scope Funs σ c Γ :
    Fun_inv k P1 P2 β rho1 H1 rho2 H2 Scope Funs σ c Γ ->
    Fun_inv_weak rho1 rho2 Scope Funs σ c Γ.
  Proof.
    intros HFun f v' Hnin Hin Hget.
    edestruct HFun as
        [vf [venv [Hnin' [Hget1 [Hget2 _]]]]]; eauto.
  Qed.
  
  Lemma FV_inv_weak_in_FV_inv k P1 P2 rho1 H1 rho2 H2 β Scope Funs c Γ FVs :
    FV_inv k P1 P2 β rho1 H1 rho2 H2 Scope Funs c Γ FVs ->
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
        (σ : var -> var) (β : Inj) (c : cTag) (Γ : var) :
    (* [Scope] invariant *)
    (forall j, (H1, rho1) ⋞ ^ (Scope ; k ; j ; IP k Hole_c ; FP 0 k H1 rho1 e1 ; β) (H2, rho2)) ->
    (* [Fun] invariant *)
    Fun_inv k (IP k Hole_c) (FP 0 k H1 rho1 e1) β rho1 H1 rho2 H2 Scope Funs σ c Γ ->
    (* Free variables invariant *)
    FV_inv k (IP k Hole_c) (FP 0 k H1 rho1 e1) β rho1 H1 rho2 H2 Scope Funs c Γ FVs ->
    (* location renaming is injective *)
    injective_subdomain (reach H1 (env_locs rho1 Scope)) β ->

    
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
    
    (forall j, (e1, rho1, H1) ⪯ ^ (k ; j ; IP k Hole_c ; IP k Hole_c; FP 0 k H1 rho1 e1 ; FP 0 k H1 rho1 e1) (C |[ e2 ]|, rho2, H2)).
  Proof with now eauto with Ensembles_DB.
    revert H1 H2 rho1 rho2 e1 e2 C Scope Funs FVs σ β c Γ.
    induction k as [k IHk] using lt_wf_rec1.
    intros H1 H2 rho1 rho2 e1 e2 C Scope Funs FVs σ β c Γ
           Henv Hfun HFVs Hinjb Hwf1 Hlocs1 Hwf2 Hlos2 Hnin Hbind Hun Hinj Hd Hcc.
    induction e1 using exp_ind'; try clear IHe1.
    - (* case Econstr *)
      inv Hcc.
      
      edestruct (binding_in_map_getlist _ rho1 l Hbind) as [vl Hgetl].
      normalize_occurs_free...
      
      edestruct project_vars_ctx_to_heap_env as [H2' [rho2' [m Hct]]]; try eassumption.
      eapply Fun_inv_weak_in_Fun_inv; eassumption.
      eapply FV_inv_weak_in_FV_inv; eassumption.

      intros j. 
      eapply cc_approx_exp_right_ctx_compat
        with (ILi := fun c => FP c  k H1 rho1 (Econstr v t l e1));
        [ now intros; eapply FP_transfer; eauto | now intros; eapply IP_ctx_to_heap_env; eauto
          | eassumption | eassumption | eassumption | eassumption | eassumption | ].
      rewrite <- plus_n_O.
      eapply cc_approx_exp_constr_compat
      with (ILi := fun c => FP c  k H1 rho1 (Econstr v t l e1));
        [ | | | eassumption | | eassumption  | | | | ].
      + admit. (* bounds *)
      + admit. (* bounds *)
      + admit. (* bounds *)
      + admit. (* well_formed *)
      + admit. (* env_locs *)
      + admit. (* project_vars_correct *)
      + admit. (* bounds *)
      + (* Inductive case *)
        intros i vs1 vs2 l1 l2 H1' H2'' Hlt Ha1 Ha2 Hall. (* bounds *)
       
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