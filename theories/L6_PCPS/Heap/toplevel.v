From L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics.

From L6.Heap Require Import heap heap_defs heap_equiv space_sem
     cc_log_rel closure_conversion closure_conversion_util bounds
     invariants GC closure_conversion_correct.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega Permutation.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module Top (H : Heap).

  Module CC := ClosureConversionCorrect H.
  
  Import H CC.Inv.Size.Util.C.LR.Sem.GC.Equiv
         CC.Inv.Size.Util.C.LR.Sem.GC.Equiv.Defs
         CC.Inv.Size.Util.C.LR.Sem.GC CC.Inv.Size.Util.C.LR.Sem
         CC.Inv.Size.Util.C.LR CC.Inv.Size.Util.C CC.Inv.Size.Util
         CC.Inv.Size CC.Inv CC.

  Definition ct := CC.Inv.Size.Util.clo_tag. 

  (** The expression relation is monotonic in the local invariant *)
  Lemma cc_approx_exp_rel_mon k j LIP1 LIP2 GIP1 (LP1 : Inv) (GP1 : GInv)
        (p1 p2 : exp * env * heap block) :
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP1 ; GP1 ) p2 ->
    inclusion _ LIP2 LIP1 ->
    p1 ⪯ ^ ( k ; j ; LIP2 ; GIP1 ; LP1 ; GP1 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2]. 
    intros Hcc Hin b1 b2 H1' H2' rho1' rho2' v1 c1 m1 HH1 Hr1 HH2 Hr2 Hip Hleq Hstep Hstuck.
    edestruct Hcc as [v2 [c2 [m2 [b' [Hstep' [HInv Hval]]]]]]; eauto.
  Qed.

  Definition install_env Γ :=
    let (lenv, H1) := alloc (Constr ct []) emp in
    (M.set Γ (Loc lenv) (M.empty _), H1).

  Lemma key_set_empty A :
    key_set (M.empty A) <--> Empty_set _.
  Proof. 
    split; eauto with Ensembles_DB.
    intros x k. unfold In, key_set in *.
    rewrite M.gempty in k. contradiction.
  Qed.

  Lemma closure_conversion_correct_lr_closed (k : nat) (e1 e2 : exp) (C : exp_ctx) (Γ : var) K rho2 H2 :
    (rho2, H2) = install_env Γ ->
    ~ Γ \in bound_var e1 ->
    unique_bindings e1 ->
    
    Closure_conversion ct (Empty_set _) (Empty_set _) id ct Γ [] e1 e2 C ->
    
    (forall j, (e1, M.empty _, emp) ⪯ ^ (k ; j ;
                              Pre (Empty_set _) K; Pre;
                              Post 0 K; Post 0)
          (C |[ e2 ]|, rho2, H2)).
  Proof with (now eauto with Ensembles_DB).
    unfold install_env.
    destruct (alloc (Constr ct []) emp) as [lenv Η2] eqn:Ha. 
    intros Ha' Hnin Hun Hcc. inv Ha'. 
    intros j.
    eapply Closure_conversion_correct in Hcc.
    eapply cc_approx_exp_rel_mon.
    - eassumption. 
    - intros [[H1 rho1] e1'] [[H2 rho2] e2'] Hpre.
      eapply PreSubsetCompat with (Funs := Empty_set var).
      eassumption. rewrite Intersection_Empty_set_abs_l...
    - intros j1. eapply cc_approx_env_Empty_set.
    - intros j2. split.
      + rewrite env_locs_set_In, <- env_locs_Empty; [| reflexivity ].
        rewrite !Union_Empty_set_neut_r.
        rewrite reach_unfold.
        simpl. rewrite post_Singleton; [| eapply gas; eassumption ].  
        simpl. rewrite reach'_Empty_set.
        rewrite !Union_Empty_set_neut_r.
        intros x b Hi Hget; inv Hi. eapply gas in Ha.
        subst_exp...
      + split.
        * unfold FV.
          rewrite key_set_empty.
          rewrite FromList_nil, !Setminus_Empty_set_neut_r. 
          rewrite !Union_Empty_set_neut_r at 1.
          rewrite Setminus_Empty_set_neut_r, !Union_Empty_set_neut_r.
          reflexivity.
        * do 2 eexists. split; [| split ].
          rewrite M.gss. reflexivity. 
          eapply gas. eassumption.
          now constructor. 
    - intros j1 x _ Hin. inv Hin.
    - unfold FV.
      rewrite FromList_nil, !Setminus_Empty_set_neut_r, !image_Empty_set, !Union_Empty_set_neut_r at 1.
      rewrite Setminus_Empty_set_neut_r, !Union_Empty_set_neut_r.
      eapply Disjoint_Singleton_l. eassumption.
    - unfold FV.
      rewrite FromList_nil, !Setminus_Empty_set_neut_r. 
      rewrite !Union_Empty_set_neut_r at 1.
      rewrite Setminus_Empty_set_neut_r, !Union_Empty_set_neut_r.
      intros x Hin. inv Hin.
    - eassumption.
    - unfold FV.
      rewrite FromList_nil, !Setminus_Empty_set_neut_r. 
      rewrite !Union_Empty_set_neut_r at 1.
      rewrite Setminus_Empty_set_neut_r, !Union_Empty_set_neut_r.
      now eauto with Ensembles_DB.

      Grab Existential Variables.
      tci. tci. exact id.
  Qed.

  (** ** Top-level theorem *) 
  
  Lemma closure_conversion_correct_top
        (k : nat) (j : nat) (e1 e2 : exp) (C : exp_ctx) (Γ : var) (* dummy varaiable for environment *)
        H2 rho2 r1 c1 m1 :
    
    (rho2, H2) = install_env Γ ->
    ~ Γ \in bound_var e1 ->
    (* The source program has unique binders *)
    unique_bindings e1 ->

    (* C[e2] is the closure converted program *)
    Closure_conversion ct (Empty_set _) (Empty_set _) id ct Γ [] e1 e2 C ->

    (* the source evaluates *)
    big_step_GC emp (M.empty _) e1 r1 c1 m1 ->
    (* and it is not a stuck program *)
    not_stuck emp (M.empty _) e1 ->
    
    exists (r2 : ans) (c2 m2 : nat) (b : Inj),
      (* the target evaluates *)
      big_step_GC_cc H2 rho2 (C |[ e2 ]|) r2 c2 m2 /\
      (* time bounds *)
      c1 <= c2 <= c1 * (1 + cost_time_exp e1) + (cost_time_exp e1) /\
      (* space bounds *)
      m2 <= m1 * (1 + (cost_mem_exp e1)) + 2 * (1 + (cost_mem_exp e1)) /\
      (* the results are related *)
      r1 ≺ ^ (k ; j ; Pre ; Post 0 ; b ) r2.  
  Proof with (now eauto with Ensembles_DB).
    unfold install_env.
    destruct (alloc (Constr ct []) emp) as [lenv H2'] eqn:Ha. 
    intros Ha' Hnin Hun Hcc Hbs Hns. inv Ha'. 
    assert (Heq : (e1, M.empty _, emp) ⪯ ^ (k + c1 ; j ;
                                            Pre (Empty_set _) 1; Pre;
                                            Post 0 1; Post 0)
                  (C |[ e2 ]|, (M.set Γ (Loc lenv) (M.empty value)), H2')).
    { eapply closure_conversion_correct_lr_closed; try eassumption.
      unfold install_env. rewrite Ha. reflexivity. }

    edestruct Heq as (r2 & c2 & m2 & b & Hbs2 & Hin & Hres).
    - reflexivity.
    - clear; now firstorder.
    - reflexivity.
    - clear; now firstorder.
    - unfold Pre. unfold size_heap, size_cc_heap.
      rewrite !HL.size_with_measure_emp. rewrite !plus_O_n at 1.
      rewrite PS_cardinal_empty.
      simpl. rewrite <- plus_n_O.
      erewrite HL.size_with_measure_alloc with (s := 0); try eassumption. 
      simpl. omega.
      eapply HL.size_with_measure_emp. 
      rewrite <- mset_eq. reflexivity. 
    - eapply le_plus_r.
    - eassumption.
    - eassumption.
    - unfold Post in Hin. destruct Hin as [[Ht1 Ht2] Hm]. do 4 eexists. split. eassumption.
      split; [| split ].
      + split. omega. unfold cost_time_heap, cost_heap in *.
        rewrite HL.max_with_measure_emp in *. rewrite <- !plus_n_O, !Max.max_0_r in *.
        omega.
      + unfold cost_mem_heap, cost_heap in *.
        rewrite HL.max_with_measure_emp in *. rewrite <- !plus_n_O, !Max.max_0_r in *.
        eapply le_trans. eassumption. eapply plus_le_compat_l.
        eapply mult_le_compat_l. eapply Max.max_lub. omega. omega. 
      + rewrite cc_approx_val_eq in Hres.
        eapply cc_approx_val_monotonic. eassumption. omega.
  Qed.

  Print Assumptions closure_conversion_correct_top.


  (* *** Remaining admits as of 09/27 *** *) 
  (* 1.) The Heap module type (in Heap.v) that we have as parameter in our definitions
         and proofs.

     2.) big_step_gc_heap_env_equiv_r 
         -> big_step_GC commutes with heap equivalence 

     3.) live'_live_inv 
         -> lemma about two equivalent definitions of GC. (* TODO remove this depndency *)

     4.) FunctionalExtensionality.functional_extensionality_dep 
         
   *)
  
End Top. 