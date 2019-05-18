From CertiCoq.L6 Require Import cps cps_util set_util identifiers ctx Ensembles_util
     List_util functions tactics map_util.

From CertiCoq.L6.Heap Require Import heap heap_impl heap_defs heap_equiv space_sem
     cc_log_rel closure_conversion closure_conversion_util bounds
     invariants GC closure_conversion_correct.

From Coq Require Import ZArith.Znumtheory Relations.Relations Arith.Wf_nat
                        Lists.List MSets.MSets MSets.MSetRBT Numbers.BinNums NArith.Ndist
                        NArith.BinNat PArith.BinPos Sets.Ensembles Omega Permutation.

Import ListNotations.

Open Scope ctx_scope.
Open Scope fun_scope.
Close Scope Z_scope.

Module Top.

  Module CC := ClosureConversionCorrect MHeap.
  
  Import MHeap CC.Inv.Size.Util.C.LR.Sem.GC.Equiv
         CC.Inv.Size.Util.C.LR.Sem.GC.Equiv.Defs
         CC.Inv.Size.Util.C.LR.Sem.GC CC.Inv.Size.Util.C.LR.Sem
         CC.Inv.Size.Util.C.LR CC.Inv.Size.Util.C CC.Inv.Size.Util
         CC.Inv.Size CC.Inv CC.

  Definition ct := CC.Inv.Size.Util.clo_tag. 

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
    has_true_mut e1 ->
    
    Closure_conversion ct (Empty_set _) (Empty_set _) id ct Γ [] e1 e2 C ->
    
    (forall j, (e1, M.empty _, emp) ⪯ ^ (k ; j ;
                              Pre (Empty_set _) 0 K; PreG;
                              Post 0 0 K; PostG)
          (C |[ e2 ]|, rho2, H2)).
  Proof with (now eauto with Ensembles_DB).
    unfold install_env.
    destruct (alloc (Constr ct []) emp) as [lenv Η2] eqn:Ha. 
    intros Ha' Hnin Hun Htm Hcc. inv Ha'. 
    intros j.
    eapply Closure_conversion_correct in Hcc.
    eapply cc_approx_exp_rel_mon_pre.
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
    - eassumption.
    - unfold FV.
      rewrite FromList_nil, !Setminus_Empty_set_neut_r. 
      rewrite !Union_Empty_set_neut_r at 1.
      rewrite Setminus_Empty_set_neut_r, !Union_Empty_set_neut_r.
      now eauto with Ensembles_DB.

      Grab Existential Variables.
      tci. tci. exact id.
  Qed.


  Lemma key_set_get {A} rho1 x (v : A) :
    M.get x rho1 = Some v ->
    x \in key_set rho1. 
  Proof.
    intros. unfold key_set, In. rewrite H. eauto.
  Qed. 

  Lemma key_set_getlist {A} rho1 xs (vs : list A) :
    getlist xs rho1 = Some vs ->
    FromList xs \subset key_set rho1. 
  Proof with (now eauto with Ensembles_DB).
    revert rho1 vs. induction xs; intros rho1 vs1 Hget; inv Hget.
    - normalize_sets...
    - normalize_sets.
      destruct (M.get a rho1) eqn:Hgeta; try congruence. 
      destruct (getlist xs rho1) eqn:Hgetl; try congruence. 
      inv H0.
      eapply Union_Included.
      + eapply Singleton_Included. eapply key_set_get.
        eassumption.
      + eauto.
  Qed. 
      
      
  (** ** Top-level theorem *) 
  Lemma closure_conversion_correct_top
        (k : nat) (j : nat) (e1 e2 : exp) (C : exp_ctx) (Γ : var) (* dummy varaiable for environment *)
        r1 c1 m1 :
    
    (* The source program has unique binders *)
    unique_bindings e1 ->
    (* Requirement for mutual rec function blocks *)
    has_true_mut e1 ->
    (* dummy var is fresh *)
    ~ Γ \in bound_var e1 ->
            
    (* C[e2] is the closure converted program *)
    Closure_conversion ct (Empty_set _) (Empty_set _) id ct Γ [] e1 e2 C ->
    
    (* the source evaluates *)
    big_step emp (M.empty _) e1 r1 c1 m1 ->

    (* and it is not a stuck program -- because currently we don't assume that r1 is a value (it can be out-of-time-exception) *)
    not_stuck emp (M.empty _) e1 ->
    
    exists (r2 : ans) (c2 m2 : nat) (b : Inj),
      (* the target evaluates *)
      big_step_GC_cc emp (M.empty _) (C |[ e2 ]|) r2 c2 m2 /\
      (* time bounds *)
      c1 <= c2 <= Ktime * c1 /\
      (* space bounds *)
      m2 <= m1 + (cost_space_exp e1) + 1 /\
      (* the results are related *)
      r1 ≺ ^ (k ; j ; PreG ; PostG ; b ) r2.  
  Proof with (now eauto with Ensembles_DB).
    unfold install_env.
    destruct (alloc (Constr ct []) emp) as [lenv H2'] eqn:Ha.
    intros Hun Htm Hnin Hcc Hbs Hns. 
    assert (Heq : (e1, M.empty _, emp) ⪯ ^ (k + c1 ; j ;
                                            Pre (Empty_set _) 0 1; PreG;
                                            Post 0 0 1; PostG)
                                             (C |[ e2 ]|, (M.set Γ (Loc lenv) (M.empty value)), H2')).
    { eapply closure_conversion_correct_lr_closed; try eassumption.
      unfold install_env. rewrite Ha. reflexivity. }
    
    edestruct Heq with (rho2' := M.empty value) (H2'0 := @emp block) (b2 := @id var)
      as (r2 & c2 & m2 & b & Hbs2 & Hin & Hres); [ | | | | | | eassumption | | ].
    - reflexivity.
    - clear; now firstorder.
    - eapply Closure_conversion_toplevel_closed_cc in Hcc. unfold closed_exp in *.
      rewrite Hcc. split; intros x v Hin; inv Hin.
    - clear; now firstorder.
    - unfold Pre. unfold size_heap.
      rewrite !plus_O_n at 1.
      rewrite PS_cardinal_empty.
      simpl. rewrite <- plus_n_O.
      rewrite HL.size_with_measure_emp. omega.
      eapply PS_cardinal_empty_l. 
      rewrite <- mset_eq. reflexivity. 
    - eapply le_plus_r.
    - eassumption.
    - unfold Post in Hin. destruct Hin as [[Ht1 Ht2] Hm]. do 4 eexists. split. eassumption.
      split; [| split ].
      + omega.
      + rewrite !plus_O_n in *. eapply le_trans. eassumption.
        eapply Nat.max_lub. omega.
        unfold cost_space_heap, cost_heap in *.
        rewrite HL.max_with_measure_emp in *. 
        rewrite Nat_as_OT.max_0_r. omega.
      + rewrite cc_approx_val_eq in Hres.
        eapply cc_approx_val_monotonic. eassumption. omega.
  Qed. 

  Lemma closure_conversion_correct_top_div
        (k : nat) (j : nat) (e1 e2 : exp) (C : exp_ctx) (Γ : var) (* dummy varaiable for environment *)
        m1 :
    
     (* The source program has unique binders *)
     unique_bindings e1 ->
     has_true_mut e1 ->
     ~ Γ \in bound_var e1 ->
     
     (* C[e2] is the closure converted program *)
     Closure_conversion ct (Empty_set _) (Empty_set _) id ct Γ [] e1 e2 C ->
            
     (* the source diverges *)
     div_src emp (M.empty _) e1 m1 ->
    
    exists (m2 : natinf),
      (* the target diverges *)
      div_trg emp (M.empty _) (C |[ e2 ]|) m2 /\
      match m1, m2 with
      | ni m1, ni m2 => m2 <= m1 + (cost_space_exp e1) + 1
      | ni _, inf => False                                                          
      | inf, _ => True
      end.
  Proof with (now eauto with Ensembles_DB).
    destruct (alloc (Constr ct []) emp) as [lenv H2'] eqn:Ha. 
    intros Hun Htm Hnin Hcc Hdiv. 

    assert (Hns: not_stuck emp (M.empty _)  e1).
    { intros j'. eexists OOT. edestruct (Hdiv j') as [m' [Hbs Hleq]].
      eexists. eassumption. }

    eexists (match m1 with
             | infty => infty
             | ni m0 => ni (m0 + cost_space_exp e1 + 1)
             end).

    split; [| now  destruct m1; eauto ]. 
    
    intros i. destruct (Hdiv i) as [m1' [Hbs Hleq]].  
    assert (Heq : (e1, M.empty _, emp) ⪯ ^ (i ; j ;
                                              Pre (Empty_set _) 0 1; PreG;
                                              Post 0 0 1; PostG)
                                               (C |[ e2 ]|, (M.set Γ (Loc lenv) (M.empty value)), H2')).
      { eapply closure_conversion_correct_lr_closed; try eassumption.
        unfold install_env. rewrite Ha. reflexivity. }
      
      edestruct Heq with (rho2' := M.empty value) (H2'0 := @emp block) (b2 := @id var)
      as (r2 & c2 & m2 & b & Hbs2 & Hin & Hres); [ | | | | | | eassumption | | ].
    - reflexivity.
    - clear; now firstorder.
    - eapply Closure_conversion_toplevel_closed_cc in Hcc. unfold closed_exp in *.
      rewrite Hcc. split; intros x v Hin; inv Hin.
    - clear; now firstorder.
    - unfold Pre. unfold size_heap.
      rewrite !plus_O_n at 1.
      rewrite PS_cardinal_empty.
      simpl. rewrite HL.size_with_measure_emp. omega.
      eapply PS_cardinal_empty_l. 
      rewrite <- mset_eq. reflexivity. 
    - reflexivity.
    - eassumption.
    - rewrite cc_approx_val_eq in Hres. simpl in Hres.
      destruct r2; try contradiction.
      
      assert (Hmon : exists m2', m2' <= m2 /\ big_step_GC_cc emp (M.empty _) (C |[ e2 ]|) OOT i m2' ).
      { eapply big_step_GC_cc_OOT_mon. eassumption.
        unfold Post in *. omega. }
      edestruct Hmon as [m2' [Hm1 Hm2]]. eexists. split. eassumption.
      destruct m1; eauto. now constructor.
      destruct Hin as [_ Hmem]. eapply le_ni_le. eapply le_trans. eassumption.
      eapply le_trans. eassumption. simpl.
      eapply Nat_as_DT.max_lub. omega.
      unfold cost_space_heap, cost_heap in *.
      rewrite HL.max_with_measure_emp in *. 
      rewrite Nat_as_OT.max_0_r.
      eapply ni_le_le in Hleq. omega.
  Qed. 

End Top.

Print Assumptions Top.closure_conversion_correct_top.

Print Assumptions Top.closure_conversion_correct_top_div.