(* Generic definitions for step-indexed logical relations for L6 language transformations
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2019
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From CertiCoq.L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util set_util
                                List_util tactics map_util.
From CertiCoq.L6.Heap Require Import heap heap_defs space_sem GC log_rel_defs.
From compcert Require Import lib.Coqlib.



Module LogRelPostCC (H : Heap).

  Module LRDefs := LogRelDefs H.

  Import H LRDefs LRDefs.Sem.GC LRDefs.Sem.GC.Equiv
         LRDefs.Sem.GC.Equiv.Defs LRDefs.Sem.
  
  Definition fun_ptr_rel (GP : GIInv) (GQ : GInv) (b : Inj)
             (v1 : value) (H1 : heap block) (v2 : value) (H2 : heap block)
             (fR : fun_body_rel) : Prop :=
    match v1, v2 with
    | FunPtr B1 f1, FunPtr B2 f2 =>
      forall rho1 ft1 xs1 e1 vs1 vs2 b,        
        find_def f1 B1 = Some (ft1, xs1, e1) ->
        setlist xs1 vs1 (def_funs B1 B1 (M.empty _)) = Some rho1 ->

        length vs1 = length vs2 ->
        
        exists ft2 xs2 e2 rho2,
          find_def f1 B1 = Some (ft2, xs2, e2) /\
          setlist xs1 vs1 (def_funs B1 B1 (M.empty _)) = Some rho2 /\
          let GP' c1 c2 :=
              let '(H1, rho1, c1) := c1 in
              let '(H2, rho2, c2) := c2 in              
              (forall H1' H2' b1 b2,
                  live' (env_locs rho1 (occurs_free e1)) H1 H1' b1 ->
                  live' (env_locs rho2 (occurs_free e2)) H2 H2' b2 ->
                  GP (Empty_set _) _ 0 0 (H1', rho1, e1) (H2', rho2, e2)) in 
          fR GP' (GP (Empty_set _) _ 0 0)
             (GQ 0 0) b vs1 H1 vs2 H2 (H1, rho1, e1) (H2, rho2, e2)           
    | _, _ => False
    end.

  Definition no_clos_rel  (GP : GIInv) (GQ : GInv) (b : Inj)
             (b1 : block) (H1 : heap block)
             (b2 : block) (H2 : heap block)
             (fR : fun_body_rel) (vR : val_rel) : Prop := False.

  Instance Proper_clos_rel : forall P Q b b1 H1 b2 H2,
      Proper ((pointwise_lifting iff fun_body_args) ==> (pointwise_lifting iff val_rel_args) ==> iff) (no_clos_rel P Q b b1 H1 b2 H2).
  Proof. clear; now firstorder. Qed. 

  Instance Proper_fun_rel : forall  P Q b v1 H1 v2 H2, Proper ((pointwise_lifting iff fun_body_args) ==> iff) (fun_ptr_rel P Q b v1 H1 v2 H2).
  Proof.
    intros. intros P1 P2 Hyp. split. 
    - unfold fun_ptr_rel. destruct v1; destruct v2; eauto.
      intros Hfun. intros.
      edestruct Hfun as [ft2 [xs2 [e2 [rho2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
      repeat eexists; eauto. eapply Hyp. eassumption.
    - unfold fun_ptr_rel. destruct v1; destruct v2; eauto.
      intros Hfun. intros.
      edestruct Hfun as [ft2 [xs2 [e2 [rho2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
      repeat eexists; eauto. eapply Hyp. eassumption.
  Qed. 
      
  Definition val_rel := val_log_rel big_step_GC_cc big_step_GC_cc no_clos_rel fun_ptr_rel. 
  Definition exp_rel := exp_log_rel val_rel big_step_GC_cc big_step_GC_cc.
  Definition var_rel := var_log_rel' big_step_GC_cc big_step_GC_cc no_clos_rel fun_ptr_rel.
  Definition env_rel := env_log_rel_P' big_step_GC_cc big_step_GC_cc no_clos_rel fun_ptr_rel.
  Definition heap_rel := heap_log_rel val_rel.

  Definition val_rel' (k : nat)  (j : nat) (IP : GIInv) (P : GInv) (b : Inj) (r1 r2 : ans) : Prop :=
    match r1, r2 with
    | OOT, OOT => True (* Both programs timeout *)
    | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
      match v1, v2 with
      | Loc l1, Loc l2 =>
        b l1 = l2 /\
        match get l1 H1, get l2 H2 with
        | Some (Constr c1 vs1), Some (Constr c2 vs2) =>
          c1 = c2 /\ 
          Forall2 (fun v1 v2 =>  forall i, (i < j)%nat -> val_rel k i IP P b (Res (v1, H1)) (Res (v2, H2))) vs1 vs2
        | _, _ => False
        end
      | FunPtr B1 f1, FunPtr B2 f2 =>
        forall rho1 ft1 xs1 e1 vs1 vs2 b,        
          find_def f1 B1 = Some (ft1, xs1, e1) ->
          setlist xs1 vs1 (def_funs B1 B1 (M.empty _)) = Some rho1 ->

          length vs1 = length vs2 ->
          
          exists ft2 xs2 e2 rho2,
            find_def f1 B1 = Some (ft2, xs2, e2) /\
            setlist xs1 vs1 (def_funs B1 B1 (M.empty _)) = Some rho2 /\
            forall i, (i < k)%nat ->
                 (forall j, Forall2 (fun v1 v2 => val_rel i j IP P b (Res (v1, H1)) (Res (v2, H2))) vs1 vs2) ->
                 (forall H1' H2' b1 b2,
                     live' (env_locs rho1 (occurs_free e1)) H1 H1' b1 ->
                     live' (env_locs rho2 (occurs_free e2)) H2 H2' b2 ->
                     IP (Empty_set _) _ 0 0 (H1', rho1, e1) (H2', rho2, e2)) /\
                 (forall j, exp_rel i j
                               (IP (Empty_set _) _ 0 0) IP
                               (P 0 0) P
                               (H1, rho1, e1) (H2, rho2, e2))            
      | _, _ => False
      end
    | _, _ => False
    end.

  Opaque val_log_rel val_log_rel'. 
  
  Lemma val_rel_eq k j IP P b r1 r2 :
    val_rel k j IP P b r1 r2 <-> val_rel' k j IP P b r1 r2.
  Proof.
    destruct k; destruct j; 
      destruct r1 as [[[l1 | lf1 f1] H1] |]; destruct r2 as [[[l2 | lf2 f2] H2] |];
        try (now split; intros; contradiction);
        try (now simpl; eauto).
    simpl.
    - split.
      + simpl. intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ]. intros. omega.
      + simpl. intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ]. intros. omega.
    - simpl. split. 
      intros Hyp. intros.
      edestruct Hyp as [ft2 [xs2 [e2 [Hdef2 [Hset2 Hrel]]]]]; try eassumption.
      do 4 eexists; repeat split; eauto. exfalso. omega. 
      exfalso; omega.
      
      intros Hyp. intros.
      edestruct Hyp as [ft2 [xs2 [e2 [Hdef2 [Hset2 Hrel]]]]]; try eassumption.
      do 4 eexists; repeat split; eauto.

    - split.
      + simpl. intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ].
        intros v1 v2 Hyp i Hlt. 
        replace i with (j - (j - i)) by omega. eapply Hyp. omega.
      + simpl. intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ].
        intros v1 v2 Hyp i Hlt.
        replace (j - (j - i)) with i by omega. eapply Hyp. omega.
    - simpl. split. 
      intros Hyp. intros.
      edestruct Hyp as [ft2 [xs2 [e2 [Hdef2 [Hset2 Hrel]]]]]; try eassumption.
      do 4 eexists; repeat split; eauto. exfalso. omega. 
      exfalso; omega.
      
      intros Hyp. intros.
      edestruct Hyp as [ft2 [xs2 [e2 [Hdef2 [Hset2 Hrel]]]]]; try eassumption.
      do 4 eexists; repeat split; eauto.
    - split.
      + simpl. intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ]. intros. omega.
      + simpl. intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ]. intros. omega.
    - simpl. split. 
      + intros Hyp. intros.  
        edestruct Hyp as [ft2 [xs2 [rho2 [e2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
        do 4 eexists; split; [| split ]; eauto. intros i Hlt Hall.
        assert (Hieq : k - (k - i) = i) by omega. 
        split.  
        eapply Hrel; eauto. intros j.   
        eapply Forall2_monotonic; [| now eapply (Hall j)  ].
        intros v1 v2 Hyp'. rewrite Hieq. now eapply Hyp'.
        
        setoid_rewrite <- Hieq. eapply Hrel; eauto. intros j. 
        eapply Forall2_monotonic; [| now eapply (Hall j)  ].
        intros v1 v2 Hyp'. rewrite Hieq. eassumption.
      + intros Hyp. intros. 
        edestruct Hyp as [ft2 [xs2 [rho2 [e2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
        do 4 eexists; split; [| split ]; eauto. intros i Hlt Hall.
        assert (Hieq : k - (k - i) = i) by omega. 
        split. 
        eapply Hrel; eauto. intros j.  
        eapply Forall2_monotonic; [| now eapply (Hall j)  ].
        intros v1 v2 Hyp'. rewrite <- Hieq. now eapply Hyp'.
        
        setoid_rewrite  Hieq. eapply Hrel; eauto. intros j. 
        eapply Forall2_monotonic; [| now eapply (Hall j)  ].
        intros v1 v2 Hyp'. rewrite <- Hieq. eassumption.
    - split.
      + simpl. intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ].
        intros v1 v2 Hyp i Hlt. 
        replace i with (j - (j - i)) by omega. eapply Hyp. omega.
      + simpl. intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ].
        intros v1 v2 Hyp i Hlt.
        replace (j - (j - i)) with i by omega. eapply Hyp. omega.
    - simpl. split. 
      + intros Hyp. intros. 
        edestruct Hyp as [ft2 [xs2 [rho2 [e2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
        do 4 eexists; split; [| split ]; eauto. intros i Hlt Hall.
        assert (Hieq : k - (k - i) = i) by omega. 
        split. 
        eapply Hrel; eauto. intros j'.  
        eapply Forall2_monotonic; [| now eapply (Hall j')  ].
        intros v1 v2 Hyp'. rewrite Hieq. now eapply Hyp'. 
        
        setoid_rewrite <- Hieq. eapply Hrel; eauto. intros j'. 
        eapply Forall2_monotonic; [| now eapply (Hall j')  ].
        intros v1 v2 Hyp'. rewrite Hieq. eassumption.
      + intros Hyp. intros. 
        edestruct Hyp as [ft2 [xs2 [rho2 [e2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
        do 4 eexists; split; [| split ]; eauto. intros i Hlt Hall.
        assert (Hieq : k - (k - i) = i) by omega. 
        split. 
        eapply Hrel; eauto. intros j'.  
        eapply Forall2_monotonic; [| now eapply (Hall j')  ].
        intros v1 v2 Hyp'. rewrite <- Hieq. now eapply Hyp'. 
        
        setoid_rewrite  Hieq. eapply Hrel; eauto. intros j'. 
        eapply Forall2_monotonic; [| now eapply (Hall j')  ].
        intros v1 v2 Hyp'. rewrite <- Hieq. eassumption.

        Grab Existential Variables. exact id. exact id.
  Qed.

  (** * Respects f_eq_subdomain *)

  
  Lemma val_rel_rename_ext IP P b b' k j r1 r2:
    val_rel k j IP P b r1 r2 ->
    f_eq_subdomain (reach_ans r1) b b' ->
    val_rel k j IP P b' r1 r2.
  Proof with (now eauto with Ensembles_DB).
    rewrite !val_rel_eq in *. revert k j b b' r1 r2.
    induction k as [k IHk] using lt_wf_rec1.
    induction j as [j IHj] using lt_wf_rec1.
    intros b b' [[v1 H1] | ] [[v2 H2] | ] Hres Hfeq; try contradiction; [| now eauto ].
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
    try contradiction; try (now simpl; eauto).
    - simpl in Hres. destruct Hres as [Heq Hres]. 
      destruct (get l1 H1) as [b1'|] eqn:Hget1; destruct (get l2 H2) as [b2'|] eqn:Hget2;
        (try now eauto);
        try (destruct b1' as [ | | ]; contradiction). 
      split; eauto.
      + rewrite <- Hfeq. eassumption.
        eapply reach'_extensive. reflexivity.
      + destruct b1' as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ]; try contradiction;
          destruct b2' as [c2 vs2 | | ]; try contradiction. 
        destruct Hres as [Hceq Hall]. split; eauto. 
        eapply Forall2_monotonic_strong; [| eassumption ]. intros x1 x2 Hin1 Hin2 HR i Hlt.
        rewrite val_rel_eq. eapply IHj. eassumption.
        rewrite <- val_rel_eq. eapply HR; eauto.
        
        eapply f_eq_subdomain_antimon; [| eassumption ].
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl. rewrite post_Singleton; [| eassumption ].
        eapply In_Union_list. eapply in_map. eassumption.
    (* - intros rho1 ft1 xs1 e1 vs1 vs2 Hdef1 Hset1 Hlen. *)
    (*   edestruct Hres as [ft2 [xs2 [e2 [rho2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption. *)
    (*   do 4 eexists. split. eassumption. split. eassumption. intros i Hlt Hall. *)
    (*   eapply Hrel. eassumption. *)
    (*   intros j'. *)
      
    (*   eapply Forall2_monotonic_strong; [| exact (Hall j') ]. intros x1 x2 Hin1 Hin2 HR. *)
    (*   rewrite val_rel_eq. eapply IHk. eassumption. *)
    (*   rewrite <- val_rel_eq. eapply HR; eauto. *)
    (*   symmetry.  *)
    (*   eapply f_eq_subdomain_antimon; [| eassumption ]. *)
    (*   rewrite (reach_unfold H1 (val_loc (Loc l1))). *)
    (*   eapply Included_Union_preserv_r. eapply reach'_set_monotonic. *)
    (*   simpl. rewrite post_Singleton; [| eassumption ]. *)
    (*   eapply In_Union_list. eapply in_map. eassumption. *)
      
    (*   ; eauto. exfalso. omega.  *)
    (*   exfalso; omega. *)
      
    (*   intros Hyp. intros. *)
    (*   edestruct Hyp as [ft2 [xs2 [e2 [Hdef2 [Hset2 Hrel]]]]]; try eassumption. *)
    (*   do 4 eexists; repeat split; eauto. *)
  Qed.

  Lemma var_rel_rename_ext k j IP P b b' H1 H2 rho1 rho2 x y: 
    var_rel k j IP P b H1 rho1 H2 rho2 x y ->
    f_eq_subdomain (reach' H1 (env_locs rho1 [set x])) b b' ->
    var_rel k j IP P b' H1 rho1 H2 rho2 x y.
  Proof with (now eauto with Ensembles_DB).
    intros Hcc Heq v Hget. edestruct Hcc as [l2 [Hget2 Hres]].
    eassumption. eexists; split; eauto.
    rewrite <- val_log_rel_eq in *; tci.
    eapply val_rel_rename_ext. eassumption.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply env_locs_Singleton; try eassumption.
  Qed. 
  
  Lemma env_rel_rename_ext S k j IP P b b' H1 H2 rho1 rho2 : 
    env_rel S k j IP P b (H1, rho1) (H2, rho2) ->
    f_eq_subdomain (reach' H1 (env_locs rho1 S)) b b' ->
    env_rel S k j IP P b' (H1, rho1) (H2, rho2).
  Proof with (now eauto with Ensembles_DB).
    intros Henv Heq x Hin v Hget. 
    eapply var_rel_rename_ext. eapply Henv. 
    eassumption. eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply env_locs_monotonic.
    eapply Singleton_Included. eassumption.
    eassumption.
  Qed.


  Lemma heap_rel_rename_ext S k j IP P b b' H1 H2 : 
    heap_rel S k j IP P b H1 H2 ->
    f_eq_subdomain (reach' H1 S) b b' ->
    heap_rel S k j IP P b' H1 H2.
  Proof with (now eauto with Ensembles_DB).
    intros Hheap Hfeq x Hin.
    eapply val_rel_rename_ext. 
    rewrite <- Hfeq. eapply Hheap. eassumption.
    eapply reach'_extensive. eassumption.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic.
    eapply Singleton_Included. eassumption.
  Qed.


  

    
  (** * Logical relation respects heap_equivalence *)  
  
  (** * Well-formedness/closedness lemmas *)

  (** * Heap monotonicity/allocation  *)
  
  (** * Reachable locations image *)

  (** * Compatibility lemmas *)

End LogRelPostCC. 

  