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
      forall H1 H2 rho1 ft1 xs1 e1 vs1 vs2 b,        
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

  Instance Proper_clos_rel_impl : forall P Q b b1 H1 b2 H2,
      Proper ((pointwise_lifting impl fun_body_args) ==> (pointwise_lifting impl val_rel_args) ==> impl)
             (no_clos_rel P Q b b1 H1 b2 H2).
  Proof. clear; now firstorder. Qed. 

  Instance Proper_fun_rel_impl : forall  P Q b v1 H1 v2 H2,
      Proper ((pointwise_lifting impl fun_body_args) ==> impl) (fun_ptr_rel P Q b v1 H1 v2 H2).
  Proof.
    intros. intros P1 P2 Hyp.
    unfold fun_ptr_rel. destruct v1; destruct v2; unfold impl; eauto.
    intros Hfun. intros.
    edestruct Hfun as [ft2 [xs2 [e2 [rho2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
    repeat eexists; eauto. eapply Hyp. eassumption.
  Qed. 

  Definition val_rel := val_log_rel' big_step_GC_cc big_step_GC_cc no_clos_rel fun_ptr_rel. 
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
        forall H1 H2 rho1 ft1 xs1 e1 vs1 vs2 b,        
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
  
  
  Notation "p1 ⪯ ^ ( k ; j ; P1 ; P2 ; P3 ; P4 ) p2" :=
    (exp_rel k j P1 P2 P3 P4 p1 p2) (at level 70, no associativity).

  Notation "p1 ≺ ^ ( k ; j ; IP ; P ; b ) p2" :=
    (val_rel k j IP P b p1 p2) (at level 70, no associativity).
  
  Notation "p1 ⋞ ^ ( R ; k ; j ; IP ; P ; b ) p2" :=
    (env_rel R k j IP P b p1 p2) (at level 70, no associativity).

  Notation "S |- H1 ≼ ^ ( k ; j ; IP ; P ; b ) H2" :=
    (heap_rel S k j IP P b H1 H2) (at level 70, no associativity).

  
  Lemma val_rel_eq k j IP P b r1 r2 :
    val_rel k j IP P b r1 r2 <-> val_rel' k j IP P b r1 r2.
  Proof.
    unfold val_rel. 
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
      edestruct Hyp as [ft2 [xs2 [e2 [rho2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
      do 4 eexists; repeat split; eauto. exfalso; omega. exfalso; omega. 
    - split.
      + intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ].
        intros v1 v2 Hyp i Hlt. 
        replace i with (j - (j - i)) by omega. unfold val_rel. rewrite <- val_log_rel_eq; tci.
        eapply Hyp. omega.
      + intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ].
        intros v1 v2 Hyp i Hlt.
        rewrite val_log_rel_eq; tci.
        eapply Hyp. omega.
    - split. intros Hyp. simpl. intros.
      edestruct Hyp as [ft2 [xs2 [e2 [rho2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
      do 4 eexists; repeat split; eauto. exfalso. omega. 
      exfalso; omega.
      
      intros Hyp. simpl. intros.
      edestruct Hyp as [ft2 [xs2 [e2 [Hdef2 [Hset2 Hrel]]]]]; try eassumption.
      do 4 eexists; repeat split; eauto; exfalso; omega.
    - split.
      + intros [Hyp1 Hyp2]. split; eauto. 
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
    - split. 
      + intros Hyp. simpl; intros.  
        edestruct Hyp as [ft2 [xs2 [rho2 [e2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
        do 4 eexists; split; [| split ]; eauto. intros i Hlt Hall.
        assert (Hieq : k - (k - i) = i) by omega. 
        split.  
        eapply Hrel; eauto. intros j.   
        eapply Forall2_monotonic; [| now eapply (Hall j)  ].
        intros v1 v2 Hyp'. rewrite val_log_rel_eq; tci. now eapply Hyp'.
        
        setoid_rewrite <- Hieq.
        unfold val_rel. setoid_rewrite <- val_log_rel_eq; tci. eapply Hrel; eauto. omega.
        intros j. eapply Forall2_monotonic; [| now eapply (Hall j) ].
        intros v1 v2 Hyp'. rewrite Hieq. rewrite val_log_rel_eq; tci.
      + intros Hyp. simpl. intros. 
        edestruct Hyp as [ft2 [xs2 [rho2 [e2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
        do 4 eexists; split; [| split ]; eauto. intros i Hlt Hall.
        assert (Hieq : k - (k - i) = i) by omega. 
        split. 
        eapply Hrel; eauto. intros j.  
        eapply Forall2_monotonic; [| now eapply (Hall j)  ].
        intros v1 v2 Hyp'. unfold val_rel.
        rewrite <- val_log_rel_eq; tci. now eapply Hyp'.

        setoid_rewrite val_log_rel_eq; tci. 
        eapply Hrel; eauto. intros j. 
        eapply Forall2_monotonic; [| now eapply (Hall j)  ].
        intros v1 v2 Hyp'. unfold val_rel.
        rewrite <- val_log_rel_eq; tci.
    - split.
      + intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ].
        intros v1 v2 Hyp i Hlt. 
        replace i with (j - (j - i)) by omega. unfold val_rel.
        rewrite <- val_log_rel_eq; tci. eapply Hyp. omega. 
      + intros [Hyp1 Hyp2]. split; eauto. 
        destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
        destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
        destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
        destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
        eapply Forall2_monotonic; [| eassumption ].
        intros v1 v2 Hyp i Hlt. rewrite val_log_rel_eq; tci.
        eapply Hyp; eauto.        
    - split. 
      + intros Hyp. simpl. intros. 
        edestruct Hyp as [ft2 [xs2 [rho2 [e2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
        do 4 eexists; split; [| split ]; eauto. intros i Hlt Hall.
        split. 
        eapply Hrel; eauto. intros j'.  
        eapply Forall2_monotonic; [| now eapply (Hall j')  ].
        intros v1 v2 Hyp'. rewrite val_log_rel_eq; tci.

        apply Hyp'; eauto. unfold val_rel. setoid_rewrite <- val_log_rel_eq; tci.          
        apply Hrel; eauto.

        intros j'. eapply Forall2_monotonic; [| now eapply (Hall j')  ].
        intros v1 v2 Hyp'. rewrite val_log_rel_eq; tci.
      + intros Hyp. simpl. intros. 
        edestruct Hyp as [ft2 [xs2 [rho2 [e2 [Hdef2 [Hset2 Hrel]]]]]]; try eassumption.
        do 4 eexists; split; [| split ]; eauto. intros i Hlt Hall.
        assert (Hieq : k - (k - i) = i) by omega. 
        split. 
        eapply Hrel; eauto. intros j'.  
        eapply Forall2_monotonic; [| now eapply (Hall j')  ].
        intros v1 v2 Hyp'. unfold val_rel. rewrite <- val_log_rel_eq; tci.
        now eapply Hyp'. setoid_rewrite val_log_rel_eq; tci.          
        apply Hrel; eauto.
        
        intros j'. eapply Forall2_monotonic; [| now eapply (Hall j')  ].
        intros v1 v2 Hyp'. unfold val_rel. rewrite <- val_log_rel_eq; tci.
        
        Grab Existential Variables.
        eassumption. eassumption. eassumption. eassumption.
        eassumption. eassumption. eassumption. eassumption.
        eassumption. eassumption. eassumption. eassumption.        

  Qed.

  (** * Respects f_eq_subdomain *)

  Lemma val_rel_rename_ext GIP GP b b' k j r1 r2:
    r1 ≺ ^ (k ; j ; GIP ; GP ; b) r2 ->
    f_eq_subdomain (reach_ans r1) b b' ->
    r1 ≺ ^ (k ; j ; GIP ; GP ; b') r2.
  Proof with (now eauto with Ensembles_DB).
    revert k j b b' r1 r2.
    induction k as [k IHk] using lt_wf_rec1.
    induction j as [j IHj] using lt_wf_rec1.
    setoid_rewrite val_rel_eq.
    intros b b' [[v1 H1] | ] [[v2 H2] | ] Hres Hfeq; try contradiction; [| now eauto ].
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2];
    try contradiction; try (now simpl; eauto). 
    - unfold val_rel' in *. destruct Hres as [Heq Hres]. 
      destruct (get l1 H1) as [b1'|] eqn:Hget1; destruct (get l2 H2) as [b2'|] eqn:Hget2;
        (try now eauto);
        try (destruct b1' as [ | | ]; contradiction). 
      split; eauto.
      + rewrite <- Hfeq. eassumption.
        eapply reach'_extensive. reflexivity.
      + destruct b1' as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ]; try contradiction;
          destruct b2' as [c2 vs2 | | ]; try contradiction. 
        destruct Hres as [Hceq Hall]. split; eauto. 
        eapply Forall2_monotonic_strong; [| eassumption ].
        intros x1 x2 Hin1 Hin2 HR i Hlt.
        eapply IHj; eauto. 
        
        eapply f_eq_subdomain_antimon; [| eassumption ].
        rewrite (reach_unfold H1 (val_loc (Loc l1))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl. rewrite post_Singleton; [| eassumption ].
        eapply In_Union_list. eapply in_map. eassumption.
  Qed.

  Lemma var_rel_rename_ext k j IP P b b' H1 H2 rho1 rho2 x y: 
    var_rel k j IP P b H1 rho1 H2 rho2 x y ->
    f_eq_subdomain (reach' H1 (env_locs rho1 [set x])) b b' ->
    var_rel k j IP P b' H1 rho1 H2 rho2 x y.
  Proof with (now eauto with Ensembles_DB).
    intros Hcc Heq v Hget. edestruct Hcc as [l2 [Hget2 Hres]].
    eassumption. eexists; split; eauto.
    eapply val_rel_rename_ext. eassumption.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply env_locs_Singleton; try eassumption.
  Qed. 
  
  Lemma env_rel_rename_ext GIP GP S k j b b' H1 H2 rho1 rho2 : 
    (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; b) (H2, rho2) ->
    f_eq_subdomain (reach' H1 (env_locs rho1 S)) b b' ->
    (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; b') (H2, rho2).
  Proof with (now eauto with Ensembles_DB).
    intros Henv Heq x Hin v Hget. 
    eapply var_rel_rename_ext. eapply Henv. 
    eassumption. eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply env_locs_monotonic.
    eapply Singleton_Included. eassumption.
    eassumption.
  Qed.


  Lemma heap_rel_rename_ext S k j IP P b b' H1 H2 : 
    S |- H1 ≼ ^ ( k ; j ; IP ; P ; b ) H2 ->
    f_eq_subdomain (reach' H1 S) b b' ->
    S |- H1 ≼ ^ ( k ; j ; IP ; P ; b' ) H2.
  Proof with (now eauto with Ensembles_DB).
    intros Hheap Hfeq x Hin.
    eapply val_rel_rename_ext. 
    rewrite <- Hfeq. eapply Hheap. eassumption.
    eapply reach'_extensive. eassumption.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic.
    eapply Singleton_Included. eassumption.
  Qed.

  Global Instance Proper_val_rel_f_eq k j IP P :
    Proper (f_eq ==> eq ==> eq ==> iff) (val_rel k j IP P).
  Proof.
    intros ? ? H ? ? ? ? ? ?. subst.
    split; intros H1. eapply val_rel_rename_ext.
    eassumption.
    rewrite H. reflexivity.
    eapply val_rel_rename_ext.
    eassumption.
    rewrite H. reflexivity.
  Qed. 

  Global Instance Proper_env_rel_f_eq S k j IP P :
    Proper (f_eq ==> eq ==> eq ==> iff) (env_rel S k j IP P).
  Proof.
    intros ? ? H [? ?] [? ?] Heq [? ?] [? ?] Heq'. inv Heq; inv Heq'.
    split; intros H1; eapply env_rel_rename_ext.
    eassumption.
    rewrite H. reflexivity.
    eassumption.
    rewrite H. reflexivity.
  Qed. 

  Global Instance Proper_heap_rel_f_eq S k j IP P :
    Proper (f_eq ==> eq ==> eq ==> iff) (heap_rel S k j IP P).
  Proof.
    intros ? ? H ? ? Heq ? ? Heq'. subst.
    split; intros H1; eapply heap_rel_rename_ext.
    eassumption.
    rewrite H. reflexivity.
    eassumption.
    rewrite H. reflexivity.
  Qed. 
    
  (** * Logical relation respects heap_equivalence *)  

    Lemma val_rel_res_eq GIP GP (k j : nat) (b' b1 b2 : Inj) (H1 H2 H1' H2' : heap block)
        (v1 v2 v1' v2' : value) :
    (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b') (Res (v2, H2)) ->

    (v1, H1) ≈_(id, b1) (v1', H1') ->
    injective_subdomain (reach' H1' (val_loc v1')) b1 ->

    (v2, H2) ≈_(b2, id) (v2', H2') ->
    injective_subdomain (reach' H2 (val_loc v2)) b2 ->
    
    (Res (v1', H1')) ≺ ^ (k ; j ; GIP ; GP ; b2 ∘ b' ∘ b1) (Res (v2', H2')).
  Proof with now eauto with Ensembles_DB.
    revert j b' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'.
    induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1.
    intros b' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'. 
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2];
      try (now intros; contradiction); try (now simpl; eauto).
    - simpl. 
      intros [Heq Hcc] (* Hwf1 Hwf2 Hl1 Hl2 *) Hres1 Hr1 Hres2 Hr2. 
      destruct (get l1 H1) as
          [[c1 vs1 | | ] | ] eqn:Hget1;
        destruct (get l2 H2) as
          [[c2 vs2 | | ] | ] eqn:Hget2; try contradiction.
      rewrite res_equiv_eq in Hres1, Hres2.
      destruct v1' as [l1' | lf1' f1']; destruct v2' as [l2' | lf2' f2'];
      try contradiction.
      simpl in Hres1, Hres2. 
      rewrite Hget1 in Hres1. rewrite Hget2 in Hres2.
      destruct Hres1 as [Heqi1 Hres1].
      destruct Hres2 as [Heqi2 Hres2]. subst.       
      destruct (get l1' H1') as [b1'|] eqn:Hget1'; [| contradiction ].
      destruct (get l2' H2') as [b2'|] eqn:Hget2'; [| contradiction ].
      destruct b1' as [c1' vs1' | | ]; [| contradiction | contradiction ].
      destruct b2' as [c2' vs2' | | ]; [| contradiction | contradiction ].
      
      destruct Hres1 as [Heqc1 Heqb1].
      destruct Hres2 as [Heqc2 Heqb2]. subst. 
      destruct Hcc as [Heqc Hall]; subst. 
      split. unfold compose. rewrite <- Heqi1. unfold id. rewrite Heqi2.
      reflexivity.
      split; eauto.
      
      eapply Forall2_vertical_l_strong
        with (R1 := fun x y => forall i : nat, i < j ->
                             Res (x, H1) ≺ ^ (k; i; GIP; GP; b2 ∘ b') Res (y, H2')); 
        [| | now eapply Heqb1 ].
      
      * intros.
        setoid_rewrite val_log_rel_eq; tci. 
        eapply val_rel_rename_ext;
          [| rewrite <- (compose_id_neut_l (b2 ∘ b' ∘ b1)); reflexivity ]. 
        rewrite <- Combinators.compose_assoc.
        eapply IHj; try eassumption; try reflexivity.
        eapply H4. eassumption. eassumption. 
        
        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold _ (val_loc (Loc l1'))).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. simpl. rewrite post_Singleton; [| eassumption ].
        eapply In_Union_list. eapply in_map. eassumption.

        clear. now firstorder.
      * eapply Forall2_vertical_r_strong; [| eapply Hall | eassumption ].
        intros x y z Hin1 Hin2 Hin3 Hin Hres. intros j' Hlt. 
        eapply val_rel_rename_ext;
          [| rewrite <- (compose_id_neut_r (b2 ∘ b')); reflexivity ]. 
        eapply IHj; [ eassumption | | reflexivity | | | ]. 
        unfold  val_rel. rewrite <- val_log_rel_eq; tci.
        clear. now firstorder. now eapply Hres.
        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold _ [set b' l1]).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. simpl. rewrite post_Singleton; [| eassumption ].
        eapply In_Union_list. eapply in_map. eassumption.
    - intros Hrel Hres1 Hinj1 Hres2 Hinj2. 
      destruct v1' as [l1' | lf1' f1']; destruct v2' as [l2' | lf2' f2'];
        try (rewrite res_equiv_eq in Hres2;
             rewrite res_equiv_eq in Hres1; contradiction).
      rewrite res_equiv_eq in Hres2; rewrite res_equiv_eq in Hres1.
      simpl in Hres1, Hres2.
      inv Hres1. inv Hres2.
      eassumption. 
  Qed.
  
  Lemma var_rel_heap_env_equiv GP GIP (S1 S2 : Ensemble var) (k j : nat)
        (β β1 β2 : Inj)
        (H1 H2 H1' H2' : heap block)
        (rho1 rho2 rho1' rho2' : env) (x1 x2 : var) :
    var_rel k j GIP GP β H1 rho1 H2 rho2 x1 x2 ->
    S1 |- (H1, rho1) ⩪_(id, β1) (H1', rho1') ->
    injective_subdomain (reach' H1' (env_locs rho1' S1)) β1 -> 
    S2 |- (H2, rho2) ⩪_(β2, id) (H2', rho2') ->
    injective_subdomain (reach' H2 (env_locs rho2 S2)) β2 ->
    x1 \in S1 -> x2 \in S2 ->
    var_rel k j GIP GP (β2 ∘ β ∘ β1)
                      H1' rho1' H2' rho2' x1 x2.
  Proof.
    intros Henv Heq1 Hinj1 Heq2 Hinj2 Hin1 Hin2 v1' Hget1'.
    assert (Hget1'' := Hget1').
    eapply Heq1 in Hget1'; [| eassumption ].
    destruct Hget1' as [v1 [Hget1 Hequiv1]]. 
    eapply Henv in Hget1. 
    destruct Hget1 as [v2 [Hget2 Hval]]; eauto.
    assert (Hget2'' := Hget2).
    eapply Heq2 in Hget2; [| eassumption ].
    destruct Hget2 as [v2' [Hget2' Hequiv2]]; eauto. 
    eexists. split; eauto.
    eapply val_rel_res_eq; try eassumption.
    symmetry. eassumption. 
    eapply injective_subdomain_antimon. eassumption.
    eapply reach'_set_monotonic. now eapply get_In_env_locs; eauto.
    eapply injective_subdomain_antimon. eassumption.
    eapply reach'_set_monotonic. now eapply get_In_env_locs; eauto.
  Qed. 
  

  Lemma env_rel_heap_env_equiv GIP GP (S S1 S2 : Ensemble var) (k j : nat)
        (b b1 b2 : Inj)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 rho1' rho2' : env) :
    (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; b ) (H2, rho2) ->
    S1 |- (H1, rho1) ⩪_(id, b1) (H1', rho1') ->
    injective_subdomain (reach' H1' (env_locs rho1' S1)) b1 -> 
    S2 |- (H2, rho2) ⩪_(b2, id) (H2', rho2') ->
    injective_subdomain (reach' H2 (env_locs rho2 S2)) b2 ->
    S \subset S1 -> S \subset S2 ->
    (H1', rho1') ⋞ ^ (S; k; j; GIP; GP; (b2 ∘ b ∘ b1)) (H2', rho2').
  Proof.
    intros Henv Heq1 Hinj1 Heq2 Hinj2 Hin1 Hin2 v1' Hget1'.
    eapply var_rel_heap_env_equiv; try eassumption; eauto.
    eapply Henv. eassumption. 
  Qed.
  
  (* Reachable values are in the LR *)
  
  Lemma val_rel_post GIP GP (k j : nat) b v1 v2 H1 H2 l :
    Res (v1, H1) ≺ ^ (k; S j; GIP ; GP; b) Res (v2, H2) ->
    l \in post H1 (val_loc v1) ->
    Res (Loc l, H1) ≺ ^ (k; j; GIP ; GP; b) Res (Loc (b l), H2).
  Proof. 
    intros Hcc [l' [b' [Hin [Hget Hin']]]].
    destruct v1 as [l1 |]; [| now inv Hin ]. inv Hin.
    destruct v2 as [l2 |]; [| now inv Hcc ].
    destruct Hcc as [Heq Hcc].
    rewrite Hget in Hcc.
    
    (destruct b' as [| |]; try contradiction;
     destruct (get l2 H2) as [[| |] | ] eqn:Hget'); try contradiction.

    - simpl in  Hin'.      
      destruct Hcc as [Heq1 Hrel]. subst.
      simpl in Hrel.
      edestruct (@Union_lists_exists loc) as [S' [Hin3 Hin2]]. eassumption.
      edestruct (list_in_map_inv _ _ _ Hin3) as [l3' [Heql Hinl]]; subst.
      destruct l3' as [l3' |]; inv Hin2.
      edestruct (Forall2_exists _ l0 l1 (Loc l) Hinl Hrel)  as [x' [Hin2 Hres']].
      specialize (Hres' j (NPeano.Nat.lt_succ_diag_r j)).
      rewrite val_log_rel_eq in Hres'; tci.
      assert (Hleq : x' = Loc (b l)) by (eapply val_log_rel_loc_eq; eauto).
      subst. eassumption.
  Qed.

  Lemma val_rel_post_n GIP GP (k j : nat) b v1 v2 H1 H2 l n :
    Res (v1, H1) ≺ ^ (k; n + j; GIP ; GP; b) Res (v2, H2) ->
    l \in (post H1 ^ n) (val_loc v1) ->
    Res (Loc l, H1) ≺ ^ (k; j; GIP ; GP; b ) Res (Loc (b l), H2).
  Proof.
    revert v1 v2 l j; induction n as [n IHn] using lt_wf_rec1;
      destruct n; intros v1 v2 l j. 
    - intros Heq Hin. destruct v1; [| now inv Hin ]. inv Hin. 
      erewrite <- !(val_log_rel_loc_eq) with (v2 := v2); eauto.
    - intros Hrel Hpost.
      replace (S n) with (n + 1) in Hpost by omega.
      rewrite app_plus in Hpost. unfold compose in Hpost. simpl in Hpost.
      edestruct post_n_exists_Singleton as [l3 [Hin1 Hinp]]; try eassumption.
      eapply IHn with (v1 := Loc l3); [| | eassumption ]. omega.
      eapply val_rel_post. eassumption. 
      eassumption. 
  Qed.
  

  Corollary val_rel_reach GIP GP (k : nat) b v1 v2 H1 H2 l :
    (forall j, Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b) Res (v2, H2)) ->
    l \in reach' H1 (val_loc v1) ->
    (forall j, Res (Loc l, H1) ≺ ^ (k; j; GIP ; GP; b ) Res (Loc (b l), H2)).
  Proof.
    intros Hres [n [_ Hin]] j. eapply val_rel_post_n; now eauto.
  Qed.

  Lemma val_rel_reach2 GIP GP (k : nat) b v1 v2 H1 H2 l2 :
    (forall j, Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b ) Res (v2, H2)) ->
    l2 \in reach' H2 (val_loc v2) ->
    (exists l1, l1 \in reach' H1 (val_loc v1) /\
           b l1 = l2 /\
           (forall j, Res (Loc l1, H1) ≺ ^ (k; j; GIP ; GP; b) Res (Loc (b l1), H2))).
  Proof. 
    intros Hres Hrin.
    assert (Hrin2 := Hrin).
    (* eapply cc_approx_val_image_eq in Hrin2; [ | eassumption ].   *)
    (* destruct Hrin2 as [l1' [Heq Hind]]; subst. *)
    (* eexists. split. eassumption. *)
    (* split. reflexivity.  *)
    (* eapply cc_approx_val_reach_cc. eassumption. eassumption. *)
  Admitted. (* needs image lemma *)


  (** * Well-formedness/closedness lemmas *)

  Lemma val_rel_well_formed_post GIP GP (k j : nat) b v1 v2 H1 H2 :
    Res (v1, H1) ≺ ^ (k; j + 1; GIP ; GP; b) Res (v2, H2) ->
    well_formed (((post H1) ^ j) (val_loc v1)) H1.
  Proof.
    intros Hcc l1 b1 Hin Hget l Hlin.
    assert (Hp : (post H1 ^ S j) (val_loc v1) l).
    { simpl. do 2 eexists. split. eassumption. 
      split; eassumption. }
    eapply val_rel_post_n with (j := 0) in Hp.
    eapply val_log_rel_in_dom1. eassumption. 
    reflexivity.
    eapply val_rel_j_monotonic; tci. omega.
  Qed.
  
  Lemma val_rel_well_formed_reach GIP GP (k : nat) b v1 v2 H1 H2 :
    (forall j, Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b) Res (v2, H2)) ->
    well_formed (reach' H1 (val_loc v1)) H1.
  Proof.
    intros Hcc l1 b1 [n [_ Hin]] Hget l Hdom.
    eapply val_rel_well_formed_post; try eassumption.
    now eauto.
  Qed.

  Lemma val_rel_closed GIP GP (k : nat) b v1 v2 H1 H2 :
    (forall j, Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b) Res (v2, H2)) ->
    closed (reach' H1 (val_loc v1)) H1.
  Proof.
    intros Hyp. eapply reach'_closed.
    eapply val_rel_well_formed_reach. eassumption.
    eapply val_log_rel_in_dom1. eapply (Hyp 0). 
  Qed.


  Lemma var_rel_well_formed_reach GP GIP (k : nat)
        (b : Inj) (H1 H2 : heap block) (rho1 rho2 : env) (x1 x2 : var) :
    (forall j, var_rel k j GIP GP b H1 rho1 H2 rho2 x1 x2) ->
    well_formed (reach' H1 (env_locs rho1 [set x1])) H1.
  Proof.
    intros Hrel.
    destruct (M.get x1 rho1) eqn:Heqb.
    rewrite env_locs_Singleton; eauto.
    
    edestruct (Hrel 0) as [v2 [Hget2 Hequiv2]]. eassumption. 
    eapply val_rel_well_formed_reach. intros j1.
    edestruct (Hrel j1) as [v2' [Hget2' Hequiv2']]. eassumption. 
    repeat subst_exp. eassumption.

    rewrite env_locs_Singleton_None; try eassumption. 
    rewrite reach'_Empty_set. eapply well_formed_Empty_set.
  Qed.  
  
  Lemma var_rel_closed_reach GP GIP (S1 S2 : Ensemble var) (k j : nat)
        (b : Inj) (H1 H2 H1' H2' : heap block)
        (rho1 rho2 rho1' rho2' : env) (x1 x2 : var) :
    (forall j, var_rel k j GIP GP b H1 rho1 H2 rho2 x1 x2) ->
    closed (reach' H1 (env_locs rho1 [set x1])) H1.
  Proof.
    intros Hvar.
    eapply reach'_closed.     
    eapply var_rel_well_formed_reach. eassumption.

    destruct (M.get x1 rho1) eqn:Heqb.
    rewrite env_locs_Singleton; eauto.
    
    edestruct (Hvar 0) as [v2 [Hget2 Hequiv2]]. eassumption. 
    now eapply val_log_rel_in_dom1; eauto.
    rewrite env_locs_Singleton_None; try eassumption.
    now eauto with Ensembles_DB. 
  Qed.  
    
  Lemma env_rel_well_fomed_reach GIP GP (P : Ensemble var) (k : nat)
        (b : Inj) (H1 H2 : heap block) (rho1 rho2 : env) :
    (forall j, (H1, rho1) ⋞ ^ (P; k; j; GIP; GP; b ) (H2, rho2)) ->
    well_formed (reach' H1 (env_locs rho1 P)) H1.
  Proof.
    intros Henv l1 b1 [n [_ Hin]] Hget l Hlocs. 
    edestruct post_n_exists_Singleton as [l1' [Hin' Hp]]. eassumption.
    edestruct Hin' as [y [Hiny Heqy]].
    destruct (M.get y rho1) as [[l1'' |] |] eqn:Hgety; try contradiction.
    inv Heqy. eapply Henv with (j := n + 1) in Hgety; [| eassumption ].
    edestruct Hgety as [l2 [Hgetyl1 Hres]]. 
    assert (Hr : In loc ((post H1 ^ (S n)) [set l1']) l). 
    { do 2 eexists; split. eassumption. split; eauto. }
    eapply val_rel_well_formed_post; eassumption.
  Qed.

  Lemma env_rel_closed_reach GIP GP (P : Ensemble var) (k : nat)
        (b : Inj) (H1 H2 : heap block) (rho1 rho2 : env) :
    (forall j, (H1, rho1) ⋞ ^ (P; k; j; GIP; GP; b ) (H2, rho2)) ->
    closed (reach' H1 (env_locs rho1 P)) H1.
  Proof.
    intros Henv. eapply reach'_closed.
    eapply env_rel_well_fomed_reach. eassumption.
    eapply env_log_rel_P_in_dom1. eapply (Henv 0).
  Qed.

  Lemma heap_rel_well_fomed_reach GIP GP (P : Ensemble var) (k : nat)
        (b : Inj) (H1 H2 : heap block) :
    (forall j, P |- H1 ≼ ^ ( k ; j ; GIP ; GP ; b ) H2) ->
    well_formed (reach' H1 P) H1.
  Proof.
    intros Henv l1 b1 [n [_ Hin]] Hget l Hlocs. 
    edestruct post_n_exists_Singleton as [l1' [Hin' Hp]]. eassumption.
    eapply val_rel_well_formed_post. eapply Henv. eassumption. simpl. eassumption.
    eassumption. eassumption.
  Qed.

  Lemma heap_rel_closed_reach GIP GP (P : Ensemble var) (k : nat)
        (b : Inj) (H1 H2 : heap block) (rho1 rho2 : env) :
    (forall j, P |- H1 ≼ ^ ( k ; j ; GIP ; GP ; b ) H2) ->
    closed (reach' H1 P) H1.
  Proof.
    intros Henv. eapply reach'_closed.
    eapply heap_rel_well_fomed_reach. eassumption.
    eapply heap_log_rel_in_dom1. eapply (Henv 0).
  Qed.

  Lemma val_rel_well_formed_post2 GIP GP (k j : nat) b v1 v2 H1 H2 :
    Res (v1, H1) ≺ ^ (k; j + 1; GIP ; GP; b) Res (v2, H2) ->
    well_formed (((post H2) ^ j) (val_loc v2)) H2.
  Proof.
    (* intros Hcc l1 b1 Hin Hget l Hlin. *)
    (* assert (Hp : (post H2 ^ S j) (val_loc v2) l). *)
    (* { simpl. do 2 eexists. split. eassumption.  *)
    (*   split; eassumption. } *)
    (* eapply val_rel_post_n with (j := 0) in Hp. *)
    (* eapply val_log_rel_in_dom2. eassumption.  *)
    (* reflexivity. *)
    (* eapply val_rel_j_monotonic; tci. omega. *)
  Admitted. (* need lemma about image *)
  
  Lemma val_rel_well_formed_reach2 GIP GP (k : nat) b v1 v2 H1 H2 :
    (forall j, Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b) Res (v2, H2)) ->
    well_formed (reach' H2 (val_loc v2)) H2.
  Proof.
    intros Hcc l1 b1 [n [_ Hin]] Hget l Hdom.
    eapply val_rel_well_formed_post2; try eassumption.
    now eauto.
  Qed.

  Lemma val_rel_closed2 GIP GP (k : nat) b v1 v2 H1 H2 :
    (forall j, Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b) Res (v2, H2)) ->
    closed (reach' H2 (val_loc v2)) H2.
  Proof.
    intros Hyp. eapply reach'_closed.
    eapply val_rel_well_formed_reach2. eassumption.
    eapply val_log_rel_in_dom2. eapply (Hyp 0). 
  Qed.


  Lemma var_rel_well_formed_reach2 GP GIP (k : nat)
        (b : Inj) (H1 H2 : heap block) (rho1 rho2 : env) (x1 x2 : var) :
    (forall j, var_rel k j GIP GP b H1 rho1 H2 rho2 x1 x2) ->
    binding_in_map [set x1] rho1 ->
    well_formed (reach' H2 (env_locs rho2 [set x2])) H2.
  Proof.
    intros Hrel [Hin Hget1]. reflexivity. 
    
    edestruct (Hrel 0) as [v2 [Hget2 Hequiv2]]. eassumption. 
    rewrite env_locs_Singleton; [| eassumption ].
    eapply val_rel_well_formed_reach2. intros j1. 
    edestruct (Hrel j1) as [v2' [Hget2' Hequiv2']]. eassumption. 
    repeat subst_exp. eassumption.
  Qed.  
  
  Lemma var_rel_closed_reach2 GP GIP (S1 S2 : Ensemble var) (k j : nat)
        (b : Inj) (H1 H2 H1' H2' : heap block)
        (rho1 rho2 rho1' rho2' : env) (x1 x2 : var) :
    (forall j, var_rel k j GIP GP b H1 rho1 H2 rho2 x1 x2) ->
    binding_in_map [set x1] rho1 ->
    closed (reach' H2 (env_locs rho2 [set x2])) H2.
  Proof.
    intros Hvar Hin.
    eapply reach'_closed.     
    eapply var_rel_well_formed_reach2; try eassumption.
    
    edestruct Hin as [v1 Hget]. reflexivity.
    edestruct (Hvar 0) as [v2' [Hget2 Hequiv2]]. eassumption. 
    rewrite env_locs_Singleton; eauto.
    
    now eapply val_log_rel_in_dom2; eauto.
  Qed.  
  
  Lemma env_rel_well_fomed_reach2 GIP GP (P : Ensemble var) (k : nat)
        (b : Inj) (H1 H2 : heap block) (rho1 rho2 : env) :
    (forall j, (H1, rho1) ⋞ ^ (P; k; j; GIP; GP; b ) (H2, rho2)) ->
    binding_in_map P rho1 ->
    well_formed (reach' H2 (env_locs rho2 P)) H2.
  Proof.
    intros Henv Hbin l1 b1 [n [_ Hin]] Hget l Hlocs. 
    edestruct post_n_exists_Singleton as [l1' [Hin' Hp]]. eassumption.
    edestruct Hin' as [y [Hiny Heqy]].
    edestruct (Hbin y) as [v1 Hgetv1]. eassumption. 
    destruct (M.get y rho2) as [[l1'' |] |] eqn:Hgety; try contradiction.
    eapply var_rel_well_formed_reach2; try eassumption.
    intros j; eapply Henv. eassumption.
    eapply binding_in_map_antimon; try eassumption.
    eapply Singleton_Included; eassumption.
    inv Heqy. rewrite env_locs_Singleton; eauto. eexists; split; eauto.
    now constructor. 
  Qed.

  Lemma env_rel_closed_reach2 GIP GP (P : Ensemble var) (k : nat)
        (b : Inj) (H1 H2 : heap block) (rho1 rho2 : env) :
    (forall j, (H1, rho1) ⋞ ^ (P; k; j; GIP; GP; b ) (H2, rho2)) ->
    binding_in_map P rho1 ->
    closed (reach' H2 (env_locs rho2 P)) H2.
  Proof.
    intros Henv Hbin. eapply reach'_closed.
    eapply env_rel_well_fomed_reach2. eassumption.
    eassumption. eapply env_log_rel_P_in_dom2. eapply (Henv 0).
    eassumption. 
  Qed.

  (* Lemma heap_rel_well_fomed_reach GIP GP (P : Ensemble var) (k : nat) *)
  (*       (b : Inj) (H1 H2 : heap block) : *)
  (*   (forall j, P |- H1 ≼ ^ ( k ; j ; GIP ; GP ; b ) H2) -> *)
  (*   well_formed (reach' H1 P) H1. *)
  (* Proof. *)
  (*   intros Henv l1 b1 [n [_ Hin]] Hget l Hlocs.  *)
  (*   edestruct post_n_exists_Singleton as [l1' [Hin' Hp]]. eassumption. *)
  (*   eapply val_rel_well_formed_post. eapply Henv. eassumption. simpl. eassumption. *)
  (*   eassumption. eassumption. *)
  (* Qed. *)

  (* Lemma heap_rel_closed_reach GIP GP (P : Ensemble var) (k : nat) *)
  (*       (b : Inj) (H1 H2 : heap block) (rho1 rho2 : env) : *)
  (*   (forall j, P |- H1 ≼ ^ ( k ; j ; GIP ; GP ; b ) H2) -> *)
  (*   closed (reach' H1 P) H1. *)
  (* Proof. *)
  (*   intros Henv. eapply reach'_closed. *)
  (*   eapply heap_rel_well_fomed_reach. eassumption. *)
  (*   eapply heap_log_rel_in_dom1. eapply (Henv 0). *)
  (* Qed. *)


  (** * Heap monotonicity/allocation  *)

  Lemma val_rel_heap_monotonic GIP GP (k : nat) b (H1 H2 H1' H2' : heap block)
        (v1 v2 : value):
    H1 ⊑ H1' -> H2 ⊑ H2' ->
    (forall j, Res (v1, H1) ≺ ^ (k ; j; GIP ; GP ; b) Res (v2, H2)) ->
    (forall j, Res (v1, H1') ≺ ^ (k ; j; GIP ; GP; b) Res (v2, H2')).
  Proof with (now eauto with Ensembles_DB).
    intros Hsub1 Husb2 Hval j.
    rewrite <- (compose_id_neut_l b).
    rewrite <- (compose_id_neut_r (id ∘ b)).    

    eapply val_rel_res_eq. eapply Hval. 
    
    eapply heap_eq_res_equiv. eapply HL.subheap_heap_eq.
    eassumption.
    eapply in_dom_closed.
    eapply val_rel_closed. eassumption.

    clear; now firstorder.

    eapply heap_eq_res_equiv. eapply HL.subheap_heap_eq.
    eassumption.
    eapply in_dom_closed.
    eapply val_rel_closed2. eassumption.
    clear; now firstorder. 
  Qed. 

  Lemma var_rel_heap_monotonic GIP GP (k : nat) b (H1 H2 H1' H2' : heap block)
       (rho1 rho2 : env) x y:
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     (forall j, var_rel k j GIP GP b H1 rho1 H2 rho2 x y) ->
     (forall j, var_rel k j GIP GP b H1' rho1 H2' rho2 x y).
   Proof.
     intros Hs1 Hs2 Hres j v Hget.
     edestruct (Hres j) as [l2 [Hget2 Hres2]]; eauto.
     eexists; split; eauto.
     eapply val_rel_heap_monotonic; try eassumption.
     intros j'.
     edestruct (Hres j') as [l2' [Hget2' Hres2']]; eauto.
     repeat subst_exp.
     eassumption.
   Qed.
   
   Lemma env_rel_heap_monotonic GIP GP S (k : nat) b
         (H1 H2 H1' H2' : heap block)
       (rho1 rho2 : env):
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     (forall j, (H1, rho1) ⋞ ^ (S ; k ; j; GIP ; GP ; b) (H2, rho2)) ->
     (forall j, (H1', rho1) ⋞ ^ (S ; k ; j; GIP ; GP; b) (H2', rho2)).
   Proof.
     intros Hs1 Hs2 Hres j x Hin.
     eapply var_rel_heap_monotonic; try eassumption.
     intros j'. eapply Hres. eassumption.
   Qed.
   
   Lemma cc_approx_clos_heap_monotonic P GIP GP (k : nat) b
        (H1 H2 H1' H2' : heap block) :
    H1 ⊑ H1' -> H2 ⊑ H2' ->
    (forall j, P |- H1 ≼ ^ (k; j; GIP; GP; b) H2) ->
    (forall j, P |- H1' ≼ ^ (k; j; GIP; GP; b) H2').
  Proof.
  Admitted. 

  (** * Reachable locations image *)

  
  (*** Compatibility lemmas *)


  (** * Compat definitions for pre and post conditions *) 

  Section CompatDefs.
    Context (IG : GInv) (* Final global *)
            (IL1 IL2: Inv) (* Final local *)          
            (IIG : GIInv) (* Global initial *)
            (IIL1 IIL2 : IInv). (* Local initial *)

    Definition InvCostBase (e1 e2 : exp) :=
      forall (H1' H2' : heap block) (rho1' rho2' : env) (c : nat),                           
        IIL1 (H1', rho1', e1) (H2', rho2', e2) ->
        cost e1 <= c -> 
        IL1 (H1', rho1', e1) (c, size_heap H1') (c, size_heap H2').
    
    Definition InvCostTimeOut (e1 e2 : exp) :=
      forall (H1' H2' : heap block) (rho1' rho2' : env) (c : nat),                           
        IIL1 (H1', rho1', e1) (H2', rho2', e2) ->
        c < cost e1 -> 
        IL1 (H1', rho1', e1) (c, size_heap H1') (c, size_heap H2').
    
    Definition InvCostBase_w (e1 e2 : exp) :=
      forall (H1' H2' : heap block) (rho1' rho2' : env) (c : nat),                           
        IIL1 (H1', rho1', e1) (H2', rho2', e2) ->
        IL1 (H1', rho1', e1) (c, size_heap H1') (c, size_heap H2').

    Definition InvCtxCompat (C1 C2 : exp_ctx) (e1 e2 : exp)  :=
      forall (H1' H2' H1'' H2'' : heap block) (rho1' rho2' rho1'' rho2'' : env) c1 c2 c1' c2' m1 m2,

        IL2 (H1'', rho1'', e1) (c1, m1) ( c2, m2) ->
        cost (C1 |[ e1 ]|) <= c1' ->

        ctx_to_heap_env C1 H1' rho1' H1'' rho1'' c1' ->
        ctx_to_heap_env_CC C2 H2' rho2' H2'' rho2'' c2' ->
        
        IL1 (H1', rho1', C1 |[ e1 ]|) (c1 + c1', m1) (c2 + c2', m2).
    
    Definition IInvCtxCompat (C1 C2 : exp_ctx) (e1 e2 : exp)  :=
      forall (H1' H2' H1'' H2'' : heap block) (rho1' rho2' rho1'' rho2'' : env) c1' c2',                         
        IIL1 (H1', rho1', C1 |[ e1 ]|) (H2', rho2', C2 |[ e2 ]|) ->
        
        ctx_to_heap_env C1 H1' rho1' H1'' rho1'' c1' ->
        ctx_to_heap_env_CC C2 H2' rho2' H2'' rho2'' c2' ->

        IIL2 (H1'', rho1'', e1) (H2'', rho2'', e2).

  End CompatDefs.
  
  Section CompatLemmas.
    Context (IG : GInv) (* Final global *)
            (IL1 IL2: Inv) (* Final local *)          
            (IIG : GIInv) (* Global initial *)
            (IIL1 IIL2 : IInv). (* Local initial *)

    Lemma exp_rel_constr_compat (k j : nat)
          (b : Inj) (H1 H2 : heap block) (rho1 rho2 : env)
          (x1 x2 : var) (t : cTag) (ys1 ys2 : list var) (e1 e2 : exp)  : 
      InvCtxCompat IL1 IL2 (Econstr_c x1 t ys1 Hole_c) (Econstr_c x2 t ys2 Hole_c) e1 e2 ->
      IInvCtxCompat IIL1 IIL2 (Econstr_c x1 t ys1 Hole_c) (Econstr_c x2 t ys2 Hole_c) e1 e2 ->
      InvCostBase_w IL1 IIL1 (Econstr x1 t ys1 e1) (Econstr x2 t ys2 e2)  ->
      
      closed (reach' H1 (env_locs rho1 (occurs_free (Econstr x1 t ys1 e1)))) H1 ->
      closed (reach' H2 (env_locs rho2 (occurs_free (Econstr x2 t ys2 e2)))) H2 ->

      (forall j, Forall2 (var_rel k j IIG IG b H1 rho1 H2 rho2) ys1 ys2) ->
      
      (forall vs1 vs2 l1 l2 H1' H2',
          k >= cost (Econstr x1 t ys1 e1) ->
          (* allocate a new location for the constructed value *)
          locs (Constr t vs1) \subset env_locs rho1 (FromList ys1) ->
          locs (Constr t vs2) \subset env_locs rho2 (FromList ys2) ->
          
          alloc (Constr t vs1) H1 = (l1, H1') ->
          alloc (Constr t vs2) H2 = (l2, H2') ->
          (* values are related *)
          (forall j, Forall2 (fun l1 l2 => (Res (l1, H1)) ≺ ^ (k - cost (Econstr x1 t ys1 e1) ; j ; IIG ; IG ; b) (Res (l2, H2))) vs1 vs2) ->
          (forall j, (H1', M.set x1 (Loc l1) rho1, e1) ⪯ ^ (k - cost (Econstr x1 t ys1 e1) ; j ; IIL2 ; IIG ; IL2 ; IG)
                                                        (H2', M.set x2 (Loc l2) rho2, e2))) ->
      
      (H1, rho1, Econstr x1 t ys1 e1) ⪯ ^ (k ; j ; IIL1; IIG ; IL1 ; IG) (H2, rho2, Econstr x2 t ys2 e2).
    Proof with now eauto with Ensembles_DB.
      intros Hinv Hiinv Hbase Hwf1 Hwf2 Hall Hpre b1 b2 H1' H2' rho1' rho2' v1 c1 m1
             Heq1 Hinj1 Heq2 Hinj2 HII Hleq1 Hstep1 Hstuck1. 
      assert (Hall' := Hall).
      inv Hstep1.
      (* Timeout! *)
      - { exists OOT, c1. eexists. exists id. repeat split. 
          - econstructor. simpl. specialize (Hall 0). erewrite <- Forall2_length; [| eassumption ].
            simpl in Hcost. omega. reflexivity.
          (* - simpl. eapply injective_subdomain_Empty_set.  *)
          - eapply Hbase; try eassumption. }
      (* Termination *)
      - { assert (Hall_eq:
                    forall j : nat, Forall2 (var_rel k j IIG IG (b2 ∘ b ∘ b1) H1' rho1' H2' rho2') ys1 ys2).
          { intros j'.
            eapply Forall2_monotonic_strong; [| now eapply Hall ].
            intros x1' x2' Hin1 Hin2 Hvar.
            eapply var_rel_heap_env_equiv; try eassumption.
            normalize_occurs_free... normalize_occurs_free... }
          assert (Hall_eq' := Hall_eq 0). 
          eapply var_log_rel_getlist in Hall_eq'; [| now eauto ].
          destruct Hall_eq' as [vs2 [Hget' Hpre']].

          edestruct heap_env_equiv_env_getlist as [vs1' [Hget1' Hall1]];
            [| symmetry; now apply Heq1 | |]; try eassumption.
          normalize_occurs_free...
          edestruct heap_env_equiv_env_getlist as [vs2' [Hget2' Hall2]];
            [| symmetry; now apply Heq2 | |]; try eassumption.
          normalize_occurs_free...
          
          destruct (alloc (Constr t vs1') H1) as [l1 H1''] eqn:Hal1.
          destruct (alloc (Constr t vs2) H2') as [l2 H''] eqn:Hal2'.
          destruct (alloc (Constr t vs2') H2) as [l2' H2''] eqn:Hal2.
          
          assert (Hval_rel :
                    forall j, Forall2 (fun v1 v2 => Res (v1, H1) ≺ ^ (k; j; IIG; IG; b) Res (v2, H2)) vs1' vs2').
          { intros j'. assert (Hall'' := Hall j'). 
            eapply var_log_rel_getlist in Hall''; [| now eauto ].
            destruct Hall'' as [vs2'' [Hget'' Hvrel]]. repeat subst_exp. 
            eassumption. }
          
          
          edestruct Hpre with (b1 := extend b1 l l1)
                              (b2 := extend b2 l2' l2)
            as [v2 [c2 [m2 [b' [Hstep [HS Hval]]]]]];
            [ | | | eassumption | eassumption | | | | | | | |  eassumption | | ].
          - simpl in *. omega.
          - simpl. eapply FromList_env_locs. eassumption. reflexivity.
          - simpl. eapply FromList_env_locs. eassumption. reflexivity.
          - intros j'; eapply Forall2_monotonic; [| now eapply (Hval_rel j') ].
            intros ? ? H. eapply val_rel_i_monotonic; [| | | | now eapply H | ]; tci.
            omega.
          - eapply heap_env_equiv_alloc;
              [ | | | | | | | eassumption | eassumption | | ]. 
            + eassumption. 
            + eapply heap_env_equiv_preserves_closed; [| eapply Hwf1 ].
              eassumption.
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. simpl.
              rewrite env_locs_FromList; eauto. reflexivity.
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. simpl.
              rewrite env_locs_FromList; eauto. reflexivity.
            + eapply heap_env_equiv_antimon. eapply heap_env_equiv_rename_ext. 
              eassumption.
              reflexivity.

              eapply f_eq_subdomain_extend_not_In_S_r.
              intros Hr. eapply reachable_in_dom in Hr.
              eapply alloc_fresh in Halloc. destruct Hr as [s Hgetl]. congruence.

              eapply well_formed_respects_heap_env_equiv.
              eapply well_formed'_closed. eassumption. eassumption.
              
              eapply Included_trans; [| eapply env_locs_closed ]. now eapply reach'_extensive. 
              eapply heap_env_equiv_preserves_closed; [| eapply Hwf1 ].
              eassumption.
              reflexivity. 
              normalize_occurs_free...
            + rewrite extend_gss. reflexivity.
            + simpl. split. reflexivity.

              
              eapply Forall2_symm_strong; [| eassumption ]. 
              intros l3 l4 Hin1 Hin2 Hin. simpl in Hin. symmetry in Hin.
              eapply res_equiv_rename_ext. eassumption.
              reflexivity.

              assert (Hsub : val_loc l3 \subset env_locs rho1' (occurs_free (Econstr x1 t ys1 e1))).
              { normalize_occurs_free. rewrite env_locs_Union.
                eapply Included_Union_preserv_l.
                
                rewrite env_locs_FromList; try eassumption. 
                eapply In_Union_list. eapply in_map. eassumption. }

              eapply f_eq_subdomain_extend_not_In_S_r.
              
              
              intros Hr. eapply reachable_in_dom in Hr.
              eapply alloc_fresh in Halloc. destruct Hr as [s Hgetl]. congruence. 
              
              eapply well_formed_antimon. eapply reach'_set_monotonic. eassumption.
              eapply well_formed'_closed.
              eapply heap_env_equiv_preserves_closed; [| eapply Hwf1 ]. eassumption.

              eapply Included_trans; [| eapply env_locs_closed ]. 
              eapply Included_trans. eassumption.  eapply reach'_extensive.
              eapply heap_env_equiv_preserves_closed; [| eapply Hwf1 ]. eassumption.

              reflexivity. 
          - eapply injective_subdomain_antimon.
            eapply injective_subdomain_extend. eassumption.
            
            intros Hc. eapply image_monotonic in Hc; [| now eapply Setminus_Included ].  
            eapply heap_env_equiv_image_reach in Hc; try eassumption.
            eapply (image_id (reach' H1 (env_locs rho1 (occurs_free (Econstr x1 t ys1 e1)))))
              in Hc.
            eapply reachable_in_dom in Hc; try eassumption. destruct Hc as [v1' Hgetv1'].
            erewrite alloc_fresh in Hgetv1'; try eassumption. congruence.
            eapply well_formed'_closed. eassumption. 
            eapply Included_trans. eapply reach'_extensive.
            eapply env_locs_closed. eassumption. 
            
            eapply Included_trans. eapply reach'_set_monotonic. eapply env_locs_monotonic.
            eapply occurs_free_Econstr_Included.
            eapply reach'_alloc_set; [| eassumption ]. 
            eapply Included_trans; [| eapply reach'_extensive ].
            normalize_occurs_free. rewrite env_locs_Union.
            eapply Included_Union_preserv_l. 
            rewrite env_locs_FromList; eauto. reflexivity.
          - eapply heap_env_equiv_alloc; [| | | | | | | now apply Hal2 | now apply Hal2' | | ].
            + eassumption.
            + eapply heap_env_equiv_preserves_closed. eassumption.
              eassumption. 
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. simpl.
              rewrite env_locs_FromList; eauto. reflexivity.
            + eapply Included_trans; [ | now eapply reach'_extensive ].
              normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. simpl.
              rewrite env_locs_FromList; eauto. reflexivity.
            + eapply heap_env_equiv_antimon. eapply heap_env_equiv_rename_ext. 
              eassumption.

              eapply f_eq_subdomain_extend_not_In_S_r.
              intros Hr. eapply reachable_in_dom in Hr. 
              eapply alloc_fresh in Hal2. destruct Hr as [s Hgetl]. congruence.
              
              eapply well_formed'_closed. eassumption. 
              eapply Included_trans. eapply reach'_extensive.
              eapply env_locs_closed. eassumption. 
              
              reflexivity. reflexivity.
              normalize_occurs_free...

            + rewrite extend_gss. reflexivity.  
            + symmetry. eapply block_equiv_rename_ext.
              split; eauto. reflexivity.
              
              eapply f_eq_subdomain_extend_not_In_S_r.
              intros Hr. eapply reach'_set_monotonic in Hr.
              eapply env_locs_closed with (H := H2) in Hr.
              eapply alloc_fresh in Hal2. destruct Hr as [s Hgetl]. congruence.
              eassumption.
              
              normalize_occurs_free. rewrite env_locs_Union. 
              eapply Included_Union_preserv_l. 
              rewrite env_locs_FromList; eauto. reflexivity.
              
              reflexivity.
              
          - eapply injective_subdomain_antimon.
            eapply injective_subdomain_extend. eassumption.
            
            intros Hc. eapply image_monotonic in Hc; [| now eapply Setminus_Included ].  
            eapply heap_env_equiv_image_reach in Hc; try (symmetry; eassumption).
            eapply (image_id (reach' H2' (env_locs rho2' (occurs_free (Econstr x2 t ys2 e2)))))
              in Hc.
            eapply env_locs_closed with (H := H2') in Hc.
            
            destruct Hc as [v1' Hgetv1'].
            erewrite alloc_fresh in Hgetv1'; try eassumption. congruence.

            eapply heap_env_equiv_preserves_closed. eassumption. eassumption.
            
            eapply Included_trans. eapply reach'_set_monotonic. eapply env_locs_monotonic.
            eapply occurs_free_Econstr_Included.
            eapply reach'_alloc_set; [| eassumption ]. 
            eapply Included_trans; [| eapply reach'_extensive ].
            normalize_occurs_free. rewrite env_locs_Union.
            eapply Included_Union_preserv_l. 
            rewrite env_locs_FromList; eauto. reflexivity.
            
          - eapply Hiinv; try eassumption.
            econstructor; eauto.
            now econstructor; eauto.
            econstructor; eauto.
            now econstructor; eauto.
          - simpl. simpl in Hcost. omega.
          - intros i. edestruct (Hstuck1 (i + cost (Econstr x1 t ys1 e1))) as [r' [m' Hstep']].
            inv Hstep'.
            * omega.
            * rewrite NPeano.Nat.add_sub in Hbs0. repeat subst_exp.
              repeat eexists; eauto.  
          - repeat eexists; eauto.
            + eapply Eval_constr_per_cc with (c := c2 + cost (Econstr x2 t ys2 e2))
              ; [ | | | rewrite NPeano.Nat.add_sub ]; try eassumption.
              simpl. omega. 
            + replace c1 with (c1 - cost (Econstr x1 t ys1 e1) + cost (Econstr x1 t ys1 e1))
                by ( simpl in *; omega).
              unfold InvCtxCompat in Hinv. simpl in Hinv. 
              eapply Hinv; try eassumption. simpl in *. omega. 
              replace (cost (Econstr x1 t ys1 e1))
                with (0 + cost_ctx (Econstr_c x1 t ys1 Hole_c)) by (simpl; omega).
              econstructor; eauto. now econstructor; eauto.
              replace (cost (Econstr x2 t ys2 e2)) with (0 + cost_ctx (Econstr_c x2 t ys2  Hole_c)) by (simpl; omega).
              econstructor; eauto. now econstructor; eauto.
            + eapply val_rel_i_monotonic; tci.
              simpl in *; omega. }
    Qed.
    
    (** Projection compatibility *)
    Lemma exp_rel_proj_compat
          (k : nat) (H1 H2 : heap block) (rho1 rho2 : env) (b : Inj)
          (x1 x2 : var) (t : cTag) (n : N) (y1 y2 : var) (e1 e2 : exp) :

      InvCtxCompat IL1 IL2 (Eproj_c x1 t n y1 Hole_c) (Eproj_c x2 t n y2 Hole_c) e1 e2 ->
      IInvCtxCompat IIL1 IIL2 (Eproj_c x1 t n y1 Hole_c) (Eproj_c x2 t n y2 Hole_c) e1 e2 ->
      InvCostBase_w IL1 IIL1 (Eproj x1 t n y1 e1) (Eproj x2 t n y2 e2) ->
      
      (forall j, var_rel k j IIG IG b H1 rho1 H2 rho2 y1 y2) ->

      
      (forall v1 v2,
          k >= cost (Eproj x1 t n y1 e1) ->
          (* allocate a new location for the constructed value *)
          val_loc v1 \subset reach' H1 (env_locs rho1 [set y1]) ->
          val_loc v2 \subset reach' H2 (env_locs rho2 [set y2]) ->

          (forall j, (Res (v1, H1)) ≺ ^ (k - cost (Eproj x1 t n y1 e1) ; j ; IIG ; IG; b) (Res (v2, H2))) ->
          (forall j, (H1, M.set x1 v1 rho1, e1) ⪯ ^ (k - cost (Eproj x1 t n y1 e1) ; j ; IIL2 ; IIG ; IL2 ; IG) (H2, M.set x2 v2 rho2, e2))) ->
      
      (forall j, (H1, rho1, Eproj x1 t n y1 e1) ⪯ ^ (k ; j ; IIL1 ; IIG ; IL1 ; IG) (H2, rho2, Eproj x2 t n y2 e2)).
    Proof with (now eauto with Ensembles_DB).
      intros Hinv Hiinv Hbase Hall Hpre j b1 b2 H1' H2' rho1' rho2' v1 c1 m1
             Heq1' Hinj1 Heq2' Hinj2 HII Hleq1 Hstep1 Hstuck. inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost. exists OOT, c1. eexists. exists id. repeat split. 
          - econstructor. simpl; omega. reflexivity.
          - eapply Hbase; eauto. }
      (* Termination *)
      - { pose (cost1 := cost_cc (Eproj x1 t n y1 e1)).
          pose (cost2 := cost_cc (Eproj x2 t n y2 e2)).
          assert (Hall' := Hall).
          
          eapply (var_rel_heap_env_equiv
                    _ _
                    (occurs_free (Eproj x1 t n y1 e1))
                    (occurs_free (Eproj x2 t n y2 e2)) _ (S j)) in Hall;
            [| eassumption | eassumption | eassumption | eassumption
             | normalize_occurs_free; now eauto with Ensembles_DB
             | normalize_occurs_free; now eauto with Ensembles_DB ].
          edestruct Hall as [l2 [Hget' Hcc']]; eauto.
          destruct l2 as [l' | l' f]; [| contradiction ].
          simpl in Hcc'. rewrite Hgetl in Hcc'.
          destruct (get l' H2') as [[ t2 vs' | | ] | ] eqn:Hgetl';
            (try destruct Hcc' as [Hteq Hcc']); try contradiction.
          
          edestruct heap_env_equiv_env_get as [l1 [Hgetl1 Hres1]]; [ now apply Hgety | | | ].
          symmetry. eassumption. now eauto.
          edestruct heap_env_equiv_env_get as [l2 [Hgetl2 Hres2]]; [ now apply Hget' | | | ].
          symmetry. eassumption. now eauto.

          edestruct (Hall' (S j))  as [l2' [Hgetl2'' Hcc]]; eauto. repeat subst_exp. 
          
          assert (Hres1' := Hres1). assert (Hres2' := Hres2). rewrite res_equiv_eq in Hres1, Hres2.
          destruct l1 as [l1 |]; try contradiction.
          destruct l2' as [l2 |]; try contradiction.
          
          simpl in Hres1, Hres2. rewrite Hgetl in Hres1. rewrite Hgetl' in Hres2.
          destruct (get l1 H1) as [bl1 |] eqn:Hgetl1'; (try destruct Hres1 as [Hb1 Hres1]); try contradiction.
          destruct (get l2 H2) as [bl2 |] eqn:Hgetl2'; (try destruct Hres2 as [Hb2 Hres2]); try contradiction.
          destruct bl1 as [t1 vs1 | | ]; try contradiction.
          destruct bl2 as [t2' vs2 | | ]; try contradiction.
          destruct Hres1 as [Hteq Hallvs1]; subst. destruct Hres2 as [Hteq' Hallvs2]; subst.
          
          simpl in Hcc. rewrite Hgetl1' in Hcc. rewrite Hgetl2' in Hcc.
          destruct Hcc as [Hbeq [Henv Hcc]]. subst.
          
          edestruct (Forall2_nthN _ _ _ _ _ Hallvs1 Hnth) as [v1' [Hnth' Hv1]].
          edestruct (Forall2_nthN
                       (fun l1 l2 => val_rel k j IIG IG b (Res (l1, H1)) (Res (l2, H2))) vs1)
            as [l3' [Hnth'' Hval']]; eauto.

          eapply Forall2_monotonic; [| eapply Hcc ]. intros. 
          unfold val_rel. now rewrite <- val_log_rel_eq; tci.
          
          edestruct (Forall2_nthN (fun v1 v2 : value => (v1, H2) ≈_( b2, id) (v2, H2'))) as [v2' [Hnth2' Hv2]]. 
          eapply Forall2_symm_strong; [| now eapply Hallvs2 ].
          intros.
          now symmetry; eauto. eassumption.
          
          edestruct Hpre with (c1 := c1 - cost1) (v1 := v1') as [v2 [c2 [m2 [b' [Hstep [HS Hres]]]]]];
            [ | | | | | | | | | | eassumption | | ].  
          - simpl in *. omega.
          - intros x Hin. eapply Included_post_reach'.
            rewrite env_locs_Singleton; [| eassumption ]. simpl. rewrite post_Singleton; [| eassumption ].
            simpl. eapply In_Union_list. eapply in_map. eapply nthN_In. eassumption.
            eassumption.
          - intros x Hin. eapply Included_post_reach'.
            rewrite env_locs_Singleton; [| eassumption ]. simpl. rewrite post_Singleton; [| eassumption ].
            simpl. eapply In_Union_list. eapply in_map. eapply nthN_In. eassumption.
            eassumption.
          - intros j'.
            
            edestruct (Hall' (j' + 1))  as [l2'' [Hgetl2'' Hcc'']]; eauto. repeat subst_exp.
            simpl in Hcc''. rewrite Hgetl1' in Hcc''. rewrite Hgetl2' in Hcc''.
            destruct Hcc'' as [_ [Henv' Hcc'']].
            
            edestruct (Forall2_nthN
                         (fun l1 l2 => val_rel k j' IIG IG b (Res (l1, H1)) (Res (l2, H2))) vs1)
              as [v2'' [Hnth2 Hv2']]; eauto.
            eapply Forall2_monotonic; [| eapply Hcc'' ]. intros. 
            unfold val_rel. rewrite <- val_log_rel_eq; tci. eapply H. omega. 
            
            repeat subst_exp.
            eapply val_rel_i_monotonic; tci. omega.
            
          - eapply heap_env_equiv_set.
            eapply heap_env_equiv_antimon. eassumption.
            repeat subst_exp. normalize_occurs_free... symmetry. eassumption.
          - eapply injective_subdomain_antimon. eassumption.

            rewrite (reach'_idempotent H1' (env_locs rho1' (occurs_free (Eproj x1 t n y1 e1)))).
            eapply reach'_set_monotonic.
            eapply Included_trans.
            eapply env_locs_set_Inlcuded'.
            eapply Union_Included.

            eapply Included_trans; [| eapply Included_post_reach' ].
            normalize_occurs_free. rewrite env_locs_Union, post_Union.
            eapply Included_Union_preserv_l.
            rewrite env_locs_Singleton; eauto. simpl. erewrite post_Singleton; eauto.
            simpl. eapply In_Union_list. eapply in_map. eapply nthN_In. eassumption.

            eapply Included_trans; [| eapply reach'_extensive ].
            eapply env_locs_monotonic. normalize_occurs_free...
          - eapply heap_env_equiv_set.
            eapply heap_env_equiv_antimon. eassumption.
            normalize_occurs_free...
            repeat subst_exp. eassumption.
          - eapply injective_subdomain_antimon. eassumption.

            rewrite (reach'_idempotent H2 (env_locs rho2 (occurs_free (Eproj x2 t n y2 e2)))).
            eapply reach'_set_monotonic.
            eapply Included_trans.
            eapply env_locs_set_Inlcuded'.
            eapply Union_Included.
            
            eapply Included_trans; [| eapply Included_post_reach' ].
            normalize_occurs_free. rewrite env_locs_Union, post_Union. eapply Included_Union_preserv_l.
            rewrite env_locs_Singleton; eauto. simpl. erewrite post_Singleton; eauto.
            simpl. eapply In_Union_list. eapply in_map. eapply nthN_In. eassumption.

            eapply Included_trans; [| eapply reach'_extensive ].
            eapply env_locs_monotonic. normalize_occurs_free...
          - eapply Hiinv; try eassumption.
            econstructor; eauto.
            now econstructor; eauto.
            econstructor; eauto.
            now econstructor; eauto.
          - unfold cost1. simpl. omega. 
          - intros i. edestruct (Hstuck (i + cost1)) as [r' [m' Hstep']].
            inv Hstep'.
            * unfold cost1 in Hcost0. simpl in Hcost0. omega.
            * simpl in Hbs0. rewrite NPeano.Nat.add_sub in Hbs0.
              repeat subst_exp.
              do 2 eexists. eassumption.
          - repeat eexists; eauto. eapply Eval_proj_per_cc with (c := c2 + cost2); try eassumption.
            unfold cost2. simpl; omega. simpl. rewrite NPeano.Nat.add_sub.
            eassumption.
            replace c1 with (c1 - cost1 + cost1) by (unfold cost1; simpl in *; omega).
            eapply Hinv; try eassumption. simpl in *. omega. 
            replace cost1 with (0 + cost_ctx (Eproj_c x1 t n y1 Hole_c)) by (unfold cost1; simpl; omega).
            econstructor; eauto. now econstructor; eauto.
            replace cost2 with (0 + cost_ctx (Eproj_c x2 t n y2 Hole_c)) by (unfold cost2; simpl; omega).
            econstructor; eauto. now econstructor; eauto.
            eapply val_rel_i_monotonic; tci. simpl in *. omega. }
    Qed.
    
    (** Halt compatibility *)
    Lemma exp_rel_halt_compat (k j : nat) (H1 H2 : heap block) (rho1 rho2 : env) (b : Inj)
          (x1 x2 : var) :
      InvCostTimeOut IL1 IIL1 (Ehalt x1) (Ehalt x2) ->
      InvCostBase_w IL1 IIL1 (Ehalt x1) (Ehalt x2) ->
      
      var_rel k j IIG IG b H1 rho1 H2 rho2 x1 x2 ->

      (H1, rho1, Ehalt x1) ⪯ ^ (k ; j ; IIL1 ; IIG ; IL1; IG) (H2, rho2, Ehalt x2).
    Proof.
      intros Hoot Hbase Hvar b1 b2 H1' H2' rho1' rho2' v1 c1 m1 Heq1 Hinj1
             Heq2 Hinj2 Hleq1 HII Hstep1 Hstuck1.
      assert (Hvar' := Hvar).
      inv Hstep1.
      - (* Timeout! *)
        { simpl in Hcost. exists OOT, c1. eexists. exists id. repeat split. 
          - econstructor; eauto.
          - eapply Hoot; try eassumption. }
      - pose (cost1 := cost_cc (Ehalt x1)).
        pose (cost2 := cost_cc (Ehalt x2)).
        eapply (var_rel_heap_env_equiv
                  _ _
                  (occurs_free (Ehalt x1))
                  (occurs_free (Ehalt x2))) in Hvar;
          [| eassumption | eassumption | eassumption | eassumption | now constructor | now constructor ]. 
        edestruct Hvar as [l' [Hgety' Hcc]]; eauto.
        eexists. exists c1. eexists. exists (b2 ∘ b ∘ b1). repeat eexists.
        * eapply Eval_halt_per_cc. simpl. simpl in Hcost. omega. eassumption.
          reflexivity. 
        * eapply Hbase; try eassumption.
        * eapply val_rel_i_monotonic; tci. omega. 
    Qed.

  End CompatLemmas.
  
  End LogRelPostCC. 

  