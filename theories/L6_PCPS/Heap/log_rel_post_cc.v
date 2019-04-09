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
    Proper (f_eq ==> eq ==> eq ==> iff) (val_rel' k j IP P).
  Proof.
    intros ? ? H ? ? ? ? ? ?. subst.
    split; intros H1.
    rewrite <- val_rel_eq. eapply val_rel_rename_ext.
    rewrite val_rel_eq. eassumption.
    rewrite H. reflexivity.
    rewrite <- val_rel_eq. eapply val_rel_rename_ext.
    rewrite val_rel_eq. eassumption.
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
 

              
  (** * Heap monotonicity/allocation  *)
  
  (** * Reachable locations image *)

  (** * Compatibility lemmas *)

End LogRelPostCC. 

  