(* Generic definitions for step-indexed logical relations for L6 language transformations
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2019
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From CertiCoq.L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util set_util
                 List_util Heap.heap Heap.heap_defs Heap.space_sem Heap.GC tactics map_util.
From compcert Require Import lib.Coqlib.


Module Log_rel (H : Heap).

  Module Sem := SpaceSem H.

  Import H Sem.GC Sem.GC.Equiv Sem.GC.Equiv.Defs Sem.
  
  (** ** Resource conditions  *)

  (* L6 configurations *)
  Definition Conf := (heap block * env * exp)%type. 
  

  (** * Preconditions *)
  
  (** Local precondition. Enforced as initial condition for the expressions being related *)
  Definition IInv := relation Conf.
  
  (** Global precondition. Enforced as initial condition for future executions of the result *)
  Definition GIInv :=
    forall (B : Ensemble var) {H : ToMSet B}, (* The set of function names is scope that appear free in the body *) 
      nat -> (* Size of the reachable heap upon function entry *)
      nat -> (* Size of the closure environment *)
      relation (heap block * env * exp).
  
  (** * Postconditions *)
  
  (** Local postconditions. Holds for the result of the execution of the expressions being related. *)
  Definition Inv := Conf -> relation (nat * nat).
  
  (** Global posconditions. Holds for the result of future execution of the result *)
  Definition GInv :=
    nat -> (* Size of the reachable heap upon function entry *)
    nat -> (* Size of the closure environment *)
    Conf -> relation (nat * nat).
  
  (** Loc Injection *)
  Definition Inj := loc -> loc.
  
  (** Tag for closure records *)
  Variable (clo_tag : cTag). 
  
  
  Section LogRelDefs.
    
    Variable (val_log_rel : nat -> nat -> GIInv -> GInv -> Inj -> ans -> ans -> Prop). 

    Variable (eval_src : heap block -> env -> exp -> ans -> nat -> nat -> Prop).
    Variable (eval_trg : heap block -> env -> exp -> ans -> nat -> nat -> Prop).
    
    
    Definition exp_log_rel
               (* step indexes *)
               (k : nat) (j : nat)
               (* Invariants *)
               (IIL : IInv) (IIG : GIInv) (IL : Inv) (IG : GInv)
               (* related expressions *)
               (p1 p2 : Conf) : Prop :=
      let '(H1, rho1, e1) := p1 in
      let '(H2, rho2, e2) := p2 in
      forall (b1 b2 : Inj) (H1' H2' : heap block) (rho1' rho2' : env) (r1 : ans) (c1 m1 : nat),
        (occurs_free e1) |- (H1, rho1) ⩪_(id, b1) (H1', rho1') ->
        injective_subdomain (reach' H1' (env_locs rho1' (occurs_free e1))) b1 ->
        (occurs_free e2) |- (H2, rho2) ⩪_(b2, id) (H2', rho2') ->
        injective_subdomain (reach' H2 (env_locs rho2 (occurs_free e2))) b2 ->
        IIL (H1', rho1', e1) (H2', rho2', e2) ->
        c1 <= k ->
        eval_src H1' rho1' e1 r1 c1 m1 ->
        not_stuck H1' rho1' e1 ->
        exists (r2 : ans) (c2 m2 : nat) (b : Inj),
          eval_trg H2' rho2' e2 r2 c2 m2 /\
          (* extra invariants for costs *)
          IL (H1', rho1', e1) (c1, m1) (c2, m2) /\
          val_log_rel (k - c1) j IIG IG b r1 r2.

    (** Environment relation for a single point (i.e. variable) *)
    Definition var_log_rel (k j : nat) IP P b (H1 : heap block) (rho1 : env)
               (H2 : heap block) (rho2 : env) (x y : var) : Prop :=
      forall l1, 
        M.get x rho1 = Some l1 -> 
        exists l2, M.get y rho2 = Some l2 /\
              val_log_rel k j IP P b (Res (l1, H1)) (Res (l2, H2)).
    
    Definition env_log_rel_P (S : Ensemble var) k j IP P b (c1 c2 : heap block * env) :=
      let (H1, rho1) := c1 in
      let (H2, rho2) := c2 in
      forall (x : var), S x -> var_log_rel k j IP P b H1 rho1 H2 rho2 x x.
    
    Definition heap_log_rel (S : Ensemble loc) k j IP P b (H1 H2 : heap block) :=
      forall (x : loc), S x -> val_log_rel k j IP P b (Res (Loc x, H1)) (Res (Loc (b x), H2)).
    

  End LogRelDefs.
  

  Section ValRelDef.

    (* Semantics of source and target *)
    Variable (eval_src : heap block -> env -> exp -> ans -> nat -> nat -> Prop).
    Variable (eval_trg : heap block -> env -> exp -> ans -> nat -> nat -> Prop).

    (* Passed to the caller *)
    Definition fun_body_rel : Type :=
      IInv -> Inv -> Inj -> list value -> heap block -> list value -> heap block -> Conf -> Conf -> Prop.  
    
    Definition val_rel : Type :=
      res -> res -> Prop. 
    
    (* Relation of closure pairs -- Given by the caller *)
    Variable (clos_rel : GIInv -> GInv -> Inj -> block -> heap block -> block -> heap block -> (* Block being related *)
                         fun_body_rel ->
                         val_rel -> 
                         Prop).

    Require Import Coq.Classes.Morphisms Coq.Classes.RelationClasses.
    
    Definition fun_body_args : Tlist :=      
      Tcons IInv (Tcons Inv (Tcons Inj (Tcons (list value) (Tcons (heap block) (Tcons (list value) (Tcons (heap block) (Tcons Conf (Tcons Conf Tnil)))))))).
    
    
    Definition val_rel_args : Tlist :=
      Tcons res (Tcons res Tnil). 
    
    (* Relation on function values -- Given by the caller *)
    Variable (fun_rel : GIInv -> GInv -> Inj -> value -> heap block -> value -> heap block ->
                        fun_body_rel ->
                        Prop).


    Variable Proper_clos_rel : forall P Q b b1 H1 b2 H2,
        Proper ((pointwise_lifting iff fun_body_args) ==> (pointwise_lifting iff val_rel_args) ==> iff) (clos_rel P Q b b1 H1 b2 H2).

    Variable Proper_fun_rel : forall  P Q b v1 H1 v2 H2, Proper ((pointwise_lifting iff fun_body_args) ==> iff) (fun_rel  P Q b v1 H1 v2 H2).
    
    (** * Value relation *)
   
    Fixpoint val_log_rel (k : nat) {struct k} :=
      let fix val_log_rel_aux 
              (j : nat) (IP : GIInv) (P : GInv) (b : Inj) (r1 r2 : ans) {struct j} : Prop :=
          (* Function relation *)
          let fun_body_rel PL QL b (* local pre and post, picked by the caller *)
                           (vs1 : list value) (H1 : heap block) 
                           (vs2 : list value) (H2 : heap block) 
                           (c1 c2 : Conf) :=
              let '(H1', rho1, e1) := c1 in
              let '(H2', rho2, e2) := c2 in              
              (forall i,
                  (i < k)%nat ->
                  match k with
                  | 0 => True
                  | S k =>
                    let R j v1 v2 := val_log_rel (k - (k - i)) j IP P b (Res (v1, H1)) (Res (v2, H2)) in
                    (forall j, Forall2 (R j) vs1 vs2) ->
                    (PL (H1', rho1, e1) (H2, rho2, e2)) /\
                    (forall j, exp_log_rel val_log_rel eval_src eval_trg
                                      (k - (k - i))
                                      j
                                      PL IP
                                      QL P
                                      (H1', rho1, e1) (H2', rho2, e2))
                  end)
          in
          let R_val p1 p2 :=
              (forall i,
                  (i < j)%nat ->
                  match j with
                  | 0 => True
                  | S j =>
                    val_log_rel_aux (j - (j - i)) IP P b (Res p1) (Res p2)
                  end)
          in
          match r1, r2 with
          | OOT, OOT => True (* Both programs timeout *)
          | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
            match v1, v2 with
            | Loc l1, Loc l2 =>
              b l1 = l2 /\
              match get l1 H1, get l2 H2 with
              | Some (Constr c1 vs1), Some (Constr c2 vs2) =>
                c1 = c2 /\ 
                let R l1 l2 := R_val (l1, H1) (l2, H2) in
                Forall2 R vs1 vs2
              | Some (Clos v1 v2), Some bl2 =>
                clos_rel IP P b (Clos v1 v2) H1 bl2 H2
                         fun_body_rel
                         R_val                          
              | _, _ => False
              end
            | FunPtr B1 f1, FunPtr B2 f2 =>
              fun_rel IP P b v1 H1 v2 H2
                      fun_body_rel
            | _, _ => False
            end
          | _, _ => False
          end
    in val_log_rel_aux.


    (* Unfolding one step of the recursion *)
    Definition val_log_rel' (k : nat)  (j : nat) (IP : GIInv) (P : GInv) (b : Inj) (r1 r2 : ans) : Prop :=
      (* Function relation *)
      let fun_body_rel PL QL b (* local pre and post, picked by the caller *)
                       (vs1 : list value) (H1 : heap block) 
                       (vs2 : list value) (H2 : heap block) 
                       (c1 c2 : Conf) :=
          let '(H1', rho1, e1) := c1 in
          let '(H2', rho2, e2) := c2 in              
          forall i, (i < k)%nat ->
               let R j v1 v2 := val_log_rel i j IP P b (Res (v1, H1)) (Res (v2, H2)) in
               (forall j, Forall2 (R j) vs1 vs2) ->
               (PL (H1', rho1, e1) (H2, rho2, e2)) /\
               (forall j, exp_log_rel val_log_rel eval_src eval_trg
                                 i
                                 j
                                 PL IP
                                 QL P
                                 (H1', rho1, e1) (H2', rho2, e2))
      in
      let R_val p1 p2 :=
          forall i, (i < j)%nat -> val_log_rel k i IP P b (Res p1) (Res p2)                                               
      in
      match r1, r2 with
      | OOT, OOT => True (* Both programs timeout *)
      | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
        match v1, v2 with
        | Loc l1, Loc l2 =>
          b l1 = l2 /\
          match get l1 H1, get l2 H2 with
          | Some (Constr c1 vs1), Some (Constr c2 vs2) =>
            c1 = c2 /\ 
            let R l1 l2 := R_val (l1, H1) (l2, H2) in
            Forall2 R vs1 vs2
          | Some (Clos v1 v2), Some bl2 =>
            clos_rel IP P b (Clos v1 v2) H1 bl2 H2
                     fun_body_rel
                     R_val                          
          | _, _ => False
          end
        | FunPtr B1 f1, FunPtr B2 f2 =>
          fun_rel IP P b v1 H1 v2 H2
                  fun_body_rel
        | _, _ => False
        end
      | _, _ => False
      end.


    Lemma val_log_rel_eq (k j : nat) IP P b (v1 v2 : ans) :
      val_log_rel k j IP P b v1 v2 <-> val_log_rel' k j IP P b v1 v2.
    Proof.
      destruct k; destruct j; 
      destruct v1 as [[[l1 | lf1 f1] H1] |]; destruct v2 as [[[l2 | lf2 f2] H2] |];
        try (now split; intros; contradiction);
        try (now simpl; eauto).
      - split.
        + simpl. intros [Hyp1 Hyp2]. split; eauto. 
          destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
          destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
          * destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
            destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
            eapply Forall2_monotonic; [| eassumption ]. intros. omega.
          * eapply Proper_clos_rel; [| | eassumption ].
            { simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto. exfalso. omega. }
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto. exfalso. omega. }
        + simpl. intros [Hyp1 Hyp2]. split; eauto. 
          destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
          destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
          * destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
            destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
            eapply Forall2_monotonic; [| eassumption ]. intros. omega.
          * eapply Proper_clos_rel; [| | eassumption ].
            { simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto. exfalso. omega. }
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto. exfalso. omega. }
      - simpl. eapply Proper_fun_rel.
        simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
        split; intros; eauto. exfalso. omega.
      - simpl. split. 
        + intros [Hyp1 Hyp2]. split; eauto. 
          destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
          destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
          * destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
            destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
            eapply Forall2_monotonic; [| eassumption ].
            simpl in *. intros v1 v2 Hyp i Hlt.
            replace i with (j - (j - i)) by omega. eapply Hyp. omega.
          * eapply Proper_clos_rel; [| | eassumption ].
            { simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto. exfalso. omega. }
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto.
              replace (j - (j - i)) with i by omega. eapply H. omega.
              replace i with (j - (j - i)) by omega. eapply H. omega. }
        + simpl. intros [Hyp1 Hyp2]. split; eauto. 
          destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
          destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
          * destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
            destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
            eapply Forall2_monotonic; [| eassumption ]. intros v1 v2 Hyp i Hlt.
            replace (j - (j - i)) with i by omega. eapply Hyp. omega.
          * eapply Proper_clos_rel; [| | eassumption ].
            { simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto. exfalso. omega. }
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto.
              replace i with (j - (j - i)) by omega. eapply H. omega.
              replace (j - (j - i)) with i by omega. eapply H. omega. }
      - simpl. eapply Proper_fun_rel.
        simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
        split; intros; eauto. exfalso. omega.
      - simpl. split. 
        + intros [Hyp1 Hyp2]. split; eauto. 
          destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
          destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
          * destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
            destruct Hyp2 as [Hyp2 Hyp3]. split; eauto. 
            eapply Forall2_monotonic; [| eassumption ]. intros; omega.
          * eapply Proper_clos_rel; [| | eassumption ].
            { simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto.
              replace (k - (k - i)) with i by omega. eapply H. omega.
              replace i with (k - (k - i)) by omega. eassumption.
              replace i with (k - (k - i)) by omega. eapply H. omega.
              replace (k - (k - i)) with i by omega. eassumption. }
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto. omega. }

        + intros [Hyp1 Hyp2]. split; eauto. 
          destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
          destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
          * destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
            destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
            eapply Forall2_monotonic; [| eassumption ].
            intros; eauto.
          *  eapply Proper_clos_rel; [| | eassumption ].
            { simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto.
              replace i with  (k - (k - i)) by omega. eapply H. omega.
              replace (k - (k - i)) with i by omega. eassumption.
              replace (k - (k - i)) with i by omega. eapply H. omega.
              replace i with  (k - (k - i)) by omega. eassumption. }
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto. omega. }
      - simpl. eapply Proper_fun_rel.
        simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
        split; intros; eauto.
        replace i with  (k - (k - i)) by omega. eapply H. omega.
        replace (k - (k - i)) with i by omega. eassumption.
        replace (k - (k - i)) with i by omega. eapply H. omega.
        replace i with  (k - (k - i)) by omega. eassumption.
      - simpl. split. 
        + intros [Hyp1 Hyp2]. split; eauto. 
          destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
          destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
          * destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
            destruct Hyp2 as [Hyp2 Hyp3]. split; eauto. 
            eapply Forall2_monotonic; [| eassumption ].
            intros v1 v2 Hyp i Hlt.
            replace i with (j - (j - i)) by omega. eapply Hyp. omega.
          * eapply Proper_clos_rel; [| | eassumption ].
            { simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto.
              replace (k - (k - i)) with i by omega. eapply H. omega.
              replace i with  (k - (k - i)) by omega. eassumption.
              replace i with  (k - (k - i)) by omega. eapply H. omega.
              replace (k - (k - i)) with i by omega. eassumption. } 
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto.
              replace (j - (j - i)) with i by omega. eapply H. omega.
              replace i with (j - (j - i)) by omega. eapply H. omega. }
        + intros [Hyp1 Hyp2]. split; eauto. 
          destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
          destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
          * destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
            destruct Hyp2 as [Hyp2 Hyp3]. split; eauto.
            eapply Forall2_monotonic; [| eassumption ]. intros v1 v2 Hyp i Hlt.
            replace (j - (j - i)) with i by omega. eapply Hyp. omega.
          * eapply Proper_clos_rel; [| | eassumption ].
            { simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto.
              replace i with  (k - (k - i)) by omega. eapply H. omega.
              replace (k - (k - i)) with i by omega. eassumption.
              replace (k - (k - i)) with i by omega. eapply H. omega.
              replace i with  (k - (k - i)) by omega. eassumption. }
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto. 
              replace i with (j - (j - i)) by omega. eapply H. omega.
              replace (j - (j - i)) with i by omega. eapply H. omega. }
      - simpl. eapply Proper_fun_rel.
        simpl. intros P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
        split; intros; eauto.
        replace i with  (k - (k - i)) by omega. eapply H. omega.
        replace (k - (k - i)) with i by omega. eassumption.
        replace (k - (k - i)) with i by omega. eapply H. omega.
        replace i with  (k - (k - i)) by omega. eassumption.
    Qed. 

    Definition exp_log_rel' := exp_log_rel val_log_rel' eval_src eval_trg. 
    Definition env_log_rel_P' := env_log_rel_P val_log_rel'.
    Definition heap_log_rel' := heap_log_rel val_log_rel'.
    
    (** * Generic Properties of the logical relation *)

    Context (LP : IInv)
            (GP : GIInv)
            (LQ : Inv)
            (GQ : GInv).
    
    Variable Proper_clos_rel_cov : forall P Q b b1 H1 b2 H2,
        Proper ((pointwise_lifting impl fun_body_args) ==> (pointwise_lifting impl val_rel_args) ==> impl)
               (clos_rel P Q b b1 H1 b2 H2).
    
    Variable Proper_fun_rel_cov : forall  P Q b v1 H1 v2 H2,
        Proper ((pointwise_lifting impl fun_body_args) ==> impl)
               (fun_rel P Q b v1 H1 v2 H2).

    (** ** Monotonicity *)
    
    (** ** Step-index *)
    Lemma val_rel_i_monotonic i i' j r1 r2 b :
      val_log_rel' i j GP GQ b r1 r2 ->
      i' <= i ->
      val_log_rel' i' j GP GQ b r1 r2.      
    Proof. 
      revert j i r1 r2. induction i' as [m IHk] using lt_wf_rec1.
      intros j. induction j as [j IHj] using lt_wf_rec1.
      intros k r1 r2.
      destruct r1 as [[[l1 | lf1 f1] H1] |]; destruct r2 as [[[l2 | lf2 f2] H2] |]; simpl;
        try (now intros; contradiction); try (now simpl; eauto).
    - destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
      intros [Heq Hcc] Hleq. split; [ eassumption |]. 
      destruct b1 as [c1 vs1 | v1 v2 | ].
      + destruct b2 as [c2 vs2 | v1' v2' | ]; eauto. 
        destruct Hcc as [He'q Hcc]. split; [ eassumption |].
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap. 
        setoid_rewrite val_log_rel_eq.  intros i Hlt. eapply IHj; try eassumption.
        setoid_rewrite <- val_log_rel_eq. eauto.
      + eapply Proper_clos_rel_cov; [| | eassumption ].
        * simpl. intros P Q b' vs1' H1' vs2' H2' [[H1'' rho1'] e1'] [[H2'' rho2'] e2'] Hyp.
          intros i Hlt Hall. eapply Hyp. omega.
          intros j'. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hyp1. eapply Hyp1.
        * simpl. intros [v3 H3] [v4 H4] Hyp1 i Hlt.
          setoid_rewrite val_log_rel_eq. eapply IHj. eauto. 
          setoid_rewrite <- val_log_rel_eq. now eauto. omega.
      + eassumption.
    - intros Hyp Hleq. eapply Proper_fun_rel_cov; [| eassumption ]. 
      simpl. intros P Q b' vs1' H1' vs2' H2' [[H1'' rho1'] e1'] [[H2'' rho2'] e2'] Hyp1.
      intros i Hlt Hall. eapply Hyp1. omega.
      intros j'. eapply Forall2_monotonic; [| now eauto ].
      intros x1 x2 Hyp2. eapply Hyp2.
    Qed.
    
    Lemma exp_rel_i_monotonic i i' j c1 c2 :
      exp_log_rel' i j LP GP LQ GQ c1 c2 ->
      i' <= i ->
      exp_log_rel' i' j LP GP LQ GQ c1 c2.      
    Proof.
      destruct c1 as [[H1 rho1] e1]. 
      destruct c2 as [[H2 rho2] e2]. 
      intros He1 Hlt b1 b2 H1' H2' rho1' rho2' r1 c1 m1 Heq1 Hinj1 Heq2 Hinj2 Hlp Hlt' Heval Hns.
      edestruct He1 as [r2 [c2 [m2 [b2' [Heval2 [Hlq Hcc]]]]]]; (try now eapply Heval); try eassumption. 
      omega.
      repeat eexists; try eassumption. apply val_rel_i_monotonic with (i := i - c1).
      eassumption. omega. 
    Qed.       

    (* Lookup-index *)
    Lemma val_rel_j_monotonic i j j' r1 r2 b :
      val_log_rel' i j GP GQ b r1 r2 ->
      j' <= j ->
      val_log_rel' i j' GP GQ b r1 r2.      
    Proof. 
      revert i j r1 r2. induction j' as [m IHk] using lt_wf_rec1.
      intros i. induction i as [i IHi] using lt_wf_rec1.
      intros k r1 r2.
      destruct r1 as [[[l1 | lf1 f1] H1] |]; destruct r2 as [[[l2 | lf2 f2] H2] |]; simpl;
        try (now intros; contradiction); try (now simpl; eauto).
      - destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
        intros [Heq Hcc] Hleq. split; [ eassumption |]. 
        destruct b1 as [c1 vs1 | v1 v2 | ].
        + destruct b2 as [c2 vs2 | v1' v2' | ]; eauto. 
          destruct Hcc as [He'q Hcc]. split; [ eassumption |].
          eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap. 
          setoid_rewrite val_log_rel_eq.  intros i' Hlt. eapply IHk with (j := i'); try eassumption.
          setoid_rewrite <- val_log_rel_eq. eapply Hap. omega. omega.
        + eapply Proper_clos_rel_cov; [| | eassumption ].
          * simpl. intros P Q b' vs1' H1' vs2' H2' [[H1'' rho1'] e1'] [[H2'' rho2'] e2'] Hyp.
            intros i' Hlt Hall. eapply Hyp. omega.
            intros j'. eapply Forall2_monotonic; [| now eauto ].
            intros x1 x2 Hyp1. eapply Hyp1.
          * simpl. intros [v3 H3] [v4 H4] Hyp1 i' Hlt.
            setoid_rewrite val_log_rel_eq. eapply IHk; [| | reflexivity ]. eauto. 
            setoid_rewrite <- val_log_rel_eq. eapply Hyp1. omega.
        + eassumption.
    Qed.
    
    Lemma exp_rel_j_monotonic i j j' c1 c2 :
      exp_log_rel' i j LP GP LQ GQ c1 c2 ->
      j' <= j ->
      exp_log_rel' i j' LP GP LQ GQ c1 c2.      
    Proof.
      destruct c1 as [[H1 rho1] e1]. 
      destruct c2 as [[H2 rho2] e2]. 
      intros He1 Hlt b1 b2 H1' H2' rho1' rho2' r1 c1 m1 Heq1 Hinj1 Heq2 Hinj2 Hlp Hlt' Heval Hns.
      edestruct He1 as [r2 [c2 [m2 [b2' [Heval2 [Hlq Hcc]]]]]]; (try now eapply Heval); try eassumption. 
      repeat eexists; try eassumption. eapply val_rel_j_monotonic.
      eassumption. omega. 
    Qed.       


    (* Index-set monotonicity *)
    
    Lemma env_log_rel_P_antimon S1 S2 k j b c1 c2 :
      env_log_rel_P' S1 k j GP GQ b c1 c2 ->
      S2 \subset S1 -> 
      env_log_rel_P' S2 k j GP GQ b c1 c2.
    Proof.
      destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
      intros Hpre Hin x Hin'. eapply Hpre; eapply Hin; eauto.
    Qed.
    
    Lemma heap_log_rel_P_antimon S1 S2 k j b H1 H2 :
      heap_log_rel' S1 k j GP GQ b H1 H2 ->
      S2 \subset S1 -> 
      heap_log_rel' S2 k j GP GQ b H1 H2.
    Proof.
      intros Hpre Hin x Hin'. eapply Hpre; eapply Hin; eauto.
    Qed.

    (* TODO pre and post monotonicity *)
    
    (** * Set lemmas *)

    Lemma env_log_rel_P'_Empty_set k j b c1 c2 :
      env_log_rel_P' (Empty_set _) k j GP GQ b c1 c2.
    Proof.
      destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
      simpl. intros x Hc. inv Hc.
    Qed.
    
    Lemma env_log_rel_P'_Union S1 S2 k j b c1 c2 :
      env_log_rel_P' S1 k j GP GQ b c1 c2 ->
      env_log_rel_P' S2 k j GP GQ b c1 c2 ->
      env_log_rel_P' (S1 :|: S2) k j GP GQ b c1 c2.
    Proof.
      destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
      intros Hyp1 Hyp2 x Hc. inv Hc; eauto.
    Qed. 

    Lemma env_log_rel_P'_Inter_l S1 S2 k j b c1 c2 :
      env_log_rel_P' S1 k j GP GQ b c1 c2 ->
      env_log_rel_P' (S1 :&: S2) k j GP GQ b c1 c2.
    Proof.
      destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
      intros Hyp1 x Hc. inv Hc; eauto.
    Qed. 
    
    Lemma env_log_rel_P'_Inter_r S1 S2 k j b c1 c2 :
      env_log_rel_P' S2 k j GP GQ b c1 c2 ->
      env_log_rel_P' (S1 :&: S2) k j GP GQ b c1 c2.
    Proof.
      destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
      intros Hyp1 x Hc. inv Hc; eauto.
    Qed. 

    
    Lemma heap_log_rel_Empty_set k j b c1 c2 :
      heap_log_rel' (Empty_set _) k j GP GQ b c1 c2.
    Proof.
      simpl. intros x Hc. inv Hc.
    Qed.
    
    Lemma heap_log_rel_Union S1 S2 k j b c1 c2 :
      heap_log_rel' S1 k j GP GQ b c1 c2 ->
      heap_log_rel' S2 k j GP GQ b c1 c2 ->
      heap_log_rel' (S1 :|: S2) k j GP GQ b c1 c2.
    Proof.
      intros Hyp1 Hyp2 x Hc. inv Hc; eauto.
    Qed. 

    Lemma heap_log_rel_Inter_l S1 S2 k j b c1 c2 :
      heap_log_rel' S1 k j GP GQ b c1 c2 ->
      heap_log_rel' (S1 :&: S2) k j GP GQ b c1 c2.
    Proof.
      intros Hyp1 x Hc. inv Hc; eauto.
    Qed. 
    
    Lemma heap_log_rel_Inter_r S1 S2 k j b c1 c2 :
      heap_log_rel' S2 k j GP GQ b c1 c2 ->
      heap_log_rel' (S1 :&: S2) k j GP GQ b c1 c2.
    Proof.
      intros Hyp1 x Hc. inv Hc; eauto.
    Qed. 

    
    