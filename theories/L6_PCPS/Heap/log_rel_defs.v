(* Generic definitions for step-indexed logical relations for L6 language transformations
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2019
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From CertiCoq.L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util set_util
                 List_util Heap.heap Heap.heap_defs Heap.space_sem Heap.GC tactics map_util.
From compcert Require Import lib.Coqlib.


Module LogRelDefs (H : Heap).

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
      IInv -> IInv -> Inv -> Inj -> list value -> heap block -> list value -> heap block -> Conf -> Conf -> Prop.  

    (* NOTE : We are passing two preconditions. The first one is enforced at the configurations right after function entry.
              The second one is passed along with the postcondition to the extression relation.  *)
    
    Definition val_rel : Type :=
      res -> res -> Prop. 
    
    (* Relation of closure pairs -- Given by the caller *)
    Variable (clos_rel : GIInv -> GInv -> Inj -> block -> heap block -> block -> heap block -> (* Block being related *)
                         fun_body_rel ->
                         val_rel -> 
                         Prop).

    Require Import Coq.Classes.Morphisms Coq.Classes.RelationClasses.
    
    Definition fun_body_args : Tlist :=      
      Tcons IInv (Tcons IInv (Tcons Inv (Tcons Inj (Tcons (list value) (Tcons (heap block) (Tcons (list value) (Tcons (heap block) (Tcons Conf (Tcons Conf Tnil))))))))).
    
    
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
          let fun_body_rel PL' PL QL b (* local pre and post, picked by the caller *)
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
                    (PL' (H1', rho1, e1) (H2, rho2, e2)) /\
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
      let fun_body_rel PL' PL QL b (* local pre and post, picked by the caller *)
                       (vs1 : list value) (H1 : heap block) 
                       (vs2 : list value) (H2 : heap block) 
                       (c1 c2 : Conf) :=
          let '(H1', rho1, e1) := c1 in
          let '(H2', rho2, e2) := c2 in              
          forall i, (i < k)%nat ->
               let R j v1 v2 := val_log_rel i j IP P b (Res (v1, H1)) (Res (v2, H2)) in
               (forall j, Forall2 (R j) vs1 vs2) ->
               (PL' (H1', rho1, e1) (H2, rho2, e2)) /\
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
            { simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
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
            { simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto. exfalso. omega. }
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto. exfalso. omega. }
      - simpl. eapply Proper_fun_rel.
        simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
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
            { simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
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
            { simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto. exfalso. omega. }
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto.
              replace i with (j - (j - i)) by omega. eapply H. omega.
              replace (j - (j - i)) with i by omega. eapply H. omega. }
      - simpl. eapply Proper_fun_rel.
        simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
        split; intros; eauto. exfalso. omega.
      - simpl. split. 
        + intros [Hyp1 Hyp2]. split; eauto. 
          destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
          destruct b1 as [c1 vs1 | v1 v2 | ]; try now eauto.
          * destruct b2 as [c2 vs2 | v1' v2' | ]; try contradiction.
            destruct Hyp2 as [Hyp2 Hyp3]. split; eauto. 
            eapply Forall2_monotonic; [| eassumption ]. intros; omega.
          * eapply Proper_clos_rel; [| | eassumption ].
            { simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
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
            { simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
              split; intros; eauto.
              replace i with  (k - (k - i)) by omega. eapply H. omega.
              replace (k - (k - i)) with i by omega. eassumption.
              replace (k - (k - i)) with i by omega. eapply H. omega.
              replace i with  (k - (k - i)) by omega. eassumption. }
            { simpl. intros [r1 Hv1] [r2 Hv2].  
              split; intros; eauto. omega. }
      - simpl. eapply Proper_fun_rel.
        simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
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
            { simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
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
            { simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
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
        simpl. intros P1' P1 Q1 d ls1 Hl1 ls2 Hl2 [[H11 rho11] e11] [[H12 rho12] e12]. 
        split; intros; eauto.
        replace i with  (k - (k - i)) by omega. eapply H. omega.
        replace (k - (k - i)) with i by omega. eassumption.
        replace (k - (k - i)) with i by omega. eapply H. omega.
        replace i with  (k - (k - i)) by omega. eassumption.
    Qed. 

    Opaque val_log_rel.
    
    Definition exp_log_rel' := exp_log_rel val_log_rel' eval_src eval_trg. 
    Definition env_log_rel_P' := env_log_rel_P val_log_rel'.
    Definition heap_log_rel' := heap_log_rel val_log_rel'.
    Definition var_log_rel' := var_log_rel val_log_rel'. 
        
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
        * simpl. intros P' P Q b' vs1' H1' vs2' H2' [[H1'' rho1'] e1'] [[H2'' rho2'] e2'] Hyp.
          intros i Hlt Hall. eapply Hyp. omega.
          intros j'. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hyp1. eapply Hyp1.
        * simpl. intros [v3 H3] [v4 H4] Hyp1 i Hlt.
          setoid_rewrite val_log_rel_eq. eapply IHj. eauto. 
          setoid_rewrite <- val_log_rel_eq. now eauto. omega.
      + eassumption.
    - intros Hyp Hleq. eapply Proper_fun_rel_cov; [| eassumption ]. 
      simpl. intros P' P Q b' vs1' H1' vs2' H2' [[H1'' rho1'] e1'] [[H2'' rho2'] e2'] Hyp1.
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
          * simpl. intros P' P Q b' vs1' H1' vs2' H2' [[H1'' rho1'] e1'] [[H2'' rho2'] e2'] Hyp.
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
    
    Lemma env_log_rel_P_antimon GP' GQ' S1 S2 k j b c1 c2 :
      env_log_rel_P' S1 k j GP' GQ' b c1 c2 ->
      S2 \subset S1 -> 
      env_log_rel_P' S2 k j GP' GQ' b c1 c2.
    Proof.
      destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
      intros Hpre Hin x Hin'. eapply Hpre; eapply Hin; eauto.
    Qed.
    
    Lemma heap_log_rel_P_antimon GP' GQ' S1 S2 k j b H1 H2 :
      heap_log_rel' S1 k j GP' GQ' b H1 H2 ->
      S2 \subset S1 -> 
      heap_log_rel' S2 k j GP' GQ' b H1 H2.
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

    
    (** * Environment extension lemmas *)
    
    Lemma var_log_rel_env_set_eq (k j : nat) (b : Inj) (rho1 rho2 : env) (H1 H2 : heap block)
          (x y : var) (v1 v2 : value) :
      val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2)) ->
      var_log_rel' k j GP GQ b H1 (M.set x v1 rho1) H2 (M.set y v2 rho2) x y.
    Proof.
      intros Hval x' Hget.
      rewrite M.gss in Hget. inv Hget. eexists.
      rewrite M.gss. split; eauto.
    Qed.
    
    Lemma var_log_rel_env_set_neq (k j : nat) (b : Inj) (rho1 rho2 : env) (H1 H2 : heap block)
          (x1 y1 x2 y2 : var) (v1 v2 : value) :
      var_log_rel' k j GP GQ b H1 rho1 H2 rho2 x1 y1 ->
      x1 <> x2 -> y1 <> y2 ->
      var_log_rel' k j GP GQ b H1 (M.set x2 v1 rho1) H2 (M.set y2 v2 rho2) x1 y1.
    Proof.
      intros Hval Hneq1 Hneq2 x' Hget.
      rewrite M.gso in Hget; eauto.      
      rewrite M.gso; eauto.
    Qed.
  
  Lemma var_log_rel_env_set (k j : nat) (b : Inj) (rho1 rho2 : env) (H1 H2 : heap block)
        (x y : var) (v1 v2 : value):
    var_log_rel' k j GP GQ b H1 rho1 H2 rho2 y y ->
    val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2)) ->
    var_log_rel' k j GP GQ b H1 (M.set x v1 rho1) H2 (M.set x v2 rho2) y y.
  Proof.
    intros Hvar Hval.
    destruct (peq y x); subst.
    - apply var_log_rel_env_set_eq; eauto.
    - apply var_log_rel_env_set_neq; eauto.
  Qed.
  
  Lemma var_log_rel_env_set_neq_l (k j : nat) (b : Inj) (rho1 rho2 : env) (H1 H2 : heap block)
        (y1 x1 y2 : var) (v1 : value) :
    var_log_rel' k j GP GQ b H1 rho1 H2 rho2 y1 y2 ->
    y1 <> x1 ->
    var_log_rel' k j GP GQ b H1 (M.set x1 v1 rho1) H2 rho2 y1 y2.
  Proof. 
    intros Hval Hneq x' Hget.
    rewrite M.gso in *; eauto.
  Qed.
  
  Lemma var_log_rel_env_set_neq_r (k j : nat) (b : Inj) (rho1 rho2 : env) (H1 H2 : heap block)
        (y1 x2 y2 : var) ( v2 : value) :
    var_log_rel' k j GP GQ b H1 rho1 H2 rho2 y1 y2 ->
    y2 <> x2 ->
    var_log_rel' k j GP GQ b H1 rho1 H2 (M.set x2 v2 rho2) y1 y2.
  Proof. 
    intros Hval Hneq x' Hget.
    rewrite M.gso in *; eauto.
  Qed.

  (** Extend the related environments with a single point *)
  Lemma env_log_rel_P_set (S : Ensemble var) (k j : nat) (b : Inj)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v1 v2 : value) :
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2) ->
    val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2)) ->
    env_log_rel_P' S k j GP GQ b (H1, M.set x v1 rho1) (H2, M.set x v2 rho2).
  Proof.
    intros Henv Hval x' HP. eapply var_log_rel_env_set; eauto. 
    eapply Henv. eassumption. 
  Qed.

  
  Lemma  env_log_rel_P_set_not_in_S_l (S : Ensemble var) (k j : nat) (b : Inj)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v1 : value) :
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2) ->
    ~ x \in S -> 
    env_log_rel_P' S k j GP GQ b (H1, M.set x v1 rho1) (H2, rho2).
  Proof.
    intros Henv Hval x' HP. eapply var_log_rel_env_set_neq_l; eauto.
    eapply Henv; eauto.
    intros Hc; subst; contradiction.
  Qed.

  Lemma env_log_rel_P_set_not_in_S_r (S : Ensemble var) (k j : nat) (b : Inj)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v1 v2 : value) :
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2) ->
    ~ x \in S -> 
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, M.set x v1 rho2).
  Proof.
    intros Henv Hval x' HP. eapply var_log_rel_env_set_neq_r; eauto.
    eapply Henv; eauto.
    intros Hc; subst; contradiction.
  Qed.
  
  (** Extend the related environments with a list *)
  Lemma env_log_rel_P_setlist_l (S : Ensemble var) (k j : nat) b
        (rho1 rho2 rho1' rho2' : env) (H1 H2 : heap block) xs (vs1 vs2 : list value) :
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2) ->
    Forall2 (fun v1 v2 => val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2))) vs1 vs2 ->
    setlist xs vs1 rho1 = Some rho1' ->
    setlist xs vs2 rho2 = Some rho2' ->
    env_log_rel_P' S k j GP GQ b (H1, rho1') (H2, rho2').
  Proof.
    intros Hcc Hall Hset1 Hset2 x HP v Hget.
    destruct (in_dec var_dec x xs).
    - edestruct (@setlist_Forall2_get value) as [v1 [v2 [Hget1 [Hget2 HP']]]];
        try eassumption. subst_exp. repeat eexists; eauto.
    - erewrite <- setlist_not_In in Hget; eauto.
      edestruct Hcc as [v2 [Hget' Hpre']]; eauto.
      repeat eexists; eauto.
      erewrite <- setlist_not_In; eauto.
  Qed.
  
  Lemma env_log_rel_P_setlist_not_in_P_l (S : Ensemble var) (k j : nat) b
        (rho1 rho1' rho2 : env) (H1 H2 : heap block) (xs : list var) (vs : list value) :
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2) ->
    Disjoint _ (FromList xs) S ->
    setlist xs vs rho1 = Some rho1' ->
    env_log_rel_P' S k j GP GQ b (H1, rho1') (H2, rho2).
  Proof. 
    intros Hcc Hnin Hset y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    erewrite setlist_not_In. eassumption. eassumption.
    intros Hc. eapply Hnin. constructor; eauto.
  Qed.

  Lemma env_log_rel_P_setlist_not_in_P_r (S : Ensemble var) (k j : nat) b
        (rho1 rho2 rho2' : env) (H1 H2 : heap block) (xs : list var) (vs : list value) :
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2) ->
    Disjoint _ (FromList xs) S ->
    setlist xs vs rho2 = Some rho2' ->
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2').
  Proof.
    intros Hcc Hnin Hset y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    eexists; split; eauto. erewrite <- setlist_not_In. eassumption. eassumption.
    intros Hc. eapply Hnin. constructor; eauto.
  Qed.

  (** * Related values are well-defined in the heap *)

  Lemma val_log_rel_in_dom1 (k j : nat) b v1 v2 H1 H2 :
    val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2)) ->
    val_loc v1 \subset dom H1.
  Proof.
    intros Hcc h Hin; destruct v1 as [l1|]; inv Hin.
    destruct v2  as [l2|]; try contradiction.
    simpl in Hcc.
    destruct (get h H1) eqn:Hget; [| destruct Hcc; contradiction ].
    clear LP LQ .
    now firstorder.
  Qed.
  
  Lemma val_log_rel_in_dom2 (k j : nat) b v1 v2 H1 H2 :
    val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2)) ->
    val_loc v2 \subset dom H2.
  Proof.
    clear LP LQ.
    intros Hcc l2 Hin; destruct v2 as [l2'|]; inv Hin.
    destruct v1 as [l1|]; try contradiction.
    simpl in Hcc.
    destruct (get l1 H1) as [b1 | ] eqn:Hget; [| destruct Hcc; contradiction ].
    destruct Hcc as [Heq1 Hcc].
    destruct b1 as [c1 vs1 | v1 v2 | ]; try contradiction.
    
    destruct (get l2 H2) as [b2 | ] eqn:Hget'; [| contradiction ].
    now eexists; eauto.
    
    destruct (get l2 H2) as [b2 | ] eqn:Hget'; [| contradiction ].
    now eexists; eauto.
  Qed.

  
  Lemma val_log_rel_Forall2_dom1 (k j : nat) b (H1 H2 : heap block)
        vs1 vs2 :
    Forall2 (fun v1 v2 => val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2))) vs1 vs2 ->
    Union_list (map val_loc vs1) \subset dom H1.  
  Proof.
    intros Hall. induction Hall; simpl.
    - now eauto with Ensembles_DB.
    - eapply Union_Included; [| eassumption ].
      eapply val_log_rel_in_dom1; eauto.
  Qed.

  Lemma val_log_rel_Forall2_dom2 (k j : nat) b (rho1 rho2 : env) (H1 H2 : heap block) vs1 vs2 :
    Forall2 (fun v1 v2 => val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2))) vs1 vs2 ->
    Union_list (map val_loc vs2) \subset dom H2.  
  Proof.
    intros Hall. induction Hall; simpl.
    - now eauto with Ensembles_DB.
    - eapply Union_Included; [| eassumption ].
      eapply val_log_rel_in_dom2; eauto.
  Qed.
  

  Lemma env_log_rel_P_in_dom1 (R : Ensemble var) (k j : nat) b
        rho1 rho2 H1 H2 :
    env_log_rel_P' R k j GP GQ b (H1, rho1) (H2, rho2) ->
    env_locs rho1 R \subset dom H1.  
  Proof. 
    intros Hcc x [y [Hget Hin]].
    destruct (M.get y rho1) as [ [l1 |] | ] eqn:Hgetl; [| now inv Hin | now inv Hin ].
    inv Hin. edestruct Hcc as [v2 [Hget' Hcc']]; eauto.
    eapply val_log_rel_in_dom1. eassumption. reflexivity.
  Qed.
  
  Lemma env_log_rel_P_in_dom2 (R : Ensemble var) (k j : nat) b
        rho1 rho2 H1 H2 :
    env_log_rel_P' R k j GP GQ b (H1, rho1) (H2, rho2) ->
    binding_in_map R rho1 ->
    env_locs rho2 R \subset dom H2.  
  Proof. 
    intros Hcc Hbin x [y [Hget Hin]].
    edestruct Hbin as [v1 Hget1]. eassumption.
    destruct (M.get y rho2) as [ [l1 |] | ] eqn:Hgetl; [| now inv Hin | now inv Hin ].
    inv Hin. edestruct Hcc as [v2 [Hget' Hcc']]; eauto.
    eapply val_log_rel_in_dom2. eassumption. subst_exp. reflexivity.
  Qed.

  Lemma heap_log_rel_in_dom1 (k j : nat) S b H1 H2 : 
    heap_log_rel' S k j GP GQ b H1 H2 ->
    S \subset dom H1.
  Proof.
    intros Hh x Hin. eapply Hh in Hin.
    eapply val_log_rel_in_dom1. eassumption. reflexivity. 
  Qed.

  Lemma heap_log_rel_in_dom2 (k j : nat) S b H1 H2 : 
    heap_log_rel' S k j GP GQ b H1 H2 ->
    image b S \subset dom H2.
  Proof.
    intros Hh x [y [Hin Heq]]. subst. eapply Hh in Hin.
    eapply val_log_rel_in_dom2. eassumption. reflexivity.
  Qed.

  (** Properties of the renaming *)
  
  Lemma val_log_rel_loc_eq (k j : nat) b H1 H2 l v2 :
    val_log_rel' k j GP GQ b (Res (Loc l, H1)) (Res (v2, H2)) ->
    v2 = Loc (b l).
  Proof.
    intros Hcc. destruct v2; [| now inv Hcc ].
    destruct Hcc as [Heq _].
    congruence.
  Qed.
  
  Lemma var_log_rel_env_image_reach
        (k : nat) j b (H1 H2 : heap block) (rho1 rho2 : env) (x y : var) (v : value) :
    var_log_rel' k j GP GQ b H1 rho1 H2 rho2 x y ->
    M.get x rho1 = Some v ->
    image b (env_locs rho1 [set x]) <--> (env_locs rho2 [set y]). 
  Proof.
    intros Hcc Hget.
    edestruct Hcc as [v' [Hget' Hv]]; eauto.
    rewrite !env_locs_Singleton at 1; eauto.
    destruct v; destruct v'; try contradiction; simpl.
    eapply val_log_rel_loc_eq in Hv. inv Hv.
    now rewrite image_Singleton. 
    now rewrite image_Empty_set.
  Qed.
  

  Lemma env_log_rel_locs_image S (k j : nat) b
        (H1 H2 : heap block) (rho1 rho2 : env) :
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2) ->
    binding_in_map S rho1 ->
    image b (env_locs rho1 S) <--> (env_locs rho2 S).
  Proof.
    intros Hres HB. split.
    - intros l' [l [Hin Heq]]; subst.
      destruct Hin as [x [Hin Hp]].
      destruct (M.get x rho1) as[[l1' |] | ] eqn:Hgetx1; try now inv Hp.
      inv Hp. eapply Hres in Hgetx1.
      edestruct Hgetx1 as [l2 [Hget2 Hval]].
      eapply val_log_rel_loc_eq in Hval. subst.
      eexists; split; eauto. rewrite Hget2. reflexivity. eassumption.
    - intros l [x [Hin Hr]].
      destruct (M.get x rho2) as[[l1' |] | ] eqn:Hgetx1; inv Hr. 
      edestruct HB as [[l1| ] Hget1]. eassumption.
      assert (Hget1' := Hget1). 
      edestruct Hres as [l2 [Hget2 Hval]].
      eassumption. eassumption.
      repeat subst_exp. 
      eapply val_log_rel_loc_eq in Hval. inv Hval. 
      eexists; split; eauto.
      eexists; split; eauto.
      rewrite Hget1. reflexivity.

      edestruct Hres as [l2 [Hget2 Hval]]; try eassumption.
      repeat subst_exp. contradiction.
  Qed. 

  
  Lemma env_log_rel_val_log_rel S (k j : nat) b
        (H1 H2 : heap block) (rho1 rho2 : env) l :
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2) ->
    l \in env_locs rho1 S ->
    val_log_rel' k j GP GQ b (Res (Loc l, H1)) (Res (Loc (b l), H2)).
  Proof.
    intros Henv [x [Hin Hget]].
    edestruct (M.get x rho1) as [[l'|] | ] eqn:Hget1; inv Hget.  
    edestruct Henv as [[l2 |] [Hget2 Hv]].
    eassumption. eassumption.
    assert (Hleq : l2 = b l). 
    { eapply val_log_rel_loc_eq in Hv. now inv Hv. }
    subst. eassumption.

    now inv Hv. 
  Qed.

  Lemma heap_log_rel_val_log_rel S (k j : nat) b
        (H1 H2 : heap block) l :
    heap_log_rel' S k j GP GQ b H1 H2 ->
    l \in S ->
    val_log_rel' k j GP GQ b (Res (Loc l, H1)) (Res (Loc (b l), H2)).
  Proof. eauto. Qed.


  (** * Getlist lemmas *)

  Lemma var_log_rel_getlist (k j : nat)
        (rho1 rho2 : env) (b : Inj) (H1 H2 : heap block) xs ys vs1 :
    Forall2 (var_log_rel' k j GP GQ b H1 rho1 H2 rho2) xs ys ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist ys rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2))) vs1 vs2.
  Proof.
    revert ys vs1. induction xs as [| x xs IHxs]; intros ys vs1 Hall Hget.
    - destruct ys; inv Hall. inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget.
      destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (getlist xs rho1) eqn:Heq2; try discriminate. inv Hget.
      destruct ys as [| y ys]; inv Hall. 
      destruct (IHxs ys l H6 eq_refl) as [vs2 [Hget HAll]].
      destruct (H4 _ Heq1) as [v2 [Heq Hpre]].
      eexists. split; simpl; eauto. rewrite Hget. rewrite Heq. reflexivity.
  Qed.
  
  Lemma env_log_rel_P_getlist_l (S : Ensemble var) (k j : nat) b
        (rho1 rho2 : env) (β : Inj) (H1 H2 : heap block)
        (xs : list var) (vs1 : list value) :
    env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2)  ->
    (FromList xs) \subset S ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist xs rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2))) vs1 vs2.
  Proof.
    intros Henv. revert vs1.
    induction xs as [| x xs IHxs]; intros ls1 Hp Hget.
    - inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget. destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (getlist xs rho1) eqn:Heq2; try discriminate. inv Hget.
      edestruct (IHxs l) as  [vs2 [Hget HAll]]; eauto.
      + intros x' Hin. eapply Hp. constructor 2; eauto.
      + eapply Henv in Heq1. destruct Heq1 as [v2 [Hyp1 Hyp2]].
        eexists. split; simpl; eauto. rewrite Hyp1. rewrite Hget.
        constructor. apply Hp. now constructor.
  Qed.
  
  Lemma env_log_rel_P_getlist_all (k : nat) b
        (rho1 rho2 : env) (H1 H2 : heap block)
        xs ys vs1 :
    Forall2 (fun x1 x2 =>
               forall j, var_log_rel' k j GP GQ b H1 rho1 H2 rho2 x1 x2
            ) xs ys ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist ys rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => forall j, val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2)))
              vs1 vs2.
  Proof.
    revert ys vs1. induction xs as [| x xs IHxs]; intros ys vs1 Hall Hget.
    - destruct ys; inv Hall. inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget.
      destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (getlist xs rho1) eqn:Heq2; try discriminate. inv Hget.
      destruct ys as [| y ys]; inv Hall. 
      destruct (IHxs ys l H6 eq_refl) as [vs2 [Hget Hall]].
      destruct (H4 0 _ Heq1) as [v2 [Heq Hpre]].
      eexists (v2 :: vs2). split. simpl. 
      rewrite Hget. rewrite Heq.
      reflexivity.
      constructor; [| eassumption ].
      intros j'. 
      destruct (H4 j' _ Heq1) as [v2' [Heq' Hpre']].
      repeat subst_exp. eassumption.
  Qed.
  
  Lemma env_log_rel_P_getlist_l_all (S : Ensemble var) (k : nat) b
        (rho1 rho2 : env)
        (H1 H2 : heap block) (xs : list var) (vs1 : list value) :
    (forall j, env_log_rel_P' S k j GP GQ b (H1, rho1) (H2, rho2))  ->
    (FromList xs) \subset S ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist xs rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => forall j, val_log_rel' k j GP GQ b (Res (v1, H1)) (Res (v2, H2))) vs1 vs2.
  Proof.
    intros Henv. revert vs1.
    induction xs as [| x xs IHxs]; intros ls1 Hp Hget.
    - inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget. destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (getlist xs rho1) eqn:Heq2; try discriminate. inv Hget.
      edestruct (IHxs l) as  [vs2 [Hget HAll]]; eauto.
      + intros x' Hin. eapply Hp. constructor 2; eauto.
      + edestruct (Henv 0) as [v2 [Hyp1 Hyp2]].
        eapply Hp. now left.  eassumption.
        
        eexists. split; eauto. simpl. rewrite Hyp1. rewrite Hget. reflexivity.
        
        constructor. intros j.
        edestruct (Henv j) as [v2' [Hyp1' Hyp2']].
        eapply Hp. now left.  eassumption.
        repeat subst_exp. eassumption. 
        eassumption.
  Qed.
  
  (** * Logical relation respects heap_equivalence *)

  Lemma exp_log_rel_heap_env_equiv k i P Q b1 b2
        H1 rho1 H1' rho1' e1 H2 rho2 H2' rho2' e2 :
    exp_log_rel' k i P GP Q GQ (H1, rho1, e1) (H2, rho2, e2) ->
    
    occurs_free e1 |- (H1, rho1) ⩪_( id, b1) (H1', rho1') ->
    injective_subdomain (reach' H1' (env_locs rho1' (occurs_free e1))) b1 ->
    occurs_free e2 |- (H2, rho2) ⩪_( b2, id) (H2', rho2') ->
    injective_subdomain (reach' H2 (env_locs rho2 (occurs_free e2))) b2 ->

    exp_log_rel' k i P GP Q GQ (H1', rho1', e1) (H2', rho2', e2).
  Proof.

    intros Hexp Heq1 Hinj1 Heq2 Hinj2 b1' b2' H1'' H2'' rho1'' rho2''
           r1 c1 m1 Heq1' Hinj1' Heq2' Hinj2' Hpre Hleq Hstep Hns. 
 
    eapply Hexp.
    
    + eapply heap_env_equiv_f_compose; [| eassumption ].
      rewrite compose_id_neut_r. eassumption.
    + eapply injective_subdomain_compose. eassumption.
      rewrite <- heap_env_equiv_image_reach; try eassumption. 
      rewrite image_id. eassumption.
    + symmetry. 
      eapply heap_env_equiv_f_compose; symmetry; [| eassumption ].
      rewrite compose_id_neut_r. eassumption.
    + eapply injective_subdomain_compose. eassumption.
      rewrite <- heap_env_equiv_image_reach; try eassumption. 
      rewrite image_id. eassumption. symmetry. eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
    + eassumption.
  Qed.

  (** * Heap monotonicity *)
  Lemma exp_log_rel_heap_monotonic (k j : nat) P Q (H1 H2 H1' H2' : heap block)
        (rho1 rho2 : env) (e1 e2 : exp) :
    exp_log_rel' k j P GP Q GQ (H1, rho1, e1) (H2, rho2, e2) ->
    
    well_formed (reach' H1 (env_locs rho1 (occurs_free e1))) H1 ->
    well_formed (reach' H2 (env_locs rho2 (occurs_free e2))) H2 ->
    (env_locs rho1 (occurs_free e1)) \subset dom H1 ->
    (env_locs rho2 (occurs_free e2)) \subset dom H2 ->
    
    H1 ⊑ H1' -> H2 ⊑ H2' ->

    exp_log_rel' k j P GP Q GQ (H1', rho1, e1) (H2', rho2, e2).
  Proof.
    intros Hyp Hwf1 Hwf22 Hs1 Hs2 Hsub1 Hsub2 b1 b2 H3 H4 rho1' rho2' r1 c1 m1
           Heq1 Hinj1 Heq2 Hinj2 HIP Hleq Hstep Hns.
    eapply Hyp; [ | | | | eassumption | eassumption | eassumption | eassumption ].
    edestruct Equivalence_heap_env_equiv with (S := (occurs_free e1)). (* ? *)
    eapply Equivalence_Transitive.
    eapply subheap_heap_env_equiv; try eassumption. now eapply reach'_extensive.
    eassumption. eassumption.
    edestruct Equivalence_heap_env_equiv with (S := (occurs_free e2)). (* ? *)
    eapply Equivalence_Transitive.
    eapply subheap_heap_env_equiv; try eassumption. now eapply reach'_extensive.
    eassumption.
    eapply injective_subdomain_antimon. eassumption.
    eapply reach'_heap_monotonic. eassumption.
  Qed.
  
  Global Instance env_log_rel_P_proper_set :
    Proper (Same_set var ==> Logic.eq ==>  Logic.eq ==> Logic.eq ==> Logic.eq ==>
            Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           env_log_rel_P'.
  Proof.
    intros s1 s2 [H1 H2]; split; intros Hpre; subst;
    eapply env_log_rel_P_antimon; subst; eauto. 
  Qed.

  Global Instance heap_log_rel_proper_set :
    Proper (Same_set _ ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
           heap_log_rel'.
  Proof.
    intros s1 s2 Hseq; constructor; subst;
    intros Hcc z Hin; eapply Hcc; eapply Hseq; eauto.
  Qed.

  End ValRelDef.

End LogRelDefs. 
