(* Step-indexed logical relation for L6 closure conversion.
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2017
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util
                       List_util Heap.heap Heap.heap_defs Heap.space_sem tactics.
From compcert Require Import lib.Coqlib.

Import ListNotations.

Module CC_log_rel (H : Heap).

  Module Sem := SpaceSem H.

  Import H Sem.Equiv Sem.Equiv.Defs Sem.

  
  (** ** Resource conditions  *)

  (** * Initial conditions *)
  
  (** Local initial condition. Enforced as initial condition for the expressions being related *)
  Definition IInv := relation (heap block * env * exp).

  (** Global initial condition. Enforced as initial condition for future executions of the result *)
  Definition GIInv := nat -> relation (heap block * env * exp).
  
  (** * Final conditions *)
  
  (** Local final conditions. Holds for the result of the execution of the expressions being related. *)
  Definition Inv := relation (nat * nat).

  (** Global final conditions. Holds for the result of future execution of the result *)
  Definition GInv := nat -> relation (heap block * env * exp * nat * nat).
  
  (** Loc Injection *)
  Definition Inj := loc -> loc.
  
  (** Tag for closure records *)
  Variable (clo_tag : cTag). 

  (** A program will not get stuck for any fuel amount *)
  (* This is used to exclude programs that may timeout for low fuel, but they might get stuck later *)
  Definition not_stuck (H : heap block) (rho : env) (e : exp) :=
    forall c, exists r m, big_step_GC H rho e r c m. 
  
  (** step-indexed relation on cps terms. Relates cps-terms with closure-converted terms  *)
  (* Expression relation : (XXX This comment is not up-to-date)
   * ---------------------
   *  (e1, ρ1, H1) ~_k (e2, ρ2, H2) iff 
   *    forall c1 <= k,
   *      H1; ρ1 |- e1 ->^c1 v1 -> 
   *      exists r2, H2; ρ2 |- e2 -> ρ2 /\ r1 ~_(k-c1) r2
   *  
   * Result relation :
   * ----------------
   * (l1, H1) ~_k (l2, H2) iff
   * if H1(l1) = v1
   * then H2(l2) = v2 and  
   *   if v1 = C[l_1, .., l_n] 
   *   then v2 = C[v'_1, .., v'_m] /\ n <= m /\ (l_1, H1) ~_(k-1) (l_1', H2) /\ ... /\ (l_n, H1) ~_(k-1) (l_n', H2)
   *   else if v1 = (λ f1 x1. e1, ρ1)
   *   then v2 = {l_clo; l_env} /\ H2(l_clo) =  λ f2 Γ x2. e2 /\ H2(l_env) = C ls /\
   *        \forall l1' l2' i < k, (l1', H1) ~_j (l2', H2)s => 
   *                (e1, ρ1[x1 -> l1', f1 -> l1], H1) ~_j 
   *                (e2, [x2 -> l2', f2 -> l_clo, Γ -> l_env], H2)
   * else True (* ? -- not quite sure yet *)
   *)
  
  (** Definitions parametric on the value relation *)
  Section cc_approx.
    
    Variable (cc_approx_val : nat -> nat -> GIInv -> GInv -> Inj -> ans -> ans -> Prop). 

    (* TODO move *)
    Definition reach_n_res (j : nat) := fun '(v, H) => reach_n H j (val_loc v).
    
    Definition reach_n_ans (j : nat) (a : ans) := 
      match a with
        | Res r => reach_n_res j r
        | OOT => Empty_set loc
        | OOM => Empty_set loc
      end.
    
    
    (** * Expression relation *)
    
    Definition cc_approx_exp
               (* step indexes *)
               (k : nat) (j : nat)
               (* Invariants *)
               (IIL : IInv) (IIG : GIInv) (IL : Inv) (IG : GInv)
               (* related expressions *)
               (p1 p2 : exp * env * heap block) : Prop :=
      let '(e1, rho1, H1) := p1 in
      let '(e2, rho2, H2) := p2 in
      forall (b1 b2 : Inj) (H1' H2' : heap block) (rho1' rho2' : env) (r1 : ans) (c1 m1 : nat),
        (occurs_free e1) |- (H1, rho1) ⩪_(id, b1) (H1', rho1') ->
        injective_subdomain (reach' H1' (env_locs rho1' (occurs_free e1))) b1 ->
        (occurs_free e2) |- (H2, rho2) ⩪_(b2, id) (H2', rho2') ->
        injective_subdomain (reach' H2 (env_locs rho2 (occurs_free e2))) b2 ->
        IIL (H1', rho1', e1) (H2', rho2', e2) ->
        c1 <= k ->
        big_step_GC H1' rho1' e1 r1 c1 m1 ->
        not_stuck H1' rho1' e1 ->
        exists (r2 : ans) (c2 m2 : nat) (b : Inj),
          big_step_GC_cc H2' rho2' e2 r2 c2 m2 /\
          injective_subdomain (reach_n_ans j r1) b /\
          (* extra invariants for costs *)
          IL (c1, m1) (c2, m2) /\
          cc_approx_val (k - c1) j IIG IG b r1 r2.
    
  End cc_approx.
  
  (** * Value relation *)
  
  Fixpoint cc_approx_val (k : nat) {struct k} :=
    let fix cc_approx_val_aux 
           (j : nat) (IP : GIInv) (P : GInv) (b : Inj) (r1 r2 : ans) {struct j} : Prop :=
    match r1, r2 with
      | OOT, OOT => True (* Both programs timeout *)
      | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
        match v1, v2 with
          | Loc l1, Loc l2 =>
            b l1 = l2 /\
            match get l1 H1, get l2 H2 with
              | Some (Constr c1 vs1), Some (Constr c2 vs2) =>
                    c1 = c2 /\
                    (forall i,
                       (i < j)%nat ->
                       match j with
                         | 0 => True
                         | S j =>
                           let R l1 l2 := cc_approx_val_aux (j - (j - i)) IP P b (Res (l1, H1)) (Res (l2, H2)) in
                           Forall2 R vs1 vs2
                       end)
              | Some (Clos (FunPtr B1 f1) (Loc env_loc1)), Some (Constr c [FunPtr B2 f2; Loc env_loc2]) =>
                                (forall j', j' <= j -> (* maybe <= *) image b ((post H1 ^ j') [set env_loc1]) <--> ((post H2 ^ j') [set env_loc2])) /\
                forall (b1 b2 : Inj)
                  (rho_clo1 rho_clo2 rho_clo3 : env) (H1' H1'' H2' : heap block)
                  (env_loc1' env_loc2' : loc)
                  (xs1 : list var) (ft : fTag) (e1 : exp) (vs1 vs2 : list value),
                  (Loc env_loc1, H1) ≈_(id, b1) (Loc env_loc1', H1') ->
                  injective_subdomain (reach' H1' [set env_loc1']) b1 ->
                  (Loc env_loc2, H2) ≈_(b2, id) (Loc env_loc2', H2') ->
                  injective_subdomain (reach' H2 [set env_loc2]) b2 ->
                  
                  get env_loc1' H1' = Some (Env rho_clo1) ->
                  find_def f1 B1 = Some (ft, xs1, e1) ->

                  def_closures B1 B1 rho_clo1 H1' env_loc1' =  (H1'', rho_clo2) ->
                  setlist xs1 vs1 rho_clo2 = Some rho_clo3 ->

                  exists (xs2 : list var) (e2 : exp) (rho2' : env),
                    find_def f2 B2 = Some (ft, xs2, e2) /\
                    Some rho2' = setlist xs2 ((Loc env_loc2') :: vs2) (def_funs B2 B2 (M.empty _)) /\
                    (forall i j',
                       (i < k)%nat -> (j' <= j)%nat ->
                       match k with
                         | 0 => True
                         | S k =>
                           forall b',
                           let R v1 v2 := cc_approx_val (k - (k - i)) j' IP P b' (Res (v1, H1'')) (Res (v2, H2')) in
                           Forall2 R vs1 vs2 ->
                           f_eq_subdomain (reach' H1' [set env_loc1']) (b2 ∘ b ∘ b1) b' ->
                           cc_approx_exp cc_approx_val
                                         (k - (k - i))
                                         j'
                                         (IP i) IP
                                         (fun p1 p2 =>
                                            P i (H1'', rho_clo3, e1, fst p1, snd p1) (H2', rho2', e2, fst p2, snd p2)) P
                                         (e1, rho_clo3, H1'') (e2, rho2', H2')
                       end)
              | _, _ => False
            end
          | _, _ => False
        end
      | _, _ => False
    end
    in cc_approx_val_aux.
  
  (** Notations for approximation relation *)
  Notation "p1 ⪯ ^ ( k ; j ; P1 ; P2 ; P3 ; P4 ) p2" :=
    (cc_approx_exp cc_approx_val k j P1 P2 P3 P4 p1 p2)
      (at level 70, no associativity).
  
  Definition cc_approx_block (k : nat) (j : nat) (IP : GIInv) (P : GInv) (b : Inj)
             (b1 : block) (H1 : heap block)
             (b2 : block) (H2 : heap block) : Prop :=
    match b1, b2 with
      | Constr c1 vs1, Constr c2 vs2 =>
        c1 = c2 /\
        (forall i,
           (i < j)%nat ->
           let R l1 l2 := cc_approx_val k i IP P b (Res (l1, H1)) (Res (l2, H2)) in
           Forall2 R vs1 vs2)
      | Clos (FunPtr B1 f1) (Loc env_loc1), Constr c [FunPtr B2 f2; Loc env_loc2] =>
        (forall j', j' <= j -> (* maybe <= *) image b ((post H1 ^ j') [set env_loc1]) <--> ((post H2 ^ j') [set env_loc2])) /\
        forall (b1 b2 : Inj) (rho_clo1 rho_clo2 rho_clo3 : env) (H1' H1'' H2' : heap block) (env_loc1' env_loc2' : loc)
          (xs1 : list var) (ft : fTag) (e1 : exp) (vs1 vs2 : list value),
          (Loc env_loc1, H1) ≈_(id, b1) (Loc env_loc1', H1') ->
          injective_subdomain (reach' H1' [set env_loc1']) b1 ->
          (Loc env_loc2, H2) ≈_(b2, id) (Loc env_loc2', H2') ->
          injective_subdomain (reach' H2 [set env_loc2]) b2 ->
                  
          get env_loc1' H1' = Some (Env rho_clo1) ->
          find_def f1 B1 = Some (ft, xs1, e1) ->
          
          def_closures B1 B1 rho_clo1 H1' env_loc1' =  (H1'', rho_clo2) ->
          setlist xs1 vs1 rho_clo2 = Some rho_clo3 ->

          (* b env_loc1 = env_loc2 /\ *)
          exists (xs2 : list var) (e2 : exp) (rho2' : env),
            find_def f2 B2 = Some (ft, xs2, e2) /\
            Some rho2' = setlist xs2 ((Loc env_loc2') :: vs2) (def_funs B2 B2 (M.empty _)) /\
            (forall i j' b',
               (i < k)%nat -> (j' <= j)%nat ->
               let R v1 v2 := cc_approx_val i j' IP P b' (Res (v1, H1'')) (Res (v2, H2')) in
               f_eq_subdomain (reach' H1' [set env_loc1']) (b2 ∘ b ∘ b1) b' ->
               Forall2 R vs1 vs2 ->
               cc_approx_exp cc_approx_val
                             i j'
                             (IP i) IP
                             (fun p1 p2 =>
                                P i (H1'', rho_clo3, e1, fst p1, snd p1) (H2', rho2', e2, fst p2, snd p2)) P
                             (e1, rho_clo3, H1'') (e2, rho2', H2'))

      | _, _ => False
    end.
  
  (** Unfold the recursion. A more compact definition of the value relation. *)
  Definition cc_approx_val' (k : nat) (j : nat) (IP : GIInv) (P : GInv) (b : Inj) (r1 r2 : ans) : Prop :=
    match r1, r2 with
      | OOT, OOT => True (* Both programs timeout *)
      | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
        match v1, v2 with
          | Loc l1, Loc l2 =>
            match get l1 H1, get l2 H2 with
              | Some b1, Some b2 =>
                b l1 = l2 /\
                cc_approx_block k j IP P b b1 H1 b2 H2
              | _, _ => False
            end
          | _, _ => False
        end
      | _, _ => False
    end.
  
  (** Correspondence of the two definitions *)
  Lemma cc_approx_val_eq (k j : nat) IP P b (v1 v2 : ans) :
    cc_approx_val k j IP P b v1 v2 <-> cc_approx_val' k j IP P b v1 v2.
  Proof.
    destruct k as [ | k ]; destruct j as [| j];
    destruct v1 as [[[l1 | lf1 f1] H1] | |]; destruct v2 as [[[l2 | lf2 f2] H2] | |];
    try (now split; intros; contradiction);
    try (now simpl; eauto). 
    - split; simpl; unfold cc_approx_block;
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now firstorder.
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; try now firstorder. 
        destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        intros [Heqb [Hin Hyp]]. split; eauto. split; eauto.
        intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft
               e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2  Hget Hfind Hdef Hset.
        edestruct Hyp
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try now eauto. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; firstorder. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + now firstorder.
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heqb [Him Hyp]]. split; eauto. split; eauto.
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft
                 e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; eauto. }
    - split; unfold cc_approx_block; simpl;
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now firstorder.
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; try now firstorder. 
        + intros [Heq1 [Heq2 Hi]]; split; [ eassumption | split; [eassumption |]].
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite !Heqi in Hap.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heq1 [Him Hyp]].
          subst. split; eauto. split; eauto.
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1
                 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2  Hget Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto). }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; firstorder. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + intros [Heq1 [Heq2 Hi]].
          subst. split; [ reflexivity | split; [ reflexivity |]].
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega. rewrite !Heqi.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heqb [Him Hyp]]. split; eauto. split; eauto.
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1
                 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto). }
    - split; unfold cc_approx_block; simpl;
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now firstorder.
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; try now firstorder.
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heqb [Him Hyp]].
          subst. split; eauto. split; eauto.
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1
                 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset.          
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          simpl. intros i j' b' Hleq Hleq' Hfeq Hall.
          assert (Heqi : k - (k - i) = i) by omega.
          setoid_rewrite <-  Heqi at 2 4. eapply Hi; eauto.
          eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap. rewrite Heqi. eassumption.
      }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; firstorder. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + intros [Heq1 [Heq2 Hi]].
          subst. split; [ reflexivity | split; [ reflexivity |]]; eauto.
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heq1 [Him Hyp]].
          subst. split; eauto. split; eauto.
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft
                 e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          intros i j b' Hleq Hleq' Hall Hfeq.
          assert (Heqi : k - (k - i) = i) by omega.
          setoid_rewrite Heqi. eapply Hi; eauto.
          eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap. rewrite <- Heqi. eassumption.
      }
    - split; unfold cc_approx_block; simpl;
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now firstorder.
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; try now firstorder.  
        + intros [Heq1 [Heq2 Hi]]; split; [ eassumption | split; [eassumption |]].
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite !Heqi in Hap.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heqb [Him Hyp]]. split; eauto. split; eauto.
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1
                 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          simpl. intros i j' b' Hleq Hleq' Hfeq Hall.
          assert (Heqi : k - (k - i) = i) by omega.
          setoid_rewrite <- Heqi at 2 4. eapply Hi; eauto.
          eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap. rewrite Heqi. eassumption.
      }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; firstorder. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + intros [Heq1 [Heq2 Hi]].
          subst. split; [ reflexivity | split; [ reflexivity |]]; eauto.
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega. rewrite !Heqi.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Hb [Him Hyp]].
          split; eauto. split; eauto.
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1
                 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2  Hget Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          intros i j' b' Hleq Hall Hfeq Hall'.
          assert (Heqi : k - (k - i) = i) by omega.
          setoid_rewrite Heqi. eapply Hi; eauto.
          eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap. rewrite <- Heqi. eassumption. }
  Qed.
  
  Opaque cc_approx_val.

  (** * Environment relations *)
  
  (** Environment relation for a single point (i.e. variable) : 
    * ρ1 ~_k^x ρ2 iff ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
    Definition cc_approx_var_env (k j : nat) IP P b (H1 : heap block) (rho1 : env)
               (H2 : heap block) (rho2 : env) (x y : var) : Prop :=
      forall l1, 
        M.get x rho1 = Some l1 -> 
        exists l2, M.get y rho2 = Some l2 /\
              cc_approx_val' k j IP P b (Res (l1, H1)) (Res (l2, H2)).
    
    (** Environment relation for a set of points (i.e. predicate over variables) :
     * ρ1 ~_k^S ρ2 iff 
     *  forall x, S x -> ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
    Definition cc_approx_env_P (S : Ensemble var) k j IP P b (c1 c2 : heap block * env) :=
      let (H1, rho1) := c1 in
      let (H2, rho2) := c2 in
      forall (x : var), S x -> cc_approx_var_env k j IP P b H1 rho1 H2 rho2 x x.

    
  Notation "p1 ≺ ^ ( k ; j ; IP ; P ; b ) p2" := (cc_approx_val' k j IP P b p1 p2)
                                                   (at level 70, no associativity).
  
  Notation "p1 ⋞ ^ ( R ; k ; j ; IP ; P ; b ) p2" := (cc_approx_env_P R k j IP P b p1 p2)
                                                      (at level 70, no associativity).
  
  
  (** Environment relation for the whole domain of definition :
    * ρ1 ~_k ρ2 iff forall x, ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
  Definition cc_approx_env (k j : nat) IP P b c1 c2 : Prop :=
    c1 ⋞ ^ (Full_set _; k; j; IP; P; b) c2.
   
  (** * Environment Invariants for Closure Conversion *)
  
  (** Naming conventions in the following  :

     [Scope] : The set of variables currently in scope.
 
     [Funs]  : The set of variables in the current block of mutually recursive
               functions.

     [FVs]   : The list of free variables (needs to be ordered).

     [Γ]     : The formal parameter of the environment after closure conversion. *)
  
  (** Invariant about the free variables *) 
  Definition FV_inv (k : nat) (IP : GIInv) (P : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) (c : cTag) (Γ : var) (FVs : list var) : Prop :=
    forall (x : var) N (v : value),
      ~ In _ Scope x ->
      ~ In _ Funs x -> 
      nthN FVs N = Some x ->
      M.get x rho1 = Some v ->
      exists (vs : list value) (l : loc) (v' : value),
        M.get Γ rho2 = Some (Loc l) /\
        get l H2 = Some (Constr c vs) /\
        nthN vs N = Some v' /\
        (forall j, Res (v, H1) ≺ ^ ( k ; j ; IP ; P ; b) Res (v', H2)).
  
  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv (k : nat) (IP : GIInv) (P : GInv) (b : Inj)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) (σ : var -> var) (c : cTag) (Γ : var)  : Prop :=
    forall (f : var) (vf1 : value),
      ~ In _ Scope f ->
      In var Funs f ->
      M.get f rho1 = Some vf1 ->
      exists (vf1 venv : value),
        ~ In _ Scope (σ f) /\
        M.get (σ f) rho2 = Some vf1 /\
        M.get Γ rho2 = Some venv /\
        forall l_clo vs,
          get l_clo H1 = Some (Constr c (vf1 :: venv :: vs)) ->
          (forall j, (Res (vf1, H1)) ≺ ^ ( k ; j; IP ; P ; b) (Res (Loc l_clo, H2))).

  (** Versions without the logical relation. Useful when we're only interested in other invariants. *)
  
  (** Invariant about the free variables *) 
  Definition FV_inv_weak (rho1 : env) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) (c : cTag) (Γ : var) (FVs : list var) : Prop :=
    forall (x : var) N (v : value),
      ~ In _ Scope x ->
      ~ In _ Funs x -> 
      nthN FVs N = Some x ->
      M.get x rho1 = Some v ->
      exists (vs : list value) (l : loc) (v' : value),
        M.get Γ rho2 = Some (Loc l) /\
        get l H2 = Some (Constr c vs) /\
        nthN vs N = Some v'.
  
  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv_weak (rho1 : env)  (rho2 : env)
             (Scope Funs : Ensemble var) (σ : var -> var) (c : cTag) (Γ : var)  : Prop :=
    forall (f : var) (vf1 : value),
      ~ In _ Scope f ->
      In var Funs f ->
      M.get f rho1 = Some vf1 ->
      exists (vf1 venv : value),
        ~ In _ Scope (σ f) /\
        M.get (σ f) rho2 = Some vf1 /\
        M.get Γ rho2 = Some venv.

  Section LogRelLemmas.
    
    Context (LIP : IInv)
            (GIP : GIInv)
            (LP : Inv)
            (GP : GInv)
            (b : Inj).
    
  (** * Monotonicity Properties *)
  
  (** The environment relation is antimonotonic in the set of free variables *) 
  Lemma cc_approx_env_P_antimon (S1 S2 : Ensemble var) (k j : nat)
        (c1 c2 : (heap block) * env) :
    c1 ⋞ ^ ( S2 ; k ; j ; GIP ; GP ; b) c2 ->
    S1 \subset S2 ->
    c1 ⋞ ^ ( S1 ; k ; j ; GIP ; GP ; b) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre Hin x Hin'. eapply Hpre; eapply Hin; eauto.
  Qed.
  
  (** The expression relation is monotonic in the local invariant *)
  Lemma cc_approx_exp_rel_mon k j LIP1 GIP1 (LP1 LP2 : Inv) (GP1 : GInv)
        (p1 p2 : exp * env * heap block) :
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP1 ; GP1 ) p2 ->
    inclusion _ LP1 LP2 ->
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP2 ; GP1 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2].
    intros Hcc Hin b1 b2 H1' H2' rho1' rho2' v1 c1 m1 HH1 Hr1 HH2 Hr2 Hip Hleq Hstep Hstuck.
    edestruct Hcc as [v2 [c2 [m2 [b' [Hstep' [Hinj [HInv Hval]]]]]]]; eauto.
    repeat eexists; eauto.
  Qed.
  
  (** The logical relation respects equivalence of the global invariant *)
  
  Lemma cc_approx_exp_same_rel_IH k j LIP1 GIP1 LP1 (GP1 GP2 : GInv) p1 p2 :
    (forall m b r1 r2,
       m <= k ->
       r1 ≺ ^ (m ; j ; GIP1 ; GP1 ; b) r2 ->
       r1 ≺ ^ (m ; j ; GIP1 ; GP2 ; b) r2) ->
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP1 ; GP1 ) p2 ->
    (forall i, same_relation _ (GP1 i) (GP2 i)) ->
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP1 ; GP2 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2].
    intros IH Hcc Hin b1 b2 H1' H2' rho1' rho2' v1 c1 m1 HH1 Hr1 HH2 Hr2 Hip Hleq Hstep Hstuck.
    edestruct Hcc as [v2 [c2 [m2 [b' [Hstep2 [Hinj [HP Hval]]]]]]]; eauto.
    repeat eexists; eauto.
    rewrite cc_approx_val_eq.
    eapply IH; eauto. omega.
    rewrite <- cc_approx_val_eq; eauto.    
  Qed.
  
  Opaque cc_approx_exp.
  
  Lemma cc_approx_val_same_rel (k j : nat) (GP1 GP2 : GInv) (b1 : Inj) r1 r2 :
    r1 ≺ ^ (k ; j ; GIP ; GP1 ; b1) r2 ->
    (forall i, same_relation _ (GP1 i) (GP2 i)) ->
    r1 ≺ ^ (k ; j ; GIP ; GP2 ; b1) r2.
  Proof.
    revert j b1 GP1 GP2 r1 r2.
    induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1.
    intros b' GP1 GP2 r1 r2.
    destruct r1 as [[[l1 | lf1 f1] H1] | |]; destruct r2 as [[[l2 | lf2 f2] H2] | |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
    destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
      destruct b2 as [c2 vs2 | | ]; eauto; intros [Heq Hcc] Hrel; split; eauto.
    - destruct Hcc as [Heq' Hcc]. split; [ eassumption |].
      intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
      intros x1 x2 Hap.
      rewrite cc_approx_val_eq in *. eapply IHj; try eassumption.
    - destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
      destruct Hcc as [Him Hcc]. split; eauto.
      intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1
             vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset.
      edestruct Hcc
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
      do 3 eexists; split; [ | split ]; try (now eauto).
      intros i j' b'' Hleq Hleq'. simpl. intros Hfeq Hrel'.
      eapply cc_approx_exp_same_rel_IH with (GP1 := GP1); try eassumption.
      + intros; eapply IHk. omega. eassumption. eassumption.
      + eapply cc_approx_exp_rel_mon. eapply Hi. eassumption.
        eassumption. eassumption.
        eapply Forall2_monotonic; [| eassumption ].
        intros. rewrite cc_approx_val_eq.
        eapply IHk; eauto. now rewrite <- cc_approx_val_eq; simpl in *; eauto.
        intros. split; now eapply Hrel.
        intros x y. now eapply Hrel.
  Qed.
  
  Transparent cc_approx_exp.
  
  Lemma cc_approx_exp_same_rel (P : relation nat) k j (GP' : GInv)
        p1 p2 :
    p1 ⪯ ^ ( k ; j ; LIP ; GIP ; LP ; GP ) p2 ->
    (forall i, same_relation _ (GP i) (GP' i)) ->
    p1 ⪯ ^ ( k ; j ; LIP ; GIP ; LP ; GP' ) p2.
  Proof.
    intros Hcc Hin. eapply cc_approx_exp_same_rel_IH; try eassumption.
    intros. eapply cc_approx_val_same_rel in Hin; eauto.
  Qed.
  
  (** The value relation is monotonic in the step index *)
  Lemma cc_approx_val_monotonic (k m j : nat) (r1 r2 : ans) b' :
    r1 ≺ ^ (k; j; GIP ; GP; b') r2 ->
    m <= k ->
    r1 ≺ ^ (m; j; GIP ; GP; b') r2.
  Proof.
    revert j k r1 r2. induction m as [m IHk] using lt_wf_rec1.
    intros j. induction j as [j IHj] using lt_wf_rec1.
    intros k r1 r2.
    destruct r1 as [[[l1 | lf1 f1] H1] | |]; destruct r2 as [[[l2 | lf2 f2] H2] | |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    - destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
      intros [Heq Hcc] Hleq. split; [ eassumption |].
      destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
      + destruct Hcc as [Heq' Hi]; split; [ eassumption |].
        intros i Hleq'. simpl.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; try eassumption.
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hcc as [Him Hcc]. split; eauto.
        intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2'
               xs1 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset.
        edestruct Hcc
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi'); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i j' Hleq' Hleq'' R Hfeq Hall. 
        eapply Hi'; try eassumption. omega.
  Qed.
  
  (** The expression relation is anti-monotonic in the step index *)
  Lemma cc_approx_exp_monotonic (k m j : nat) p1 p2 :
    p1 ⪯ ^ ( k ; j ; LIP ; GIP ; LP ; GP ) p2 ->
    m <= k ->
    p1 ⪯ ^ ( m ; j ; LIP ; GIP ; LP ; GP ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1]; destruct p2 as [[e2 H2] rho2].
    intros Hpre Hleq b1 b2 H1' H2' rho1' rho2' v1 c1 m1 HH1 Hr1 HH2 Hr2 HIP Hleq' Hstep Hstuck.
    edestruct (Hpre b1 b2 H1' H2' rho1' rho2' v1 c1)
      as [v2 [c2 [m2 [b2' [Hstep2 [Hinj [Hleq2 H3]]]]]]]; eauto.
    omega. do 4 eexists; repeat split; eauto.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_monotonic; eauto. omega.
  Qed.
  
  
  (** The environment relations are anti-monotonic in the step index *)
  Lemma cc_approx_env_P_monotonic (R : Ensemble var) (k m j : nat)
        c1 c2 :
    c1 ⋞ ^ ( R ; k ; j ; GIP ; GP ; b ) c2 ->
    m <= k ->
    c1 ⋞ ^ ( R ; m ; j ; GIP ; GP ; b ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hcc Hleq x HP v Hget.
    edestruct Hcc as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.
  
  Lemma cc_approx_env_monotonic (k m j : nat) c1 c2 :
    cc_approx_env k j GIP GP b c1 c2 ->
    m <= k ->
    cc_approx_env m j GIP GP b c1 c2.
  Proof.
    intros Hleq H. eapply cc_approx_env_P_monotonic; eauto.
  Qed.  
  
  (** The value relation is monotonic in the heap index *)
  Lemma cc_approx_val_j_monotonic GIP' GP' (k i j : nat) (r1 r2 : ans) b' :
    r1 ≺ ^ (k; j; GIP' ; GP' ; b') r2 ->
    i <= j ->
    r1 ≺ ^ (k; i; GIP' ; GP' ; b') r2.
  Proof.
    destruct r1 as [[[l1 | lf1 f1] H1] | |]; destruct r2 as [[[l2 | lf2 f2] H2] | |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
    intros [Heq Hcc] Hleq. split; [ eassumption |].
    destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
      destruct b2 as [c2 vs2 | | ]; eauto.
    + destruct Hcc as [Heq' Hi]; split; [ eassumption |].
      intros i' Hleq'. simpl. eapply (Hi i'); omega.
    + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
      destruct Hcc as [Him Hcc]. split; eauto.
      intros j' Hj'. eapply Him; omega.
      intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2'
             xs1 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset.
      edestruct Hcc
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi'); eauto.
      do 3 eexists; split; [ | split ]; try (now eauto).
      intros i' j' Hleq' Hleq'' R Hall. eapply Hi'. eassumption.
      omega.
  Qed.
  
  (** The expression relation is anti-monotonic in the step index *)
  Lemma cc_approx_exp_j_monotonic (k j j' : nat) p1 p2 :
    p1 ⪯ ^ ( k ; j ; LIP ; GIP ; LP ; GP ) p2 ->
    j' <= j ->
    p1 ⪯ ^ ( k ; j' ; LIP ; GIP ; LP ; GP ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1]; destruct p2 as [[e2 H2] rho2].
    intros Hpre Hleq b1 b2 H1' H2' rho1' rho2' v1 c1 m1 HH1 Hr1 HH2 Hr2 HIP Hleq' Hstep Hstuck.
    edestruct (Hpre b1 b2 H1' H2' rho1' rho2' v1 c1)
      as [v2 [c2 [m2 [b2' [Hstep2 [Hinj [Hleq2 H3]]]]]]]; eauto.
    do 4 eexists; repeat split; eauto.
    eapply injective_subdomain_antimon. eassumption.
    destruct v1 as [[l H] | | ]; simpl; try now reflexivity.
    now eapply reach_n_monotonic; eauto.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.
  
  
  (** The environment relations are anti-monotonic in the step index *)
  Lemma cc_approx_env_P_j_monotonic (R : Ensemble var) (k j j' : nat)
        c1 c2 :
    c1 ⋞ ^ ( R ; k ; j ; GIP ; GP ; b ) c2 ->
    j' <= j ->
    c1 ⋞ ^ ( R ; k ; j' ; GIP ; GP ; b ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hcc Hleq x HP v Hget.
    edestruct Hcc as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.
  
  Lemma cc_approx_env_j_monotonic (k j' j : nat) c1 c2 :
    cc_approx_env k j GIP GP b c1 c2 ->
    j' <= j ->
    cc_approx_env k j' GIP GP b c1 c2.
  Proof.
    intros Hleq H. eapply cc_approx_env_P_j_monotonic; eauto.
  Qed.

  (** * Set lemmas *)
  
  Lemma cc_approx_env_Empty_set (k j : nat) c1 c2 :
    c1 ⋞ ^ ( Empty_set var ; k ; j ; GIP ; GP ; b ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    firstorder.
  Qed.
  
  Lemma cc_approx_env_P_union (P1 P2 : Ensemble var) (k j : nat) c1 c2 :
    c1 ⋞ ^ ( P1 ; k ; j ; GIP ; GP ; b ) c2 ->
    c1 ⋞ ^ ( P2 ; k ; j ; GIP ; GP ; b ) c2 ->
    c1 ⋞ ^ ( P1 :|: P2 ; k ; j ; GIP ; GP ; b) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre1 Hpre2 x HP2. inv HP2; eauto.
  Qed.
  
  Lemma cc_approx_env_P_inter_l (P1 P2 : Ensemble var) (k j : nat) c1 c2 :
    c1 ⋞ ^ ( P1 ; k ; j ; GIP ; GP ; b ) c2 ->
    c1 ⋞ ^ ( P1 :&: P2 ; k ; j ; GIP ; GP ; b ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre x HP2. inv HP2; eauto.
  Qed.
  
  Lemma cc_approx_env_P_inter_r (P1 P2 : Ensemble var) (k j : nat) c1 c2 :
    c1 ⋞ ^ ( P2 ; k ; j ; GIP ; GP ; b ) c2 ->
    c1 ⋞ ^ ( P1 :&: P2 ; k ; j ; GIP ; GP ; b ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre x HP2. inv HP2; eauto.
  Qed.
  
  (** * Preservation under enviroment extension lemmas *)
  
  Lemma cc_approx_var_env_set_eq :
    forall (k j : nat) (rho1 rho2 : env) (H1 H2 : heap block)
      (x y : var) (v1 v2 : value),
      (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b ) (Res (v2, H2)) ->
      cc_approx_var_env k j GIP GP b H1 (M.set x v1 rho1) H2 (M.set y v2 rho2) x y.
  Proof.
    intros rho1 rho2 H1 H2 k j x y v1 v2 Hval x' Hget.
    rewrite M.gss in Hget. inv Hget. eexists.
    rewrite M.gss. split; eauto.
  Qed.
  
  Lemma cc_approx_var_env_set_neq :
    forall (k j : nat)  (rho1 rho2 : env) (H1 H2 : heap block)
      (x1 x2 y1 y2 : var) (v1 v2 : value),
      cc_approx_var_env k j GIP GP b H1 rho1 H2 rho2 y1 y2 ->
      y1 <> x1 -> y2 <> x2 ->
      cc_approx_var_env k j GIP GP b H1 (M.set x1 v1 rho1) H2 (M.set x2 v2 rho2) y1 y2.
  Proof. 
    intros k j rho1 rho2 H1 H2 x1 x2 y1 y2 v1 v2 Hval Hneq Hneq' x' Hget.
    rewrite M.gso in *; eauto.
  Qed.
  
  Lemma cc_approx_var_env_set :
    forall (k j : nat)  (rho1 rho2 : env) (H1 H2 : heap block)
      (x y : var) (v1 v2 : value),
      cc_approx_var_env k j GIP GP b H1 rho1 H2 rho2 y y ->
      (Res (v1, H1)) ≺ ^ (k; j; GIP ; GP; b) (Res (v2, H2)) ->
      cc_approx_var_env k j GIP GP b H1 (M.set x v1 rho1) H2 (M.set x v2 rho2) y y.
  Proof.
    intros k j rho1 rho2 H1 H2 x y v1 v2 Hvar Hval.
    destruct (peq y x); subst.
    - apply cc_approx_var_env_set_eq; eauto.
    - apply cc_approx_var_env_set_neq; eauto.
  Qed.
  
  (** Extend the related environments with a single point *)
  Lemma cc_approx_env_P_set (S : Ensemble var) (k j : nat)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v1 v2 : value) :
      (H1, rho1) ⋞ ^ ( S \\ [set x] ; k ; j ; GIP ; GP ; b) (H2, rho2) ->
      (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP; b) (Res (v2, H2)) ->
      (H1, M.set x v1 rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b) (H2, M.set x v2 rho2).
  Proof.
    intros Henv Hval x' HP v1' Hget.
    rewrite M.gsspec in Hget. destruct (peq x' x); subst.
    - inv Hget. eexists. rewrite M.gss. split; eauto.
    - apply Henv in Hget; eauto. destruct Hget as [v2' [Heq Hpre]].
      eexists; split; eauto. rewrite M.gso; eauto. constructor; eauto.
      intros Hin. inv Hin. congruence.
  Qed.
  
  (** Extend the related environments with a list *)
  Lemma cc_approx_env_P_setlist_l (S : Ensemble var) (k j : nat)
        (rho1 rho2 rho1' rho2' : env) (H1 H2 : heap block) xs (vs1 vs2 : list value) :
    (H1, rho1) ⋞ ^ ( S \\ (FromList xs) ; k ; j ; GIP ; GP ; b ) (H2, rho2) ->
    Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b ) (Res (v2, H2))) vs1 vs2 ->
    setlist xs vs1 rho1 = Some rho1' ->
    setlist xs vs2 rho2 = Some rho2' ->
    (H1, rho1') ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, rho2').
  Proof.
    intros Hcc Hall Hset1 Hset2 x HP v Hget.
    destruct (in_dec var_dec x xs).
    - edestruct (@setlist_Forall2_get value) as [v1 [v2 [Hget1 [Hget2 HP']]]];
      try eassumption. subst_exp. repeat eexists; eauto.
    - erewrite <- setlist_not_In in Hget; eauto.
      edestruct Hcc as [v2 [Hget' Hpre']]; eauto.
      constructor; eauto. repeat eexists; eauto.
      erewrite <- setlist_not_In; eauto.
  Qed.
  
  Lemma cc_approx_env_P_set_not_in_P_l (S : Ensemble var) (k j : nat) 
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v : value) :
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, rho2) ->
    ~ x \in S ->
    (H1, M.set x v rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, rho2).
  Proof. 
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    destruct (peq y x); subst.
    - contradiction.
    - rewrite M.gso in Hget; eauto.
  Qed.
  
  Lemma cc_approx_env_P_set_not_in_P_r (S : Ensemble var) (k j : nat)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v : value) :
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, rho2) ->
    ~ x \in S ->
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, M.set x v rho2).
  Proof. 
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    exists v''. rewrite M.gsspec.
    destruct (peq y x); subst.
    - contradiction.
    - eauto.
  Qed.
  
  (** * The logical relation respects function extensionality *)

  (* TODO move *)
  Lemma f_eq_subdomain_compose_compat {A B C} S (f1 f2: A -> B) (g1 g2 : B -> C) :
     f_eq_subdomain S f1 f2 ->
     f_eq_subdomain (image f1 S) g1 g2 ->
     f_eq_subdomain S (g1 ∘ f1) (g2 ∘ f2).
   Proof.
     intros Heq1 Heq2 x Hin. unfold compose.
     rewrite <- Heq1; eauto. rewrite Heq2. reflexivity.
     eexists; split; eauto.
   Qed.

  Instance Proper_cc_approx_val_f_eq :
    Proper (eq ==> eq ==> eq ==> eq ==> f_eq ==> eq ==> eq ==> iff) cc_approx_val'.
  Proof.
    clear.
    intros k' k Heq1 j' j Heq2  GI GI' Heq3 II II' Heq4 b1 b2 Heq5
           r1' r1 Heq6 r2' r2 Heq7; subst.
    revert j b1 b2 Heq5 r1 r2. induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1. intros b1 b2 Heq5 r1 r2.
    simpl.
    destruct r1 as [[v1 H1] | |];  destruct r2 as [[v2 H2] | |]; try now eauto.
    destruct v1 as [l1 | ? ? ]; destruct v2 as [l2 | ? ?]; try now eauto.
    split; intros Hres.
    - simpl in *. destruct (get l1 H1) as [bl1 |]; eauto; destruct (get l2 H2) as [bl2 |]; eauto.
      destruct Hres as [Heq Hres]; split; eauto. rewrite <- Heq5; eassumption.
      destruct bl1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct bl2 as [c2 vs2 | | ]; eauto.
      + destruct Hres as [Heq1 Hi]. split; eauto.
        intros i' Hleq.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; eauto. symmetry. eassumption.
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hres as [Him Hres]. split. setoid_rewrite <- Heq5. eassumption.
        intros b1' b2' tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1
               vs1 vs2 Heq1' Hr1' Heq2 Hr2 Hget Hfind Hdef Hset.
        edestruct Hres
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i' j' b' Hleq Hleq' HR Hfeq Hall. eapply Hi. eassumption. eassumption.
        eapply Equivalence_Transitive; [| eassumption ]. eapply f_eq_subdomain_compose_compat.
        reflexivity. eapply f_eq_subdomain_compose_compat; [| reflexivity ].
        rewrite Heq5. reflexivity.
        eapply Forall2_monotonic; [| now eauto ].
        unfold HR. intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eassumption.
    - simpl in *.
      destruct (get l1 H1) as [bl1 |]; eauto. destruct (get l2 H2) as [bl2 |]; eauto.
      destruct Hres as [Hbeq Hres]; split. rewrite Heq5. eassumption.
      destruct bl1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct bl2 as [c2 vs2 | | ]; eauto.
      + destruct Hres as [Heq1 Hi]. split; eauto.
        intros i' Hleq.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; eauto.
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hres as [Him Hres].
        split; eauto. setoid_rewrite Heq5. eassumption.
        intros b1' b2' tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1
               vs1 vs2 Heq1' Hr1' Heq2 Hr2 Hget Hfind Hdef Hset.
        edestruct Hres
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i' j' b' Hleq Hleq' HR Hfeq Hall. eapply Hi. eassumption. eassumption.
        eapply Equivalence_Transitive; [| eassumption ]. eapply f_eq_subdomain_compose_compat.
        reflexivity. eapply f_eq_subdomain_compose_compat; [| reflexivity ].
        rewrite Heq5. reflexivity. eapply Forall2_monotonic; [| now eauto ].
        unfold HR. intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eassumption.
  Qed.

  Instance Proper_cc_approx_env_P_f_eq :
    Proper (eq ==> eq ==> eq ==> eq ==> eq ==> f_eq ==> eq ==> eq ==> iff) cc_approx_env_P.
  Proof.
    intros S' S Heq k' k Heq1 j' j Heq2  GI GI' Heq3 II II' Heq4 b1 b2 Heq5
           [H1' rho1'] [H1 rho1] Heq6 [H2' rho2'] [H2 rho2] Heq7; inv Heq6; inv Heq7; subst.
    split; intros Hcc x Hin v Hget.
    edestruct Hcc as [l2 [Hget' Hres]]; eauto. eexists; split; eauto.
    rewrite <- Heq5. eassumption.
    edestruct Hcc as [l2 [Hget' Hres]]; eauto. eexists; split; eauto.
    rewrite Heq5. eassumption.
  Qed.    

    
  Lemma cc_approx_val_image_eq (k j : nat) (β : Inj)  (H1 H2 : heap block)
        (v1 v2 : value) :
    (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β) (Res (v2, H2)) ->
    image β ((post H1 ^ j) (val_loc v1)) <--> ((post H2 ^ j) (val_loc v2)).
  Proof with now eauto with Ensembles_DB.
    revert j v1 v2 H1 H2.
    induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1.
    intros v1 v2 H1 H2.
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    intros Hcc.
    destruct (get l1 H1) as [b1'|] eqn:Hget1; destruct (get l2 H2) as [b2'|] eqn:Hget2; try contradiction.
    destruct Hcc as [Hbs Hcc].
    destruct b1' as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; try contradiction;
    destruct b2' as [c2 vs2 | | ]; try contradiction.
    + destruct Hcc as [Heqc Hcc]; subst.
      destruct j.
      * simpl. rewrite !image_Singleton. reflexivity.
      * replace (S j) with (j + 1) by omega.
        rewrite !app_plus. unfold compose. simpl.
        rewrite (proper_post_n H1);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
        rewrite (proper_post_n H2);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
        specialize (Hcc j (NPeano.Nat.lt_succ_diag_r j)).
        clear Hget1 Hget2. induction Hcc; simpl.
        rewrite !post_n_Empty_set. rewrite !image_Empty_set. reflexivity.
        rewrite !post_n_Union, !image_Union.
        eapply Same_set_Union_compat. eapply IHj. omega.
        rewrite <- cc_approx_val_eq. eassumption.
        eapply IHHcc; eauto. 
    + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction.
      destruct Hcc as [Him Hcc].
      destruct j.
      * simpl. rewrite !image_Singleton. subst. reflexivity.
      * replace (S j) with (j + 1) by omega.
        rewrite !app_plus. unfold compose. simpl.
        rewrite (proper_post_n H1);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
        rewrite (proper_post_n H2);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
        simpl.
         rewrite (proper_post_n H1);
            [| rewrite !Union_Empty_set_neut_l; reflexivity ].
        rewrite (proper_post_n H2);
           [| rewrite !Union_Empty_set_neut_l, !Union_Empty_set_neut_r; reflexivity ].
        eapply Him. omega.
  Qed.
  
  Lemma cc_approx_var_env_image_eq
        (k j : nat) (β : Inj) 
        (H1 H2 : heap block) (rho1 rho2 : env) (x y : var) (v : value) :
    cc_approx_var_env k j GIP GP β H1 rho1 H2 rho2 x y ->
    M.get x rho1 = Some v -> 
    image β ((post H1 ^ j) (env_locs rho1 [set x])) <--> (post H2 ^ j) (env_locs rho2 [set y]).
  Proof.
    intros Hcc Hget.
    edestruct Hcc as [v' [Hget' Hv]]; eauto.
    eapply Same_set_trans. eapply image_Proper_Same_set. reflexivity.
    eapply proper_post_n.
    rewrite !env_locs_Singleton; eauto. reflexivity.
    rewrite cc_approx_val_image_eq; try eassumption.
    eapply proper_post_n.
    rewrite !env_locs_Singleton; eauto. reflexivity.
  Qed.
  
  Lemma cc_approx_val_image_reach_n_eq (k j : nat) (β : Inj)  (H1 H2 : heap block)
        (v1 v2 : value) :
    (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β) (Res (v2, H2)) ->
    image β (reach_n H1 j (val_loc v1)) <--> (reach_n H2 j (val_loc v2)).
  Proof.
    intros Hres. split.
    - intros l' [l [[m [Hm Hr]] Hin]].
      eapply cc_approx_val_j_monotonic in Hres; eauto. 
      eapply cc_approx_val_image_eq in Hres. eexists m.
      split; eauto. eapply Hres. eexists. split; eauto.
    - intros l' [m [Hm Hr]].
      eapply cc_approx_val_j_monotonic in Hres; eauto. 
      eapply cc_approx_val_image_eq in Hres. eapply Hres in Hr.
      destruct Hr as [l [Heql Hin]]. eexists; split; eauto.
      eexists; split; eauto.
  Qed.
    
  Lemma cc_approx_var_env_image_reach_n_eq
        (k j : nat) (β : Inj)
        (H1 H2 : heap block) (rho1 rho2 : env) (x y : var) (v : value) :
    cc_approx_var_env k j GIP GP β H1 rho1 H2 rho2 x y ->
    M.get x rho1 = Some v -> 
    image β (reach_n H1 j (env_locs rho1 [set x])) <-->
      reach_n H2 j (env_locs rho2 [set y]).
  Proof.
    intros Hcc Hget.
    edestruct Hcc as [v' [Hget' Hv]]; eauto.
    rewrite !env_locs_Singleton; eauto.
    rewrite cc_approx_val_image_reach_n_eq; try eassumption.
    reflexivity.
  Qed.
  
  Opaque cc_approx_exp.

  (** * The logical relation respects heap equivalences *)

  Lemma cc_approx_val_res_eq (k j : nat) (b' b1 b2 : Inj)  (H1 H2 H1' H2' : heap block)
        (v1 v2 v1' v2' : value) :
    (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b') (Res (v2, H2)) ->

    (v1, H1) ≈_(id, b1) (v1', H1') ->
    injective_subdomain (reach' H1' (val_loc v1')) b1 ->

    (v2, H2) ≈_(b2, id) (v2', H2') ->
    injective_subdomain (reach' H2 (val_loc v2)) b2 ->
    
    (Res (v1', H1')) ≺ ^ (k ; j ; GIP ; GP ; b2 ∘ b' ∘ b1 ) (Res (v2', H2')).
  Proof with now eauto with Ensembles_DB.
    revert j b' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'.
    induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1.
    intros b' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'.
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    intros Hcc (* Hwf1 Hwf2 Hl1 Hl2 *) Hres1 Hr1 Hres2 Hr2.
    destruct (get l1 H1) as [b1'|] eqn:Hget1; destruct (get l2 H2) as [b2'|] eqn:Hget2; try contradiction.

    destruct Hcc as [Hbs Hcc].
    destruct b1' as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; try contradiction;
    destruct b2' as [c2 vs2 | | ]; try contradiction.
        + rewrite res_equiv_eq in Hres1, Hres2.
      destruct v1' as [l1' | lf1' f1']; destruct v2' as [l2' | lf2' f2']; try contradiction.
      simpl in Hres1, Hres2. 
      rewrite Hget1 in Hres1. rewrite Hget2 in Hres2. clear b LIP LP.
      destruct (get l1' H1') as [b1'|] eqn:Hget1'; [| now firstorder ].
      destruct (get l2' H2') as [b2'|] eqn:Hget2'; [| now firstorder ].
      destruct b1' as [c1' vs1' | | ]; [|  now firstorder | now firstorder ].
      destruct b2' as [c2' vs2' | | ]; [|  now firstorder | now firstorder ].
      
      destruct Hres1 as [Heqi1 [Heqc1 Heqb1]].
      destruct Hres2 as [Heqi2 [Heqc2 Heqb2]]. subst. 
      destruct Hcc as [Heqc Hcc]; subst.
      split. unfold compose. rewrite <- Heqi1. unfold id. rewrite Heqi2. reflexivity.
      split; eauto. intros i Hleq.
      eapply Forall2_vertical_l_strong; [| | eassumption ].
      * simpl. intros. rewrite cc_approx_val_eq in *.
        rewrite <- (compose_id_neut_l (b2 ∘ b' ∘ b1)).
        rewrite <- Combinators.compose_assoc.
        eapply IHj; try eassumption.
        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold _ (val_loc (Loc l1'))).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. simpl. rewrite post_Singleton; [| eassumption ].
        eapply In_Union_list. eapply in_map. eassumption.
        reflexivity. firstorder.
      * simpl in Hcc. eapply Forall2_vertical_r_strong; [| | eassumption ].
        simpl. intros x y z Hin1 Hin2 Hin3 Hin Hres.
        rewrite cc_approx_val_eq.
        rewrite <- (compose_id_neut_r (b2 ∘ b')).
        eapply IHj; [ eassumption | | reflexivity | | | ]. 
        now eapply Hin.
        now firstorder. eapply Hres.
        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold _ [set b' l1]).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. simpl. rewrite post_Singleton; [| eassumption ].
        eapply In_Union_list. eapply in_map. eassumption.
        eapply Forall2_monotonic. intros x1 x2 HR. rewrite <- cc_approx_val_eq.
        now eapply HR. eapply Hcc; eassumption.
    + simpl in  Hcc. destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction. 
      destruct v1' as [l1' | lf1' f1']; destruct v2' as [l2' | lf2' f2'];
      try (rewrite res_equiv_eq in Hres2; rewrite res_equiv_eq in Hres1; contradiction). 
      rewrite res_equiv_eq in Hres2; rewrite res_equiv_eq in Hres1.
      simpl in Hres1, Hres2.
      rewrite Hget1 in Hres1. rewrite Hget2 in Hres2.
      destruct Hres1 as [Hptr1 Henv1].
      destruct Hres2 as [Heqc2 Hall]. subst. unfold id in Hptr1, Heqc2. subst.

      destruct (get l1' H1') as [b1'|] eqn:Hget1'; try contradiction. 
      destruct (get (b2 (b' (b1 l1'))) H2') as [b2'|] eqn:Hget2'; try contradiction.
      split. unfold compose. reflexivity.

      destruct b1' as [c1' vs1' | | ]; try contradiction.
      destruct b2' as [c2' vs2' | | ]; try contradiction.

      destruct Hall as [Hceq Hall].
      destruct Henv1 as [Hres Hlocs]. subst. rewrite res_equiv_eq in *.
      destruct v as [l3' | lf3' f3']; destruct v0 as [l4' | lf4' f4']; try contradiction.
      inv Hall. inv H5. inv H7.
      rewrite res_equiv_eq in *. 
      destruct y as [l5' | lf5' f5']; destruct y0 as [l6' | lf6' f6']; try contradiction.
      destruct Hcc as [Him Hcc]. split; eauto.
      
      rewrite <- res_equiv_eq in *.       
      intros j' Hlt. rewrite !image_compose.
      eapply res_equiv_image_post with (i := j') in Hlocs. simpl in Hlocs.
      rewrite <- Hlocs, image_id, (Him j' Hlt).
      eapply res_equiv_image_post with (i := j') in H4. simpl in H4.
      rewrite H4, image_id. reflexivity.

      simpl in H3. inv H3.
      
      subst. simpl in Hres. inv Hres.
      intros b1' b2' tc1 tc2 tc3 H3 H3' H4' env_loc1' env_loc2' xs1 ft
             e1 vs1 vs2 Hres1 Hinj1 Hres2 hinj2 Hget Hfind Hdef Hset.
 
      rewrite <- res_equiv_eq in *. 
      edestruct Hcc as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi)
      ; [| | | | eassumption | eassumption | eassumption | eassumption | ].
      * eapply res_equiv_f_compose; [| eassumption ].
        rewrite compose_id_neut_r. eassumption.
      * eapply injective_subdomain_compose. eassumption.
        eapply res_equiv_image_reach in Hres1.
        rewrite image_id in Hres1. rewrite <- Hres1.
        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold H1' (val_loc (Loc l1'))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl. rewrite post_Singleton; eauto... 
      * symmetry. eapply res_equiv_f_compose; [| symmetry; eassumption ].
        symmetry. rewrite compose_id_neut_r. eassumption.
      * eapply injective_subdomain_compose.
        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold H2 [set (b' _)]).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl. rewrite post_Singleton; eauto. simpl...
        eapply res_equiv_image_reach in H4.
        rewrite image_id in H4. rewrite H4. eassumption.
      * exists xs2, e2, rho2'. repeat split; eauto.
  Qed. 


  Lemma cc_approx_val_heap_eq (k j : nat) (β β1 β2 : Inj)
        (H1 H2 H1' H2' : heap block)
        (v1 v2 : value) :
    (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β) (Res (v2, H2)) ->
    (val_loc v1) |- H1 ≃_(id, β1) H1' ->
    injective_subdomain (reach' H1' (val_loc v1)) β1 ->
    (val_loc v2) |- H2 ≃_(β2, id) H2' ->
    injective_subdomain (reach' H2 (val_loc v2)) β2 ->
    (Res (v1, H1')) ≺ ^ (k ; j ; GIP ; GP ; β2 ∘ β ∘ β1) (Res (v2, H2')).
  Proof with now eauto with Ensembles_DB.
    intros.
    eapply cc_approx_val_res_eq; try eassumption.
    eapply heap_equiv_res_equiv; try eassumption. reflexivity.
    eapply heap_equiv_res_equiv; try eassumption. reflexivity.
  Qed.

  Lemma cc_approx_var_env_heap_env_equiv (S1 S2 : Ensemble var) (k j : nat) (β β1 β2 : Inj)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 rho1' rho2' : env) (x1 x2 : var) :
    cc_approx_var_env k j GIP GP β H1 rho1 H2 rho2 x1 x2 ->
    S1 |- (H1, rho1) ⩪_(id, β1) (H1', rho1') ->
    injective_subdomain (reach' H1' (env_locs rho1' S1)) β1 -> 
    S2 |- (H2, rho2) ⩪_(β2, id) (H2', rho2') ->
    injective_subdomain (reach' H2 (env_locs rho2 S2)) β2 ->
    x1 \in S1 -> x2 \in S2 ->
    cc_approx_var_env k j GIP GP (β2 ∘ β ∘ β1) H1' rho1' H2' rho2' x1 x2.
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
    eapply cc_approx_val_res_eq; try eassumption.
    now symmetry.
    eapply injective_subdomain_antimon. eassumption.
    eapply reach'_set_monotonic. now eapply get_In_env_locs; eauto.
    eapply injective_subdomain_antimon. eassumption.
    eapply reach'_set_monotonic. now eapply get_In_env_locs; eauto.
  Qed.
  
  Lemma cc_approx_env_P_heap_eq (S : Ensemble var) (k j : nat) (β β1 β2 : Inj)
        (P : GInv) (H1 H2 H1' H2' : heap block) (rho1 rho2 rho1' rho2' : env) :
    (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; β ) (H2, rho2) ->
    S |- (H1, rho1) ⩪_(id, β1) (H1', rho1') ->
    injective_subdomain (reach' H1' (env_locs rho1' S)) β1 -> 
    S |- (H2, rho2) ⩪_(β2, id) (H2', rho2') ->
    injective_subdomain (reach' H2 (env_locs rho2 S)) β2 ->    
    (H1', rho1') ⋞ ^ (S; k; j; GIP; GP; β2 ∘ β ∘ β1) (H2', rho2').
  Proof.
    intros Henv Heq1 Hinj1 Heq2 Hinj2 x HS.
    eapply cc_approx_var_env_heap_env_equiv; eauto.
  Qed.

  Lemma cc_approx_val_res_eq_rev (k j : nat) (b' b1 b2 : Inj)  (H1 H2 H1' H2' : heap block)
        (v1 v2 v1' v2' : value) :
    (Res (v1', H1')) ≺ ^ (k ; j ; GIP ; GP ; b2 ∘ b' ∘ b1 ) (Res (v2', H2')) ->

    (v1, H1) ≈_(id, b1) (v1', H1') ->
    injective_subdomain (reach' H1' (val_loc v1')) b1 ->

    (v2, H2) ≈_(b2, id) (v2', H2') ->
    injective_subdomain (reach' H2 (val_loc v2)) b2 ->

    (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b') (Res (v2, H2)).
  Proof with now eauto with Ensembles_DB.
    revert j b' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'.
    induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1.
    intros b' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'.
    intros Hcc.
    assert (Him : Res (v1', H1') ≺ ^ (k; 0; GIP; GP; b2 ∘ b' ∘ b1) Res (v2', H2')).
    { admit. }
    eapply cc_approx_val_image_eq in Him. simpl in Hcc. 
    destruct v1' as [l1 | lf1 f1]; destruct v2' as [l2 | lf2 f2]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    intros Hres1 Hr1 Hres2 Hr2. 
    destruct (get l1 H1') as [b1'|] eqn:Hget1; destruct (get l2 H2') as [b2'|] eqn:Hget2; try contradiction.  
    destruct Hcc as [Hbs Hcc].
    destruct b1' as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; try contradiction;
    destruct b2' as [c2 vs2 | | ]; try contradiction.
    + rewrite res_equiv_eq in Hres1, Hres2.
      destruct v1 as [l1' | lf1' f1']; destruct v2 as [l2' | lf2' f2']; try contradiction.
      simpl in Hres1, Hres2. 
      rewrite Hget1 in Hres1. rewrite Hget2 in Hres2. 
      destruct (get l1' H1) as [b1'|] eqn:Hget1'; [| now firstorder ].
      destruct (get l2' H2) as [b2'|] eqn:Hget2'; [| now firstorder ].
      destruct b1' as [c1' vs1' | | ]; [|  now firstorder | now firstorder ].
      destruct b2' as [c2' vs2' | | ]; [|  now firstorder | now firstorder ].
      destruct Hres1 as [Heqi1 [Heqc1 Heqb1]].
      destruct Hres2 as [Heqi2 [Heqc2 Heqb2]]. subst. 
      destruct Hcc as [Heqc Hcc]; subst.
      Abort.
  (*     split; eauto. intros i Hleq. *)
  (*     eapply Forall_vertical_l_strong; [| | eassumption ]. *)
  (*     * simpl. intros. rewrite cc_approx_val_eq in *. *)
  (*       rewrite <- (compose_id_neut_l (b2 ∘ b' ∘ b1)). *)
  (*       rewrite <- Combinators.compose_assoc. *)
  (*       eapply IHj; try eassumption. *)
  (*       eapply injective_subdomain_antimon. eassumption. *)
  (*       rewrite (reach_unfold _ (val_loc (Loc l1'))). *)
  (*       eapply Included_Union_preserv_r. *)
  (*       eapply reach'_set_monotonic. simpl. rewrite post_Singleton; [| eassumption ]. *)
  (*       eapply In_Union_list. eapply in_map. eassumption. *)
  (*       reflexivity. firstorder. *)
  (*     * simpl in Hcc. eapply Forall_vertical_r_strong; [| | eassumption ]. *)
  (*       simpl. intros x y z Hin1 Hin2 Hin3 Hin Hres. *)
  (*       rewrite cc_approx_val_eq. *)
  (*       rewrite <- (compose_id_neut_r (b2 ∘ b')). *)
  (*       eapply IHj; [ eassumption | | reflexivity | | | ].  *)
  (*       now eapply Hin. *)
  (*       now firstorder. eapply Hres. *)
  (*       eapply injective_subdomain_antimon. eassumption. *)
  (*       rewrite (reach_unfold _ [set b' l1]). *)
  (*       eapply Included_Union_preserv_r. *)
  (*       eapply reach'_set_monotonic. simpl. rewrite post_Singleton; [| eassumption ]. *)
  (*       eapply In_Union_list. eapply in_map. eassumption. *)
  (*       eapply Forall2_monotonic. intros x1 x2 HR. rewrite <- cc_approx_val_eq. *)
  (*       now eapply HR. eapply Hcc; eassumption. *)
  (*   + simpl in Hcc. destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction. *)
  (*     (* intros Hyp Hres1 Hres2. rewrite res_equiv_eq in *. *) *)
  (*     destruct v1' as [l1' | lf1' f1']; destruct v2' as [l2' | lf2' f2']; *)
  (*     try (rewrite res_equiv_eq in Hres2; rewrite res_equiv_eq in Hres1; contradiction). *)
  (*     rewrite res_equiv_eq in Hres2; rewrite res_equiv_eq in Hres1. *)
  (*     simpl in Hres1, Hres2. *)
  (*     rewrite Hget1 in Hres1. rewrite Hget2 in Hres2.  *)
  (*     destruct (get l1' H1') as [b1'|] eqn:Hget1'; try contradiction. *)
  (*     destruct (get l2' H2') as [b2'|] eqn:Hget2'; try contradiction. *)
  (*     destruct Hres1 as [Hbeq1 Hres1]. *)
  (*     destruct Hres2 as [Hbeq2 Hres2].  *)
  (*     split. unfold compose. unfold id in *. congruence. *)
  (*     destruct b1' as [c1' vs1' | | ]; try contradiction. *)
  (*     destruct b2' as [c2' vs2' | | ]; try contradiction. *)
  (*     destruct Hres1 as [Hptr1 Henv1]. *)
  (*     destruct Hres2 as [Heqc2 Hall]. subst. *)
  (*     rewrite res_equiv_eq in *. *)
  (*     destruct v as [l3' | lf3' f3']; destruct v0 as [l4' | lf4' f4']; try contradiction. *)
  (*     inv Hall. inv H5. inv H7. *)
  (*     rewrite res_equiv_eq in *. *)
  (*     destruct y as [l5' | lf5' f5']; destruct y0 as [l6' | lf6' f6']; try contradiction. *)
      
  (*     inv H3. inv Hptr1. simpl.  *)
  (*     intros b1' b2' tc1 tc2 tc3 H3 H3' H4' env_loc1' env_loc2' xs1 ft *)
  (*            e1 vs1 vs2 Hres1 Hinj1 Hres2 hinj2 Hget Hfind Hdef Hset. *)
  (*     rewrite <- res_equiv_eq in *. *)
  (*     edestruct Hcc as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi) *)
  (*     ; [| | | | eassumption | eassumption | eassumption | eassumption | ]. *)
  (*     * eapply res_equiv_f_compose; [| eassumption ]. *)
  (*       rewrite compose_id_neut_r. eassumption. *)
  (*     * eapply injective_subdomain_compose. eassumption. *)
  (*       eapply res_equiv_image_reach in Hres1. *)
  (*       rewrite image_id in Hres1. rewrite <- Hres1. *)
  (*       eapply injective_subdomain_antimon. eassumption. *)
  (*       rewrite (reach_unfold H1' (val_loc (Loc l1'))). *)
  (*       eapply Included_Union_preserv_r. eapply reach'_set_monotonic. *)
  (*       simpl. rewrite post_Singleton; eauto...  *)
  (*     * symmetry. eapply res_equiv_f_compose; [| symmetry; eassumption ]. *)
  (*       symmetry. rewrite compose_id_neut_r. eassumption. *)
  (*     * eapply injective_subdomain_compose. *)
  (*       eapply injective_subdomain_antimon. eassumption. *)
  (*       rewrite (reach_unfold H2 [set b' l1]). *)
  (*       eapply Included_Union_preserv_r. eapply reach'_set_monotonic. *)
  (*       simpl. rewrite post_Singleton; eauto. simpl... *)
  (*       eapply res_equiv_image_reach in H4. *)
  (*       rewrite image_id in H4. rewrite H4. eassumption. *)
  (*     * exists xs2, e2, rho2'. repeat split; eauto. *)
  (*     * now inv Hres2. *)
  (*     * now inv Hres1.  *)
  (* Qed. *)
  

  (** * Preservation under allocation lemmas *)
  
  (* Lemma cc_approx_val_alloc_Vconstr_set (k : nat) (P : GInv) *)
  (*       (H1 H2 H1' H2' : heap block) (v1 v2 : value) (l1 l2 : loc) *)
  (*       (c : cTag) (vs1 vs2 : list value) : *)
  (*   well_formed (reach' H1 (val_loc v1)) H1 -> *)
  (*   (val_loc v1) \subset dom H1 -> *)
  (*   well_formed (reach' H2 (val_loc v2)) H2 -> *)
  (*   (val_loc v2) \subset dom H2 -> *)
  (*   (Res (v1, H1))  ≺ ^ (k; P) (Res (v2, H2)) -> *)
  (*   alloc b1 H1 = (l1, H1') -> *)
  (*   alloc b2 H2 = (l2, H2') -> *)
  (*   Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k - 1; P) (Res (v2, H2))) vs1 vs2 -> *)
  (*   (Res (v1, H1'))  ≺ ^ (k; P) (Res (v2, H2')). *)
  (* Proof with now eauto with Ensembles_DB. *)
  (*   revert P H1 H2 H1' H2' v1 v2. induction k as [k IHk] using lt_wf_rec1. *)
  (*   intros P H1 H2 H1' H2' v1 v2 Hwf1 Hsub1 Hwf2 Hsub2 Hyp Ha1 Ha2 Hall. *)
  (*   destruct k as [ | k ]; *)
  (*   destruct v1 as [l1' | lf1 f1]; destruct v2 as [l2' | lf2 f2]; *)
  (*   try (now intros; contradiction). *)
  (*   - destruct Hyp as [c' [vs1' [vs2' [Hget1 [Hget2 Hall']]]]]. *)
  (*     repeat eexists; eauto; erewrite gao; eauto. *)
  (*     intros Hc; subst. erewrite alloc_fresh in Hget1; eauto. congruence. *)
  (*     intros Hc; subst. erewrite alloc_fresh in Hget2; eauto. congruence. *)
  (*   - destruct Hyp *)
  (*       as (rho1 & B1 & lf2 & f2 & v_env & rho2 & B2 & Hget & Hgetl2 & Hgetlf2 & Hyp'). *)
  (*     do 7 eexists; split; [ | split; [| split] ]; (try now eauto). *)
  (*     erewrite gao; try eassumption. *)
  (*     intros Hc; subst. erewrite alloc_fresh in Hget; eauto. congruence. *)
  (*     erewrite gao; try eassumption. *)
  (*     intros Hc; subst. erewrite alloc_fresh in Hgetl2; eauto. congruence. *)
  (*     erewrite gao; try eassumption. *)
  (*     intros Hc; subst. erewrite alloc_fresh in Hgetlf2; eauto. congruence. *)
  (*     intros xs1 ft e1 rho1' vs3 vs4 j Hfind Hlen Hset; *)
  (*     destruct (Hyp' xs1 ft e1 rho1' vs3 vs4 j Hfind Hlen Hset) *)
  (*       as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi). *)
  (*     do 3 eexists; repeat split; try now eauto. *)
  (*   - destruct Hyp as [c' [vs1' [vs2' [Hget1 [Hget2 Hall']]]]]. *)
  (*     repeat eexists; try eassumption; try erewrite gao; eauto. *)
  (*     intros Hc; subst. erewrite alloc_fresh in Hget1; eauto. congruence. *)
  (*     intros Hc; subst. erewrite alloc_fresh in Hget2; eauto. congruence. *)
  (*     eapply Forall2_monotonic_strong; [| eassumption ]. *)
  (*     intros. rewrite cc_approx_val_eq in *. *)
  (*     eapply IHk; try eassumption. *)
  (*     + omega. *)
  (*     + eapply well_formed_antimon; [| eassumption ]. *)
  (*       rewrite (reach_unfold _ [set val_loc (Loc l1')]). *)
  (*       eapply Included_Union_preserv_r. *)
  (*       eapply reach'_set_monotonic. eapply Singleton_Included. *)
  (*       repeat eexists; eauto. simpl. rewrite FromList_map_image_FromList. *)
  (*       eapply In_image. eassumption. *)
  (*     + eapply Hwf1; [| now apply Hget1 |]. *)
  (*       eapply reach'_extensive. reflexivity. *)
  (*       simpl. rewrite FromList_map_image_FromList. *)
  (*       eexists; split; eauto. *)
  (*     + eapply well_formed_antimon; [| eassumption ]. *)
  (*       rewrite (reach_unfold _ [set val_loc (Loc l2')]). *)
  (*       eapply Included_Union_preserv_r. *)
  (*       eapply reach'_set_monotonic. eapply Singleton_Included. *)
  (*       repeat eexists; eauto. simpl. rewrite FromList_map_image_FromList. *)
  (*       eexists; split; eauto. *)
  (*     + eapply Hwf2; [| now apply Hget2 |]. *)
  (*       eapply reach'_extensive. reflexivity. *)
  (*       simpl. rewrite FromList_map_image_FromList. *)
  (*       eapply In_image. eassumption. *)
  (*     + eapply Forall2_monotonic; [| eassumption ]. intros. *)
  (*       eapply cc_approx_val_monotonic. now apply H4. omega. *)
  (*   - destruct Hyp *)
  (*       as (rho1 & B1 & lf2 & f2 & v_env  & rho2 & B2 & Hget & Hgetl2 & Hgetlf2 & Hyp'). *)
  (*     do 7 eexists; split; [ | split; [| split] ]; (try now eauto). *)
  (*     erewrite gao; try eassumption. *)
  (*     intros Hc; subst. erewrite alloc_fresh in Hget; eauto. congruence. *)
  (*     erewrite gao; try eassumption. *)
  (*     intros Hc; subst. erewrite alloc_fresh in Hgetl2; eauto. congruence. *)
  (*     erewrite gao; try eassumption. *)
  (*     intros Hc; subst. erewrite alloc_fresh in Hgetlf2; eauto. congruence. *)
  (*     intros xs1 ft e1 rho1' vs3 vs4 j Hfind Hlen Hset; *)
  (*     destruct (Hyp' xs1 ft e1 rho1' vs3 vs4 j Hfind Hlen Hset) *)
  (*       as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi). *)
  (*     do 3 eexists; repeat split; try now eauto. *)
  (*     intros Hlt H1'' H2'' HH1 HH2. eapply Hi. *)
  (*     + omega. *)
  (*     + eapply Equivalence_Transitive; try eassumption. *)
  (*       * eapply heap_eq_antimon; [|  eapply subheap_heap_eq ]. *)
  (*         eapply reachable_in_dom. eassumption. *)
  (*         eapply Singleton_Included. *)
  (*         now repeat eexists; eauto. eapply alloc_subheap. eassumption. *)
  (*       * eapply heap_eq_antimon; [| eassumption ]. *)
  (*         eapply reach'_heap_monotonic. eapply alloc_subheap. eassumption. *)
  (*     + eapply Equivalence_Transitive. *)
  (*       * eapply heap_eq_antimon; [|  eapply subheap_heap_eq ]. *)
  (*         eapply reachable_in_dom. eassumption. *)
  (*         eapply Singleton_Included. *)
  (*         now repeat eexists; eauto. eapply alloc_subheap. eassumption. *)
  (*       * eapply heap_eq_antimon; [| eassumption ]. *)
  (*         eapply reach'_heap_monotonic. eapply alloc_subheap. eassumption. *)
  (* Qed. *)
  
  (** * Getlist lemmas *)
  
  Lemma cc_approx_var_env_getlist (k j : nat)
        (rho1 rho2 : env) (β : Inj) (H1 H2 : heap block) xs ys vs1 :
    Forall2 (cc_approx_var_env k j GIP GP β H1 rho1 H2 rho2) xs ys ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist ys rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k; j; GIP ; GP ; β) (Res (v2, H2))) vs1 vs2.
  Proof.
    revert ys vs1. induction xs as [| x xs IHxs]; intros ys vs1 Hall Hget.
    - destruct ys; inv Hall. inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget.
      destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (getlist xs rho1) eqn:Heq2; try discriminate. inv Hget.
      destruct ys as [| y ys]; inv Hall. 
      destruct (IHxs ys l H6 eq_refl) as [vs2 [Hget HAll]].
      destruct (H4 _ Heq1) as [v2 [Heq Hpre]].
      eexists. split; simpl; eauto. rewrite Hget, Heq. eauto.
  Qed.
  
  Lemma cc_approx_env_P_getlist_l (S : Ensemble var) (k j : nat)
        (rho1 rho2 : env) (β : Inj) (H1 H2 : heap block) (xs : list var) (vs1 : list value) :
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; β) (H2, rho2) ->
    (FromList xs) \subset S ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist xs rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β) (Res (v2, H2))) vs1 vs2.
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
  

  (* (** * cc_approx respects heap_eq  *) *)

  (*  Lemma cc_approx_exp_heap_equiv (k : nat) (H1 H2 H1' H2' : heap block) *)
  (*        (rho1 rho2 : env) (e1 e2 : exp) : *)
  (*   (e1, rho1, H1) ⪯ ^ (k ; LIP ; GIP ; LP ; GP) (e2, rho2, H2) -> *)
  (*   (env_locs rho1 (occurs_free e1)) |- H1 ≃ H1' -> *)
  (*   (env_locs rho2 (occurs_free e2)) |- H2 ≃ H2' -> *)
  (*   (IP (H1', rho1, e1) (H2', rho2, e2) -> IP (H1, rho1, e1) (H2, rho2, e2)) -> *)
  (*   (e1, rho1, H1') ⪯ ^ (k ; LIP ; GIP ; LP ; GP) (e2, rho2, H2'). *)
  (*  Proof with now eauto with Ensembles_DB. *)
  (*    intros Hexp Heq1 Heq2 H1'' H2'' rho1' rho2' r1 c1 m1 Heq1' Heq2' HIP Hleq Hbs Hns. *)
  (*    eapply heap_env_equiv_heap_equiv in Heq1. *)
  (*    eapply heap_env_equiv_heap_equiv in Heq2. *)
  (*    eapply Hexp; [| | | eassumption | ]; eauto;      *)
  (*    eapply Equivalence_Transitive; try eassumption. *)
  (*  Qed. *)


  Transparent cc_approx_exp.
   
   Lemma cc_approx_exp_heap_monotonic (k j : nat) (H1 H2 H1' H2' : heap block)
         (rho1 rho2 : env) (e1 e2 : exp) :
     well_formed (reach' H1 (env_locs rho1 (occurs_free e1))) H1 ->
     well_formed (reach' H2 (env_locs rho2 (occurs_free e2))) H2 ->
     (env_locs rho1 (occurs_free e1)) \subset dom H1 ->
     (env_locs rho2 (occurs_free e2)) \subset dom H2 ->
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     (e1, rho1, H1)  ⪯ ^ ( k ; j ; LIP ; GIP ; LP ; GP) (e2, rho2, H2) ->
     (e1, rho1, H1') ⪯ ^ ( k ; j ; LIP ; GIP ; LP ; GP) (e2, rho2, H2').
   Proof.
     intros Hwf1 Hwf22 Hs1 Hs2 Hsub1 Hsub2 Hyp b1 b2 H3 H4 rho1' rho2' r1 c1 m1
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


   Lemma cc_approx_val_heap_monotonic (k j : nat) (β : Inj) (H1 H2 H1' H2' : heap block)
       (v1 v2 : value):
     well_formed (reach' H1 (val_loc v1)) H1 ->
     well_formed (reach' H2 (val_loc v2)) H2 ->
     val_loc v1 \subset dom H1 ->
     val_loc v2 \subset dom H2 ->
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     Res (v1, H1) ≺ ^ (k ; j; GIP ; GP ; β) Res (v2, H2) ->
     Res (v1, H1') ≺ ^ (k ; j; GIP ; GP; β) Res (v2, H2').
   Proof with (now eauto with Ensembles_DB).
     revert j v1 v2. induction k as [k IHk] using lt_wf_rec1; intros j.
     induction j as [j IHj] using lt_wf_rec1. intros v1 v2 Hwf1 Hwf2 Hin1 Hin2 Hsub1 Hsub2 Hcc.
     destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
     try (now intros; contradiction); try (now simpl; eauto).
     simpl in Hcc.
     destruct (get l1 H1) as [b1|] eqn:Hget1; destruct (get l2 H2) as [b2|] eqn:Hget2; try contradiction.
     eapply Hsub1 in Hget1. eapply Hsub2 in Hget2. rewrite Hget1, Hget2.
     destruct Hcc as [Heq Hcc].
     split; eauto. destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
       destruct b2 as [c2 vs2 | | ]; try contradiction. 
     + subst.
       edestruct Hin1 as [b1 Hget1']. reflexivity.
       assert (Hget1'' := Hget1'). eapply Hsub1 in Hget1''.
       subst_exp.
       edestruct Hin2 as [b2 Hget2']. reflexivity.
       assert (Hget2'' := Hget2'). eapply Hsub2 in Hget2''.
       subst_exp. destruct Hcc as [Heq Hall].
       split; eauto.
       intros i Hleq. simpl.
       eapply Forall2_monotonic_strong; [| eapply Hall; eassumption ].
       intros x1 x2 Hinx1 Hinx2 Hr.
       assert (Hr1 : val_loc x1 \subset post H1 (val_loc (Loc l1))).
       { simpl. rewrite post_Singleton; [| eassumption ].
         simpl. eapply In_Union_list.
         eapply in_map. eassumption. }
       assert (Hr2 : val_loc x2 \subset post H2 (val_loc (Loc (β l1)))).
       { simpl. rewrite post_Singleton; [| eassumption ].
         simpl. eapply In_Union_list.
         eapply in_map. eassumption. }
       rewrite cc_approx_val_eq. eapply IHj; try eassumption.
       * eapply well_formed_antimon; [| eassumption ].
         rewrite (reach_unfold _ (val_loc (Loc l1))).
         eapply Included_Union_preserv_r.
         eapply reach'_set_monotonic. eassumption.
       * eapply well_formed_antimon; [| eassumption ].
         rewrite (reach_unfold _ (val_loc (Loc (β l1)))).
         eapply Included_Union_preserv_r.
         eapply reach'_set_monotonic. eassumption.
       * eapply Included_trans; [| eapply reachable_in_dom ]; try eassumption.
         eapply Included_trans; [| eapply Included_post_reach']; eassumption.
       * eapply Included_trans; [| eapply reachable_in_dom ]; try eassumption.
         eapply Included_trans; [| eapply Included_post_reach']; eassumption.
       * rewrite <- cc_approx_val_eq. eassumption.
     + subst.
       edestruct Hin1 as [b1 Hget1']. reflexivity.
       assert (Hget1'' := Hget1'). eapply Hsub1 in Hget1''.
       subst_exp.
       edestruct Hin2 as [b2 Hget2']. reflexivity.
       assert (Hget2'' := Hget2'). eapply Hsub2 in Hget2''.
       subst_exp.
       destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
       simpl. destruct Hcc as [Him Hcc].
       split. intros j' Hlt.
       rewrite <- (well_formed_post_n_subheap_same _ H1 H1'); try eassumption.
       rewrite <- (well_formed_post_n_subheap_same _ H2 H2'); try eassumption.
       eapply Him. eassumption.
       eapply well_formed_antimon; [| eassumption ].
       simpl. rewrite (reach_unfold _ [set (β l1)]).
       eapply Included_Union_preserv_r.
       eapply reach'_set_monotonic. rewrite post_Singleton; simpl; try eassumption.
       simpl... 
       eapply Included_trans; [| eapply reachable_in_dom; try eassumption ].
       simpl. rewrite (reach_unfold _ [set (β l1)]).
       eapply Included_Union_preserv_r.
       eapply Included_trans; [| now eapply reach'_extensive ].
       rewrite post_Singleton; simpl; try eassumption.
       simpl... 
       eapply well_formed_antimon; [| eassumption ].
       simpl. rewrite (reach_unfold _ [set l1]).
       eapply Included_Union_preserv_r.
       eapply reach'_set_monotonic. rewrite post_Singleton; simpl; try eassumption.
       simpl... 
       eapply Included_trans; [| eapply reachable_in_dom; try eassumption ].
       simpl. rewrite (reach_unfold _ [set l1]).
       eapply Included_Union_preserv_r.
       eapply Included_trans; [| now eapply reach'_extensive ].
       rewrite post_Singleton; simpl; try eassumption.
       simpl...
       
       intros b1 b2 tc1 tc2 tc3  H3 H3' H4' env_loc1' env_loc2' xs1 ft e1 vs1 vs2
              Heq1 Hinj1 Heq2 Hinj2 Hget Hfind Hdef Hset.
       edestruct Hcc
         as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi).
       * eapply Equivalence_Transitive; [| now apply Heq1 ].
         eapply subheap_res_equiv; try eassumption.
         eapply Included_trans; [| now eapply Included_post_reach' ].
         edestruct Hin1 as [b'1 Hget1'']. reflexivity.
         eexists. eexists. split; [| split; [ eassumption |]].
         reflexivity. eapply Hsub1 in Hget1''. subst_exp.
         simpl. right. eassumption.
       * eassumption.
       * eapply Equivalence_Transitive; [| eassumption ].
         eapply subheap_res_equiv; try eassumption.
         eapply Included_trans; [| now eapply Included_post_reach' ].
         edestruct Hin2 as [b2' Hget2'']. reflexivity.
         eexists. eexists.  split; [| split; [ eassumption |]].
         reflexivity. eapply Hsub2 in Hget2''. subst_exp.
         simpl. right. left. eassumption.  
       * eapply injective_subdomain_antimon. eassumption.
         eapply reach'_heap_monotonic. eassumption.
       * eassumption.
       * eassumption.
       * eassumption.
       * eassumption.
       * do 3 eexists; split; [ | split ]; try (now eauto).
   Qed.

   Lemma cc_approx_var_env_heap_monotonic (k j : nat) (β : Inj) (H1 H2 H1' H2' : heap block)
       (rho1 rho2 : env) x y:
     well_formed (reach' H1 (env_locs rho1 [set x])) H1 ->
     well_formed (reach' H2 (env_locs rho2 [set y])) H2 ->
     env_locs rho1 [set x] \subset dom H1 ->
     env_locs rho2 [set y] \subset dom H2 ->
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     cc_approx_var_env k j GIP GP β H1 rho1 H2 rho2 x y ->
     cc_approx_var_env k j GIP GP β H1' rho1 H2' rho2 x y.
   Proof.
     intros Hwf1 Hwf2 Hlocs1 Hlocs2 Hs1 Hs2 Hres v Hget.
     edestruct Hres as [l2 [Hget2 Hres2]]; eauto.
     eexists; split; eauto.
     eapply cc_approx_val_heap_monotonic; try eassumption.
     eapply well_formed_antimon; [| eassumption ].
     rewrite env_locs_Singleton; eauto. reflexivity.
     eapply well_formed_antimon; [| eassumption ].
     rewrite env_locs_Singleton; eauto. reflexivity.
     eapply Included_trans; [| eassumption ].
     rewrite env_locs_Singleton; eauto. reflexivity.
     eapply Included_trans; [| eassumption ].
     rewrite env_locs_Singleton; eauto. reflexivity.
   Qed.
   
   Lemma cc_approx_env_heap_monotonic S (k j : nat) (β : Inj) (H1 H2 H1' H2' : heap block)
       (rho1 rho2 : env):
     well_formed (reach' H1 (env_locs rho1 S)) H1 ->
     well_formed (reach' H2 (env_locs rho2 S)) H2 ->
     env_locs rho1 S \subset dom H1 ->
     env_locs rho2 S \subset dom H2 ->
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     (H1, rho1) ⋞ ^ (S ; k ; j; GIP ; GP ; β) (H2, rho2) ->
     (H1', rho1) ⋞ ^ (S ; k ; j; GIP ; GP; β) (H2', rho2).
   Proof.
     intros Hwf1 Hwf2 Hlocs1 Hlocs2 Hs1 Hs2 Hres x Hin.
     eapply cc_approx_var_env_heap_monotonic; try eassumption.
     eapply well_formed_antimon; [| eassumption ].
     eapply reach'_set_monotonic. eapply env_locs_monotonic.
     eapply Singleton_Included. eassumption.
     eapply well_formed_antimon; [| eassumption ].
     eapply reach'_set_monotonic. eapply env_locs_monotonic.
     eapply Singleton_Included. eassumption.
     eapply Included_trans; [| eassumption ].
     eapply env_locs_monotonic.
     eapply Singleton_Included. eassumption.
     eapply Included_trans; [| eassumption ].
     eapply env_locs_monotonic.
     eapply Singleton_Included. eassumption.
     eapply Hres; eauto.
   Qed.

   Lemma cc_approx_env_set_alloc_Constr S (k j : nat)
         c vs1 vs2 l1 l2  (H1 H2 H1' H2' : heap block)
         (rho1 rho2 : env) x:

     well_formed (reach' H1 (env_locs rho1 S)) H1 ->
     well_formed (reach' H2 (env_locs rho2 S)) H2 ->
     env_locs rho1 S \subset dom H1 ->
     env_locs rho2 S \subset dom H2 ->
     locs (Constr c vs1) \subset env_locs rho1 S ->
     locs (Constr c vs2) \subset env_locs rho2 S ->

     (H1, rho1) ⋞ ^ (S \\ [set x]; k; j; GIP; GP; b) (H2, rho2) ->
     
     alloc (Constr c vs1) H1 = (l1, H1') ->
     alloc (Constr c vs2) H2 = (l2, H2') ->  

     b l1 = l2 ->
     (forall j', j' < j ->  Forall2 (fun v1 v2 => Res (v1, H1) ≺ ^ (k; j'; GIP; GP; b) Res (v2, H2)) vs1 vs2) ->
     
     (H1', M.set x (Loc l1) rho1) ⋞ ^ (S; k; j; GIP; GP; b) (H2', M.set x (Loc l2) rho2).
   Proof with (now eauto with Ensembles_DB).
     intros Hwf1 Hwf2 Hlocs1 Hlocs2 Hl1 Hl2 Henv Ha1 Ha2 Hb Hres.
     eapply cc_approx_env_P_set; try eassumption.
     eapply cc_approx_env_heap_monotonic; try eassumption.
     eapply well_formed_antimon; [| eassumption ].
     eapply reach'_set_monotonic. eapply env_locs_monotonic...
     eapply well_formed_antimon; [| eassumption ].
     eapply reach'_set_monotonic. eapply env_locs_monotonic...
     eapply Included_trans; [| now apply Hlocs1 ]. eapply env_locs_monotonic...
     eapply Included_trans; [| now apply Hlocs2 ]. eapply env_locs_monotonic...
     eapply HL.alloc_subheap; eassumption.
     eapply HL.alloc_subheap; eassumption.
     simpl. erewrite !gas; eauto.
     split. eassumption.
     simpl. split; eauto. intros i Hlt.
     specialize (Hres i Hlt).
     eapply Forall2_monotonic_strong; [| eassumption ].
     intros x1 x2 Hin1 Hin2 Heq.
     rewrite cc_approx_val_eq.
     eapply cc_approx_val_heap_monotonic; try eassumption.
     eapply well_formed_antimon; [| now eapply Hwf1 ].
     eapply reach'_set_monotonic. eapply Included_trans; [| eassumption ].
     eapply In_Union_list. eapply in_map. eassumption.
     eapply well_formed_antimon; [| now eapply Hwf2 ].
     eapply reach'_set_monotonic. eapply Included_trans; [| eassumption ].
     eapply In_Union_list. eapply in_map. eassumption.
     eapply Included_trans; [| now apply Hlocs1 ].
     eapply Included_trans; [| eassumption ].
     eapply In_Union_list. eapply in_map. eassumption.
     eapply Included_trans; [| now apply Hlocs2 ].
     eapply Included_trans; [| eassumption ].
     eapply In_Union_list. eapply in_map. eassumption.
     eapply HL.alloc_subheap; eassumption.
     eapply HL.alloc_subheap; eassumption.
     now apply Heq.
   Qed.

   Lemma cc_approx_val_rename_ext  β β' k j H1 H2 v1 v2:
     (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β') (Res (v2, H2)) ->
     f_eq_subdomain (reach' H1 (val_loc v1)) β β' ->
     (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β) (Res (v2, H2)).
  Proof with (now eauto with Ensembles_DB).
    revert k j H1 H2 v1 v2.
    induction k as [k IHk] using lt_wf_rec1.
    induction j as [j IHj] using lt_wf_rec1.
    intros H1 H2 v1 v2 Hres Hfeq.
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    simpl in Hres.
    destruct (get l1 H1) as [b1'|] eqn:Hget1; destruct (get l2 H2) as [b2'|] eqn:Hget2; try contradiction.
    destruct Hres as [Hbeq Hbeq'].
    split. rewrite Hfeq. eassumption. eapply reach'_extensive. reflexivity.
    destruct b1' as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; try contradiction;
    destruct b2' as [c2 vs2 | | ]; try contradiction.
    + simpl in Hbeq'. destruct Hbeq' as [ceq Hi]. split; eauto. subst.
      intros i Hlt. simpl.
      eapply Forall2_monotonic_strong. intros x1 x2 Hin1 Hin2 HR.
      rewrite cc_approx_val_eq. eapply IHj. eassumption.
      rewrite <- cc_approx_val_eq. now apply HR.
      eapply f_eq_subdomain_antimon; [| eassumption ].
      rewrite (reach_unfold H1 (val_loc (Loc l1))).
      eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
      simpl. rewrite post_Singleton; [| eassumption ].
      eapply In_Union_list. eapply in_map. eassumption.
      eapply Hi; eauto.
    + simpl in Hbeq'.
      destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction.
      destruct Hbeq' as [Him Hcc].
      simpl. split. intros j' Hleq. rewrite <- Him; eauto.
      eapply image_f_eq_subdomain. eapply f_eq_subdomain_antimon; [| eassumption ].
      rewrite reach_unfold. eapply Included_Union_preserv_r.
      eapply Included_trans. eapply Included_post_n_reach'.
      eapply reach'_set_monotonic. simpl. rewrite post_Singleton; eauto...
      intros b1' b2' tc1 tc2 tc3 H3 H3' H4' env_loc1' env_loc2' xs1 ft
             e1 vs1 vs2 Hres1 Hinj1 Hres2 hinj2 Hget Hfind Hdef Hset.
      edestruct Hcc as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi)
      ; [| | | | eassumption | eassumption | eassumption | eassumption | ]; try eassumption.
      exists xs2, e2, rho2'. repeat split; eauto.
      intros i j' b' Hlt Hleq Hfeq' Hall. eapply Hi; try eassumption.
      eapply Equivalence_Transitive; [| eassumption ].
      eapply f_eq_subdomain_compose_compat. reflexivity.
      eapply f_eq_subdomain_compose_compat; [| reflexivity ].
      replace ([set env_loc1']) with (val_loc (Loc env_loc1')) by reflexivity.
      eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].
      rewrite <- res_equiv_image_reach; [| eassumption ].
      rewrite image_id. rewrite (reach_unfold H1 (val_loc (Loc l1))).
      eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
      simpl. rewrite post_Singleton; eauto...
  Qed.
  
  Lemma cc_approx_var_env_rename_ext  (k j : nat) (β β': Inj) (H1 H2 : heap block) 
         (rho1 rho2 : env) (x y : var) :
     cc_approx_var_env k j GIP GP β H1 rho1 H2 rho2 x y ->
     f_eq_subdomain (reach' H1 (env_locs rho1 [set x])) β β' ->
     cc_approx_var_env k j GIP GP β' H1 rho1 H2 rho2 x y.
   Proof with (now eauto with Ensembles_DB).
     intros Hcc Heq v Hget. edestruct Hcc as [l2 [Hget2 Hres]].
     eassumption. eexists; split; eauto.
     eapply cc_approx_val_rename_ext. eassumption.
     eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].
     eapply reach'_set_monotonic. eapply env_locs_Singleton; try eassumption.
   Qed.
  
   Lemma cc_approx_env_rename_ext S β β' H1 H2 rho1 rho2 k j :
     (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; β) (H2, rho2) ->
     f_eq_subdomain (reach' H1 (env_locs rho1 S)) β β' ->
     (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; β') (H2, rho2).
  Proof with (now eauto with Ensembles_DB).
    intros Henv Heq x Hin.
    eapply cc_approx_var_env_rename_ext. now eauto.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply env_locs_monotonic.
    eapply Singleton_Included. eassumption.
  Qed.

  End LogRelLemmas.


  (** * Proper Instances *)

  
  Global Instance cc_approx_env_proper_set :
    Proper (Same_set var ==> Logic.eq ==>  Logic.eq ==> Logic.eq ==>
            Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           cc_approx_env_P.
  Proof.
    intros s1 s2 [H1 H2]; split; intros Hpre;
    subst; eapply cc_approx_env_P_antimon; subst; eauto. 
  Qed.


End CC_log_rel.