(* Step-indexed logical relation for L6 closure conversion.
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2017
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util set_util
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
  Definition GIInv := relation (heap block * env * exp).
  
  (** * Final conditions *)
  
  (** Local final conditions. Holds for the result of the execution of the expressions being related. *)
  Definition Inv := relation (heap block * env * exp * nat * nat).

  (** Global final conditions. Holds for the result of future execution of the result *)
  Definition GInv := nat -> relation (heap block * env * exp * nat * nat).
  
  (** Loc Injection *)
  Definition Inj := loc -> loc.

  (** Env Injection *)
  Definition EInj := loc -> option loc.
  
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
    
    Variable (cc_approx_val : nat -> nat -> GIInv -> GInv -> Inj -> EInj -> ans -> ans -> Prop). 
    Variable (cc_approx_val' : nat -> GIInv -> GInv -> Inj -> EInj -> ans -> ans -> Prop). 

    (* TODO move *)
    (* Definition reach_n_res (j : nat) := fun '(v, H) => reach_n H j (val_loc v). *)
    
    (* Definition reach_n_ans (j : nat) (a : ans) :=  *)
    (*   match a with *)
    (*     | Res r => reach_n_res j r *)
    (*     | OOT => Empty_set loc *)
    (*     | OOM => Empty_set loc *)
    (*   end. *)
    
    
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
        exists (r2 : ans) (c2 m2 : nat) (b : Inj) (b' : EInj),
          big_step_GC_cc H2' rho2' e2 r2 c2 m2 /\
          (* extra invariants for costs *)
          IL (H1', rho1', e1, c1, m1) (H2', rho2', e2, c2, m2) /\
          cc_approx_val (k - c1) j IIG IG b b' r1 r2.

    Definition cc_approx_clos
               (* step indexes *)
               (j : nat)
               (* Invariants *)
               (GI : GIInv) (GP : GInv)
               (b : Inj) (d : EInj)
               (* *)
               (FV : Ensemble var)
               (p1 : env * heap block)
               (p2 : loc * heap block) : Prop :=
      let '(rho1, H1) := p1 in
      let '(l, H2) := p2 in
      exists c (vs : list value) FVs,
        FromList FVs <--> FV /\
        NoDup FVs /\
        get l H2 = Some (Constr c vs) /\
        Forall2 (fun (x1 : var) (v2 : value)  =>
                   exists l1, M.get x1 rho1 = Some (Loc l1) /\
                         cc_approx_val' j GI GP b d (Res (Loc l1, H1)) (Res (v2, H2)))
                FVs vs.

  End cc_approx.
  
  (** * Value relation *)
   
  Fixpoint cc_approx_val (k : nat) {struct k} :=
    let fix cc_approx_val_aux 
           (j : nat) (IP : GIInv) (P : GInv) (b : Inj) (d : EInj) (r1 r2 : ans) {struct j} : Prop :=
    match r1, r2 with
      | OOT, OOT => True (* Both programs timeout *)
      | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
        match v1, v2 with
          | Loc l1, Loc l2 =>
            b l1 = l2 /\
            match get l1 H1, get l2 H2 with
              | Some (Constr c1 vs1), Some (Constr c2 vs2) =>
                    d l1 = None /\ c1 = c2 /\ 
                    (forall i,
                       (i < j)%nat ->
                       match j with
                         | 0 => True
                         | S j =>
                           let R l1 l2 := cc_approx_val_aux (j - (j - i)) IP P b d (Res (l1, H1)) (Res (l2, H2)) in
                           Forall2 R vs1 vs2
                       end)
              | Some (Clos (FunPtr B1 f1) rho_clo), Some (Constr c [FunPtr B2 f2; Loc env_loc]) =>
                d l1 = Some env_loc /\
                (forall i, (i < j)%nat ->
                      match j with
                         | 0 => True
                         | S j =>
                           cc_approx_clos cc_approx_val_aux (j - (j - i)) IP P b d 
                                          (occurs_free_fundefs B1) (rho_clo, H1) (env_loc, H2)
                      end) /\ 
                forall (b1 b2 : Inj)
                  (rho_clo' rho_clo1 rho_clo2 : env) (H1' H1'' H2' : heap block)
                  (env_loc' : loc)
                  (xs1 : list var) (ft : fTag) (e1 : exp) (vs1 vs2 : list value),
                  (occurs_free_fundefs B1) |- (H1, rho_clo) ⩪_(id, b1) (H1', rho_clo') ->
                  injective_subdomain (reach' H1' (env_locs rho_clo' (occurs_free_fundefs B1))) b1 ->
                  (Loc env_loc, H2) ≈_(b2, id) (Loc env_loc', H2') ->
                  injective_subdomain (reach' H2 [set env_loc]) b2 ->
                  
                  find_def f1 B1 = Some (ft, xs1, e1) ->
                  
                  def_closures B1 B1 rho_clo' H1' rho_clo' =  (H1'', rho_clo1) ->
                  setlist xs1 vs1 rho_clo1 = Some rho_clo2 ->
                  
                  exists (xs2 : list var) (e2 : exp) (rho2' : env),
                    find_def f2 B2 = Some (ft, xs2, e2) /\
                    Some rho2' = setlist xs2 ((Loc env_loc') :: vs2) (def_funs B2 B2 (M.empty _)) /\
                    (forall i j',
                       (i < k)%nat -> (j' <= j)%nat ->
                       match k with
                         | 0 => True
                         | S k =>
                           forall b' d',
                           let R v1 v2 := cc_approx_val (k - (k - i)) j' IP P b' d' (Res (v1, H1'')) (Res (v2, H2')) in
                           Forall2 R vs1 vs2 ->
                           f_eq_subdomain (reach' H1' (env_locs rho_clo' (occurs_free_fundefs B1))) (b2 ∘ b ∘ b1) b' ->
                           f_eq_subdomain (reach' H1' (env_locs rho_clo' (occurs_free_fundefs B1))) ((lift b2) ∘ d ∘ b1) d' ->
                           (forall (H1 H2  : heap block) (e1 e2 : exp),
                              live (env_locs rho_clo2 (occurs_free e1)) H1'' H1 ->
                              live' (env_locs rho2' (occurs_free e2)) H2' H2 ->
                              IP (H1, rho_clo2, e1) (H2, rho2', e2)) /\
                           cc_approx_exp cc_approx_val
                                         (k - (k - i))
                                         j'
                                         IP IP
                                         (P (k - (k - i))) P
                                         (e1, rho_clo2, H1'') (e2, rho2', H2')
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

  Notation "p1 << ^ ( k ; j ; P1 ; P2 ; b ; d ; S ) p2" :=
        (cc_approx_clos (cc_approx_val k) j P1 P2 b d S p1 p2)
          (at level 70, no associativity).


    
  (** Unfold the recursion. A more compact definition of the value relation. *)
  Definition cc_approx_val' (k : nat) (j : nat) (IP : GIInv) (P : GInv) (b : Inj) (d : EInj) (r1 r2 : ans) : Prop :=
    match r1, r2 with
      | OOT, OOT => True (* Both programs timeout *)
      | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
        match v1, v2 with
          | Loc l1, Loc l2 =>
            b l1 = l2 /\
            match get l1 H1, get l2 H2 with
              | Some (Constr c1 vs1), Some (Constr c2 vs2) =>
                    c1 = c2 /\ d l1 = None /\ 
                    (forall i, (i < j)%nat ->
                          let R l1 l2 := cc_approx_val k i IP P b d (Res (l1, H1)) (Res (l2, H2)) in
                          Forall2 R vs1 vs2)
              | Some (Clos (FunPtr B1 f1) rho_clo), Some (Constr c [FunPtr B2 f2; Loc env_loc]) =>
                d l1 = Some env_loc /\
                (forall i, (i < j)%nat -> (rho_clo, H1) << ^ ( k ; i ; IP ; P ; b ; d ; occurs_free_fundefs B1) (env_loc, H2) ) /\
                forall (b1 b2 : Inj)
                  (rho_clo' rho_clo1 rho_clo2 : env) (H1' H1'' H2' : heap block)
                  (env_loc' : loc)
                  (xs1 : list var) (ft : fTag) (e1 : exp) (vs1 vs2 : list value),
                  (occurs_free_fundefs B1) |- (H1, rho_clo) ⩪_(id, b1) (H1', rho_clo') ->
                  injective_subdomain (reach' H1' (env_locs rho_clo' (occurs_free_fundefs B1))) b1 ->
                  (Loc env_loc, H2) ≈_(b2, id) (Loc env_loc', H2') ->
                  injective_subdomain (reach' H2 [set env_loc]) b2 ->
                  
                  find_def f1 B1 = Some (ft, xs1, e1) ->
                  
                  def_closures B1 B1 rho_clo' H1' rho_clo' =  (H1'', rho_clo1) ->
                  setlist xs1 vs1 rho_clo1 = Some rho_clo2 ->
                  
                  exists (xs2 : list var) (e2 : exp) (rho2' : env),
                    find_def f2 B2 = Some (ft, xs2, e2) /\
                    Some rho2' = setlist xs2 ((Loc env_loc') :: vs2) (def_funs B2 B2 (M.empty _)) /\
                    (forall i j',
                       (i < k)%nat -> (j' <= j)%nat ->
                       forall b' d',
                         let R v1 v2 := cc_approx_val i j' IP P b' d' (Res (v1, H1'')) (Res (v2, H2')) in
                         Forall2 R vs1 vs2 ->
                         f_eq_subdomain (reach' H1' (env_locs rho_clo' (occurs_free_fundefs B1))) (b2 ∘ b ∘ b1) b' ->
                         f_eq_subdomain (reach' H1' (env_locs rho_clo' (occurs_free_fundefs B1))) ((lift b2) ∘ d ∘ b1) d' ->
                         (forall (H1 H2  : heap block) (e1 e2 : exp),
                            live (env_locs rho_clo2 (occurs_free e1)) H1'' H1 ->
                            live' (env_locs rho2' (occurs_free e2)) H2' H2 ->
                            IP (H1, rho_clo2, e1) (H2, rho2', e2)) /\
                         cc_approx_exp cc_approx_val
                                       i j'
                                       IP IP
                                       (P i) P
                                       (e1, rho_clo2, H1'') (e2, rho2', H2'))
              | _, _ => False
            end
          | _, _ => False
        end
      | _, _ => False
    end.


  Opaque cc_approx_clos.

  (** Correspondence of the two definitions *)
  Lemma cc_approx_val_eq (k j : nat) IP P b d (v1 v2 : ans) :
    cc_approx_val k j IP P b d v1 v2 <-> cc_approx_val' k j IP P b d v1 v2.
  Proof.
    destruct k as [ | k ]; destruct j as [| j];
    destruct v1 as [[[l1 | lf1 f1] H1] | |]; destruct v2 as [[[l2 | lf2 f2] H2] | |];
    try (now split; intros; contradiction);
    try (now simpl; eauto).  
    - split; simpl; [ intros [Heqb Hc] |];
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
      { destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct b2 as [c2 vs2 | ]; try contradiction.
        destruct Hc as [Heq' [Heq'' Hyp]]. 
        split. eauto. now split; eauto.
        
        destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hc as [Hin [Henv Hyp]]. 
        split; eauto. split; eauto. split; eauto.

        intros i Hlt; omega.

        intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft
               e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hfind Hdef Hset.
        edestruct Hyp
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try now eauto. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct b2 as [c2 vs2 | ]; eauto. 
        + clear; now firstorder.
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heqb [Him [_ Hyp]]]. split; eauto. split; eauto.
          split.

          intros i Hlt; omega.

          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft
                 e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; eauto. }
    - split; simpl; [ intros [Heqb Hc] |];
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto.
      { destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct b2 as [c2 vs2 | ]; try contradiction.
        + destruct Hc as [Hin [Hd Hyp]].
          split; [ eassumption | split; [ eassumption |]].
          split; [ eassumption |].
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite !Heqi in Hap. 
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          destruct Hc as [Hd [Henv Hyp]].
          subst. split; eauto. split; eauto. split.
 
          intros i Hlt.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite <- Heqi. now eapply Henv; eauto.
          
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1
                 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto). }
      { destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct b2 as [c2 vs2 | ]; eauto.
        + intros [Heq1 [Heq2 [Hd Hi]]].
          subst. split; [ reflexivity | split; [ eassumption |]].
          split; [ reflexivity |].
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega. rewrite !Heqi.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heqb [Heqd [Henv Hyp]]]. split; eauto. split; eauto.
          split.
          intros i Hlt. assert (Heqi : j - (j - i) = i) by omega.
          rewrite Heqi. now eapply Henv; eauto.
          
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
                 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto). }
    - split; simpl; [ intros [Heqb Hc] |];
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto.
      { destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct b2 as [c2 vs2 | ]; try contradiction.
        + destruct Hc as [Hc [Hd Hyp]].
          split; eauto. split; eauto. split; eauto. intros; omega.
        + simpl. destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          destruct Hc as [Hc [Henv Hyp]].
          subst. split; eauto. split; eauto.
          split.

          intros; omega.
          
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
                 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          simpl. intros i j' b' Hleq Hleq' Hfeq Hall.
          assert (Heqi : k - (k - i) = i) by omega.
          setoid_rewrite <-  Heqi. eapply Hi; eauto.
          eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap. rewrite Heqi. simpl in Hap. eassumption.
      }
      { destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct b2 as [c2 vs2 | ]; eauto.
        + intros [Heq1 [Heq2 [Heq3 Hi]]].
          subst. split; [ reflexivity | split; [ eassumption |]]; eauto.
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heq1 [Heq2 [Henv Hyp]]].
          subst. split; eauto. split; eauto. split.

          intros i Hlt; omega.
          
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft
                 e1 vs1 vs2 Heq1 Hr1 Heq2' Hr2 Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          intros i j b' Hleq Hleq' Hall Hfeq.
          assert (Heqi : k - (k - i) = i) by omega.
          setoid_rewrite Heqi. eapply Hi; eauto.
          eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap. rewrite <- Heqi. eassumption.
      }
    - split; simpl; [ intros [Heqb Hc] |];
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto.
      { destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1];
        destruct b2 as [c2 vs2 | ]; try contradiction.
        + destruct Hc as [Heq2 [Heq3 Hi]]; split; [ eassumption | split; [eassumption |]].
          split. eassumption.
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite !Heqi in Hap.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          destruct Hc as [Heq2 [Henv Hyp]]; split; eauto. split; eauto.
          split.

          intros i Hlt.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite <- Heqi. now eapply Henv; eauto.
          
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1
                 ft e1 vs1 vs2 Heq1 Hr1 Heq2' Hr2 Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          simpl. intros i j' b' Hleq Hleq' Hfeq Hall.
          assert (Heqi : k - (k - i) = i) by omega.
          setoid_rewrite <- Heqi. eapply Hi; eauto.
          eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap. rewrite Heqi. eassumption.
      }
      { destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct b2 as [c2 vs2 | ]; eauto.
        + intros [Heq1 [Heq2 [Heq3 Hi]]].
          subst. split; [ reflexivity | split; [ eassumption |]]; eauto.
          split. reflexivity.

          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega. rewrite !Heqi.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Hb [Hd [Henv Hyp]]].
          split; eauto. split; eauto. split.

          intros i Hlt.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite Heqi. now eapply Henv; eauto.
          
          intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1
                 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2  Hfind Hdef Hset.
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
    Definition cc_approx_var_env (k j : nat) IP P b d (H1 : heap block) (rho1 : env)
               (H2 : heap block) (rho2 : env) (x y : var) : Prop :=
      forall l1, 
        M.get x rho1 = Some l1 -> 
        exists l2, M.get y rho2 = Some l2 /\
              cc_approx_val' k j IP P b d (Res (l1, H1)) (Res (l2, H2)).
    
    (** Environment relation for a set of points (i.e. predicate over variables) :
     * ρ1 ~_k^S ρ2 iff 
     *  forall x, S x -> ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
    Definition cc_approx_env_P (S : Ensemble var) k j IP P b d (c1 c2 : heap block * env) :=
      let (H1, rho1) := c1 in
      let (H2, rho2) := c2 in
      forall (x : var), S x -> cc_approx_var_env k j IP P b d H1 rho1 H2 rho2 x x.

    Notation "p1 ≺ ^ ( k ; j ; IP ; P ; b ; d ) p2" := (cc_approx_val' k j IP P b d p1 p2)
                                                         (at level 70, no associativity).
    
    Notation "p1 ⋞ ^ ( R ; k ; j ; IP ; P ; b ; d ) p2" := (cc_approx_env_P R k j IP P b d p1 p2)
                                                             (at level 70, no associativity).

    Definition cc_approx_heap (S : Ensemble loc) k j IP P b d (H1 H2 : heap block) :=
      forall (x : loc), S x -> Res (Loc x, H1) ≺ ^ ( k ; j ; IP ; P ; b ; d ) Res (Loc (b x), H2).


    Notation "S |- H1 ≼ ^ ( k ; j ; IP ; P ; b ; d ) H2" :=
      (cc_approx_heap S k j IP P b d H1 H2) (at level 70, no associativity).
  
  
  (** Environment relation for the whole domain of definition :
    * ρ1 ~_k ρ2 iff forall x, ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
    Definition cc_approx_env (k j : nat) IP P b d c1 c2 : Prop :=
    c1 ⋞ ^ (Full_set _; k; j; IP; P; b; d) c2.
  
  (** * Environment Invariants for Closure Conversion *)
  
  (** Naming conventions in the following  :

     [Scope] : The set of variables currently in scope.
 
     [Funs]  : The set of variables in the current block of mutually recursive
               functions.

     [FVs]   : The list of free variables (needs to be ordered).

     [Γ]     : The formal parameter of the environment after closure conversion. *)
  
  Section LogRelLemmas.
    
    Context (LIP : IInv)
            (GIP : GIInv)
            (LP : Inv)
            (GP : GInv)
            (b : Inj)
            (d : EInj).
    
  (** * Monotonicity Properties *)
  
  (** The environment relation is antimonotonic in the set of free variables *) 
  Lemma cc_approx_env_P_antimon (S1 S2 : Ensemble var) (k j : nat)
        (c1 c2 : (heap block) * env) :
    c1 ⋞ ^ ( S2 ; k ; j ; GIP ; GP ; b; d) c2 ->
    S1 \subset S2 ->
    c1 ⋞ ^ ( S1 ; k ; j ; GIP ; GP ; b; d) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre Hin x Hin'. eapply Hpre; eapply Hin; eauto.
  Qed.

  Lemma cc_approx_heap_antimon P1 P2 k j IP P (H1 H2 : heap block) :
    P1 \subset P2 ->
    P2 |- H1 ≼ ^ ( k ; j ; IP ; P ; b ; d ) H2 ->
    P1 |- H1 ≼ ^ ( k ; j ; IP ; P ; b ; d ) H2.
  Proof.
    intros Hsub Hcc x Hin. eapply Hcc; eauto. eapply Hsub; eauto.
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
    (forall m b d r1 r2,
       m <= k ->
       r1 ≺ ^ (m ; j ; GIP1 ; GP1 ; b; d) r2 ->
       r1 ≺ ^ (m ; j ; GIP1 ; GP2 ; b; d) r2) ->
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP1 ; GP1 ) p2 ->
    (forall i, same_relation _ (GP1 i) (GP2 i)) ->
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP1 ; GP2 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2].
    intros IH Hcc Hin b1 b2 H1' H2' rho1' rho2'
           v1 c1 m1 HH1 Hr1 HH2 Hr2 Hip Hleq Hstep Hstuck.
    edestruct Hcc as [v2 [c2 [m2 [b' [Hstep2 [Hinj [HP Hval]]]]]]]; eauto.
    repeat eexists; eauto.
    rewrite cc_approx_val_eq.
    eapply IH; eauto. omega.
    rewrite <- cc_approx_val_eq; eauto.    
  Qed.
  
  Opaque cc_approx_exp.
  
  Lemma cc_approx_val_same_rel (k j : nat) (GP1 GP2 : GInv) (b1 : Inj) (d1 : EInj) r1 r2 :
    r1 ≺ ^ (k ; j ; GIP ; GP1 ; b1 ; d1 ) r2 ->
    (forall i, same_relation _ (GP1 i) (GP2 i)) ->
    r1 ≺ ^ (k ; j ; GIP ; GP2 ; b1 ; d1 ) r2.
  Proof.
    revert j b1 d1 GP1 GP2 r1 r2.
    induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1.
    intros b' d1 GP1 GP2 r1 r2.
    destruct r1 as [[[l1 | lf1 f1] H1] | |];
      destruct r2 as [[[l2 | lf2 f2] H2] | |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
    destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
      destruct b2 as [c2 vs2 | ]; eauto; intros [Heq Hcc] Hrel; split; eauto.
    - destruct Hcc as [Heq' [Heq'' Hcc]]. split; [ eassumption |].
      split; [ eassumption | ].
      intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
      intros x1 x2 Hap.
      rewrite cc_approx_val_eq in *. eapply IHj; try eassumption.
    - destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
      destruct Hcc as [Hd [Henv Hcc]]. split; eauto.
      split; eauto.

      intros i Hlt.
      edestruct Henv as (c & vs & FVs & Hnd & Hget1 & Heqfv & Hall); try eassumption.
      do 3 eexists. split. eassumption. split. eassumption.
      split. eassumption. eapply Forall2_monotonic; [| eassumption ].
      intros x1 x2 [l1' [Hget Hval]].
      eexists; split; eauto. rewrite cc_approx_val_eq in *.
      eapply IHj; eassumption.
      
      intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
             vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hfind Hdef Hset.
      edestruct Hcc
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
      do 3 eexists; split; [ | split ]; try (now eauto).
      intros i j'  Hleq Hleq' b'' d''. simpl. intros Hrel' Hfeq1 Hfeq2.
      split.
      edestruct (Hi i j') as [HI Hcc']; eauto.
      + eapply Forall2_monotonic; [| eassumption ].
        intros. rewrite cc_approx_val_eq.
        eapply IHk; eauto. now rewrite <- cc_approx_val_eq; simpl in *; eauto.
        intros. split; now eapply Hrel.
      + eapply cc_approx_exp_same_rel_IH with (GP1 := GP1); try eassumption.
        intros; eapply IHk. omega. eassumption. eassumption.
        eapply cc_approx_exp_rel_mon. eapply Hi. eassumption.
        eassumption.
        eapply Forall2_monotonic; [| eassumption ].
        intros. rewrite cc_approx_val_eq.
        eapply IHk; eauto. now rewrite <- cc_approx_val_eq; simpl in *; eauto.
        intros. split; now eapply Hrel. eassumption. eassumption.
        now eapply Hrel.
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
  Lemma cc_approx_val_monotonic (k m j : nat) (r1 r2 : ans) b' d' :
    r1 ≺ ^ (k; j; GIP ; GP; b'; d') r2 ->
    m <= k ->
    r1 ≺ ^ (m; j; GIP ; GP; b'; d') r2.
  Proof.
    revert j k r1 r2. induction m as [m IHk] using lt_wf_rec1.
    intros j. induction j as [j IHj] using lt_wf_rec1.
    intros k r1 r2.
    destruct r1 as [[[l1 | lf1 f1] H1] | |]; destruct r2 as [[[l2 | lf2 f2] H2] | |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    - destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
      intros [Heq Hcc] Hleq. split; [ eassumption |].
      destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct b2 as [c2 vs2 | ]; eauto.
      + destruct Hcc as [Heq' [Heq'' Hi]]; split; [ eassumption |].
        split; [ eassumption |]. intros i Hleq'. simpl.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; try eassumption.
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hcc as [Hd [Henv Hcc]]. split; eauto.
        split; eauto.

        intros i Hlt.
        edestruct Henv as (c & vs & FVs & Hnd & Hget1 & Heqfv & Hall); try eassumption.
        do 3 eexists. split. eassumption. split. eassumption. split. eassumption.
        eapply Forall2_monotonic; [| eassumption ].
        intros x1 x2 [l1' [Hget Hval]]. eexists; split. eassumption.
        rewrite cc_approx_val_eq in *. eapply IHj; eassumption.

        intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc'
               xs1 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hfind Hdef Hset.
        edestruct Hcc
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi'); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i j' Hleq' Hleq'' R Hfeq Hall. 
        eapply Hi'; try eassumption. omega.
  Qed.

  Lemma cc_approx_heap_monotonic S (k m j : nat) (H1 H2 : heap block) b' d' :
    S |- H1 ≼ ^ (k; j; GIP; GP; b'; d') H2 ->
    m <= k ->
    S |- H1 ≼ ^ (m; j; GIP; GP; b'; d') H2.
  Proof.
    intros Hheap Hleq x Hin. eapply cc_approx_val_monotonic; eauto.
  Qed.

  Lemma cc_approx_clos_monotonic S (k m j : nat) (p1 : env * heap block)
        (p2 : loc * heap block) b' d' :
    p1 << ^ (k; j; GIP; GP; b'; d'; S) p2 ->
    m <= k ->
    p1 << ^ (m; j; GIP; GP; b'; d'; S) p2.
  Proof.
    intros Hheap Hleq. destruct p1 as [rho1 H1]. destruct p2 as [l2 H2]. 
    edestruct Hheap as (c & vs & FVs & Hnd & Hget1 & Heqfv & Hall); try eassumption.
    do 3 eexists. split. eassumption. split. eassumption. split. eassumption.
    eapply Forall2_monotonic; [| eassumption ].
    intros x1 x2 [y [Hval Hcc]]. 
    eexists; split.
    eassumption.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_monotonic; eauto.
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
    
    omega. do 5 eexists; repeat split; eauto.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_monotonic; eauto. omega.
  Qed.
  
  
  (** The environment relations are anti-monotonic in the step index *)
  Lemma cc_approx_env_P_monotonic (R : Ensemble var) (k m j : nat)
        c1 c2 :
    c1 ⋞ ^ ( R ; k ; j ; GIP ; GP ; b ; d) c2 ->
    m <= k ->
    c1 ⋞ ^ ( R ; m ; j ; GIP ; GP ; b ; d) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hcc Hleq x HP v Hget.
    edestruct Hcc as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.
  
  Lemma cc_approx_env_monotonic (k m j : nat) c1 c2 :
    cc_approx_env k j GIP GP b d c1 c2 ->
    m <= k ->
    cc_approx_env m j GIP GP b d c1 c2.
  Proof.
    intros Hleq H. eapply cc_approx_env_P_monotonic; eauto.
  Qed.  
  
  (** The value relation is monotonic in the heap index *)
  Lemma cc_approx_val_j_monotonic GIP' GP' (k i j : nat) (r1 r2 : ans) b' d' :
    r1 ≺ ^ (k; j; GIP' ; GP' ; b'; d') r2 ->
    i <= j ->
    r1 ≺ ^ (k; i; GIP' ; GP' ; b'; d') r2.
  Proof.
    destruct r1 as [[[l1 | lf1 f1] H1] | |]; destruct r2 as [[[l2 | lf2 f2] H2] | |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
    intros [Heq Hcc] Hleq. split; [ eassumption |].
    destruct b1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
      destruct b2 as [c2 vs2 | ]; eauto.
    + destruct Hcc as [Heq' [Heq'' Hi]]; split; [ eassumption |].
      split. eassumption. intros i' Hleq'. simpl. eapply (Hi i'); omega.
    + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
      destruct Hcc as [Hd [Henv Hcc]]. split; eauto.
      split.

      intros j' Hlt. eapply Henv. omega. 
      
      intros b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc'
             xs1 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hfind Hdef Hset.
      edestruct Hcc
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi'); eauto.
      do 3 eexists; split; [ | split ]; try (now eauto).
      intros i' j' Hleq' Hleq'' R Hall. eapply Hi'. eassumption.
      omega.
  Qed.

   Lemma cc_approx_heap_j_monotonic S (k j i : nat) (H1 H2 : heap block) b' d' :
    S |- H1 ≼ ^ (k; j; GIP; GP; b'; d') H2 ->
    i <= j ->
    S |- H1 ≼ ^ (k; i; GIP; GP; b'; d') H2.
  Proof.
    intros Hheap Hleq x Hin. eapply cc_approx_val_j_monotonic; eauto.
  Qed.

  Lemma cc_approx_clos_j_monotonic S (k j i : nat)  (p1 : env * heap block)
        (p2 : loc * heap block) b' d' :
    p1 << ^ (k; j; GIP; GP; b'; d'; S) p2 ->
    i <= j ->
    p1 << ^ (k; i; GIP; GP; b'; d'; S) p2.
  Proof.
    intros Hheap Hleq. destruct p1 as [rho1 H1]. destruct p2 as [l2 H2]. 
    edestruct Hheap as (c & vs & FVs & Hnd & Hget1 & Heqfv & Hall); try eassumption.
    do 3 eexists. split. eassumption. split. eassumption. split. eassumption.
    eapply Forall2_monotonic; [| eassumption ].
    intros x1 x2 [y [Hget Hval]].
    eexists; split; eauto.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_j_monotonic; eauto.
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
    do 5 eexists; repeat split; eauto.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.
  
  
  (** The environment relations are anti-monotonic in the step index *)
  Lemma cc_approx_env_P_j_monotonic (R : Ensemble var) (k j j' : nat)
        c1 c2 :
    c1 ⋞ ^ ( R ; k ; j ; GIP ; GP ; b ; d) c2 ->
    j' <= j ->
    c1 ⋞ ^ ( R ; k ; j' ; GIP ; GP ; b ; d) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hcc Hleq x HP v Hget.
    edestruct Hcc as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.
  
  Lemma cc_approx_env_j_monotonic (k j' j : nat) c1 c2 :
    cc_approx_env k j GIP GP b d c1 c2 ->
    j' <= j ->
    cc_approx_env k j' GIP GP b d c1 c2.
  Proof.
    intros Hleq H. eapply cc_approx_env_P_j_monotonic; eauto.
  Qed.
  
  (** * Set lemmas *)
  
  Lemma cc_approx_env_Empty_set (k j : nat) c1 c2 :
    c1 ⋞ ^ ( Empty_set var ; k ; j ; GIP ; GP ; b ; d) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    simpl. intros x Hc. inv Hc.
  Qed.
  
  Lemma cc_approx_env_P_union (P1 P2 : Ensemble var) (k j : nat) c1 c2 :
    c1 ⋞ ^ ( P1 ; k ; j ; GIP ; GP ; b ; d) c2 ->
    c1 ⋞ ^ ( P2 ; k ; j ; GIP ; GP ; b ; d) c2 ->
    c1 ⋞ ^ ( P1 :|: P2 ; k ; j ; GIP ; GP ; b ; d) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre1 Hpre2 x HP2. inv HP2; eauto.
  Qed.
  
  Lemma cc_approx_env_P_inter_l (P1 P2 : Ensemble var) (k j : nat) c1 c2 :
    c1 ⋞ ^ ( P1 ; k ; j ; GIP ; GP ; b ; d) c2 ->
    c1 ⋞ ^ ( P1 :&: P2 ; k ; j ; GIP ; GP ; b ; d) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre x HP2. inv HP2; eauto.
  Qed.
  
  Lemma cc_approx_env_P_inter_r (P1 P2 : Ensemble var) (k j : nat) c1 c2 :
    c1 ⋞ ^ ( P2 ; k ; j ; GIP ; GP ; b ; d) c2 ->
    c1 ⋞ ^ ( P1 :&: P2 ; k ; j ; GIP ; GP ; b ; d) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre x HP2. inv HP2; eauto.
  Qed.

  Lemma cc_approx_heap_Empty_set (k j : nat) c1 c2 :
    Empty_set var |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ; d) c2.
  Proof.
    now firstorder.
  Qed.
  
  Lemma cc_approx_heap_union (S1 S2 : Ensemble var) (k j : nat) c1 c2 :
    S1 |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ; d) c2 ->
    S2 |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ; d) c2 ->
    S1 :|: S2 |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ; d) c2.
  Proof.
    intros Hcc1 Hcc2 x Hin; inv Hin; eauto.
  Qed.
  
  Lemma cc_approx_heap_inter_l (S1 S2 : Ensemble var) (k j : nat) c1 c2 :
    S1 |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ; d) c2 ->
    S1 :&: S2  |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ; d) c2.
  Proof.
    intros Hpre x HP2. eapply Hpre; eauto.
    now inv HP2.
  Qed.

  Lemma cc_approx_heap_inter_r (S1 S2 : Ensemble var) (k j : nat) c1 c2 :
    S2 |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ; d) c2 ->
    S1 :&: S2  |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ; d) c2.
  Proof.
    intros Hpre x HP2. eapply Hpre; eauto.
    now inv HP2.
  Qed.
  
  (** * Preservation under enviroment extension lemmas *)
  
  Lemma cc_approx_var_env_set_eq :
    forall (k j : nat) (rho1 rho2 : env) (H1 H2 : heap block)
      (x y : var) (v1 v2 : value),
      (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b ; d) (Res (v2, H2)) ->
      cc_approx_var_env k j GIP GP b d H1 (M.set x v1 rho1) H2 (M.set y v2 rho2) x y.
  Proof.
    intros rho1 rho2 H1 H2 k j x y v1 v2 Hval x' Hget.
    rewrite M.gss in Hget. inv Hget. eexists.
    rewrite M.gss. split; eauto.
  Qed.
  
  Lemma cc_approx_var_env_set_neq :
    forall (k j : nat)  (rho1 rho2 : env) (H1 H2 : heap block)
      (x1 x2 y1 y2 : var) (v1 v2 : value),
      cc_approx_var_env k j GIP GP b d H1 rho1 H2 rho2 y1 y2 ->
      y1 <> x1 -> y2 <> x2 ->
      cc_approx_var_env k j GIP GP b d H1 (M.set x1 v1 rho1) H2 (M.set x2 v2 rho2) y1 y2.
  Proof. 
    intros k j rho1 rho2 H1 H2 x1 x2 y1 y2 v1 v2 Hval Hneq Hneq' x' Hget.
    rewrite M.gso in *; eauto.
  Qed.
  
  Lemma cc_approx_var_env_set :
    forall (k j : nat)  (rho1 rho2 : env) (H1 H2 : heap block)
      (x y : var) (v1 v2 : value),
      cc_approx_var_env k j GIP GP b d H1 rho1 H2 rho2 y y ->
      (Res (v1, H1)) ≺ ^ (k; j; GIP ; GP; b; d) (Res (v2, H2)) ->
      cc_approx_var_env k j GIP GP b d H1 (M.set x v1 rho1) H2 (M.set x v2 rho2) y y.
  Proof.
    intros k j rho1 rho2 H1 H2 x y v1 v2 Hvar Hval.
    destruct (peq y x); subst.
    - apply cc_approx_var_env_set_eq; eauto.
    - apply cc_approx_var_env_set_neq; eauto.
  Qed.
  
  Lemma cc_approx_var_env_set_neq_r :
    forall (k j : nat)  (rho1 rho2 : env) (H1 H2 : heap block)
      (y1 x2 y2 : var) ( v2 : value),
      cc_approx_var_env k j GIP GP b d H1 rho1 H2 rho2 y1 y2 ->
      y2 <> x2 ->
      cc_approx_var_env k j GIP GP b d H1 rho1 H2 (M.set x2 v2 rho2) y1 y2.
  Proof. 
    intros k j rho1 rho2 H1 H2 x2 y1 y2 v2 Hval Hneq x' Hget.
    rewrite M.gso in *; eauto.
  Qed.

  
  (** Extend the related environments with a single point *)
  Lemma cc_approx_env_P_set (S : Ensemble var) (k j : nat)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v1 v2 : value) :
      (H1, rho1) ⋞ ^ ( S \\ [set x] ; k ; j ; GIP ; GP ; b; d) (H2, rho2) ->
      (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP; b; d) (Res (v2, H2)) ->
      (H1, M.set x v1 rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b; d) (H2, M.set x v2 rho2).
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
    (H1, rho1) ⋞ ^ ( S \\ (FromList xs) ; k ; j ; GIP ; GP ; b ; d) (H2, rho2) ->
    Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b ; d) (Res (v2, H2))) vs1 vs2 ->
    setlist xs vs1 rho1 = Some rho1' ->
    setlist xs vs2 rho2 = Some rho2' ->
    (H1, rho1') ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ; d) (H2, rho2').
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
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ; d) (H2, rho2) ->
    ~ x \in S ->
    (H1, M.set x v rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ; d) (H2, rho2).
  Proof. 
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    destruct (peq y x); subst.
    - contradiction.
    - rewrite M.gso in Hget; eauto.
  Qed.
  
  Lemma cc_approx_env_P_set_not_in_P_r (S : Ensemble var) (k j : nat)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v : value) :
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ; d) (H2, rho2) ->
    ~ x \in S ->
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ; d) (H2, M.set x v rho2).
  Proof. 
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    exists v''. rewrite M.gsspec.
    destruct (peq y x); subst.
    - contradiction.
    - eauto.
  Qed.
  
  (** * The logical relation respects function extensionality *)

  Instance Proper_cc_approx_val_f_eq :
    Proper (eq ==> eq ==> eq ==> eq ==> f_eq ==> eq ==> eq ==> eq ==> iff) cc_approx_val'.
  Proof.
    clear.
    intros k' k Heq1 j' j Heq2  GI GI' Heq3 II II' Heq4 b1 b2 Heq5 d1 d2 Heqd
           r1' r1 Heq6 r2' r2 Heq7; subst.
    revert j b1 b2 Heq5 r1 r2. induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1. intros b1 b2 Heq5 r1 r2.
    simpl. 
    destruct r1 as [[v1 H1] | |];  destruct r2 as [[v2 H2] | |]; try now eauto.
    destruct v1 as [l1 | ? ? ]; destruct v2 as [l2 | ? ?]; try now eauto.
    split; intros Hres.
    - simpl in *. destruct (get l1 H1) as [bl1 |]; eauto; destruct (get l2 H2) as [bl2 |]; eauto.
      destruct Hres as [Heq Hres]; split; eauto; try (rewrite <- Heq5; eassumption). 
      destruct bl1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct bl2 as [c2 vs2 | ]; eauto.
      + destruct Hres as [Heq1 [Heq2 Hi]]. split; eauto. split; eauto.
        intros i' Hleq.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; eauto. symmetry. eassumption.
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hres as [Hd [Henv Hres]]. split. eassumption. split.

        intros i Hlt.
        edestruct Henv as (c & vs & FVs & Hnd & Hget1 & Heqfv & Hall); try eassumption.
        do 3 eexists. split. eassumption. split. eassumption.
        split. eassumption. eapply Forall2_monotonic; [| eassumption ].
        intros x1 x2 [y [Hgety Hval]].
        eexists; split; eauto. 
        rewrite cc_approx_val_eq in *. eapply IHj. omega. symmetry. eassumption.
        eassumption. 
        
        intros b1' b2' tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
               vs1 vs2 Heq1' Hr1' Heq2 Hr2 Hfind Hdef Hset.
        edestruct Hres
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i' j' b' Hleq Hleq' HR Hfeq Hall. eapply Hi. eassumption. eassumption.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eassumption.
        eapply Equivalence_Transitive; [| eassumption ]. eapply f_eq_subdomain_compose_compat.
        reflexivity. eapply f_eq_subdomain_compose_compat; [| reflexivity ].
        rewrite Heq5. reflexivity.
      + rewrite <- Heq5; eauto.
      + rewrite <- Heq5; eauto.
      + rewrite <- Heq5; eauto. 
    - simpl in *.
      destruct (get l1 H1) as [bl1 |]; eauto. destruct (get l2 H2) as [bl2 |]; eauto.
      destruct Hres as [Hbeq Hres]; split. rewrite Heq5. eassumption.
      destruct bl1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct bl2 as [c2 vs2 | ]; eauto.
      + destruct Hres as [Heq1 [Heq2 Hi]]. split; eauto.
        split; eauto.
        
        intros i' Hleq.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; eauto.

      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hres as [Hd [Henv Hres]].
        split; eauto. split; eauto.

        intros i Hlt.
        edestruct Henv as (c & vs & FVs & Hnd & Hget1 & Heqfv & Hall); try eassumption.
        do 3 eexists. split. eassumption. split. eassumption.
        split. eassumption.
        eapply Forall2_monotonic; [| eassumption ].
        intros x1 x2 [y [Hgety Hval]].
        eexists; split; eauto.
        rewrite cc_approx_val_eq in *. eapply IHj. omega. eassumption.
        eassumption. 
        
        intros b1' b2' tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
               vs1 vs2 Heq1' Hr1' Heq2 Hr2 Hfind Hdef Hset.
        edestruct Hres
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i' j' b' Hleq Hleq' HR Hfeq Hall. eapply Hi. eassumption. eassumption.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eassumption.
        eapply Equivalence_Transitive; [| eassumption ]. eapply f_eq_subdomain_compose_compat.
        reflexivity. eapply f_eq_subdomain_compose_compat; [| reflexivity ].
        rewrite Heq5. reflexivity.
      + rewrite Heq5; eauto.
      + rewrite Heq5; eauto.
  Qed.
  
  Instance Proper_cc_approx_val_f_eq' :
    Proper (eq ==> eq ==> eq ==> eq ==> eq ==> f_eq ==> eq ==> eq ==> iff) cc_approx_val'.
  Proof.
    clear.
    intros k' k Heq1 j' j Heq2  GI GI' Heq3 II II' Heq4 b1 b2 Heq5 d1 d2 Heqd
           r1' r1 Heq6 r2' r2 Heq7; subst.
    revert j d1 d2 Heqd r1 r2. induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1. intros d1 d2 Heqd r1 r2.
    simpl. 
    destruct r1 as [[v1 H1] | |];  destruct r2 as [[v2 H2] | |]; try now eauto.
    destruct v1 as [l1 | ? ? ]; destruct v2 as [l2 | ? ?]; try now eauto.
    split; intros Hres.
    - simpl in *. destruct (get l1 H1) as [bl1 |]; eauto; destruct (get l2 H2) as [bl2 |]; eauto.
      destruct Hres as [Heq Hres]; split; eauto; try (rewrite <- Heq5; eassumption). 
      destruct bl1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct bl2 as [c2 vs2 | ]; eauto.
      + destruct Hres as [Heq1 [Heq2 Hi]]. split; eauto.
        split; eauto. now rewrite <- Heqd; eauto.
        
        intros i' Hleq.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; eauto. symmetry. eassumption.

      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hres as [Heq1 [Henv Hres]]. split. rewrite <- Heqd. eassumption.
        split.

        intros i' Hleq.
        edestruct Henv as (c & vs & FVs & Hnd & Hget1 & Heqfv & Hall); try eassumption.
        do 3 eexists. split. eassumption. split. eassumption. split. eassumption.
        eapply Forall2_monotonic; [| eassumption ].
        intros x1 x2 [y [Hget Hval]]. eexists; split; eauto.
        rewrite cc_approx_val_eq in *. eapply IHj. omega. symmetry. eassumption.         
        eassumption.

        intros b1' b2' tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
               vs1 vs2 Heq1' Hr1' Heq2 Hr2 Hfind Hdef Hset.
        edestruct Hres
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i' j' b' d' Hleq Hleq' Hall Hfeq Hfeq'. eapply Hi. eassumption. eassumption.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eassumption. eassumption.
        eapply Equivalence_Transitive; [| eassumption ]. eapply f_eq_subdomain_compose_compat.
        reflexivity. eapply f_eq_subdomain_compose_compat; [| reflexivity ].
        rewrite <- Heqd. reflexivity.
    - simpl in *.
      destruct (get l1 H1) as [bl1 |]; eauto.
      destruct (get l2 H2) as [bl2 |]; eauto.
      destruct Hres as [Hbeq Hres]; split. eassumption.
      destruct bl1 as [c1 vs1 | [? | B1 f1] env_loc1 ];
        destruct bl2 as [c2 vs2 | ]; eauto.
      + destruct Hres as [Heq1 [Heq2 Hi]]. split; eauto.
        split. rewrite Heqd. eassumption.

        intros i' Hleq.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; eauto.

      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hres as [Hd1 [Henv Hres]].
        split; eauto. rewrite Heqd; eassumption.
        split.

        intros i' Hleq.
        edestruct Henv as (c & vs & FVs & Hnd & Hget1 & Heqfv & Hall); try eassumption.
        do 3 eexists. split. eassumption. split. eassumption. split. eassumption.
        eapply Forall2_monotonic; [| eassumption ].
        intros x1 x2 [y [Hgety Hval]]. eexists; split; eauto.
        rewrite cc_approx_val_eq in *.
        eapply IHj. omega. eassumption.
        eassumption.
        
        intros b1' b2' tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
               vs1 vs2 Heq1' Hr1' Heq2 Hr2 Hfind Hdef Hset.
        edestruct Hres
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i' j' b' d' Hleq Hleq' HR Hfeq Hfeq'. eapply Hi. eassumption. eassumption.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eassumption. eassumption.
        eapply Equivalence_Transitive; [| eassumption ]. eapply f_eq_subdomain_compose_compat.
        reflexivity. eapply f_eq_subdomain_compose_compat; [| reflexivity ].
         rewrite Heqd. reflexivity.
  Qed.
  
  Instance Proper_cc_approx_env_P_f_eq' :
    Proper (eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> f_eq ==> eq ==> eq ==> iff) cc_approx_env_P.
  Proof.
    intros S' S Heq k' k Heq1 j' j Heq2  GI GI' Heq3 II II' Heq4 b1 b2 Heq5 d1 d2 Heqd
           [H1' rho1'] [H1 rho1] Heq6 [H2' rho2'] [H2 rho2] Heq7; inv Heq6; inv Heq7; subst.
    split; intros Hcc x Hin v Hget.
    edestruct Hcc as [l2 [Hget' Hres]]; eauto. eexists; split; eauto.
    rewrite <- Heqd. eassumption.
    edestruct Hcc as [l2 [Hget' Hres]]; eauto. eexists; split; eauto.
    rewrite Heqd. eassumption.
  Qed.    

  (* TODO Maybe add more instances? *)

  (** * Reachable set bijections *)
  Lemma cc_approx_val_image_eq (k : nat) (β : Inj) (δ : EInj) (H1 H2 : heap block)
        (v1 v2 : value) :
    (forall j, (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β; δ) (Res (v2, H2))) ->
    image β (reach' H1 (val_loc v1)) :|: image' δ (reach' H1 (val_loc v1)) <-->
    reach' H2 (val_loc v2). 
  Proof with now eauto with Ensembles_DB.
    intros Hval. split.
    - intros l' [l [l1 [[n [_ Hp]] Heq]] | l [l1 [[n [_ Hp]] Heq]]]; subst.
      + revert l1 v1 v2 Hval Hp. clear.
        induction n; intros l1 v1 v2 Hval Hp. 
        * simpl in Hp. eapply reach'_extensive.
          destruct v1 as [l'|]; inv Hp.
          specialize (Hval 1).
          destruct v2 as [l2 | ]; try contradiction.
          destruct Hval as [Hcc Hval]. subst.
          destruct (get l1 H1) as [b1'|] eqn:Hget1;
            destruct (get (β l1) H2) as [b2'|] eqn:Hget2; try contradiction;
          destruct b1' as [c1 vs1 | [? | B1 f1] env_loc1 ]; try contradiction;
          destruct b2' as [c2 vs2 | ]; try destruct Hval as [Heq1 [Heq2 _]]; try contradiction. 
          reflexivity. reflexivity.
        * replace (S n) with (n + 1) in Hp by omega.
          rewrite app_plus in Hp. unfold compose in Hp. simpl in Hp.
          (* eapply IHn in Hin; [| eassumption ].  *)
          assert (Hval' := Hval). specialize (Hval (S n)). 
          destruct v1 as [l1' | lf1 f1]; destruct v2 as [l2' | lf2 f2]; simpl;
          try (now intros; contradiction); try (now simpl; eauto).
          destruct Hval as [Heq Hcc]. subst.
          destruct (get l1' H1) as [b1'|] eqn:Hget1;
            destruct (get (β l1') H2) as [b2'|] eqn:Hget2; try contradiction;
          destruct b1' as [c1 vs1 | [? | B1 f1] env_loc1 ]; try contradiction;
          destruct b2' as [c2 vs2 | ]; try destruct Hcc as [Heq1 [Heq2 Hcc]]; try contradiction.
          { subst.
            rewrite reach_unfold. right.
            rewrite post_Singleton; [| eassumption ].
            simpl in Hp.
            assert (Hp' : In _  ((post H1 ^ n) (post H1 [set l1'])) l1) by assumption.
            rewrite (proper_post_n H1) in Hp';
              [| rewrite !post_Singleton; try eassumption; reflexivity ].
            simpl in Hp'. simpl. specialize (Hcc n).
            assert (Hall : forall j, Forall2
                                  (fun l1 l2 : value =>
                                     cc_approx_val k j GIP GP β δ (Res (l1, H1)) (Res (l2, H2))) vs1 vs2).
            { intros j. specialize (Hval' (S j)).
              simpl in Hval'. rewrite Hget1, Hget2 in Hval'.
              destruct Hval' as [Hbeq [Hc [Hdeq Hall]]].
              eapply Hall. omega. }
            eapply Forall2_forall in Hall; [| constructor; exact 0 ]. 
            clear Hget1 Hget2 Hval' Hcc. induction Hall.
            - rewrite post_n_Empty_set in Hp'. inv Hp'.
            - simpl. rewrite reach'_Union.
              simpl in Hp'. rewrite post_n_Union in Hp'.
              inv Hp'; eauto.
              left. eapply IHn.
              intros j. rewrite <- cc_approx_val_eq. now eauto.
              eassumption. }         
          { destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction.
            destruct Hcc as [Heq2 [Henv Hcc]].
            subst.
            rewrite reach_unfold. right.
            rewrite post_Singleton; [| eassumption ].
            simpl in Hp.
            assert (Hp' : In _  ((post H1 ^ n) (post H1 [set l1'])) l1) by assumption.
            rewrite (proper_post_n H1) in Hp';
              [| rewrite !post_Singleton; try eassumption; reflexivity ].
            simpl in Hp'. simpl.
            rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r.
            rewrite (proper_post_n H1) in Hp';
              [| reflexivity ].
            specialize (Henv n (Nat.lt_succ_diag_r n)).
            destruct Henv as (c & vs2' & FVs & Hnd & Hget1' & Hget2' & Hcc').
            rewrite reach_unfold. right.
            rewrite post_Singleton; eauto. clear Hcc.
            simpl.
            edestruct post_n_exists_Singleton as [l3 [Hin1 Hinp]]; try eassumption.
            edestruct Hin1 as [x1 [Hinx Hgetx]]. 
            destruct (M.get x1 env_loc1) as [[ l' |] | ] eqn:Hgetx1; try now inv Hgetx.
            simpl in Hgetx. inv Hgetx. 
            eapply Hnd in Hinx.
            edestruct (@Forall2_exists loc) with (x := x1) as
                [v2 [Hin Hv]]; try eassumption.
            destruct Hv as [l' [Hgetl' Hv]]. 
            eapply reach'_set_monotonic with (S1 := val_loc (Loc (β l'))).
            - eapply In_Union_list. eapply in_map.              
              rewrite cc_approx_val_eq in Hv.
              assert (Heq : v2 = Loc (β l')).
              { destruct v2; try (simpl in *; contradiction).
                destruct Hv as [Heq _]. subst. repeat subst_exp. congruence. }
              subst. eassumption.
            - repeat subst_exp.
              eapply IHn with (v1 := Loc l'); [| try eassumption ].
              intros j. specialize (Hval' (S j)).
              simpl in Hval'. rewrite Hget1, Hget2 in Hval'.
              destruct Hval' as [Hbeq [Hc [Henv _]]].
              specialize (Henv j (Nat.lt_succ_diag_r j)). 
              destruct Henv as (c' & vs2'' & FVs' & Hnd' & Hget1'' & Hget2'' & Hall).
              edestruct (@Forall2_exists loc) with (x := x1) as
                [v2' [Hin' Hv']]; try now apply Hall.
              eapply Hnd'. eapply Hnd. eassumption.
              destruct Hv' as [l'' [Hgetl'' Hv']]. repeat subst_exp.
              rewrite cc_approx_val_eq in Hv'.
              assert (Heq : v2' = Loc (β l'')).
              { destruct v2'; try (simpl in *; contradiction).
                destruct Hv' as [Heq _]. congruence. }
              subst. eassumption.  }
      + revert l1 v1 v2 Hval Hp Heq. clear.
        induction n; intros l1 v1 v2 Hval Hp Heq. 
        * simpl in Hp. eapply Included_post_reach'.
          destruct v1 as [l'|]; inv Hp.
          specialize (Hval 1).
          destruct v2 as [l2 | ]; try contradiction.
          destruct Hval as [Hcc Hval]. subst.
          destruct (get l1 H1) as [b1'|] eqn:Hget1;
            destruct (get (β l1) H2) as [b2'|] eqn:Hget2; try contradiction;
          destruct b1' as [c1 vs1 | [? | B1 f1] env_loc1 ]; try contradiction;
          destruct b2' as [c2 vs2 | ]; try destruct Hval as [Heq1 [Heq2 _]]; try contradiction. 
          congruence.
          destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction.
          destruct Hval as [Heq1 [Heq2 _]].
          simpl. rewrite post_Singleton; eauto. right; simpl.
          left. rewrite Heq1 in Heq. inv Heq; reflexivity.
        * replace (S n) with (n + 1) in Hp by omega.
          rewrite app_plus in Hp. unfold compose in Hp. simpl in Hp.
          (* eapply IHn in Hin; [| eassumption ].  *)
          assert (Hval' := Hval). specialize (Hval (S n)).
          destruct v1 as [l1' | lf1 f1]; destruct v2 as [l2' | lf2 f2]; simpl;
          try (now intros; contradiction); try (now simpl; eauto).
          destruct Hval as [Heq' Hcc]. subst.
          destruct (get l1' H1) as [b1'|] eqn:Hget1;
            destruct (get (β l1') H2) as [b2'|] eqn:Hget2; try contradiction;
          destruct b1' as [c1 vs1 | [? | B1 f1] env_loc1 ]; try contradiction;
          destruct b2' as [c2 vs2 | ]; try destruct Hcc as [Heq1 [Heq2 Hcc]]; try contradiction.
          { subst.
            rewrite reach_unfold. right.
            rewrite post_Singleton; [| eassumption ].
            simpl in Hp.
            assert (Hp' : In _  ((post H1 ^ n) (post H1 [set l1'])) l1) by assumption.
            rewrite (proper_post_n H1) in Hp';
              [| rewrite !post_Singleton; try eassumption; reflexivity ].
            simpl in Hp'. simpl. specialize (Hcc n).
            assert (Hall : forall j, Forall2
                                  (fun l1 l2 : value =>
                                     cc_approx_val k j GIP GP β δ (Res (l1, H1)) (Res (l2, H2))) vs1 vs2).
            { intros j. specialize (Hval' (S j)).
              simpl in Hval'. rewrite Hget1, Hget2 in Hval'.
              destruct Hval' as [Hbeq [Hc [Hdeq Hall]]].
              eapply Hall. omega. }
            eapply Forall2_forall in Hall; [| constructor; exact 0 ]. 
            clear Hget1 Hget2 Hval' Hcc. induction Hall.
            - rewrite post_n_Empty_set in Hp'. inv Hp'.
            - simpl. rewrite reach'_Union.
              simpl in Hp'. rewrite post_n_Union in Hp'.
              inv Hp'; eauto.
              left. eapply IHn.
              intros j. rewrite <- cc_approx_val_eq; now eauto.
              eassumption. eassumption. }
          { destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction.
            destruct Hcc as [Heq2 [Henv Hcc]].
            subst.
            rewrite reach_unfold. right.
            rewrite post_Singleton; [| eassumption ].
            simpl in Hp.
            assert (Hp' : In _  ((post H1 ^ n) (post H1 [set l1'])) l1) by assumption.
            rewrite (proper_post_n H1) in Hp';
              [| rewrite !post_Singleton; try eassumption; reflexivity ].
            simpl in Hp'. simpl.
            rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r.
            rewrite (proper_post_n H1) in Hp';
              [| reflexivity ].
            specialize (Henv n (Nat.lt_succ_diag_r n)).
            destruct Henv as (c & vs2' & FVs & Hnd & Hget1' & Hget2' & Hcc').
            rewrite reach_unfold. right.
            rewrite post_Singleton; eauto. clear Hcc.
            simpl.
            edestruct post_n_exists_Singleton as [l3 [Hin1 Hinp]]; try eassumption.
            
            edestruct Hin1 as [x1 [Hinx Hgetx]]. 
            destruct (M.get x1 env_loc1) as [[ l' |] | ] eqn:Hgetx1; try now inv Hgetx.
            simpl in Hgetx. inv Hgetx. 
            eapply Hnd in Hinx.
            edestruct (@Forall2_exists loc) with (x := x1) as
                [v2 [Hin Hv]]; try eassumption.
            destruct Hv as [l' [Hgetl' Hv]]. 
            eapply reach'_set_monotonic with (S1 := val_loc (Loc (β l'))).
            - eapply In_Union_list. eapply in_map.              
              rewrite cc_approx_val_eq in Hv.
              assert (Heq' : v2 = Loc (β l')).
              { destruct v2; try (simpl in *; contradiction).
                destruct Hv as [Heq' _]. subst. repeat subst_exp. congruence. }
              subst. eassumption.
            - repeat subst_exp.
              eapply IHn with (v1 := Loc l'); try eassumption.
              intros j. specialize (Hval' (S j)).
              simpl in Hval'. rewrite Hget1, Hget2 in Hval'.
              destruct Hval' as [Hbeq [Hc [Henv _]]].
              specialize (Henv j (Nat.lt_succ_diag_r j)). 
              destruct Henv as (c' & vs2'' & FVs' & Hnd' & Hget1'' & Hget2'' & Hall).
              edestruct (@Forall2_exists loc) with (x := x1) as
                [v2' [Hin' Hv']]; try now apply Hall.
              eapply Hnd'. eapply Hnd. eassumption.
              destruct Hv' as [l'' [Hgetl'' Hv']]. repeat subst_exp.
              rewrite cc_approx_val_eq in Hv'.
              assert (Heq' : v2' = Loc (β l'')).
              { destruct v2'; try (simpl in *; contradiction).
                destruct Hv' as [Heq' _]. congruence. }
              subst. eassumption.  }
    - intros l [n [_ Hp]]; subst.
      + revert l v1 v2 Hval Hp. clear.
        induction n as [[|n] IHn] using lt_wf_rec1; intros l1 v1 v2 Hval Hp. 
        * simpl in Hp. left. eapply image_monotonic. eapply reach'_extensive.
          destruct v2 as [l'|]; inv Hp.
          specialize (Hval 1).
          destruct v1 as [l2 | ]; try contradiction.
          destruct Hval as [Hcc Hval]. subst.
          destruct (get l2 H1) as [b1'|] eqn:Hget1;
            destruct (get (β l2) H2) as [b2'|] eqn:Hget2; try contradiction;
          destruct b1' as [c1 vs1 | [? | B1 f1] env_loc1 ]; try contradiction;
          destruct b2' as [c2 vs2 | ]; try destruct Hval as [Heq1 [Heq2 _]]; try contradiction. 
          now eexists; split; eauto.
          now eexists; split; eauto.
        * replace (S n) with (n + 1) in Hp by omega.
          rewrite app_plus in Hp. unfold compose in Hp. simpl in Hp.
          assert (Hval' := Hval). specialize (Hval (S n)).
          destruct v1 as [l1' | lf1 f1]; destruct v2 as [l2' | lf2 f2]; simpl;
          try (now intros; contradiction); try (now simpl; eauto).
          destruct Hval as [Heq' Hcc]. subst.
          destruct (get l1' H1) as [b1'|] eqn:Hget1;
            destruct (get (β l1') H2) as [b2'|] eqn:Hget2; try contradiction;
          destruct b1' as [c1 vs1 | [? | B1 f1] env_loc1 ]; try contradiction;
          destruct b2' as [c2 vs2 | ]; try destruct Hcc as [Heq1 [Heq2 Hcc]]; try contradiction.
          { subst.
            rewrite !(reach_unfold _ [set l1']) at 1.
            rewrite !image_Union, !image'_Union. rewrite <- !Union_assoc. right.
            rewrite Union_assoc. rewrite (Union_commut _ (image' δ [set l1'])).
            rewrite <- Union_assoc. right.
            rewrite !post_Singleton at 1; try eassumption.
            simpl.

            assert (Hp' : In _  ((post H2 ^ n) (post H2 [set (β l1')])) l1) by assumption.
            rewrite (proper_post_n H2) in Hp';
              [| rewrite !post_Singleton; try eassumption; reflexivity ].
            specialize (Hcc n).
            assert (Hall : forall j, Forall2
                                  (fun l1 l2 : value =>
                                     cc_approx_val k j GIP GP β δ (Res (l1, H1)) (Res (l2, H2))) vs1 vs2).
            { intros j. specialize (Hval' (S j)).
              simpl in Hval'. rewrite Hget1, Hget2 in Hval'.
              destruct Hval' as [Hbeq [Hc [Hdeq Hall]]].
              eapply Hall. omega. }
            eapply Forall2_forall in Hall; [| constructor; exact 0 ]. 
            clear Hget1 Hget2 Hval' Hcc. induction Hall.
            - rewrite post_n_Empty_set in Hp'. inv Hp'.
            - simpl. rewrite !reach'_Union, !image_Union, !image'_Union at 1.
              simpl in Hp'. rewrite post_n_Union in Hp'.
              rewrite <- !Union_assoc. rewrite (Union_assoc _ (image' δ (reach' H1 (val_loc x)))).
              rewrite (Union_commut _ (image' δ (reach' H1 (val_loc x)))).
              rewrite <- !Union_assoc.
              rewrite (Union_assoc _ (image' δ (reach' H1 (val_loc x)))). 
              inv Hp'; eauto.
              left. eapply IHn with (m := n). omega.
              intros j. rewrite <- cc_approx_val_eq; now eauto.
              eassumption. } 
          { destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction.
            destruct Hcc as [Heq2 [Henv Hcc]]. subst. clear Hcc.
            rewrite !(reach_unfold _ [set l1']) at 1.
            rewrite !image_Union, !image'_Union. rewrite <- Union_assoc.
            rewrite (Union_assoc _ (image' δ [set l1'])).
            rewrite (Union_commut _ (image' δ [set l1'])).
            rewrite !Union_assoc.
            rewrite <- (Union_assoc _ (image β (reach' H1 (post H1 [set l1'])))).
            
            rewrite !post_Singleton at 1; try eassumption.
            rewrite !image_Singleton at 1; try eassumption.
            rewrite !image'_Singleton_Some at 1; try eassumption.
            simpl. 
            assert (Hp' : In _  ((post H2 ^ n) (post H2 [set (β l1')])) l1) by assumption.
            rewrite (proper_post_n H2) in Hp';
              [| rewrite !post_Singleton; try eassumption;
                 simpl; rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r; reflexivity ].
            simpl in Hp'.
            specialize (Henv n (Nat.lt_succ_diag_r n)).

            destruct Henv as (c & vs2' & FVs & Hnd & Hget1' & Hget2' & Hcc').
            
            destruct n. 
            - inv Hp'. left...
            - replace (S n) with (n + 1) in Hp' by omega.
              rewrite app_plus in Hp'. unfold compose in Hp'. 
              simpl in Hp'. 
              rewrite (proper_post_n H2) in Hp';
                [| rewrite post_Singleton; try eassumption; reflexivity ].
              simpl in Hp'. right.
              edestruct post_n_exists_Singleton as [l3 [Hin1 Hinp]]; try eassumption.
              edestruct (@Union_lists_exists loc) as [S [Hin3 Hin2]]. eassumption.
              edestruct (list_in_map_inv _ _ _ Hin3) as [l3' [Heql Hinl]]; subst.
              destruct l3' as [l3' |]; inv Hin2.
              edestruct (@Forall2_exists_r) with (x := Loc l3) as [l4 [Hin2 Hcc]]; try eassumption.
              simpl in Hcc. destruct Hcc as [l2' [Hgetl4' Hval'']]. rewrite cc_approx_val_eq in Hval''.
              
              assert (Heq' : l3 = (β l2')).
              { destruct Hval'' as [Heq' _]. congruence. }
              subst.

              

              (* eapply Hget2' in Hin2.   *)
              eapply Included_trans; [| reflexivity | ].
              eapply Included_Union_compat.
              eapply image_monotonic. eapply reach'_set_monotonic with (S1 := val_loc (Loc l2')).
              eapply Singleton_Included.
              eexists. split. eapply Hnd. eassumption. rewrite Hgetl4'. reflexivity.
              eapply image'_monotonic. eapply reach'_set_monotonic with (S1 := val_loc (Loc l2')).
              eapply Singleton_Included.
              eexists. split. eapply Hnd. eassumption. rewrite Hgetl4'. reflexivity.
              
              eapply IHn with (m := n) (v2 := Loc (β l2')); [| | eassumption].
              omega.
              intros j.
              specialize (Hval' (S j)).
              simpl in Hval'. rewrite Hget1, Hget2 in Hval'.
              destruct Hval' as [Hbeq [Hc [Henv _]]].
              specialize (Henv j (Nat.lt_succ_diag_r j)).
              destruct Henv as (c' & vs2'' & FVs' & Hnd'' & Hget1'' & Hget2'' & Hcc'').
              repeat subst_exp.
              eapply Hnd in Hin2.
              eapply Hnd'' in Hin2.  
              edestruct @Forall2_exists with (x := l4) as [l4' [Hin2' Hv]];
                try now apply Hcc''; try eassumption.
              eassumption.
              destruct Hv as [l' [Hgetl' Hval]]. repeat subst_exp.
              rewrite cc_approx_val_eq in Hval.
              assert (Heq' : l4' = Loc (β l')).
              { destruct l4'; try contradiction. destruct Hval as [Heq' _].
                congruence. }
              subst. eassumption. 
          }
  Qed.

    
  Lemma cc_approx_var_env_image_reach
        (k : nat) (β : Inj)  (δ : EInj)
        (H1 H2 : heap block) (rho1 rho2 : env) (x y : var) (v : value) :
    (forall j, cc_approx_var_env k j GIP GP β δ H1 rho1 H2 rho2 x y) ->
    M.get x rho1 = Some v ->
    image β (reach' H1 (env_locs rho1 [set x])) :|: image' δ (reach' H1 (env_locs rho1 [set x])) <-->
    reach' H2 (env_locs rho2 [set y]). 
  Proof.
    intros Hcc Hget.
    assert (Hcc := Hcc).
    edestruct (Hcc 1) as [v' [Hget' Hv]]; eauto.
    rewrite !env_locs_Singleton at 1; eauto.
    rewrite cc_approx_val_image_eq; try eassumption.
    reflexivity.
    intros j'.
    edestruct (Hcc j') as [v'' [Hget'' Hv']]; eauto.
    repeat subst_exp. eassumption.
  Qed.

  

  Lemma cc_approx_env_image_reach S (k : nat)
        (H1 H2 : heap block) (rho1 rho2 : env) :
    (forall j, (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; b; d) (H2, rho2)) ->
    binding_in_map S rho1 ->
    image b (reach' H1 (env_locs rho1 S)) :|: image' d (reach' H1 (env_locs rho1 S)) <-->
    reach' H2 (env_locs rho2 S).
  Proof.
    intros Hres HB. split.
    - intros l' [l'' [l [Hin Heq]] | l'' [l [Hin Heq]]]; subst.
      + destruct Hin as [n [_ Hp]].
        edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
        destruct Hin as [x [Hin Heq]]. 
        destruct (M.get x rho1) as[[l1' |] | ] eqn:Hgetx1; inv Heq.
        eapply reach'_set_monotonic.
        eapply env_locs_monotonic. eapply Singleton_Included. eassumption.
        eapply cc_approx_var_env_image_reach; try eassumption.
        intros j. eapply Hres. eassumption.
        left. eexists. split; eauto.
        rewrite !env_locs_Singleton at 1; try eassumption.
        eexists; split; eauto. now constructor.
      + destruct Hin as [n [_ Hp]].
        edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
        destruct Hin as [x [Hin Heq']]. 
        destruct (M.get x rho1) as[[l1' |] | ] eqn:Hgetx1; inv Heq'.
        eapply reach'_set_monotonic.
        eapply env_locs_monotonic. eapply Singleton_Included. eassumption.
        eapply cc_approx_var_env_image_reach; try eassumption.
        intros j. eapply Hres. eassumption.
        right. eexists. split; eauto.
        rewrite !env_locs_Singleton at 1; try eassumption.
        eexists; split; eauto. now constructor.
    - intros l [m [Hm Hr]].
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      destruct Hin as [x [Hin Heq]]. 
      destruct (M.get x rho2) as[[l1' |] | ] eqn:Hgetx1; inv Heq.
      edestruct HB as [v1 Hget1]. eassumption.
      eapply Included_trans; [| reflexivity | ]. eapply Included_Union_compat.
      eapply image_monotonic. eapply reach'_set_monotonic.
      eapply env_locs_monotonic. eapply Singleton_Included. eassumption.
      eapply image'_monotonic. eapply reach'_set_monotonic.
      eapply env_locs_monotonic. eapply Singleton_Included. eassumption.
      
      rewrite cc_approx_var_env_image_reach; [| intros j; eapply Hres; eassumption | eassumption ].
      rewrite env_locs_Singleton at 1; eauto.      
      eexists; split; eauto.
  Qed. 

  Lemma cc_approx_env_image_eq S (k : nat)
        (H1 H2 : heap block) (rho1 rho2 : env) :
    (forall j, (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; b; d) (H2, rho2)) ->
    binding_in_map S rho1 ->
    image b (env_locs rho1 S) <--> env_locs rho2 S.
  Proof.
    intros Hj Hbin. specialize (Hj 0). split; intros l.
    - intros [y [[x [Hin' Heq]] Hin]]; subst.
      destruct (M.get x rho1) as[[l1' |] | ] eqn:Hgetx1; inv Heq.
      edestruct Hj as [[l2|] [Hget2 Hcc]]; eauto; try contradiction.
      destruct Hcc as [Heq1 _]. subst.
      eexists; split; eauto. rewrite Hget2. reflexivity.
    - intros [x [Hin' Heq]]; subst.
      destruct (M.get x rho2) as[[l2 |] | ] eqn:Hgetx1; inv Heq.
      edestruct Hbin as [v1 Hget1]; try eassumption. 
      edestruct Hj as [[l2|] [Hget2 Hcc]]; eauto; subst_exp; try contradiction.
      destruct v1 as [l1|]; try contradiction.
      destruct Hcc as [Heq1 _]. subst.
      eexists; split; eauto.
      eexists; split; eauto.
      rewrite Hget1. reflexivity.
  Qed.
     
  Lemma cc_approx_heap_image_reach S (k : nat)
        (H1 H2 : heap block) :
    (forall j, S |- H1 ≼ ^ (k; j; GIP; GP; b; d) H2 ) ->
    image b (reach' H1 S) :|: image' d (reach' H1 S) <-->
    reach' H2 (image b S).
  Proof.
    intros Hres. split.
    - intros l' [l'' [l [Hin Heq]] | l'' [l [Hin Heq]]]; subst.
      + destruct Hin as [n [_ Hp]].
        edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
        eapply reach'_set_monotonic with (S1 := val_loc (Loc (b l1))). eapply Singleton_Included.
        eexists; split; eauto.

        eapply cc_approx_val_image_eq; try eassumption.
        intros j. eapply Hres. eassumption.

        left. eexists. split; eauto.
        eexists; split; eauto. now constructor.
      + destruct Hin as [n [_ Hp]].
        edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
        eapply reach'_set_monotonic. eapply image_monotonic with (S0 := val_loc (Loc l1)). 
        eapply Singleton_Included. eassumption.
        assert (Hseq : image b (val_loc (Loc l1)) <--> val_loc (Loc (b l1))).
        { simpl. rewrite image_Singleton. reflexivity. }
        rewrite Hseq.
        eapply cc_approx_val_image_eq.
        intros j. eapply Hres. eassumption.
        
        right. eexists. split; eauto.
        eexists; split; eauto. now constructor.
    - intros l [m [Hm Hr]].
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      destruct Hin as [x [Hin Heq]]. subst.
      eapply Included_trans; [| reflexivity | ]. eapply Included_Union_compat.
      eapply image_monotonic. eapply reach'_set_monotonic with (S1 := val_loc (Loc x)).
      eapply Singleton_Included. eassumption.
      eapply image'_monotonic. eapply reach'_set_monotonic with (S1 := val_loc (Loc x)).
      eapply Singleton_Included. eassumption.

      eapply cc_approx_val_image_eq.
      intros j. eapply Hres. eassumption.
      eexists; split; eauto.
  Qed.

  Lemma cc_approx_clos_image_reach S (k : nat)
        (H1 H2 : heap block) rho1 l2 :
    (forall j,  (rho1, H1) << ^ (k; j; GIP; GP; b; d; S) (l2, H2) ) ->
    image b (reach' H1 (env_locs rho1 S)) :|: image' d (reach' H1 (env_locs rho1 S)) <-->
    reach' H2 (post H2 [set l2]).
  Proof.
    intros Hheap. split.
    - intros l' [l'' [l [Hin Heq]] | l'' [l [Hin Heq]]]; subst.
      + destruct Hin as [n [_ Hp]].
        edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
        
        edestruct (Hheap 0) as (c & vs & FLS & Hget1 & Hnd & Heq & Hall). 
        rewrite post_Singleton; eauto. simpl. 

        destruct Hin as [y [Hin' Hall']].
        destruct (M.get y rho1) as [ [|] | ] eqn:Hgety; try inv Hall'. 
        
        edestruct (@Forall2_exists loc) with (x := y) as [v2 [Hin'' Hv]]; try eassumption.
        eapply Hget1; eassumption.

        simpl in Hv. destruct Hv as [l1' [Hgety' Hv]].
        rewrite cc_approx_val_eq in Hv.
        edestruct v2 as [ l2' |]; try contradiction.
        
        eapply reach'_set_monotonic. 
        eapply In_Union_list. eapply in_map. eassumption. 
        eapply cc_approx_val_image_eq with (v1 := Loc l1); try eassumption;
        [| left; eexists; split; eauto; eexists; split; eauto; now constructor ].
        intros j.

        edestruct (Hheap j) as (c' & vs' & FLS' & Hget1' & Hnd' & Heq' & Hall');
          repeat subst_exp.

        edestruct (@Forall2_exists loc) with (x := y) as [v2' [Hin1' Hv']]; try eassumption.
        now eapply Hget1'; eauto.
        
        destruct Hv as [Heqb _]. subst.
        destruct Hv' as [l1'' [Hgetz Hv']].
        
        rewrite cc_approx_val_eq in Hv'.
        
        assert (Heq1 : v2' = Loc (b l1'')).
        { destruct v2'; try contradiction.
          destruct Hv' as [Heqv _]. subst. reflexivity. }
        subst. repeat subst_exp. eassumption.
      + destruct Hin as [n [_ Hp]].
        edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
        
        edestruct (Hheap 0) as (c & vs & FLS & Heq' & Hnd & Hget' & Hall). 
        rewrite post_Singleton; eauto. simpl. 

        edestruct Hin as [y [Hgety Hiny]].
        destruct (M.get y rho1) as [ [|] |]  eqn:Hgety'; inv Hiny.

        edestruct (@Forall2_exists loc) with (x := y) as [v2 [Hin' Hv]]; try eassumption.
        eapply Heq'; try eassumption.
        destruct Hv as [l1' [Hgetl1 Hv]].
        rewrite cc_approx_val_eq in Hv.
        edestruct v2 as [ l2' |]; try contradiction.
        
        eapply reach'_set_monotonic. 
        eapply In_Union_list. eapply in_map. eassumption. 
        eapply cc_approx_val_image_eq with (v1 := Loc l1); try eassumption;
        [| right; eexists; split; eauto; eexists; split; eauto; now constructor ].

        intros j.
        edestruct (Hheap j) as (c' & vs' & FLS' & Heq'' & Hnd' & Hget1'  & Hall').
        repeat subst_exp.

        edestruct (@Forall2_exists loc) with (x := y) as [v2' [Hin'' Hv']]; try eassumption.
        eapply Heq''. eassumption.
        destruct Hv as [Heqb _]. subst.
        destruct Hv' as [l1 [Hgety'' Hv']]. repeat subst_exp.
        rewrite cc_approx_val_eq in Hv'.
        assert (Heq1 : v2' = Loc (b l1)).
        { destruct v2'; try contradiction.
          destruct Hv' as [Heqv _]. subst. reflexivity. }
        subst. eassumption.
    - intros l [m [Hm Hr]].
      edestruct (Hheap 0) as (c & vs & FLS & Heq & Hnd' & Hget1 & Hall). 
      eapply (proper_post_n H2) in Hr;
        [| rewrite !post_Singleton; try eassumption; try reflexivity ].
      simpl in Hr.
      
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      edestruct (@Union_lists_exists loc) as [S' [Hin3 Hin2]]. eassumption.
      edestruct (list_in_map_inv _ _ _ Hin3) as [l3' [Heql Hinl]]; subst.
      destruct l3' as [l3' |]; inv Hin2.
      edestruct (@Forall2_exists_r) with (x := Loc l1) as [l4 [Hin2 Hcc]]; try eassumption.
      repeat subst_exp. 
      destruct Hcc as [l1' [Hgetx1 Hcc]]. rewrite cc_approx_val_eq in Hcc.
      assert (Heq' : l1 = (b l1')).
      { destruct Hcc as [Heq' _]. congruence. }
      subst.
      eapply Heq in Hin2.
      eapply Included_trans; [| reflexivity | ].
      eapply Included_Union_compat.
      eapply image_monotonic. eapply reach'_set_monotonic with (S1 := val_loc (Loc l1')).
      eapply get_In_env_locs; eassumption.
      eapply image'_monotonic. eapply reach'_set_monotonic with (S1 := val_loc (Loc l1')).
      eapply get_In_env_locs; eassumption.
      
      eapply cc_approx_val_image_eq with (v2 := Loc (b l1')).
      
      intros j.
      edestruct (Hheap j) as (c' & vs2'' & FVs' & Heq'' & Hnd'' & Hget2'' & Hcc'').
      repeat subst_exp.

      eapply Heq'' in Hin2. 
      
      edestruct (Forall2_exists _ _ _ _ Hin2 Hcc'') as [l4' [Hin2' Hv]]; try eassumption.

      destruct Hv as [l2' [Hgetl2 Hval]]. repeat subst_exp. 
      rewrite cc_approx_val_eq in Hval.
      
      assert (Heq' : l4' = Loc (b l2')).
      { destruct l4'; try contradiction. destruct Hval as [Heq' _]. congruence. }
      subst. eassumption. 

      eexists.
      split. now constructor.
      eassumption. 
  Qed.
  
  (* TODO move *)
  Lemma heap_env_equiv_image_root (S : Ensemble var) (β1 β2 : loc -> loc)
        (H1 H2 : heap block) (rho1 rho2 : env) :
    S |- (H1, rho1) ⩪_( β1, β2) (H2, rho2) ->
    image β1 (env_locs rho1 S) <--> image β2 (env_locs rho2 S).
  Proof.     
    intros Heq. split.
    - intros l1 [l2 [[x [Hin1 Hin2]] Heq']]. 
      destruct (M.get x rho1) as [[ l1' |] |] eqn:Hget1; try now inv Hin2.
      inv Hin2.
      edestruct heap_env_equiv_env_get as [v2 [Hget2 Heqv]]; try eassumption. 
      rewrite res_equiv_eq in Heqv. destruct v2 as [l2' |]; try contradiction.
      destruct Heqv as [Heq1 _]. rewrite Heq1.
      eexists; split; eauto.
      eexists; split; eauto. rewrite Hget2; reflexivity.
    - intros l1 [l2 [[x [Hin1 Hin2]] Heq']]. 
      destruct (M.get x rho2) as [[ l1' |] |] eqn:Hget1; try now inv Hin2.
      inv Hin2.
      edestruct heap_env_equiv_env_get as [v2 [Hget2 Heqv]]; try eassumption.
      symmetry. eassumption.
      rewrite res_equiv_eq in Heqv. destruct v2 as [l2' |]; try contradiction.
      destruct Heqv as [Heq1 _]. rewrite Heq1.
      eexists; split; eauto.
      eexists; split; eauto. rewrite Hget2; reflexivity.
  Qed.


  Opaque cc_approx_exp.
  
  
  Lemma cc_approx_heap_post (P : Ensemble var) k j (H1 H2 : heap block) : 
    P |- H1 ≼ ^ (k; 1 + j; GIP; GP; b; d) H2 ->
    post H1 P |- H1 ≼ ^ (k; j; GIP; GP; b; d) H2.
  Proof.   
    intros Hheap x [l [b' [Hin [Hget Hin']]]].
    specialize (Hheap _ Hin).
    simpl in Hheap. rewrite Hget in Hheap.
    destruct Hheap as [_ Hres].
    destruct b' as [c1 vs1 | [| B1 f1] rhoc ]; try contradiction;
    destruct (get (b l) H2) as [[c2 vs2 | [| B2 f2] rhoc2 ] |]; try contradiction.
    - destruct Hres as [Heq1 [Heq2 Hall]].
      specialize (Hall j (Nat.lt_succ_diag_r j)). subst.
      simpl in Hin'.
      edestruct (@Union_lists_exists loc) as [S' [Hin3 Hin2]]. eassumption.
      edestruct (list_in_map_inv _ _ _ Hin3) as [l3' [Heql Hinl]]; subst.
      destruct l3' as [l3' |]; inv Hin2.
      edestruct (Forall2_exists _ vs1 vs2 (Loc x) Hinl Hall)  as [x' [Hin2 Hres']].
      rewrite cc_approx_val_eq in *. destruct x'; try contradiction.
      assert (Hres'' := Hres').  destruct Hres'' as [Hbeq _]. subst.
      eassumption.
    - destruct vs2 as [| [|] [| [|] [|] ] ]; try contradiction.
      destruct Hres as [Hd [Henv _]]. subst.
      specialize (Henv j (Nat.lt_succ_diag_r j)).
      edestruct Henv as (c & vs & FLS & Heq & Hnd & Hget' & Hall); try eassumption.
      simpl in Hin'. destruct Hin' as [x' [Hgetx Hinx]].
      destruct (M.get x' rhoc) as [ [|] | ] eqn:Hgetx'; inv Hinx.
      eapply Heq in Hgetx.
      edestruct (Forall2_exists _ FLS vs x' Hgetx Hall)  as [y [Hin2 Hres']].
      destruct Hres' as [y' [Hgety' Hval]]. 
      rewrite cc_approx_val_eq in *. destruct y; try contradiction.
      assert (Hres'' := Hval).  destruct Hres'' as [Hbeq _]. subst.
      repeat subst_exp. eassumption.
  Qed.
  
  Lemma cc_approx_heap_reach_closed (P : Ensemble var) k j (H1 H2 : heap block) : 
    (forall j, P |- H1 ≼ ^ (k; j; GIP; GP; b; d) H2) ->
    reach' H1 P |- H1 ≼ ^ (k; j; GIP; GP; b; d) H2.
  Proof.
    intros Hyp j' [n [_ Hp]]. revert P Hyp Hp.
    induction n; intros P Hyp Hp.
    - simpl in Hp. eapply Hyp. eassumption.
    - replace (S n) with (n + 1) in Hp by omega.
      rewrite app_plus in Hp. unfold compose in Hp. simpl in Hp.
      eapply IHn in Hp. eassumption.
      intros i. eapply cc_approx_heap_post; eauto.
  Qed.
      
  (** * The logical relation respects heap equivalences *)

  (* TODO move *)
  Lemma Forall2_vertical_strong
        {A B C D : Type} (R1 : A -> B -> Prop) (R2 : A -> C -> Prop) (R3 : B -> D -> Prop) (R4 : C -> D -> Prop)
        (l1 : list A) (l2 : list B) (l3 : list C) (l4 : list D):
  (forall (x : A) (y : B) (z : C) (w : D),
         List.In x l1 -> List.In y l2 -> List.In z l3 ->  List.In w l4 ->
         R1 x y -> R2 x z -> R3 y w -> R4 z w) ->
      Forall2 R1 l1 l2 -> Forall2 R2 l1 l3 -> Forall2 R3 l2 l4 -> Forall2 R4 l3 l4.
  Proof.
    intros Hyp Hr1.
    revert l3 l4 Hyp. induction Hr1; intros l3 l4 Hyp Hr2 Hr3; inv Hr2; inv Hr3. 
    - now constructor.
    - constructor; eauto. eapply Hyp; try eassumption; now constructor.
      eapply IHHr1; try eassumption.
      intros. eapply Hyp; try eassumption; now constructor.
  Qed.
  

   (* TODO move *)
  Lemma block_equiv_Constr_r β1 β2 (H1 H2 : heap block) (c1 c2 : cTag)
        (vs vs' : list value) :
    block_equiv (β1, H1, Constr c1 vs) (β2, H2, Constr c2 vs') ->
    Forall2 (fun l1 l2 => (l1, H1) ≈_(β1, β2) (l2, H2)) vs vs'.
  Proof.
    intros [Heq Hall]; eauto.
  Qed.
  
  Lemma map_id {A} (l : list A) :
    map id l = l.
  Proof.
    induction l; eauto.
    simpl; f_equal; eauto.
  Qed.

  Lemma Forall2_map_r_strong {A B} (P : A -> B -> Prop) (f : A -> B) (l : list A) :
    (forall x, List.In x l -> P x (f x)) ->
    Forall2 P l (map f l).
  Proof.
    intros Hyp. induction l; try now constructor.
    simpl. constructor.
    eapply Hyp; eauto; try now constructor.
    eapply IHl; intros; eauto. eapply Hyp.
    now constructor 2.
  Qed.

  Lemma Forall2_map_l_strong {A B} (P : B -> A -> Prop) (f : A -> B) (l : list A) :
    (forall x, List.In x l -> P (f x) x) ->
    Forall2 P (map f l) l.
  Proof.
    intros Hyp. induction l; try now constructor.
    simpl. constructor.
    eapply Hyp; eauto; try now constructor.
    eapply IHl; intros; eauto. eapply Hyp.
    now constructor 2.
  Qed.

  Lemma FromList_image_exists {A B} (f : A -> B) l S :
    FromList l \subset image f S ->
    exists l', l = map f l'.
  Proof with (now eauto with Ensembles_DB).
    revert S; induction l; intros S Heq; eauto.
    - eexists []. reflexivity.
    - rewrite FromList_cons in Heq.
      edestruct IHl as [l' Heql'].
      + eapply Included_trans; try eassumption...
      + edestruct Heq as [a' [Heqa Hina]]. now left.
        eexists (a' :: l'). simpl; f_equal; eauto.
  Qed.

  Lemma Union_Same_set_Disjoint {A} (S1 S2 S3 : Ensemble A) :
    S1 :|: S2 <--> S1 :|: S3 ->
    Disjoint _ S1 S2 ->
    Disjoint _ S1 S3 ->
    S2 <--> S3.
  Proof.
    intros Heq HD HD'. split; intros x Hin.
    - assert (Hin' : (S1 :|: S3) x).
      { eapply Heq. now right. }
      inv Hin'; eauto.
      exfalso. eapply HD; eauto.
    - assert (Hin' : (S1 :|: S2) x).
      { eapply Heq. now right. }
      inv Hin'; eauto.
      exfalso. eapply HD'; eauto.
  Qed.

  Lemma FromList_image_injective_exists (f : positive -> positive) l S :
    FromList l <--> image f S ->
    injective_subdomain S f ->
    exists l', l = map f l' /\ FromList l' <--> S.
  Proof with (now eauto with Ensembles_DB).
    revert S; induction l; intros S Heq Hinj; eauto.
    - eexists []. split; eauto.
      rewrite !FromList_nil in Heq.
      rewrite FromList_nil.
      split; intros x Hin; try now inv Hin.
      assert (Hc : Empty_set _ (f x)). 
      { eapply Heq. eexists; split; eauto. }
      inv Hc. 
    - rewrite FromList_cons in Heq.
      assert (Ha : image f S a).
      { eapply Heq; now left. }
      destruct Ha as [a' [Heqa Hina]]. subst.
      
      destruct (Decidable_FromList l) as [Decl].
      destruct (Decl (f a')).
      + rewrite Union_Same_set in Heq; 
        [| eapply Singleton_Included; now eauto ].  
        edestruct IHl as [l' [Heql Heqs]]; eauto.
        subst.
        eexists (a' :: l'). split. now simpl; f_equal; eauto.
        rewrite FromList_cons.
        rewrite Union_Same_set. eassumption.
        rewrite Heqs. eapply Singleton_Included. eassumption.
      + assert (Heq' := Heq).
        rewrite (Union_Setminus_Same_set S [set a']) in Heq;
        [| eapply Singleton_Included; now eauto ].  
        rewrite image_Union, image_Singleton in Heq.
        eapply Union_Same_set_Disjoint in Heq.
        * edestruct IHl as [l' [Heql Heqs]]; try now apply Heq; eauto; subst.
          eapply injective_subdomain_antimon; try eassumption...
           
          eexists (a' :: l'). split. now simpl; f_equal; eauto.
          rewrite FromList_cons.
          rewrite Heqs.
          rewrite <- (Union_Setminus_Same_set S [set a']);
            [| eapply Singleton_Included; now eauto ].
          reflexivity.
        * eapply Disjoint_Singleton_l. eauto.
        * rewrite <- image_Singleton.
          eapply injective_subdomain_Union_not_In_image.
          eapply injective_subdomain_antimon; try eassumption...
          eapply Disjoint_Singleton_l.
          intros Hc; inv Hc; eauto.
  Qed.

  (* TODO move *)
  Lemma heap_env_approx_res_approx 
        (S : Ensemble var) (β : loc -> loc)
        (H1 H2 : heap block) (rho1 rho2 : M.t value) l :
    heap_env_approx S (β, (H1, rho1)) (id, (H2, rho2)) ->
    l \in env_locs rho1 S ->
    (Loc l, H1) ≈_(β, id) (Loc (β l), H2).
  Proof.
    intros Henv [x [Heq1 Heq2]].
    destruct (M.get x rho1) as [[l1|] |] eqn:Hget; inv Heq2.
    edestruct Henv as [v2 [Hget2 Hres]]; eauto.
    assert (Hres' := Hres). rewrite res_equiv_eq in Hres.
    destruct v2 as [l2|]; try contradiction. simpl in Hres.
    destruct Hres as [Hres'' _]. unfold id in *; subst.
    eassumption.
  Qed.

  Lemma heap_env_equiv_res_equiv
        (S : Ensemble var) (β : loc -> loc)
        (H1 H2 : heap block) (rho1 rho2 : M.t value) l :
    S |- (H1, rho1) ⩪_(id, β) (H2, rho2) ->
    l \in env_locs rho2 S ->
    (Loc (β l), H1) ≈_(id, β) (Loc l, H2).
  Proof.
    intros Henv Hin.
    symmetry. eapply heap_env_approx_res_approx.
    destruct Henv. eassumption.
    eassumption.
  Qed.


  Lemma cc_approx_val_res_eq (k j : nat) (b' b1 b2 : Inj) d'  (H1 H2 H1' H2' : heap block)
        (v1 v2 v1' v2' : value) :
    (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b'; d') (Res (v2, H2)) ->

    (v1, H1) ≈_(id, b1) (v1', H1') ->
    injective_subdomain (reach' H1' (val_loc v1')) b1 ->

    (v2, H2) ≈_(b2, id) (v2', H2') ->
    injective_subdomain (reach' H2 (val_loc v2)) b2 ->
    
    (Res (v1', H1')) ≺ ^ (k ; j ; GIP ; GP ; b2 ∘ b' ∘ b1; lift b2 ∘ d' ∘ b1 ) (Res (v2', H2')).
  Proof with now eauto with Ensembles_DB.
    clear LIP LP b d.
    revert j b' d' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'.
    induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1.
    intros b' d' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'.
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    intros [Heq Hcc] (* Hwf1 Hwf2 Hl1 Hl2 *) Hres1 Hr1 Hres2 Hr2. 
    destruct (get l1 H1) as [[c1 vs1 | [? | B1 f1] env_loc1 ] | ] eqn:Hget1;
      destruct (get l2 H2) as [[c2 vs2 | ] | ] eqn:Hget2; try contradiction.
    + rewrite res_equiv_eq in Hres1, Hres2.
      destruct v1' as [l1' | lf1' f1']; destruct v2' as [l2' | lf2' f2'];
      try contradiction.
      simpl in Hres1, Hres2. 
      rewrite Hget1 in Hres1. rewrite Hget2 in Hres2.
      destruct Hres1 as [Heqi1 Hres1].
      destruct Hres2 as [Heqi2 Hres2]. subst.       
      destruct (get l1' H1') as [b1'|] eqn:Hget1'; [| contradiction ].
      destruct (get l2' H2') as [b2'|] eqn:Hget2'; [| contradiction ].
      destruct b1' as [c1' vs1' | ]; [| contradiction ].
      destruct b2' as [c2' vs2' | ]; [| contradiction ].
      
      destruct Hres1 as [Heqc1 Heqb1].
      destruct Hres2 as [Heqc2 Heqb2]. subst. 
      destruct Hcc as [Heqc [Hd' Hall]]; subst. 
      split. unfold compose. rewrite <- Heqi1. unfold id. rewrite Heqi2. reflexivity.
      split; eauto. split; eauto.
      unfold id in *. subst. unfold compose. rewrite Hd'. simpl. reflexivity.
         
      intros i Hlt. specialize (Hall i Hlt).
      eapply Forall2_vertical_l_strong; [| | eassumption ].
      * simpl. intros. rewrite cc_approx_val_eq in *.
        rewrite <- (compose_id_neut_l (b2 ∘ b' ∘ b1)).
        rewrite <- Combinators.compose_assoc.
        rewrite <- (compose_id_neut_l (lift b2 ∘ d' ∘ b1)).
        rewrite <- (Combinators.compose_assoc _ _ _ _ b1).
        assert (Hfeq : f_eq (id ∘ (lift b2 ∘ d') ∘ b1)
                           ((lift (@id loc)) ∘ (lift b2 ∘ d') ∘ b1)).
        { intros z'. unfold compose.
          rewrite <- (@lift_id loc). reflexivity. }
        rewrite Hfeq. 
        eapply IHj; try eassumption.
        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold _ (val_loc (Loc l1'))).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. simpl. rewrite post_Singleton; [| eassumption ].
        eapply In_Union_list. eapply in_map. eassumption.
        reflexivity. clear. now firstorder.
      * eapply Forall2_vertical_r_strong; [| | eassumption ].
        simpl. intros x y z Hin1 Hin2 Hin3 Hin Hres.
        rewrite cc_approx_val_eq.
        rewrite <- (compose_id_neut_r (b2 ∘ b')).
        eapply IHj; [ eassumption | | reflexivity | | | ]. 
        now eapply Hin.
        clear. now firstorder. eapply Hres.
        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold _ [set b' l1]).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. simpl. rewrite post_Singleton; [| eassumption ].
        eapply In_Union_list. eapply in_map. eassumption.
        eapply Forall2_monotonic. intros x1 x2 HR. rewrite <- cc_approx_val_eq.
        now eapply HR. eapply Hall.
    + simpl in Hcc.
      destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction.
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

      destruct b1' as [c1' vs1' | ]; try contradiction.
      destruct b2' as [c2' vs2' | ]; try contradiction.
      
      destruct Hall as [Hceq Hall].
      destruct v as [l3' | lf3' f3']; try contradiction.

      destruct Henv1 as [Hres [Hlocs Henv]]. subst. repeat subst_exp.
      inv Hall. inv H5. inv H7.
      rewrite res_equiv_eq in *. 
      destruct y as [l5' | lf5' f5']; destruct y0 as [l6' | lf6' f6']; try contradiction.
      destruct Hcc as [Hd [Henv' Hcc]]. split; eauto.
      
      unfold compose. rewrite Hd. simpl.
      destruct H4 as [Heq H4']. rewrite Heq; reflexivity.
      
      (* subst. simpl in *. inv H3. destruct H4 as [Hb Hres]. inv Hres. *)
      split.

      intros i Hlt. 

      edestruct (Henv' i) as (c & vs & FLS & Heq & Hnd & Hget & Hall); try eassumption. 
      destruct H4 as [Hbeq Hres].
      rewrite Hget in Hres.
      unfold id in Hbeq. subst.
      destruct (get (b2 env_loc2) H2') as [b2'|] eqn:Hgetb2'; try contradiction.
      destruct b2' as [c' vs'|]; try contradiction.

      clear Hcc. 
      (* rewrite <- image_id with (S := env_locs env_loc1 (occurs_free_fundefs lf3')) in Heq. *)
      (* rewrite heap_env_equiv_image_root in Heq; [| eassumption ].   *)
      (* edestruct FromList_image_injective_exists as [FLS' [HeqFL Him]]. *)
      (* rewrite Heq. reflexivity. *)
      (* eapply injective_subdomain_antimon. eassumption. *)
      (* eapply Included_trans; [| now eapply Included_post_reach' ]. simpl. *)
      (* rewrite post_Singleton; eauto... subst. *)
      
      do 3 eexists. split. eassumption. split. eassumption. split. eassumption.
      
      eapply Forall2_vertical_strong with (R2 := fun x y => x = y); [| eassumption | | ].
      
      intros x y z w Hin1 Hin2 Hin3 Hin4 Hr1' Hr2' Hr3'. 
      destruct Hr1' as [l2 [Hgetl2 Hr1']]. simpl in Hr1'.
      rewrite cc_approx_val_eq in Hr1'.  subst.
      edestruct heap_env_equiv_env_get as [l2' [Hgetl2' Hres']].
      eassumption. eassumption. eapply Heq; eassumption.
      destruct l2' as [l2' |]; try (rewrite res_equiv_eq in Hres'; contradiction).
      eexists. split. subst. eassumption. rewrite cc_approx_val_eq.
      eapply IHj. eassumption. now apply Hr1'.
      eassumption.

      eapply injective_subdomain_antimon. eassumption.
      rewrite (reach_unfold H1' (val_loc (Loc l1'))). eapply Included_Union_preserv_r.
      eapply reach'_set_monotonic. simpl post. rewrite post_Singleton; eauto. 
      eapply get_In_env_locs; try eassumption. eapply Heq. eassumption.

      now apply Hr3'.

      eapply injective_subdomain_antimon. eassumption.
      rewrite (reach_unfold H2 [set b' (b1 l1')]). eapply Included_Union_preserv_r.
      rewrite (reach_unfold H2 (post H2 [set b' (b1 l1')])). eapply Included_Union_preserv_r.
      eapply reach'_set_monotonic. rewrite post_Singleton; eauto. simpl.
      rewrite Union_Empty_set_neut_r, Union_Empty_set_neut_l.
      rewrite post_Singleton; eauto. simpl.
      eapply In_Union_list. eapply in_map. eassumption. 
      
      eapply Forall2_refl; eauto.

      eapply block_equiv_Constr_r. eassumption.
      
      intros b1' b2' tc1 tc2 tc3 H3' H3'' H4' env_loc1' xs1 ft
             e1 vs1 vs2 Hres1 Hinj1 Hres2 hinj2 Hfind Hdef Hset.

      simpl in H3. inv H3.
      rewrite <- res_equiv_eq in *.
   
      edestruct Hcc with (env_loc' := env_loc1')
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi)                 
      ; [| | | | eassumption | eassumption | eassumption | ].
      * eapply heap_env_equiv_f_compose; [| eassumption ].
        eassumption.
      * eapply injective_subdomain_compose. eassumption.
        eapply heap_env_equiv_image_reach in Hres1.
        rewrite image_id in Hres1. rewrite <- Hres1.
        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold H1' (val_loc (Loc l1'))).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl. rewrite post_Singleton; eauto... 
      * symmetry. eapply res_equiv_f_compose; [| symmetry; eassumption ].
        symmetry. rewrite compose_id_neut_r.
        eassumption.
      * eapply injective_subdomain_compose.
        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold H2 [set (b' _)]).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        simpl. rewrite post_Singleton; eauto. simpl...
        eapply res_equiv_image_reach in H4.
        rewrite image_id in H4. rewrite H4.
        eassumption.
      * exists xs2, e2, rho2'. repeat (split; eauto).
    eapply Hi; eauto. eapply Equivalence_Transitive; [| eassumption ].        
    rewrite <- !Combinators.compose_assoc.  
    eapply f_eq_subdomain_compose_compat. reflexivity.
    eapply f_eq_subdomain_compose_compat. reflexivity.
    eapply f_eq_subdomain_compose_compat. reflexivity.
    rewrite lift_compose; reflexivity.

    eapply Hi; eauto. eapply Equivalence_Transitive; [| eassumption ].        
    rewrite <- !Combinators.compose_assoc.  
    eapply f_eq_subdomain_compose_compat. reflexivity.
    eapply f_eq_subdomain_compose_compat. reflexivity.
    eapply f_eq_subdomain_compose_compat. reflexivity.
    rewrite lift_compose; reflexivity.
  Qed.
  

  Lemma cc_approx_val_heap_eq (k j : nat) (β β1 β2 : Inj) (δ : EInj)
        (H1 H2 H1' H2' : heap block)
        (v1 v2 : value) :
    (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β ; δ) (Res (v2, H2)) ->
    (val_loc v1) |- H1 ≃_(id, β1) H1' ->
    injective_subdomain (reach' H1' (val_loc v1)) β1 ->
    (val_loc v2) |- H2 ≃_(β2, id) H2' ->
    injective_subdomain (reach' H2 (val_loc v2)) β2 ->
    (Res (v1, H1')) ≺ ^ (k ; j ; GIP ; GP ; β2 ∘ β ∘ β1 ; lift β2 ∘ δ ∘ β1) (Res (v2, H2')).
  Proof with now eauto with Ensembles_DB.
    intros.
    eapply cc_approx_val_res_eq; try eassumption.
    eapply heap_equiv_res_equiv; try eassumption. reflexivity.
    eapply heap_equiv_res_equiv; try eassumption. reflexivity.
  Qed.

  Lemma cc_approx_var_env_heap_env_equiv (S1 S2 : Ensemble var) (k j : nat)
        (β β1 β2 : Inj) (δ : EInj)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 rho1' rho2' : env) (x1 x2 : var) :
    cc_approx_var_env k j GIP GP β δ H1 rho1 H2 rho2 x1 x2 ->
    S1 |- (H1, rho1) ⩪_(id, β1) (H1', rho1') ->
    injective_subdomain (reach' H1' (env_locs rho1' S1)) β1 -> 
    S2 |- (H2, rho2) ⩪_(β2, id) (H2', rho2') ->
    injective_subdomain (reach' H2 (env_locs rho2 S2)) β2 ->
    x1 \in S1 -> x2 \in S2 ->
    cc_approx_var_env k j GIP GP (β2 ∘ β ∘ β1) (lift β2 ∘ δ ∘ β1)
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
    eapply cc_approx_val_res_eq; try eassumption.
    now symmetry.
    eapply injective_subdomain_antimon. eassumption.
    eapply reach'_set_monotonic. now eapply get_In_env_locs; eauto.
    eapply injective_subdomain_antimon. eassumption.
    eapply reach'_set_monotonic. now eapply get_In_env_locs; eauto.
  Qed.

  (* TODO move *)
  Lemma heap_equiv_antimon (S1 S2 : Ensemble var) (H1 H2 : heap block)
         (b1 b2 : loc -> loc) :
    S1 |- H1 ≃_( b1, b2) H2 ->
    S2 \subset S1 ->
    S2 |- H1 ≃_( b1, b2) H2.
  Proof.
    intros [Ha1 Ha2] Hsub. split; intros x Hin; eauto.
  Qed. 
  
  Lemma cc_approx_heap_env_equiv (S : Ensemble var) (k j : nat) (β β1 β2 : Inj)
        (δ : EInj) (H1 H2 H1' H2' : heap block)  :
    S |- H1 ≼ ^ (k; j; GIP; GP; β ; δ) H2 ->
    S |- H1 ≃_(id, β1) H1' ->
    injective_subdomain (reach' H1' S) β1 -> 
    image β S |- H2 ≃_(β2, id) H2' ->
    injective_subdomain (reach' H2 (image β S)) β2 ->
    S |- H1' ≼ ^ (k; j; GIP; GP; β2 ∘ β ∘ β1; (lift β2 ∘ δ ∘ β1)) H2'.
  Proof.
    intros Henv [Heq1 Heq1'] Hinj1 [Heq2 Heq2'] Hinj2 x HS.
    assert (Heqb : (β2 ∘ β ∘ β1) x = β x).
    { specialize (Henv _ HS).
      specialize (Heq1 _ HS). destruct Heq1 as [Heq1 _].
      assert (HS' : image β S (β x)).
      { eexists; split; eauto. } 
      specialize (Heq2 _ HS'). destruct Heq2 as [Heq2 _].
      unfold compose, id in *. rewrite <- Heq1, Heq2.
      reflexivity. }
    specialize (Henv _ HS). eapply cc_approx_val_heap_eq.
    
    rewrite Heqb. eassumption.

    eapply heap_equiv_antimon. split; eassumption.
    eapply Singleton_Included. eassumption.

    eapply injective_subdomain_antimon. eassumption.
    eapply reach'_set_monotonic. eapply Singleton_Included.
    eassumption.
    
    rewrite Heqb.  
    try eassumption. eapply heap_equiv_antimon. split; eassumption.
    eapply Singleton_Included. now eexists; split; eauto.

    rewrite Heqb.  
    eapply injective_subdomain_antimon. eassumption.
    eapply reach'_set_monotonic. eapply Singleton_Included.
    now eexists; split; eauto.
  Qed.
    
  Lemma cc_approx_clos_heap_env_equiv (S : Ensemble var) (k j : nat) (β β1 β2 : Inj)
        (δ : EInj) (H1 H2 H1' H2' : heap block) rho1 rho1' l2 l2' :
    (rho1, H1) << ^ (k; j; GIP; GP; β; δ; S) (l2, H2) ->
    S |- (H1, rho1) ⩪_(id, β1) (H1', rho1') ->
    injective_subdomain (reach' H1' (env_locs rho1' S)) β1 -> 
    (Loc l2, H2) ≈_(β2, id) (Loc l2', H2') ->
    injective_subdomain (reach' H2 [set l2]) β2 ->
    (rho1', H1') << ^ (k; j; GIP; GP; β2 ∘ β ∘ β1; (lift β2 ∘ δ ∘ β1); S) (l2', H2').
  Proof.
    intros Henv Heq1 Hin1 Heq2 Hinj2.
    edestruct Henv as (c & vs & FLS & Heq & Hnd & Hget & Hall); try eassumption.
    rewrite res_equiv_eq in Heq2. destruct Heq2 as [Hbeq Heq2]. unfold id in *. subst.
    rewrite Hget in Heq2.
    destruct (get (β2 l2) H2') as [[c' vs'|] |] eqn:Hget2; try contradiction.
    simpl in Heq2.
    destruct Heq2 as [Heqb' all]. subst. 
    (* edestruct FromList_image_injective_exists as [FLS' [HeqFL Him]]. *)
    (* eassumption. eapply injective_subdomain_antimon. eassumption. *)
    (* eapply reach'_extensive. *)

    do 2 eexists; exists FLS. split. now eauto.
    split. now eauto. 
    split. eassumption. 
    eapply Forall2_vertical_strong with (R2 := eq); [| eassumption | | eassumption ].
    
    intros x y z w Hin1' Hin2 Hin3 Hin4 [l1 [Hgetl1 Hr1']] Hr2' Hr3'.
    subst.
    edestruct heap_env_equiv_env_get as [l2' [Hgetl2' Hres']].
    eassumption. eassumption. eapply Heq; eassumption.
    destruct l2' as [l2' |]; try (rewrite res_equiv_eq in Hres'; contradiction).
    eexists. split. subst. eassumption. rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_res_eq. eassumption. eassumption.

    eapply injective_subdomain_antimon. eassumption.
    eapply reach'_set_monotonic.
    eapply get_In_env_locs; try eassumption. eapply Heq; eassumption.

    eassumption.

    eapply injective_subdomain_antimon. eassumption.
    
    rewrite (reach_unfold H2 [set l2]). eapply Included_Union_preserv_r.
    rewrite post_Singleton; eauto. simpl.
    eapply reach'_set_monotonic. simpl.
    eapply In_Union_list. eapply in_map. eassumption. 

    subst.
    eapply Forall2_refl; eauto.
  Qed.


  (* Lemma cc_approx_val_res_eq_rev (k j : nat) (b' b1 b2 : Inj)  (H1 H2 H1' H2' : heap block) *)
  (*       (v1 v2 v1' v2' : value) : *)
  (*   (Res (v1', H1')) ≺ ^ (k ; j ; GIP ; GP ; b2 ∘ b' ∘ b1 ) (Res (v2', H2')) -> *)

  (*   (v1, H1) ≈_(id, b1) (v1', H1') -> *)
  (*   injective_subdomain (reach' H1' (val_loc v1')) b1 -> *)

  (*   (v2, H2) ≈_(b2, id) (v2', H2') -> *)
  (*   injective_subdomain (reach' H2 (val_loc v2)) b2 -> *)

  (*   (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b') (Res (v2, H2)). *)
  (* Proof with now eauto with Ensembles_DB. *)
  (*   revert j b' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'. *)
  (*   induction k as [k IHk] using lt_wf_rec1. intros j. *)
  (*   induction j as [j IHj] using lt_wf_rec1. *)
  (*   intros b' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'. *)
  (*   intros Hcc. *)
  (*   assert (Him : Res (v1', H1') ≺ ^ (k; 0; GIP; GP; b2 ∘ b' ∘ b1) Res (v2', H2')). *)
  (*   { admit. } *)
  (*   eapply cc_approx_val_image_eq in Him. simpl in Hcc.  *)
  (*   destruct v1' as [l1 | lf1 f1]; destruct v2' as [l2 | lf2 f2]; simpl; *)
  (*   try (now intros; contradiction); try (now simpl; eauto). *)
  (*   intros Hres1 Hr1 Hres2 Hr2.  *)
  (*   destruct (get l1 H1') as [b1'|] eqn:Hget1; destruct (get l2 H2') as [b2'|] eqn:Hget2; try contradiction.   *)
  (*   destruct Hcc as [Hbs Hcc]. *)
  (*   destruct b1' as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; try contradiction; *)
  (*   destruct b2' as [c2 vs2 | | ]; try contradiction. *)
  (*   + rewrite res_equiv_eq in Hres1, Hres2. *)
  (*     destruct v1 as [l1' | lf1' f1']; destruct v2 as [l2' | lf2' f2']; try contradiction. *)
  (*     simpl in Hres1, Hres2.  *)
  (*     rewrite Hget1 in Hres1. rewrite Hget2 in Hres2.  *)
  (*     destruct (get l1' H1) as [b1'|] eqn:Hget1'; [| now firstorder ]. *)
  (*     destruct (get l2' H2) as [b2'|] eqn:Hget2'; [| now firstorder ]. *)
  (*     destruct b1' as [c1' vs1' | | ]; [|  now firstorder | now firstorder ]. *)
  (*     destruct b2' as [c2' vs2' | | ]; [|  now firstorder | now firstorder ]. *)
  (*     destruct Hres1 as [Heqi1 [Heqc1 Heqb1]]. *)
  (*     destruct Hres2 as [Heqi2 [Heqc2 Heqb2]]. subst. *)
  (*     destruct Hcc as [Heqc Hcc]; subst. *)
  (*     Abort. *)
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
        (rho1 rho2 : env) (β : Inj) (δ : EInj) (H1 H2 : heap block) xs ys vs1 :
    Forall2 (cc_approx_var_env k j GIP GP β δ H1 rho1 H2 rho2) xs ys ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist ys rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k; j; GIP ; GP ; β ; δ) (Res (v2, H2))) vs1 vs2.
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
  
  Lemma cc_approx_env_P_getlist_l (S : Ensemble var) (k j : nat)
        (rho1 rho2 : env) (β : Inj) δ (H1 H2 : heap block) (xs : list var) (vs1 : list value) :
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; β; δ) (H2, rho2) ->
    (FromList xs) \subset S ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist xs rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β ; δ) (Res (v2, H2))) vs1 vs2.
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


   Lemma cc_approx_val_heap_monotonic (k j : nat) (β : Inj) δ (H1 H2 H1' H2' : heap block)
       (v1 v2 : value):
     well_formed (reach' H1 (val_loc v1)) H1 ->
     well_formed (reach' H2 (val_loc v2)) H2 ->
     val_loc v1 \subset dom H1 ->
     val_loc v2 \subset dom H2 ->
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     Res (v1, H1) ≺ ^ (k ; j; GIP ; GP ; β; δ) Res (v2, H2) ->
     Res (v1, H1') ≺ ^ (k ; j; GIP ; GP; β; δ) Res (v2, H2').
   Proof with (now eauto with Ensembles_DB).
     revert j v1 v2. induction k as [k IHk] using lt_wf_rec1; intros j.
     induction j as [j IHj] using lt_wf_rec1. intros v1 v2 Hwf1 Hwf2 Hin1 Hin2 Hsub1 Hsub2 Hcc.
     destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
     try (now intros; contradiction); try (now simpl; eauto).
     simpl in Hcc. destruct Hcc as [Heq Hcc]; split; eauto.
     destruct (get l1 H1) as [b1|] eqn:Hget1; destruct (get l2 H2) as [b2|] eqn:Hget2;
     try contradiction; try (now destruct b1 as [c1 vs1 | [? | B1 f1 ] env_loc1 ]; contradiction).
     eapply Hsub1 in Hget1. eapply Hsub2 in Hget2. rewrite Hget1, Hget2.    
     destruct b1 as [c1 vs1 | [? | B1 f1 ] env_loc1 ];
       destruct b2 as [c2 vs2 | ]; try contradiction. 
     + subst.
       edestruct Hin1 as [b1 Hget1']. reflexivity.
       assert (Hget1'' := Hget1'). eapply Hsub1 in Hget1''.
       subst_exp.
       edestruct Hin2 as [b2 Hget2']. reflexivity.
       assert (Hget2'' := Hget2'). eapply Hsub2 in Hget2''.
       subst_exp. destruct Hcc as [Heq [Heq' Hall]].
       split; eauto. split; eauto.
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
       simpl. destruct Hcc as [Hd [Henv Hcc]]. split; eauto.
       split. clear Hcc.

       intros i Hlt.
       edestruct (Henv i Hlt) as (c & vs & FVs & Heqfv & Hnd & Hget3 & Hall); try eassumption.
       do 3 eexists. split. eassumption. split. eassumption.
       split. now erewrite <- Hsub2; eauto.
       eapply Forall2_monotonic_strong; [| eapply Hall; eassumption ].
       intros x1 x2 Hinx1 Hinx2 [l1' [Hgetl1 Hr]].
       eexists; split; eauto.
       rewrite cc_approx_val_eq in *. 
       assert (Heqx : x2  = Loc (β l1')).
       { destruct x2; try contradiction. destruct Hr. subst. 
         reflexivity. }
       subst.
       assert (Hr1 : val_loc (Loc l1') \subset reach' H1 (val_loc (Loc l1))).
       { intros l Hin. inv Hin. simpl.
         eapply Included_post_reach'.
        rewrite post_Singleton; eauto. simpl.
        rewrite <- Heqfv. eapply get_In_env_locs.
        eassumption. eassumption. reflexivity. }
       assert (Hr2 : val_loc (Loc (β l1')) \subset reach' H2 (val_loc (Loc (β l1)))).
       { rewrite reach'_idempotent.
         eapply Included_trans; [| eapply reach'_set_monotonic; eapply Included_post_reach' ].
         eapply Included_trans; [| eapply Included_post_reach' ]. 
         simpl post. rewrite post_Singleton; eauto.
         simpl post.
         rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r, post_Singleton; eauto.
         eapply In_Union_list.
         eapply in_map with (f := val_loc). eassumption. }
       { eapply IHj; try eassumption.
         * eapply well_formed_antimon; [| eassumption ].
           rewrite (reach'_idempotent _ (val_loc (Loc l1))).
           eapply reach'_set_monotonic. eassumption.
         * eapply well_formed_antimon; [| eassumption ].
           rewrite (reach'_idempotent _ (val_loc (Loc (β l1)))).
           eapply reach'_set_monotonic. eassumption.
         * eapply Included_trans; [| eapply reachable_in_dom ]; try eassumption.
         * eapply Included_trans; [| eapply reachable_in_dom ]; try eassumption. }
       
       
       intros b1 b2 tc1 tc2 tc3  H3 H3' H4' env_loc xs1 ft e1 vs1 vs2
              Heq1 Hinj1 Heq2 Hinj2 Hfind Hdef Hset.
       edestruct Hcc
         as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi).
       * eapply Equivalence_Transitive; [| now apply Heq1 ].
         eapply subheap_heap_env_equiv; try eassumption.
         eapply Included_trans; [| now eapply Included_post_reach' ].
         edestruct Hin1 as [b'1 Hget1'']. reflexivity.
         eexists. eexists. split; [| split; [ eassumption |]].
         reflexivity. eapply Hsub1 in Hget1''. subst_exp.
         eassumption.
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
       * do 3 eexists; split; [ | split ]; try (now eauto).
   Qed.

   Lemma cc_approx_var_env_heap_monotonic (k j : nat) (β : Inj) (δ : EInj) (H1 H2 H1' H2' : heap block)
       (rho1 rho2 : env) x y:
     well_formed (reach' H1 (env_locs rho1 [set x])) H1 ->
     well_formed (reach' H2 (env_locs rho2 [set y])) H2 ->
     env_locs rho1 [set x] \subset dom H1 ->
     env_locs rho2 [set y] \subset dom H2 ->
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     cc_approx_var_env k j GIP GP β δ H1 rho1 H2 rho2 x y ->
     cc_approx_var_env k j GIP GP β δ H1' rho1 H2' rho2 x y.
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
   
   Lemma cc_approx_env_heap_monotonic S (k j : nat) (β : Inj) (δ : EInj)
         (H1 H2 H1' H2' : heap block)
       (rho1 rho2 : env):
     well_formed (reach' H1 (env_locs rho1 S)) H1 ->
     well_formed (reach' H2 (env_locs rho2 S)) H2 ->
     env_locs rho1 S \subset dom H1 ->
     env_locs rho2 S \subset dom H2 ->
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     (H1, rho1) ⋞ ^ (S ; k ; j; GIP ; GP ; β; δ) (H2, rho2) ->
     (H1', rho1) ⋞ ^ (S ; k ; j; GIP ; GP; β; δ) (H2', rho2).
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

   Lemma cc_approx_heap_heap_monotonic (S : Ensemble loc) (k j : nat) (β : Inj)
         (δ : EInj) (H1 H2 H1' H2' : heap block)  :
     well_formed (reach' H1 S) H1 ->
     well_formed (reach' H2 (image β S)) H2 ->
     S \subset dom H1 ->
     (image β S) \subset dom H2 ->
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     S |- H1 ≼ ^ (k; j; GIP; GP; β ; δ) H2 ->
     S |- H1' ≼ ^ (k; j; GIP; GP; β ; δ) H2'.
  Proof.
    intros Hwf1 Hwf2 Hlocs1 Hlocs2 Hs1 Hs2 Hres x HS.
    eapply cc_approx_val_heap_monotonic; try eassumption.

    eapply well_formed_antimon; [| eassumption ]. eapply reach'_set_monotonic.
    eapply Singleton_Included. eassumption.

    eapply well_formed_antimon; [| eassumption ]. eapply reach'_set_monotonic.
    eapply Singleton_Included. eexists; split; now eauto.

    eapply Included_trans; [| eassumption ].
    eapply Singleton_Included. eassumption.

    eapply Included_trans; [| eassumption ].
    eapply Singleton_Included. eexists; split; now eauto.

    now eauto.
  Qed. 
    
  Lemma cc_approx_clos_heap_monotonic (S : Ensemble var) (k j : nat) (β β1 β2 : Inj)
        (δ : EInj) (H1 H2 H1' H2' : heap block) rho1 l2 :
    well_formed (reach' H1 (env_locs rho1 S)) H1 ->
    well_formed (reach' H2 [set l2]) H2 ->
    env_locs rho1  S \subset dom H1 ->
    H1 ⊑ H1' -> H2 ⊑ H2' ->
    (rho1, H1) << ^ (k; j; GIP; GP; β; δ; S) (l2, H2) ->
    (rho1, H1') << ^ (k; j; GIP; GP; β ; δ ; S) (l2, H2').
  Proof.
    intros Hwf1 Hwf2 Hlocs1 Hs1 Hs2 Henv.
    edestruct Henv as (c & vs & FLS & Heq & Hnd & Hget & Hall); try eassumption.
    do 3 eexists. split.
    eassumption. split. eassumption. split. erewrite <- Hs2. reflexivity.
    eassumption.
    
    eapply Forall2_monotonic_strong; [| eapply Hall; eassumption ].
    intros x1 x2 Hinx1 Hinx2 [l1 [Hgetx Hr]]. 
    assert (Hr1 : val_loc (Loc x1) \subset reach' H1 S).
    { intros l Hin. inv Hin. simpl.
      eapply reach'_extensive. eapply Heq. eassumption. }
    assert (Hr2 : val_loc x2 \subset reach' H2 [set l2]).
    { eapply Included_trans; [| eapply Included_post_reach' ]. 
      simpl. rewrite post_Singleton; eauto. simpl.
      eapply In_Union_list.
      eapply in_map. eassumption. }
    eexists. split. eassumption.
    rewrite cc_approx_val_eq in *. 
    eapply cc_approx_val_heap_monotonic; try eassumption.
    * eapply well_formed_antimon; [| eassumption ].
      eapply reach'_set_monotonic. eapply get_In_env_locs.
      eapply Heq. eassumption.
      eassumption.
    * eapply well_formed_antimon; [| eassumption ].
      rewrite (reach'_idempotent _ [set l2]). eapply reach'_set_monotonic. eassumption.
    *  eapply Included_trans; [| eapply reachable_in_dom ]; try eassumption.
       eapply Included_trans; [| eapply reach'_extensive ].
       eapply get_In_env_locs.
       eapply Heq. eassumption. eassumption. 
    * eapply Included_trans; [| eapply reachable_in_dom ]; try eassumption.
      eexists; eauto. inv H. eassumption.
  Qed.


   
  Lemma cc_approx_env_set_alloc_Constr S (k j : nat)
        c vs1 vs2 l1 l2  (H1 H2 H1' H2' : heap block)
        (rho1 rho2 : env) x:

     well_formed (reach' H1 (env_locs rho1 (S \\ [set x]))) H1 ->
     well_formed (reach' H2 (env_locs rho2 (S \\ [set x]))) H2 ->
     env_locs rho1 (S \\ [set x]) \subset dom H1 ->
     env_locs rho2 (S \\ [set x])  \subset dom H2 ->

     well_formed (reach' H1 (locs (Constr c vs1))) H1 ->
     well_formed (reach' H2 (locs (Constr c vs2))) H2 ->
     locs (Constr c vs1) \subset dom H1 ->
     locs (Constr c vs2) \subset dom H2 ->

     (H1, rho1) ⋞ ^ (S \\ [set x]; k; j; GIP; GP; b; d) (H2, rho2) ->
     
     alloc (Constr c vs1) H1 = (l1, H1') ->
     alloc (Constr c vs2) H2 = (l2, H2') ->  

     b l1 = l2 ->
     d l1 = None ->
     (forall j', j' < j ->  Forall2 (fun v1 v2 => Res (v1, H1) ≺ ^ (k; j'; GIP; GP; b; d) Res (v2, H2)) vs1 vs2) ->
     
     (H1', M.set x (Loc l1) rho1) ⋞ ^ (S; k; j; GIP; GP; b; d) (H2', M.set x (Loc l2) rho2).
   Proof with (now eauto with Ensembles_DB).
     intros Hwf1 Hwf2 Hlocs1 Hlocs2 Hwf3 Hwf4 Hlocs3 Hlocs4 Henv Ha1 Ha2 Hb Hd Hres.
     eapply cc_approx_env_P_set; try eassumption.
     eapply cc_approx_env_heap_monotonic; try eassumption.
     eapply HL.alloc_subheap; eassumption.
     eapply HL.alloc_subheap; eassumption.
     simpl. erewrite !gas; eauto.
     split. eassumption.
     simpl. split; eauto. split. eauto. intros i Hlt.
     specialize (Hres i Hlt).
     eapply Forall2_monotonic_strong; [| eassumption ].
     intros x1 x2 Hin1 Hin2 Heq.
     rewrite cc_approx_val_eq.
     eapply cc_approx_val_heap_monotonic; [ | | | | | | now apply Heq ]. try eassumption.
     eapply well_formed_antimon; [| now eapply Hwf3 ]. 
     eapply reach'_set_monotonic.
     eapply In_Union_list. eapply in_map. eassumption.
     eapply well_formed_antimon; [| now eapply Hwf4 ].
     eapply reach'_set_monotonic.
     eapply In_Union_list. eapply in_map. eassumption.
     eapply Included_trans; [| now apply Hlocs3 ].
     eapply In_Union_list. eapply in_map. eassumption.
     eapply Included_trans; [| now apply Hlocs4 ].
     eapply In_Union_list. eapply in_map. eassumption.
     eapply HL.alloc_subheap; eassumption.
     eapply HL.alloc_subheap; eassumption.
   Qed.

   Lemma cc_approx_val_rename_ext  β β' δ δ' k j H1 H2 v1 v2:
     (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β' ; δ') (Res (v2, H2)) ->
     f_eq_subdomain (reach' H1 (val_loc v1)) β β' ->
     f_eq_subdomain (reach' H1 (val_loc v1)) δ δ' ->
     (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β ; δ) (Res (v2, H2)).
  Proof with (now eauto with Ensembles_DB).
    revert k j H1 H2 v1 v2.
    induction k as [k IHk] using lt_wf_rec1.
    induction j as [j IHj] using lt_wf_rec1.
    intros H1 H2 v1 v2 Hres Hfeq.
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    simpl in Hres. 
    destruct (get l1 H1) as [b1'|] eqn:Hget1; destruct (get l2 H2) as [b2'|] eqn:Hget2;
    try now eauto;
    try (destruct b1' as [c1 vs1 | [? | B1 f1] env_loc1 ]; try contradiction).
    destruct Hres as [Hbeq Hbeq']. 
    split. rewrite Hfeq. eassumption. eapply reach'_extensive. reflexivity. 
    destruct b1' as [c1 vs1 | [? | B1 f1] env_loc1 ]; try contradiction;
    destruct b2' as [c2 vs2 | ]; try contradiction. 
    + simpl in Hbeq'. destruct Hbeq' as [ceq [dec Hi]]. split; eauto. subst.
      split; eauto. rewrite H; eauto. now eapply reach'_extensive.
      subst. intros i Hlt. simpl.
      eapply Forall2_monotonic_strong. intros x1 x2 Hin1 Hin2 HR.
      rewrite cc_approx_val_eq. eapply IHj. eassumption.
      rewrite <- cc_approx_val_eq. now apply HR.
      eapply f_eq_subdomain_antimon; [| eassumption ].
      rewrite (reach_unfold H1 (val_loc (Loc l1))).
      eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
      simpl. rewrite post_Singleton; [| eassumption ].
      eapply In_Union_list. eapply in_map. eassumption.
      eapply f_eq_subdomain_antimon; [| eassumption ].
      rewrite (reach_unfold H1 (val_loc (Loc l1))).
      eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
      simpl. rewrite post_Singleton; [| eassumption ].
      eapply In_Union_list. eapply in_map. eassumption.
      eapply Hi; eauto.
    + simpl in Hbeq'.
      destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction.
      destruct Hbeq' as [Hd [Henv Hcc]].
      simpl. split.
      rewrite H. eassumption. eapply reach'_extensive. reflexivity. split.

      intros i Hlt.
      edestruct (Henv i Hlt) as (c & vs & FVs & Heqfv & Hnd & Hget & Hall); try eassumption.
      do 3 eexists. split. eassumption. split. eassumption. split. eassumption. 
      eapply Forall2_monotonic_strong; [| eapply Hall; eassumption ].
      intros x1 x2 Hinx1 Hinx2 [l1' [Hgetx Hr]].
      assert (Hr1 : val_loc (Loc l1') \subset reach' H1 (val_loc (Loc l1))).
      { intros l Hin. inv Hin. simpl.
        eapply Included_post_reach'.
        rewrite post_Singleton; eauto. simpl.
        rewrite <- Heqfv. eapply get_In_env_locs. eassumption.
        eassumption. reflexivity. }
      { eexists; split; eauto.
        rewrite cc_approx_val_eq in *.
        eapply IHj; try eassumption.
         * eapply f_eq_subdomain_antimon; [| eassumption ].
           rewrite (reach'_idempotent _ (val_loc (Loc l1))).
           eapply reach'_set_monotonic. eassumption.
         * eapply f_eq_subdomain_antimon; [| eassumption ].
           rewrite (reach'_idempotent _ (val_loc (Loc l1))).
           eapply reach'_set_monotonic. eassumption. }

       intros b1' b2' tc1 tc2 tc3 H3 H3' H4' env_loc' xs1 ft
       e1 vs1 vs2 Hres1 Hinj1 Hres2 hinj2 Hfind Hdef Hset.
       edestruct Hcc as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi)
       ; [| | | | eassumption | eassumption | eassumption | ]; try eassumption.
       exists xs2, e2, rho2'. split; [| split ]; eauto. intros. 
       eapply Hi; try eassumption.
       eapply Equivalence_Transitive; [| eassumption ].
       eapply f_eq_subdomain_compose_compat. reflexivity.
       eapply f_eq_subdomain_compose_compat; [| reflexivity ].
       eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].
       rewrite <- heap_env_equiv_image_reach; [| eassumption ].
       rewrite image_id. rewrite (reach_unfold H1 (val_loc (Loc l1))).
       eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
       simpl. rewrite post_Singleton; eauto...
       eapply Equivalence_Transitive; [| eassumption ].      
       eapply f_eq_subdomain_compose_compat. reflexivity.
       eapply f_eq_subdomain_compose_compat; [| reflexivity ].
       eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].
       rewrite <- heap_env_equiv_image_reach; [| eassumption ].
       rewrite image_id. rewrite (reach_unfold H1 (val_loc (Loc l1))).
       eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
       simpl. rewrite post_Singleton; eauto...
  Qed.
  
  Lemma cc_approx_var_env_rename_ext  (k j : nat) (β β': Inj) (δ δ' : EInj) (H1 H2 : heap block) 
         (rho1 rho2 : env) (x y : var) :
     cc_approx_var_env k j GIP GP β δ H1 rho1 H2 rho2 x y ->
     f_eq_subdomain (reach' H1 (env_locs rho1 [set x])) β β' ->
     f_eq_subdomain (reach' H1 (env_locs rho1 [set x])) δ δ' ->
     cc_approx_var_env k j GIP GP β' δ' H1 rho1 H2 rho2 x y.
  Proof with (now eauto with Ensembles_DB).
    intros Hcc Heq Heq' v Hget. edestruct Hcc as [l2 [Hget2 Hres]].
    eassumption. eexists; split; eauto.
    eapply cc_approx_val_rename_ext. eassumption.
    eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].
    eapply reach'_set_monotonic. eapply env_locs_Singleton; try eassumption.
    eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].
    eapply reach'_set_monotonic. eapply env_locs_Singleton; try eassumption.
  Qed.
  
   Lemma cc_approx_env_rename_ext S β β' δ δ' H1 H2 rho1 rho2 k j :
     (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; β; δ) (H2, rho2) ->
     f_eq_subdomain (reach' H1 (env_locs rho1 S)) β β' ->
     f_eq_subdomain (reach' H1 (env_locs rho1 S)) δ δ' ->
     (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; β'; δ') (H2, rho2).
  Proof with (now eauto with Ensembles_DB).
    intros Henv Heq Heq' x Hin.
    eapply cc_approx_var_env_rename_ext. now eauto.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply env_locs_monotonic.
    eapply Singleton_Included. eassumption.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply env_locs_monotonic.
    eapply Singleton_Included. eassumption.
  Qed.

  Lemma cc_approx_heap_rename_ext (S : Ensemble loc) (k j : nat) (β β' : Inj)
        (δ δ' : EInj) (H1 H2 : heap block)  :
     S |- H1 ≼ ^ (k; j; GIP; GP; β ; δ) H2 ->
     f_eq_subdomain (reach' H1 S) β β' ->
     f_eq_subdomain (reach' H1 S) δ δ' ->
     S |- H1 ≼ ^ (k; j; GIP; GP; β' ; δ') H2.
  Proof.
    intros Hres Hfeq1 Hfeq2 x HS.
    eapply cc_approx_val_rename_ext; eauto.
    
    rewrite <- Hfeq1. now eauto.
    eapply reach'_extensive. eassumption.

    symmetry; eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic.
    eapply Singleton_Included. eassumption.

    symmetry; eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic.
    eapply Singleton_Included. eassumption.
  Qed. 
    
  Lemma cc_approx_clos_rename_ext (S : Ensemble var) (k j : nat) (β β': Inj)
        (δ δ' : EInj) (H1 H2 : heap block) rho1 l2 :
    (rho1, H1) << ^ (k; j; GIP; GP; β; δ; S) (l2, H2) ->
    f_eq_subdomain (reach' H1 (env_locs rho1 S)) β β' ->
    f_eq_subdomain (reach' H1 (env_locs rho1 S)) δ δ' ->
    (rho1, H1) << ^ (k; j; GIP; GP; β' ; δ' ; S) (l2, H2).
  Proof.
    intros Henv Hfeq1 Hfeq2.
    edestruct Henv as (c & vs & FLS & Heq & Hnd & Hget & Hall); try eassumption.
    do 3 eexists. split. eassumption.
    split. eassumption. 
    split. eassumption.
    eapply Forall2_monotonic_strong; [| eapply Hall; eassumption ].
    intros x1 x2 Hinx1 Hinx2 [l1 [Hgetl1 Hr]].
    eexists; split; eauto.
    assert (Hr1 : val_loc (Loc l1) \subset reach' H1 (env_locs rho1 S)).
    { intros l Hin. inv Hin. simpl. 
      eapply reach'_extensive. eapply get_In_env_locs.
      eapply Heq. eassumption. eassumption. reflexivity. }
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_rename_ext; try eassumption.
    * eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].
      rewrite (reach'_idempotent _ (env_locs rho1 S)).
      eapply reach'_set_monotonic. eassumption.
    * eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].
      rewrite (reach'_idempotent _ (env_locs rho1 S)).
      eapply reach'_set_monotonic. eassumption.
  Qed.

  End LogRelLemmas.


  (** * Proper Instances *)

  
  Global Instance cc_approx_env_proper_set :
    Proper (Same_set var ==> Logic.eq ==>  Logic.eq ==> Logic.eq ==> Logic.eq ==>
            Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           cc_approx_env_P.
  Proof.
    intros s1 s2 [H1 H2]; split; intros Hpre;
    subst; eapply cc_approx_env_P_antimon; subst; eauto. 
  Qed.

  Global Instance Proper_cc_approx_heap :
    Proper (Same_set _ ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff) cc_approx_heap.
  Proof.
    intros s1 s2 Hseq; constructor; subst;
    intros Hcc z Hin; eapply Hcc; eapply Hseq; eauto.
  Qed.
  

End CC_log_rel.