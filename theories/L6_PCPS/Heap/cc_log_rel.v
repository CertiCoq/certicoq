(* Step-indexed logical relation for L6 closure conversion.
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2017
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From CertiCoq.L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util set_util
                 List_util Heap.heap Heap.heap_defs Heap.space_sem Heap.GC tactics map_util.
From compcert Require Import lib.Coqlib.

Import ListNotations.

Module CC_log_rel (H : Heap).

  Module Sem := SpaceSem H.

  Import H Sem.GC Sem.GC.Equiv Sem.GC.Equiv.Defs Sem.

  (** ** Resource conditions  *)

  (** * Preconditions *)
  
  (** Local precondition. Enforced as initial condition for the expressions being related *)
  Definition IInv := relation (heap block * env * exp).

  (** Global precondition.
      Enforced as initial condition for future executions of the result *)
  Definition GIInv :=
    forall (B : Ensemble var) {H : ToMSet B},
      nat -> nat -> relation (heap block * env * exp).
  
  (** * Postconditions *)
  
  (** Local postconditions. Holds for the result of the execution
      of the expressions being related. *)
  Definition Inv := relation (heap block * env * exp * nat * nat).

  (** Global posconditions. Holds for the result of future execution of the result *)
  Definition GInv :=
    (* forall (B : Ensemble var) {H : ToMSet B}, nat -> *)
      nat -> nat -> relation (heap block * env * exp * nat * nat).
  
  (** Loc Injection *)
  Definition Inj := loc -> loc.

  (** Env Injection -- partial *)
  Definition EInj := loc -> option loc.
  
  (** Tag for closure records *)
  Variable (clo_tag : cTag). 

  (** A program will not get stuck for any fuel amount *)
  (* This is used to exclude programs that may timeout for low fuel,
      but they might get stuck later *)
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
    Variable (cc_approx_val' : nat -> GIInv -> GInv -> Inj -> ans -> ans -> Prop).     
    
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
        big_step H1' rho1' e1 r1 c1 m1 ->
        not_stuck H1' rho1' e1 ->
        exists (r2 : ans) (c2 m2 : nat) (b : Inj),
          big_step_GC_cc H2' rho2' e2 r2 c2 m2 /\
          (* extra invariants for costs *)
          IL (H1', rho1', e1, c1, m1) (H2', rho2', e2, c2, m2) /\
          cc_approx_val (k - c1) j IIG IG b r1 r2.

    Definition cc_approx_clos
               (* step indexes *)
               (j : nat)
               (* Invariants *)
               (GI : GIInv) (GP : GInv)
               (b : Inj)
               
               (p1 : loc * heap block)
               (p2 : loc * heap block) : Prop :=
      let '(l1, H1) := p1 in
      let '(l2, H2) := p2 in
      l2 = b l1 /\
      exists rho1 c (vs : list value) FVs,
        key_set rho1 <--> FromList FVs /\
        NoDup FVs /\
        get l1 H1 = Some (Env rho1) /\
        get l2 H2 = Some (Constr c vs) /\
        Forall2 (fun (x1 : var) (v2 : value)  =>
                   exists l1, M.get x1 rho1 = Some (Loc l1) /\
                         cc_approx_val' j GI GP b (Res (Loc l1, H1)) (Res (v2, H2)))
                FVs vs.

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
                (forall i, (i < j)%nat ->
                      match j with
                         | 0 => True
                         | S j =>
                           cc_approx_clos cc_approx_val_aux (j - (j - i)) IP P b
                                          (env_loc1, H1) (env_loc2, H2)
                      end) /\
                forall (b1 b2 : Inj)
                  env_loc1' (rho_clo rho_clo1 rho_clo2 : env) (H1' H1'' H2' : heap block)
                  (env_loc2' : loc)
                  (xs1 : list var) (ft : fTag) (e1 : exp) (vs1 vs2 : list value),
                  (Loc env_loc1, H1) ≈_(id, b1) (Loc env_loc1', H1') ->
                  injective_subdomain (reach' H1' [set env_loc1']) b1 ->
                  (Loc env_loc2, H2) ≈_(b2, id) (Loc env_loc2', H2') ->
                  injective_subdomain (reach' H2 [set env_loc2]) b2 ->
                  
                  find_def f1 B1 = Some (ft, xs1, e1) ->
                  get env_loc1' H1' = Some (Env rho_clo) ->
                  
                  def_closures B1 B1 rho_clo H1' (Loc env_loc1') =  (H1'', rho_clo1) ->
                  setlist xs1 vs1 rho_clo1 = Some rho_clo2 ->
                  length vs1 = length vs2 ->

                  exists (xs2 : list var) (e2 : exp) (rho2' : env),
                    find_def f2 B2 = Some (ft, xs2, e2) /\
                    Some rho2' = setlist xs2 ((Loc env_loc2') :: vs2) (def_funs B2 B2 (M.empty _)) /\
                    (forall i,
                       (i < k)%nat ->
                       match k with
                         | 0 => True
                         | S k =>
                           forall b',
                             let R j v1 v2 := cc_approx_val (k - (k - i)) j IP P b' (Res (v1, H1')) (Res (v2, H2')) in
                             (forall j, Forall2 (R j) vs1 vs2) ->
                             f_eq_subdomain (reach' H1' [set env_loc1']) (b2 ∘ b ∘ b1) b' ->
                             (forall (H2  : heap block) b2,
                                live' (env_locs rho2' (occurs_free e2)) H2' H2 b2 ->
                                IP (name_in_fundefs B1 :&: occurs_free e1 \\ FromList xs1) _
                                   (reach_size H1'' rho_clo2 e1)
                                   (1 + (PS.cardinal (fundefs_fv B1)))
                                   (H1'', rho_clo2, e1) (H2, subst_env b2 rho2', e2)) /\
                             (forall j, cc_approx_exp cc_approx_val
                                                 (k - (k - i))
                                                 j
                                                 (IP (name_in_fundefs B1 :&: occurs_free e1 \\ FromList xs1) _
                                                     (reach_size H1'' rho_clo2 e1)
                                                     (1 + (PS.cardinal (fundefs_fv B1)))) IP
                                                 (P (reach_size H1'' rho_clo2 e1)
                                                    (1 + (PS.cardinal (fundefs_fv B1)))) P
                                                 (e1, rho_clo2, H1'') (e2, rho2', H2'))
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

  Notation "p1 << ^ ( k ; j ; P1 ; P2 ; b ) p2" :=
        (cc_approx_clos (cc_approx_val k) j P1 P2 b p1 p2)
          (at level 70, no associativity).
  
   
  (** Unfold the recursion. A more compact definition of the value relation. *)
  Definition cc_approx_val' (k : nat) (j : nat) (IP : GIInv) (P : GInv) (b : Inj) (r1 r2 : ans) : Prop :=
    match r1, r2 with
      | OOT, OOT => True (* Both programs timeout *)
      | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
        match v1, v2 with
          | Loc l1, Loc l2 =>
            b l1 = l2 /\
            match get l1 H1, get l2 H2 with
              | Some (Constr c1 vs1), Some (Constr c2 vs2) =>
                    c1 = c2 /\
                    (forall i, (i < j)%nat ->
                          let R l1 l2 := cc_approx_val k i IP P b (Res (l1, H1)) (Res (l2, H2)) in
                          Forall2 R vs1 vs2)
              | Some (Clos (FunPtr B1 f1) (Loc env_loc1)), Some (Constr c [FunPtr B2 f2; Loc env_loc2]) =>
                (forall i, (i < j)%nat -> (env_loc1, H1) << ^ ( k ; i ; IP ; P ; b ) (env_loc2, H2) ) /\
                forall (b1 b2 : Inj)
                  env_loc1' (rho_clo rho_clo1 rho_clo2 : env) (H1' H1'' H2' : heap block)
                  (env_loc2' : loc)
                  (xs1 : list var) (ft : fTag) (e1 : exp) (vs1 vs2 : list value),
                  (Loc env_loc1, H1) ≈_(id, b1) (Loc env_loc1', H1') ->
                  injective_subdomain (reach' H1' [set env_loc1']) b1 ->
                  (Loc env_loc2, H2) ≈_(b2, id) (Loc env_loc2', H2') ->
                  injective_subdomain (reach' H2 [set env_loc2]) b2 ->
                  
                  find_def f1 B1 = Some (ft, xs1, e1) ->
                  get env_loc1' H1' = Some (Env rho_clo) ->

                  def_closures B1 B1 rho_clo H1' (Loc env_loc1') =  (H1'', rho_clo1) ->
                  setlist xs1 vs1 rho_clo1 = Some rho_clo2 ->
                  length vs1 = length vs2 ->

                  exists (xs2 : list var) (e2 : exp) (rho2' : env),
                    find_def f2 B2 = Some (ft, xs2, e2) /\
                    Some rho2' = setlist xs2 ((Loc env_loc2') :: vs2) (def_funs B2 B2 (M.empty _)) /\
                    (forall i ,
                       (i < k)%nat  ->
                       forall b',
                         let R j v1 v2 := cc_approx_val i j IP P b'(Res (v1, H1')) (Res (v2, H2')) in
                         (forall j, Forall2 (R j) vs1 vs2) ->
                         f_eq_subdomain (reach' H1' [set env_loc1']) (b2 ∘ b ∘ b1) b' ->
                         (forall (H2 : heap block) b2, (* redundant *)
                             live' (env_locs rho2' (occurs_free e2)) H2' H2 b2 ->
                             IP (name_in_fundefs B1 :&: occurs_free e1 \\ FromList xs1) _
                                (reach_size H1'' rho_clo2 e1)
                                (1 + (PS.cardinal (fundefs_fv B1)))
                                (H1'', rho_clo2, e1) (H2, subst_env b2 rho2', e2)) /\
                         (forall j, cc_approx_exp cc_approx_val
                                             i j
                                             (IP (name_in_fundefs B1 :&: occurs_free e1 \\ FromList xs1) _
                                                 (reach_size H1'' rho_clo2 e1)
                                                 (1 + (PS.cardinal (fundefs_fv B1)))) IP
                                             (P (reach_size H1'' rho_clo2 e1)
                                                (1 + (PS.cardinal (fundefs_fv B1)))) P
                                             (e1, rho_clo2, H1'') (e2, rho2', H2')))
              | _, _ => False
            end
          | _, _ => False
        end
      | _, _ => False
    end.


  Opaque cc_approx_clos.
  
  (** Correspondence of the two definitions *)
  Lemma cc_approx_val_eq (k j : nat) IP P b (v1 v2 : ans) :
    cc_approx_val k j IP P b v1 v2 <-> cc_approx_val' k j IP P b v1 v2.
  Proof.
    destruct k as [ | k ]; destruct j as [| j];
    destruct v1 as [[[l1 | lf1 f1] H1] |]; destruct v2 as [[[l2 | lf2 f2] H2] |];
    try (now split; intros; contradiction);
    try (now simpl; eauto).   
    - split; simpl; [ intros [Heqb Hc] |];
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto. 
      { destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1 | ] | ];
        destruct b2 as [c2 vs2 | | ]; try contradiction.
        destruct Hc as [Heq' Hyp]. 
        split. eauto. now split; eauto.
        
        destruct vs2 as [ | [| B2 f2 ] [| [ env_loc2 |] [|]] ]; try contradiction.
        destruct Hc as [Hcc Hyp]. 
        split; eauto. split; eauto. split; eauto. omega. omega. 
        
        intros b1 b2 el tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft
               e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hfind Hget Hdef Hset Hlen.
        edestruct Hyp
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try now eauto. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto. 
        + clear; now firstorder.
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heqb [Him Hyp]]. split; eauto. split; eauto.
          
          intros b1 b2 el tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft
                 e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset Hlen.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; eauto. } 
    - split; simpl; [ intros [Heqb Hc] |];
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto.
      { destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; try contradiction.
        + destruct Hc as [Hin Hyp].
          split; [ eassumption | split; [ eassumption |]].
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite !Heqi in Hap. 
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          destruct Hc as [Henv Hyp].
          subst.
          split; eauto. split. 
          intros i Hlt.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite <- Heqi. now eapply Henv; eauto.
          
          intros b1 b2 el tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1
                 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset Hlen.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto). }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1|] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + intros [Heq1 [Heq2 Hi]]. subst.
          split; [ reflexivity | split; [ reflexivity |]].

          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega. rewrite !Heqi.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heqb [Henv Hyp]]. split; eauto.
          split. 
          intros i Hlt. assert (Heqi : j - (j - i) = i) by omega.
          rewrite Heqi. now eapply Henv; eauto.
          
          intros b1 b2 el tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
                 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset Hlen.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto). }
    - split; simpl; [ intros [Heqb Hc] |];
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto.
      { destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; try contradiction.
        + destruct Hc as [Hc Hyp].
          split; eauto. split; eauto. intros; omega.
        + simpl. destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          destruct Hc as [Henv Hyp].
          subst. split; eauto. split.

          intros; omega.
          
          intros b1 b2 el tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
                 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset Hlen.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto. 
          do 3 eexists; split; [ | split ]; try (now eauto).
          simpl. intros i Hleq b' Hall Hfeq.
          assert (Heqi : k - (k - i) = i) by omega.
          replace i with (k - (k - i)) by eassumption. 
          eapply Hi; eauto. intros j'.
          eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap. rewrite Heqi. simpl in Hap. eassumption.
      }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + intros [Heq1 [Heq2 Hi]].
          subst. split; [ reflexivity | split; [ reflexivity |]]; eauto.
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Heq1 [Heq2 Hyp]].
          subst. split; eauto. split.

          intros i Hlt; omega.
          
          intros le b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft
                 e1 vs1 vs2 Heq1 Hr1 Heq2' Hr2 Hget Hfind Hdef Hset Hlen.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          intros i b' Hleq Hall Hfeq.
          assert (Heqi : k - (k - i) = i) by omega.
          replace i with (k - (k - i)) in Hi by eassumption. 
          eapply Hi; eauto. omega. }
      (*     eapply Forall2_monotonic; [| now eauto ]. *)
      (*   intros x1 x2 Hap. rewrite <- Heqi. eassumption. *)
      (* } *)
    - split; simpl; [ intros [Heqb Hc] |];
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; try now eauto.
      { destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; try contradiction.
        + destruct Hc as [Heq2 Hi]; split; [ eassumption | split; [eassumption |]].
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite !Heqi in Hap.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          destruct Hc as [Henv Hyp]; split; eauto. split.
          
          intros i Hlt.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite <- Heqi. now eapply Henv; eauto.
          
          intros b1 b2 el tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1
                 ft e1 vs1 vs2 Heq1 Hr1 Heq2' Hr2 Hget Hfind Hdef Hset Hlen.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          simpl. intros i b' Hleq Hfeq Hall.
          assert (Heqi : k - (k - i) = i) by omega.
          replace i with (k - (k - i)) by eassumption. 
          eapply Hi; eauto. intros j'.
          eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap. rewrite Heqi. eapply Hap.
      }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + intros [Heq1 [Heq2 Hi]].
          subst. split; [ reflexivity | split; [ reflexivity |]]; eauto.
          
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : j - (j - i) = i) by omega. rewrite !Heqi.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros [Hb [Henv Hyp]].
         split; eauto. split.
          
          intros i Hlt.
          assert (Heqi : j - (j - i) = i) by omega.
          rewrite Heqi. now eapply Henv; eauto.
          
          intros el b1 b2 tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1
                 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset Hlen.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          intros i b' Hleq Hfeq Hall'.
          assert (Heqi : k - (k - i) = i) by omega.
          replace i with (k - (k - i)) in Hi by eassumption. 
          eapply Hi; eauto. omega. }
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

    Definition cc_approx_heap (S : Ensemble loc) k j IP P b (H1 H2 : heap block) :=
      forall (x : loc), S x ->
                   Res (Loc x, H1) ≺ ^ ( k ; j ; IP ; P ; b ) Res (Loc (b x), H2) \/
                   (x, H1) << ^ ( k ; j ; IP ; P ; b ) (b x, H2).
    

    Notation "S |- H1 ≼ ^ ( k ; j ; IP ; P ; b ) H2" :=
      (cc_approx_heap S k j IP P b H1 H2) (at level 70, no associativity).
  
  
  (** Environment relation for the whole domain of definition :
    * ρ1 ~_k ρ2 iff forall x, ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
    Definition cc_approx_env (k j : nat) IP P b c1 c2 : Prop :=
    c1 ⋞ ^ (Full_set _; k; j; IP; P; b ) c2.
  
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
            (b : Inj).
    
  (** * Monotonicity Properties *)
  
  (** The environment relation is antimonotonic in the set of free variables *) 
  Lemma cc_approx_env_P_antimon (S1 S2 : Ensemble var) (k j : nat)
        (c1 c2 : (heap block) * env) :
    c1 ⋞ ^ ( S2 ; k ; j ; GIP ; GP ; b ) c2 ->
    S1 \subset S2 ->
    c1 ⋞ ^ ( S1 ; k ; j ; GIP ; GP ; b ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre Hin x Hin'. eapply Hpre; eapply Hin; eauto.
  Qed.

  Lemma cc_approx_heap_antimon P1 P2 k j IP P (H1 H2 : heap block) :
    P1 \subset P2 ->
    P2 |- H1 ≼ ^ ( k ; j ; IP ; P ; b ) H2 ->
    P1 |- H1 ≼ ^ ( k ; j ; IP ; P ; b ) H2.
  Proof.
    intros Hsub Hcc x Hin. eapply Hcc; eauto. eapply Hsub; eauto.
  Qed.

  (** The expression relation is monotonic in the local invariant *)
  Lemma cc_approx_exp_rel_mon_post k j LIP1 GIP1 (LP1 LP2 : Inv) (GP1 : GInv)
        (p1 p2 : exp * env * heap block) :
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP1 ; GP1 ) p2 ->
    inclusion _ LP1 LP2 ->
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP2 ; GP1 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2]. 
    intros Hcc Hin b1 b2 H1' H2' rho1' rho2' v1 c1 m1 HH1 Hr1 HH2 Hr2 Hip Hleq Hstep Hstuck.
    edestruct Hcc as [v2 [c2 [m2 [b' [Hstep' [HInv Hval]]]]]]; eauto.
    repeat eexists; eauto.
  Qed.

  (** The expression relation is monotonic in the local invariant *)
  Lemma cc_approx_exp_rel_mon_pre k j LIP1 LIP2 GIP1 (LP1 : Inv) (GP1 : GInv)
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

  
  (** The logical relation respects equivalence of the global invariant *)
  
  Lemma cc_approx_exp_same_rel_IH k j LIP1 GIP1 LP1 (GP1 GP2 : GInv) p1 p2 :
    (forall m b r1 r2,
       m <= k ->
       r1 ≺ ^ (m ; j ; GIP1 ; GP1 ; b ) r2 ->
       r1 ≺ ^ (m ; j ; GIP1 ; GP2 ; b ) r2) ->
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP1 ; GP1 ) p2 ->
    (forall k1 k2, same_relation _ (GP1 k1 k2) (GP2 k1 k2)) ->
    p1 ⪯ ^ ( k ; j ; LIP1 ; GIP1 ; LP1 ; GP2 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2].
    intros IH Hcc Hin b1 b2 H1' H2' rho1' rho2'
           v1 c1 m1 HH1 Hr1 HH2 Hr2 Hip Hleq Hstep Hstuck.
    edestruct Hcc as [v2 [c2 [m2 [b' [Hstep' [HInv Hval]]]]]]; eauto.
    repeat eexists; eauto.
    rewrite cc_approx_val_eq.
    eapply IH; eauto. omega.
    rewrite <- cc_approx_val_eq; eauto.
  Qed.
  
  Opaque cc_approx_exp.
  
  Lemma cc_approx_val_same_rel (k j : nat) (GP1 GP2 : GInv) (b1 : Inj) r1 r2 :
    r1 ≺ ^ (k ; j ; GIP ; GP1 ; b1 ) r2 ->
    (forall k1 k2, same_relation _ (GP1 k1 k2) (GP2 k1 k2)) ->
    r1 ≺ ^ (k ; j ; GIP ; GP2 ; b1 ) r2.
  Proof.
    revert j b1 GP1 GP2 r1 r2.
    induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1.
    intros b' GP1 GP2 r1 r2.
    destruct r1 as [[[l1 | lf1 f1] H1] |];
      destruct r2 as [[[l2 | lf2 f2] H2] |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
    destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ];
      destruct b2 as [c2 vs2 | | ]; eauto; intros [Heq Hcc] Hrel; split; eauto.
    - destruct Hcc as [Heq' Hcc]. split; [ eassumption |].
      intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
      intros x1 x2 Hap.
      rewrite cc_approx_val_eq in *. eapply IHj; try eassumption.
    - destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
      destruct Hcc as [Henv Hcc]. split; eauto.
      
      intros i Hlt.
      edestruct Henv as (Heql & rhoc & c & vs & FVs & Hnd & Hget1 & Heqfv & Hget2 & Hall); try eassumption.
      split; eauto. do 4 eexists. repeat (split; try eassumption).
      eapply Forall2_monotonic; [| eassumption ].
      intros x1 x2 [l1' [Hget Hval]].
      eexists; split; eauto. rewrite cc_approx_val_eq in *.
      eapply IHj; eassumption.
      
      intros b1 b2 el tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
             vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset Hlen.
      edestruct Hcc
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
      do 3 eexists; split; [ | split ]; try (now eauto).
      intros i Hleq b''. simpl. intros Hrel' Hfeq1.
      split.
      edestruct (Hi i) as [HI Hcc']; eauto.
      + intros j'. eapply Forall2_monotonic; [| now eapply Hrel' ].
        intros. rewrite cc_approx_val_eq.
        eapply IHk; eauto. now rewrite <- cc_approx_val_eq; simpl in *; eauto.
        intros. split; now eapply Hrel.
      + intros j'. eapply cc_approx_exp_same_rel_IH with (GP1 := GP1); try eassumption.
        intros; eapply IHk. omega. eassumption. eassumption.
        eapply cc_approx_exp_rel_mon_post. eapply Hi. eassumption.
        intros j''. 
        eapply Forall2_monotonic; [| now eapply Hrel' ].
        intros. rewrite cc_approx_val_eq.
        eapply IHk; eauto. now rewrite <- cc_approx_val_eq; simpl in *; eauto.
        intros. split; now eapply Hrel. eassumption.
        now eapply Hrel.
  Qed.

  Transparent cc_approx_exp.
  
  Lemma cc_approx_exp_same_rel (P : relation nat) k j (GP' : GInv)
        p1 p2 :
    p1 ⪯ ^ ( k ; j ; LIP ; GIP ; LP ; GP ) p2 ->
    (forall k1 k2, same_relation _ (GP k1 k2) (GP' k1 k2)) ->
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
    destruct r1 as [[[l1 | lf1 f1] H1] |]; destruct r2 as [[[l2 | lf2 f2] H2] |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    - destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
      intros [Heq Hcc] Hleq. split; [ eassumption |].
      destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1 | ] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
      + destruct Hcc as [Heq' Hi]; split; [ eassumption |].
        intros i Hleq'. simpl.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; try eassumption.
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hcc as [Henv Hcc]. split; eauto.
        
        intros i Hlt.
        edestruct Henv as (Heql & rhoc & c & vs & FVs & Hnd & Hget1 & Heqfv & Hget2 & Hall); try eassumption.
        split; eauto. do 4 eexists. repeat (split; try eassumption).
        eapply Forall2_monotonic; [| eassumption ].
        intros x1 x2 [l1' [Hget Hval]]. eexists; split. eassumption.
        rewrite cc_approx_val_eq in *. eapply IHj; eassumption.

        intros b1 b2 el tc1 tc2 tc3 H1' H1'' H2' env_loc'
               xs1 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset Hlen.
        edestruct Hcc
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi'); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i Hleq' R Hfeq Hall. 
        eapply Hi'; try eassumption. omega.
  Qed.


  Lemma cc_approx_clos_monotonic (k m j : nat) (p1 : loc * heap block)
        (p2 : loc * heap block) b' :
    p1 << ^ (k; j; GIP; GP; b') p2 ->
    m <= k ->
    p1 << ^ (m; j; GIP; GP; b') p2.
  Proof.
    intros Hheap Hleq. destruct p1 as [l1 H1]. destruct p2 as [l2 H2]. 
    edestruct Hheap as (Heql & rho1 & c & vs & FVs & Hnd & Hget1 & Heqfv & Hget2 & Hall); try eassumption.
    split; eauto.
    do 4 eexists. repeat (split; try eassumption).
    eapply Forall2_monotonic; [| eassumption ].
    intros x1 x2 [y [Hval Hcc]]. 
    eexists; split.
    eassumption.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_monotonic; eauto.
  Qed.

  Lemma cc_approx_heap_monotonic S (k m j : nat) (H1 H2 : heap block) b' :
    S |- H1 ≼ ^ (k; j; GIP; GP; b') H2 ->
    m <= k ->
    S |- H1 ≼ ^ (m; j; GIP; GP; b') H2.
  Proof.
    intros Hheap Hleq x Hin. eapply Hheap in Hin. inv Hin.
    left. eapply cc_approx_val_monotonic; eauto.
    right. eapply cc_approx_clos_monotonic; eauto.
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
      as [v2 [c2 [m2 [b2' [Hstep2 [Hleq2 H3]]]]]]; eauto.
    omega. do 5 eexists; repeat split; eauto.
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
    r1 ≺ ^ (k; j; GIP' ; GP' ; b' ) r2 ->
    i <= j ->
    r1 ≺ ^ (k; i; GIP' ; GP' ; b' ) r2.
  Proof.
    destruct r1 as [[[l1 | lf1 f1] H1] |]; destruct r2 as [[[l2 | lf2 f2] H2] |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
    intros [Heq Hcc] Hleq. split; [ eassumption |].
    destruct b1 as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ];
      destruct b2 as [c2 vs2 | | ]; eauto.
    + destruct Hcc as [Heq' Hi]; split; [ eassumption |].
      intros i' Hleq'. simpl. eapply (Hi i'); omega.
    + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
      destruct Hcc as [Henv Hcc]. split; eauto.

      intros j' Hlt. eapply Henv. omega.
      
      (* intros b1 b2 el tc1 tc2 tc3 H1' H1'' H2' env_loc' *)
      (*        xs1 ft e1 vs1 vs2 Heq1 Hr1 Heq2 Hr2 Hget Hfind Hdef Hset. *)
      (* edestruct Hcc *)
      (*   as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi'); eauto. *)
      (* do 3 eexists; split; [ | split ]; try (now eauto). *)
      (* intros i' j' Hleq' Hleq'' R Hall. eapply Hi'. eassumption. *)
      (* omega. eassumption.  *)
  Qed.

  Lemma cc_approx_clos_j_monotonic (k j i : nat) (p1 : loc * heap block)
        (p2 : loc * heap block) b' :
    p1 << ^ (k; j; GIP; GP; b' ) p2 ->
    i <= j ->
    p1 << ^ (k; i; GIP; GP; b' ) p2.
  Proof.
    intros Hheap Hleq. destruct p1 as [rho1 H1]. destruct p2 as [l2 H2]. 
    edestruct Hheap as (Hleq' & rho & c & vs & FVs & Hnd & Hget1 & Heqfv & Hget &  Hall); try eassumption.
    split; eauto.
    do 4 eexists. repeat (split; try eassumption). 
    eapply Forall2_monotonic; [| eassumption ].
    intros x1 x2 [y [Hget' Hval]].
    eexists; split; eauto.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_j_monotonic; eauto.
  Qed.

  Lemma cc_approx_heap_j_monotonic S (k j i : nat) (H1 H2 : heap block) b' :
    S |- H1 ≼ ^ (k; j; GIP; GP; b') H2 ->
    i <= j ->
    S |- H1 ≼ ^ (k; i; GIP; GP; b') H2.
  Proof.
    intros Hheap Hleq x Hin. eapply Hheap in Hin. inv Hin.
    left. eapply cc_approx_val_j_monotonic; eauto.
    right. eapply cc_approx_clos_j_monotonic; eauto.
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
      as [v2 [c2 [m2 [b2' [Hstep2 [Hleq2 H3]]]]]]; eauto.
    do 5 eexists; repeat split; eauto.
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
    simpl. intros x Hc. inv Hc.
  Qed.
  
  Lemma cc_approx_env_P_union (P1 P2 : Ensemble var) (k j : nat) c1 c2 :
    c1 ⋞ ^ ( P1 ; k ; j ; GIP ; GP ; b ) c2 ->
    c1 ⋞ ^ ( P2 ; k ; j ; GIP ; GP ; b ) c2 ->
    c1 ⋞ ^ ( P1 :|: P2 ; k ; j ; GIP ; GP ; b ) c2.
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

  Lemma cc_approx_heap_Empty_set (k j : nat) c1 c2 :
    Empty_set var |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ) c2.
  Proof.
    now firstorder.
  Qed.
  
  Lemma cc_approx_heap_union (S1 S2 : Ensemble var) (k j : nat) c1 c2 :
    S1 |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ) c2 ->
    S2 |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ) c2 ->
    S1 :|: S2 |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ) c2.
  Proof.
    intros Hcc1 Hcc2 x Hin; inv Hin; eauto.
  Qed.
  
  Lemma cc_approx_heap_inter_l (S1 S2 : Ensemble var) (k j : nat) c1 c2 :
    S1 |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ) c2 ->
    S1 :&: S2  |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ) c2.
  Proof.
    intros Hpre x HP2. eapply Hpre; eauto.
    now inv HP2.
  Qed.

  Lemma cc_approx_heap_inter_r (S1 S2 : Ensemble var) (k j : nat) c1 c2 :
    S2 |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ) c2 ->
    S1 :&: S2  |- c1 ≼ ^ (k ; j ; GIP ; GP ; b ) c2.
  Proof.
    intros Hpre x HP2. eapply Hpre; eauto.
    now inv HP2.
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
      (Res (v1, H1)) ≺ ^ (k; j; GIP ; GP; b ) (Res (v2, H2)) ->
      cc_approx_var_env k j GIP GP b H1 (M.set x v1 rho1) H2 (M.set x v2 rho2) y y.
  Proof.
    intros k j rho1 rho2 H1 H2 x y v1 v2 Hvar Hval.
    destruct (peq y x); subst.
    - apply cc_approx_var_env_set_eq; eauto.
    - apply cc_approx_var_env_set_neq; eauto.
  Qed.
  
  Lemma cc_approx_var_env_set_neq_r :
    forall (k j : nat)  (rho1 rho2 : env) (H1 H2 : heap block)
      (y1 x2 y2 : var) ( v2 : value),
      cc_approx_var_env k j GIP GP b H1 rho1 H2 rho2 y1 y2 ->
      y2 <> x2 ->
      cc_approx_var_env k j GIP GP b H1 rho1 H2 (M.set x2 v2 rho2) y1 y2.
  Proof. 
    intros k j rho1 rho2 H1 H2 x2 y1 y2 v2 Hval Hneq x' Hget.
    rewrite M.gso in *; eauto.
  Qed.

  
  (** Extend the related environments with a single point *)
  Lemma cc_approx_env_P_set (S : Ensemble var) (k j : nat)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v1 v2 : value) :
      (H1, rho1) ⋞ ^ ( S \\ [set x] ; k ; j ; GIP ; GP ; b ) (H2, rho2) ->
      (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP; b ) (Res (v2, H2)) ->
      (H1, M.set x v1 rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, M.set x v2 rho2).
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

  Lemma cc_approx_env_P_setlist_not_in_P_l (S : Ensemble var) (k j : nat) 
        (rho1 rho1' rho2 : env) (H1 H2 : heap block) (xs : list var) (vs : list value) :
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, rho2) ->
    Disjoint _ (FromList xs) S ->
    setlist xs vs rho1 = Some rho1' -> 
    (H1, rho1') ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, rho2).
  Proof. 
    intros Hcc Hnin Hset y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    erewrite setlist_not_In. eassumption. eassumption.
    intros Hc. eapply Hnin. constructor; eauto.
  Qed.

  Lemma cc_approx_env_P_setlist_not_in_P_r (S : Ensemble var) (k j : nat) 
        (rho1 rho2 rho2' : env) (H1 H2 : heap block) (xs : list var) (vs : list value) :
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, rho2) ->
    Disjoint _ (FromList xs) S ->
    setlist xs vs rho2 = Some rho2' -> 
    (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, rho2').
  Proof. 
    intros Hcc Hnin Hset y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    eexists; split; eauto. erewrite <- setlist_not_In. eassumption. eassumption.
    intros Hc. eapply Hnin. constructor; eauto.
  Qed.
  (** * Related values are well-defined in the heap *)

  Lemma cc_approx_val_dom1 (k j : nat) v1 v2 H1 H2 :
    Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b ) Res (v2, H2) ->
    val_loc v1 \subset dom H1.
  Proof.
    intros Hcc h Hin; destruct v1 as [l1|]; inv Hin.
    destruct v2  as [l2|]; try contradiction.
    simpl in Hcc.
    destruct (get h H1) eqn:Hget; [| destruct Hcc; contradiction ].
    clear LP LIP.
    now firstorder.
  Qed.

  Lemma cc_approx_val_dom2 (k j : nat) v1 v2 H1 H2 :
    Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b ) Res (v2, H2) ->
    val_loc v2 \subset dom H2.
  Proof.
    clear LP LIP.
    intros Hcc h Hin; destruct v2 as [l2|]; inv Hin.
    destruct v1 as [l1|]; try contradiction.
    simpl in Hcc.
    destruct (get l1 H1) as [b1 | ] eqn:Hget; [| destruct Hcc; contradiction ].
    destruct Hcc as [Heq1 Hcc].
    destruct b1 as [c1 vs1 | [ b1 | ] [ lrho1 | ] | ]; try contradiction.

    destruct (get h H2) as [b2 | ] eqn:Hget'; [| contradiction ].
    now eexists; eauto.

    destruct (get h H2) as [b2 | ] eqn:Hget'; [| contradiction ].
    now eexists; eauto.
  Qed.

  Lemma cc_approx_env_P_dom1 (R : Ensemble var) (k j : nat)
        rho1 rho2 H1 H2 :
    (H1, rho1) ⋞ ^ ( R ; k ; j ; GIP ; GP ; b ) (H2, rho2) ->
    env_locs rho1 R \subset dom H1.  
  Proof. 
    intros Hcc x [y [Hget Hin]].
    destruct (M.get y rho1) as [ [l1 |] | ] eqn:Hgetl; [| now inv Hin | now inv Hin ].
    inv Hin. edestruct Hcc as [v2 [Hget' Hcc']]; eauto.
    eapply cc_approx_val_dom1. eassumption. reflexivity.
  Qed.

  Lemma cc_approx_env_P_dom2 (R : Ensemble var) (k j : nat)
        rho1 rho2 H1 H2 :
    (H1, rho1) ⋞ ^ ( R ; k ; j ; GIP ; GP ; b ) (H2, rho2) ->
    binding_in_map R rho1 ->
    env_locs rho2 R \subset dom H2.  
  Proof. 
    intros Hcc Hbin x [y [Hget Hin]].
    edestruct Hbin as [v1 Hget1]. eassumption.
    destruct (M.get y rho2) as [ [l1 |] | ] eqn:Hgetl; [| now inv Hin | now inv Hin ].
    inv Hin. edestruct Hcc as [v2 [Hget' Hcc']]; eauto.
    eapply cc_approx_val_dom2. eassumption. subst_exp. reflexivity.
  Qed.

  Lemma cc_approx_clos_post_dom1 (k : nat) j
        (H1 H2 : heap block) l1 l2 :
    (l1, H1) << ^ (k; j; GIP; GP; b) (l2, H2) ->  
    post H1 [set l1] \subset dom H1.
  Proof.
    intros Henv x [l' [b' [Hin [ Hget Hin'] ]]]. inv Hin. 
    edestruct Henv as (Hleq & rho1 & c & vs & FLS &  Hget1 & Hnd & Heq & Hget2 & Hall). 
    repeat subst_exp. destruct Hin' as [y [Hin Hgety]]. 
    destruct (M.get y rho1) as [ [l1 |] | ] eqn:Hgetl; [| now inv Hget | now inv Hget ].
    inv Hget. inv Hgety. 
    edestruct (@Forall2_exists loc) with (x := y) as [v2 [Hin'' Hv]]; try eassumption.
    eapply Hget1. unfold key_set. unfold In. now rewrite Hgetl.  
    
    simpl in Hv. destruct Hv as [l1' [Hgety' Hv]].
    rewrite cc_approx_val_eq in Hv. repeat subst_exp.
    eapply cc_approx_val_dom1. eassumption. reflexivity.

  Qed.

  Lemma cc_approx_clos_dom1 (k : nat) j
        (H1 H2 : heap block) l1 l2 :
    (l1, H1) << ^ (k; j; GIP; GP; b) (l2, H2) ->  
    l1 \in dom H1.
  Proof.
    intros Henv.
    edestruct Henv as (rho1 & c & vs & FLS & Hseq & Hget1 & Hnd & Heq & Hget2 & Hall). 
    eexists; eauto.
  Qed.

  Lemma cc_approx_clos_dom2 (k : nat) j
        (H1 H2 : heap block) l1 l2 :
    (l1, H1) << ^ (k; j; GIP; GP; b) (l2, H2) ->  
    l2 \in dom H2.
  Proof.
    intros Henv.
    edestruct Henv as (Hleq & rho & c & vs & FLS  & Hget1 & Hnd & Heq & Hget2 & Hall). 
    eexists; eauto. 
  Qed.


  Lemma cc_approx_heap_dom1 (k j : nat) S H1 H2 : 
    S |- H1 ≼ ^ (k; j; GIP; GP; b) H2 ->
    S \subset dom H1.
  Proof.
    intros Hh x Hin. eapply Hh in Hin. inv Hin.
    eapply cc_approx_val_dom1. eassumption. reflexivity. 
    eapply cc_approx_clos_dom1. eassumption.
  Qed.

  Lemma cc_approx_heap_dom2 (k j : nat) S H1 H2 : 
    S |- H1 ≼ ^ (k; j; GIP; GP; b) H2 ->
    image b S \subset dom H2.
  Proof.
    intros Hh x [y [Hin Heq]]. subst. eapply Hh in Hin. inv Hin.
    eapply cc_approx_val_dom2. eassumption. reflexivity.
    eapply cc_approx_clos_dom2. eassumption.
  Qed.
    
  Lemma cc_approx_val_loc_eq v2 (k j : nat) H1 H2 l :
    Res (Loc l, H1) ≺ ^ (k; j; GIP ; GP; b) Res (v2, H2) ->
    v2 = Loc (b l).
  Proof.
    intros Hcc. destruct v2; [| now inv Hcc ].
    destruct Hcc as [Heq _].
    congruence.
  Qed.

  Lemma cc_approx_clos_loc_eq (k : nat) j
        (H1 H2 : heap block) l1 l2 :
    (l1, H1) << ^ (k; j; GIP; GP; b ) (l2, H2) ->
    l2 = b l1.
  Proof.
    intros Henv.
    edestruct Henv as (Hleq & rho & c & vs & FLS & Hget1 & Hnd & Heq & Hget2 & Hall). 
    eassumption.
  Qed.
  
    
  Lemma Forall2_dom1 (k j : nat) (H1 H2 : heap block)
        vs1 vs2 :
    Forall2 (fun v1 v2 => forall j, (Res (v1, H1)) ≺ ^ (k; j; GIP ; GP ; b )
                                                 (Res (v2, H2)))
            vs1 vs2 ->
    Union_list (map val_loc vs1) \subset dom H1.  
  Proof.
    intros Hall. induction Hall; simpl.
    - now eauto with Ensembles_DB.
    - eapply Union_Included; [| eassumption ].
      eapply cc_approx_val_dom1 with (j := 0); eauto.
  Qed.

  Lemma Forall2_dom2 (k j : nat) (rho1 rho2 : env) (H1 H2 : heap block) vs1 vs2 :
    Forall2 (fun v1 v2 => forall j, (Res (v1, H1)) ≺ ^ (k; j; GIP ; GP ; b)
                            (Res (v2, H2)))
            vs1 vs2 ->
    Union_list (map val_loc vs2) \subset dom H2.  
  Proof.
    intros Hall. induction Hall; simpl.
    - now eauto with Ensembles_DB.
    - eapply Union_Included; [| eassumption ].
      eapply cc_approx_val_dom2 with (j := 0); eauto.
  Qed.

  (** * Reachable values are related *)
  
  Lemma cc_approx_val_post_cc (k j : nat) v1 v2 H1 H2 l :
    Res (v1, H1) ≺ ^ (k; S j; GIP ; GP; b) Res (v2, H2) ->
    l \in post H1 (val_loc v1) ->
    Res (Loc l, H1) ≺ ^ (k; j; GIP ; GP; b) Res (Loc (b l), H2) \/
    (l, H1) << ^ (k; j; GIP; GP; b ) (b l, H2).
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
      specialize (Hrel j (NPeano.Nat.lt_succ_diag_r j)).
      edestruct (@Union_lists_exists loc) as [S' [Hin3 Hin2]]. eassumption.
      edestruct (list_in_map_inv _ _ _ Hin3) as [l3' [Heql Hinl]]; subst.
      destruct l3' as [l3' |]; inv Hin2.
      edestruct (Forall2_exists _ l0 l1 (Loc l) Hinl Hrel)  as [x' [Hin2 Hres']].
      rewrite cc_approx_val_eq in *. 
      assert (Hres'' := Hres').
      destruct x'; [| now destruct Hres' ].
      destruct Hres'' as [Hbeq _]. subst. left.
      eassumption.
    - destruct v as [|]; try contradiction.
      destruct v0 as [|]; try contradiction. 
      destruct l0 as [| [|] [ | [|] [|] ] ]; try contradiction. 
      simpl in Hin'. destruct Hcc as [ Henv _ ].
      specialize (Henv j (NPeano.Nat.lt_succ_diag_r j)).
      edestruct Henv as (le & rho1 & c' & vs & FLS & Hseq & Hget1 & Hnd & Heq' & Hget2 ).
      rewrite Union_Empty_set_neut_l in Hin'. inv Hin'. right. eassumption.
      (* rewrite <- Hget1 in Hin'. *)
      (* edestruct Hin' as [y [Hiny Hgety]]. *)
      (* destruct (M.get y e) as [ [l1 | ]  |] eqn:Hgety'; try contradiction. *)
      (* inv Hgety.  *)
      (* edestruct @Forall2_exists with (x := y) as [v3 [Hin2' Hcc']]; *)
      (*   try eassumption. *)
      (* eassumption. *)
      (* edestruct Hcc' as [l1' [Hgetl1' Hval]]. *)
      (* rewrite cc_approx_val_eq in Hval. *)
      (* assert (Hres'' := Hval). repeat subst_exp. *)
      (* destruct v3; [| now destruct Hval ]. *)
      (* destruct Hres'' as [Hbeq _]. subst. *)
      (* eassumption. *)
    - destruct v; destruct v0; try contradiction.
    - destruct v; destruct v0; try contradiction.
    - destruct v; destruct v0; try contradiction.
  Qed.

  Lemma cc_approx_clos_post_cc (k j : nat) l1 l2 H1 H2 l :
    (l1, H1) << ^ (k; j; GIP; GP; b ) (l2, H2) ->
    l \in post H1 [set l1] ->
    Res (Loc l, H1) ≺ ^ (k; j; GIP ; GP; b) Res (Loc (b l), H2).
  Proof. 
    intros Henv [l' [b' [Hin [Hget Hin']]]]. inv Hin. 
    edestruct Henv as (Hleq & rho1 & c & vs & FLS & Hget1 & Hnd & Heq & Hget2 & Hall). 
    repeat subst_exp. destruct Hin' as [y [Hin Hgety]]. 
    destruct (M.get y rho1) as [ [l1 |] | ] eqn:Hgetl; [| now inv Hget | now inv Hget ].
    inv Hget. inv Hgety. 
    edestruct (@Forall2_exists loc) with (x := y) as [v2 [Hin'' Hv]]; try eassumption.
    eapply Hget1. unfold key_set. unfold In. now rewrite Hgetl.  
    
    simpl in Hv. destruct Hv as [l1' [Hgety' Hv]].
    rewrite cc_approx_val_eq in Hv. repeat subst_exp.

    assert (Hv' := Hv).

    eapply cc_approx_val_loc_eq in Hv'. subst. 
    eassumption.
  Qed. 

  
  Lemma cc_approx_val_post_n_cc (k j : nat) v1 v2 H1 H2 l n :
    Res (v1, H1) ≺ ^ (k; n + j; GIP ; GP; b ) Res (v2, H2) ->
    l \in (post H1 ^ n) (val_loc v1) ->
    Res (Loc l, H1) ≺ ^ (k; j; GIP ; GP; b ) Res (Loc (b l), H2) \/
    (l, H1) << ^ (k; j; GIP; GP; b ) (b l, H2).
  Proof. 
    revert v1 v2 l j; induction n as [n IHn] using lt_wf_rec1; destruct n; intros v1 v2 l j. 
    - intros Heq Hin. destruct v1; [| now inv Hin ]. inv Hin. 
      erewrite <- !(cc_approx_val_loc_eq v2); eauto.
    - intros Hres1 Hpost.
      replace (S n) with (n + 1) in Hpost by omega.
      rewrite app_plus in Hpost. unfold compose in Hpost. simpl in Hpost.
      edestruct post_n_exists_Singleton as [l3 [Hin1 Hinp]]; try eassumption.
      simpl plus in Hres1.
      eapply cc_approx_val_post_cc in Hin1; [| eassumption ]. inv Hin1. 
      eapply IHn; try eassumption. omega.

      destruct n. inv Hinp. now right. 
      edestruct H as (Hleq & rho1 & c & vs & FLS & Hget1 & Hnd & Heq & Hget2 & Hall). 
      replace (S n) with (n + 1) in Hinp by omega.
      rewrite app_plus in Hinp. unfold compose in Hinp. simpl in Hinp.
      edestruct post_n_exists_Singleton as [l3' [Hin1 Hinp3]]; try eassumption.
      eapply cc_approx_clos_post_cc in Hin1; [| eassumption ]. 
      eapply (IHn n). omega.

      eapply cc_approx_val_j_monotonic. eassumption. omega.
      eassumption.
  Qed.

  Lemma cc_approx_clos_post_n_cc (k j : nat) l1 l2 H1 H2 l n :
    (l1, H1) << ^ (k; n + j; GIP; GP; b ) (l2, H2) ->
    l \in (post H1 ^ n) [set l1] ->
    Res (Loc l, H1) ≺ ^ (k; j; GIP ; GP; b ) Res (Loc (b l), H2) \/
    (l, H1) << ^ (k; j; GIP; GP; b ) (b l, H2).
  Proof. 
    revert l1 l2 l j; induction n as [n IHn] using lt_wf_rec1; destruct n; intros l11 l2 l j. 
    - intros Heq Hin. inv Hin. 
      erewrite <- !(cc_approx_clos_loc_eq _ _ _ _ l l2); eauto.
    - intros Hres1 Hpost.
      replace (S n) with (n + 1) in Hpost by omega.
      rewrite app_plus in Hpost. unfold compose in Hpost. simpl in Hpost.
      edestruct post_n_exists_Singleton as [l3 [Hin1 Hinp]]; try eassumption.
      simpl plus in Hres1.
      eapply cc_approx_clos_post_cc in Hin1; [| eassumption ].
      eapply cc_approx_val_post_n_cc with (n := n).
      eapply cc_approx_val_j_monotonic. eassumption. omega.
      eassumption.
  Qed. 
  
  Lemma cc_approx_val_reach_cc (k : nat) v1 v2 H1 H2 l :
    (forall j, Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b) Res (v2, H2)) ->
    l \in reach' H1 (val_loc v1) ->
    (forall j, Res (Loc l, H1) ≺ ^ (k; j; GIP ; GP; b) Res (Loc (b l), H2))  \/
    (forall j, (l, H1) << ^ (k; j; GIP; GP; b ) (b l, H2)).
  Proof. 
    intros Hres [n [_ Hpost]]. assert (Hpost' := Hpost).
    eapply cc_approx_val_post_n_cc with (j := 0) in Hpost; [| now eauto ].
    inv Hpost.
    - left. intros j. 
      eapply cc_approx_val_post_n_cc with (j := j) in Hpost'; [| now eauto ].
      inv Hpost'. eassumption.
      simpl in H.
      edestruct H0 as (Hleq & rho1 & c & vs & FLS & Hget1 & Hnd & Heq & Hget2 & Hall). 
      erewrite Heq in H. now destruct H. 
    - right. intros j. 
      eapply cc_approx_val_post_n_cc with (j := j) in Hpost'; [| now eauto ].
      inv Hpost'; try eassumption.
      simpl in H0.
      edestruct H as (Hleq & rho1 & c & vs & FLS & Hget1 & Hnd & Heq & Hget2 & Hall). 
      erewrite Heq in H0. now destruct H0. 
  Qed. 

  Lemma cc_approx_clos_reach_cc (k : nat) l1 l2 H1 H2 l :
    (forall j, (l1, H1) << ^ (k; j; GIP; GP; b ) (l2, H2)) ->
    l \in reach' H1 [set l1] ->
    (forall j, Res (Loc l, H1) ≺ ^ (k; j; GIP ; GP; b) Res (Loc (b l), H2))  \/
    (forall j, (l, H1) << ^ (k; j; GIP; GP; b ) (b l, H2)).
  Proof. 
    intros Hres [n [_ Hpost]]. assert (Hpost' := Hpost).
    eapply cc_approx_clos_post_n_cc with (j := 0) in Hpost; [| now eauto ].
    inv Hpost.
    - left. intros j. 
      eapply cc_approx_clos_post_n_cc with (j := j) in Hpost'; [| now eauto ].
      inv Hpost'. eassumption.
      simpl in H.
      edestruct H0 as (Hleq & rho1 & c & vs & FLS & Hget1 & Hnd & Heq & Hget2 & Hall). 
      erewrite Heq in H. now destruct H. 
    - right. intros j. 
      eapply cc_approx_clos_post_n_cc with (j := j) in Hpost'; [| now eauto ].
      inv Hpost'; try eassumption.
      simpl in H0.
      edestruct H as (Hleq & rho1 & c & vs & FLS & Hget1 & Hnd & Heq & Hget2 & Hall). 
      erewrite Heq in H0. now destruct H0. 
  Qed. 

  
  (** * The logical relation respects functional extensionality *)

  Instance Proper_cc_approx_val_f_eq :
    Proper (eq ==> eq ==> eq ==> eq ==> f_eq ==> eq ==> eq ==> iff) cc_approx_val'.
  Proof.
    clear.
    intros k' k Heq1 j' j Heq2  GI GI' Heq3 II II' Heq4 b1 b2 Heq5
           r1' r1 Heq6 r2' r2 Heq7; subst.
    revert j b1 b2 Heq5 r1 r2. induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1. intros b1 b2 Heq5 r1 r2.
    simpl. 
    destruct r1 as [[v1 H1] |];  destruct r2 as [[v2 H2] |]; try now eauto.
    destruct v1 as [l1 | ? ? ]; destruct v2 as [l2 | ? ?]; try now eauto.
    split; intros Hres.
    - simpl in *. destruct (get l1 H1) as [bl1 |]; eauto; destruct (get l2 H2) as [bl2 |]; eauto.
      destruct Hres as [Heq Hres]; split; eauto; try (rewrite <- Heq5; eassumption). 
      destruct bl1 as [c1 vs1 | [? | B1 f1] [env_loc1|] | ];
        destruct bl2 as [c2 vs2 | | ]; eauto.
      + destruct Hres as [Heq1 Hi]. split; eauto.
        intros i' Hleq.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; eauto. symmetry. eassumption.
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hres as [Henv Hres]. split.
        
        intros i Hlt.
        edestruct Henv as (Hleq & rho & c & vs & FVs & Hnd & Heqfv & Hget1 & Hget2 & Hall); try eassumption.
        split. rewrite <- Heq5. eassumption.
        do 4 eexists. split. eassumption. split. eassumption.
        split. eassumption. split. eassumption. eapply Forall2_monotonic; [| eassumption ].
        intros x1 x2 [y [Hgety Hval]].
        eexists; split; eauto. 
        rewrite cc_approx_val_eq in *. eapply IHj. omega. symmetry. eassumption.
        eassumption. 
        
        intros b1' b2' el tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
               vs1 vs2 Heq1' Hr1' Heq2 Hr2 Hgetl Hfind Hdef Hset Hlen.
        edestruct Hres
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i' b' Hleq Hall Hfeq. eapply Hi. eassumption. eassumption.
        eapply Equivalence_Transitive; [| eassumption ]. eapply f_eq_subdomain_compose_compat.
        reflexivity. eapply f_eq_subdomain_compose_compat; [| reflexivity ].
        rewrite Heq5. reflexivity.
      + rewrite <- Heq5; eauto.
      + rewrite <- Heq5; eauto.
      + rewrite <- Heq5; eauto. 
    - simpl in *.
      destruct (get l1 H1) as [bl1 |]; eauto. destruct (get l2 H2) as [bl2 |]; eauto.
      destruct Hres as [Hbeq Hres]; split. rewrite Heq5. eassumption.
      destruct bl1 as [c1 vs1 | [? | B1 f1] [ env_loc1 | ] |];
        destruct bl2 as [c2 vs2 | | ]; eauto.
      + destruct Hres as [Heq1 Hi]. split; eauto.
        
        intros i' Hleq.
        eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHj; eauto.

      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        destruct Hres as [Henv Hres].
        split; eauto.
        intros i Hlt.
        edestruct Henv as (Heql & rhoc & c & vs & FVs & Hnd & Heqfv & Hget1 & Hget2 & Hall); try eassumption.
        split.
        rewrite Heq5. eassumption.
        
        do 4 eexists. split. eassumption. split. eassumption.
        split. eassumption. split. eassumption.
        
        eapply Forall2_monotonic; [| eassumption ].
        intros x1 x2 [y [Hgety Hval]].
        eexists; split; eauto.
        rewrite cc_approx_val_eq in *. eapply IHj. omega. eassumption.
        eassumption. 
        
        intros b1' b2' el tc1 tc2 tc3 H1' H1'' H2' env_loc' xs1 ft e1
               vs1 vs2 Heq1' Hr1' Heq2 Hr2 Hget Hfind Hdef Hset Hlen.
        edestruct Hres
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i' b' Hleq Hfeq Hall. eapply Hi. eassumption. eassumption.
        eapply Equivalence_Transitive; [| eassumption ]. eapply f_eq_subdomain_compose_compat.
        reflexivity. eapply f_eq_subdomain_compose_compat; [| reflexivity ].
        rewrite Heq5. reflexivity.
      + rewrite Heq5; eauto.
      + rewrite Heq5; eauto.
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
  

  Lemma env_locs_key_set rho:
    env_locs rho (Full_set var) <--> env_locs rho (key_set rho).
  Proof.
    split; intros l [x [Hin Hm]];
    destruct (M.get x rho) as [ [l' |] | ] eqn:Hget; inv Hm.
    eexists; split; eauto. unfold key_set. 
    now rewrite Hget. 
    now rewrite Hget.

    eexists; split; eauto. now constructor.
    now rewrite Hget.
  Qed. 
    
    
  (** * Reachable set bijections *)
  Lemma cc_approx_val_image_eq_mut (k : nat) j (H1 H2 : heap block)
        (v1 v2 : value) l1 l2 :
    ((Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b) (Res (v2, H2)) ->
     image b ((post H1 ^ j) (val_loc v1)) <--> (post H2 ^ j) (val_loc v2)) /\
    ((l1, H1) << ^ (k; j; GIP; GP; b ) (l2, H2) ->
     image b ((post H1 ^ j) [set l1]) <--> (post H2 ^ j) [set l2]). 
  Proof with now eauto with Ensembles_DB.
    revert v1 v2 l1 l2; induction j; intros v1 v2 l1 l2.
    - split.
      + intros Hval. destruct v1 as [l1' |]; try contradiction.
        destruct v2 as [l2' |]; try contradiction. 
        simpl. eapply cc_approx_val_loc_eq in Hval. subst.
        rewrite image_Singleton. inv Hval. reflexivity.
      + intros Hval.
        simpl. eapply cc_approx_clos_loc_eq in Hval. subst.
        rewrite image_Singleton. reflexivity.
    - split.
      + intros Hval. destruct v1 as [l1' |]; try contradiction.
        destruct v2 as [l2' |]; try contradiction.
        replace (S j) with (j + 1) by omega.
        rewrite !app_plus. unfold compose. simpl.
        simpl in Hval. destruct Hval as [Heq1 Hval]; subst.  
        destruct (get l1' H1) as [b1'|] eqn:Hget1;
          destruct (get (b l1') H2) as [b2'|] eqn:Hget2; try contradiction;
          destruct b1' as [c1 vs1 | [? | B1 f1] [ env_loc1 |] |]; try contradiction;
          destruct b2' as [c2 vs2 | | ]; try destruct Hval as [Heq1 [Heq2 _]]; try contradiction. 
        * rewrite (proper_post_n H1);
          [| rewrite !post_Singleton; try eassumption; reflexivity ].
          rewrite (proper_post_n H2);
            [| rewrite !post_Singleton; try eassumption; reflexivity ].
          simpl. destruct Hval as [Heq' Hi].
          clear Hget1 Hget2.
          specialize (Hi j (Nat.lt_succ_diag_r j)). induction Hi.
          
          simpl. rewrite !post_n_Empty_set, image_Empty_set. reflexivity.
          simpl. rewrite !post_n_Union, image_Union. rewrite IHHi.
          rewrite cc_approx_val_eq in H. eapply IHj in H. rewrite H. reflexivity. 
          exact (1%positive).
          exact (1%positive).
        * destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction. 
          rewrite (proper_post_n H1);
            [| rewrite !post_Singleton; try eassumption; 
               simpl; rewrite !Union_Empty_set_neut_l; reflexivity ].
          rewrite (proper_post_n H2);
            [| rewrite !post_Singleton; try eassumption;
               simpl; rewrite !Union_Empty_set_neut_l, !Union_Empty_set_neut_r; reflexivity ].

          eapply IHj.
          exact (Loc 1%positive).
          exact (Loc 1%positive).
          destruct Hval as [Henv _]. eapply Henv. omega.
      + intros Henv.
        destruct Henv as (Heql & rhoc & c & vs2' & FVs & Hseq & Hnd & Hget1' & Hget2' & Hcc').
        replace (S j) with (j + 1) by omega.
        rewrite !app_plus. unfold compose. simpl.
        rewrite (proper_post_n H1);
          [| rewrite !post_Singleton; try eassumption;
             simpl; rewrite env_locs_key_set, Hseq; reflexivity ].
        rewrite (proper_post_n H2);
          [| rewrite !post_Singleton; try eassumption; reflexivity ]. simpl.
        clear Hget1' Hget2' Hseq Hnd.
        induction Hcc'.
        * rewrite (proper_post_n H1);
          [| rewrite !FromList_nil, env_locs_Empty_set; reflexivity ]. simpl. 
          rewrite !post_n_Empty_set, image_Empty_set at 1. reflexivity.
        * destruct H as [l1' [Hgetx Hcc]]. 
          rewrite (proper_post_n H1);
            [| rewrite !FromList_cons, env_locs_Union, env_locs_Singleton; eauto; reflexivity ].
          simpl.
          rewrite !post_n_Union, image_Union. rewrite IHHcc'.
          eapply Same_set_Union_compat; [| reflexivity ].
          rewrite cc_approx_val_eq in Hcc. eapply IHj with (v1 := Loc l1').
          exact (1%positive).
          exact (1%positive). eapply cc_approx_val_j_monotonic. eassumption.
          omega. 
  Qed. 

  Lemma cc_approx_val_image_eq (k : nat) (H1 H2 : heap block)
        (v1 v2 : value) :
    (forall j, (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b) (Res (v2, H2))) ->
    image b (reach' H1 (val_loc v1)) <--> reach' H2 (val_loc v2). 
  Proof with now eauto with Ensembles_DB.
    intros Hval. split.
    - intros l1 [l2 [[n [_ Hin]] eq]].
      specialize (Hval n). eexists. split.
      now econstructor. 
      eapply (cc_approx_val_image_eq_mut k n).
      exact (1%positive).  
      exact (1%positive).
      eapply Hval. eexists. split; eauto. 
    - intros l1 [n [_ Hin]].
      specialize (Hval n).
      eapply (cc_approx_val_image_eq_mut k n) in Hval.
      eapply Hval in Hin. 
      eapply image_monotonic; [| eassumption ].
      eapply Included_post_n_reach'. 
      exact (1%positive).  
      exact (1%positive).
  Qed.

  Lemma cc_approx_clos_image_eq (k : nat) (H1 H2 : heap block)
        l1 l2 :
    (forall j, (l1, H1) << ^ (k; j; GIP; GP; b ) (l2, H2)) ->
    image b (reach' H1 [set l1]) <--> reach' H2 [set l2]. 
  Proof with now eauto with Ensembles_DB.
    intros Hval. split.
    - intros l1' [l2' [[n [_ Hin]] eq]].
      specialize (Hval n). eexists. split.
      now econstructor. 
      eapply (cc_approx_val_image_eq_mut k n).
      exact (Loc 1%positive).  
      exact (Loc 1%positive).
      eapply Hval. eexists. split; eauto. 
    - intros l1' [n [_ Hin]].
      specialize (Hval n).
      eapply (cc_approx_val_image_eq_mut k n) in Hval.
      eapply Hval in Hin. 
      eapply image_monotonic; [| eassumption ].
      eapply Included_post_n_reach'. 
      exact (Loc 1%positive).  
      exact (Loc 1%positive).
  Qed.
    
  Lemma cc_approx_var_env_image_reach
        (k : nat)
        (H1 H2 : heap block) (rho1 rho2 : env) (x y : var) (v : value) :
    (forall j, cc_approx_var_env k j GIP GP b H1 rho1 H2 rho2 x y) ->
    M.get x rho1 = Some v ->
    image b (reach' H1 (env_locs rho1 [set x])) <--> reach' H2 (env_locs rho2 [set y]). 
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
    (forall j, (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; b) (H2, rho2)) ->
    binding_in_map S rho1 ->
    image b (reach' H1 (env_locs rho1 S)) <-->
    reach' H2 (env_locs rho2 S).
  Proof.
    intros Hres HB. split.
    - intros l' [l [Hin Heq]]; subst.
      destruct Hin as [n [_ Hp]].
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      destruct Hin as [x [Hin Heq]]. 
      destruct (M.get x rho1) as[[l1' |] | ] eqn:Hgetx1; inv Heq.
      eapply reach'_set_monotonic.
      eapply env_locs_monotonic. eapply Singleton_Included. eassumption.
      eapply cc_approx_var_env_image_reach; try eassumption.
      intros j. eapply Hres. eassumption.
      rewrite !env_locs_Singleton at 1; try eassumption.
      eexists; split; eauto. eexists; split; eauto. now constructor.
    - intros l [m [Hm Hr]].
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      destruct Hin as [x [Hin Heq]]. 
      destruct (M.get x rho2) as[[l1' |] | ] eqn:Hgetx1; inv Heq.
      edestruct HB as [v1 Hget1]. eassumption.
      eapply Included_trans; [| reflexivity | ].
      eapply image_monotonic. eapply reach'_set_monotonic.
      eapply env_locs_monotonic. eapply Singleton_Included. eassumption.
      
      rewrite cc_approx_var_env_image_reach; [| intros j; eapply Hres; eassumption | eassumption ].
      rewrite env_locs_Singleton at 1; eauto.      
      eexists; split; eauto.
  Qed. 

  Lemma cc_approx_env_image_reach_included S (k : nat)
        (H1 H2 : heap block) (rho1 rho2 : env) :
    (forall j, (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; b) (H2, rho2)) ->
    image b (reach' H1 (env_locs rho1 S)) \subset
    reach' H2 (env_locs rho2 S).
  Proof.
    intros Hres l' [l [Hin Heq]]; subst.
    destruct Hin as [n [_ Hp]].
    edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
    destruct Hin as [x [Hin Heq]]. 
    destruct (M.get x rho1) as[[l1' |] | ] eqn:Hgetx1; inv Heq.
    eapply reach'_set_monotonic.
    eapply env_locs_monotonic. eapply Singleton_Included. eassumption.
    eapply cc_approx_var_env_image_reach; try eassumption.
    intros j. eapply Hres. eassumption.
    eexists. split; eauto.
    rewrite !env_locs_Singleton at 1; try eassumption.
    eexists; split; eauto. now constructor.
  Qed.

  
  Lemma cc_approx_env_image_eq S (k : nat)
        (H1 H2 : heap block) (rho1 rho2 : env) :
    (forall j, (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; b) (H2, rho2)) ->
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
    (forall j, S |- H1 ≼ ^ (k; j; GIP; GP; b) H2 ) ->
    image b (reach' H1 S) <--> reach' H2 (image b S).
  Proof.
    intros Hres. split. 
    - intros l' [l [Hin Heq]]; subst.
      destruct Hin as [n [_ Hp]].
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      eapply reach'_set_monotonic with (S1 := val_loc (Loc (b l1))). eapply Singleton_Included.
      eexists; split; eauto. 
      assert (Hin' := Hin). eapply (Hres n) in Hin. inv Hin. 
      eapply cc_approx_val_image_eq_mut in H. eexists n. split.
      now constructor. eapply H. eexists. split; eauto.
      eassumption. eassumption. (* XX remove params *) 

      eapply cc_approx_val_image_eq_mut in H. eexists n. split.
      now constructor. eapply H. eexists. split; eauto.
      exact (Loc l1). exact (Loc l1).
    - intros l [m [Hm Hr]].
      edestruct post_n_exists_Singleton as [l1 [Hin Hp']]; try eassumption.
      destruct Hin as [x [Hin Heq]]. subst. 
      eapply Included_trans; [| reflexivity | ].
      eapply image_monotonic. eapply reach'_set_monotonic with (S1 := val_loc (Loc x)).
      eapply Singleton_Included. eassumption.

      eapply image_monotonic. eapply Included_post_n_reach' with (n := m).
      assert (Hin' := Hin). eapply (Hres m) in Hin. inv Hin. 
      
      eapply cc_approx_val_image_eq_mut in H.
      eapply H. eassumption. 
      exact l. exact l.
      
      eapply cc_approx_val_image_eq_mut in H.
      eapply H. eassumption. 
      exact (Loc l). exact (Loc l).
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
  
(*   
  Lemma cc_approx_heap_post (P : Ensemble var) k j (H1 H2 : heap block) : 
    P |- H1 ≼ ^ (k; 1 + j; GIP; GP; b) H2 ->
    post H1 P |- H1 ≼ ^ (k; j; GIP; GP; b) H2.
  Proof.   
    intros Hheap x [l [b' [Hin [Hget Hin']]]].
    specialize (Hheap _ Hin).
    simpl in Hheap. rewrite Hget in Hheap.
    destruct Hheap as [_ Hres].
    destruct b' as [c1 vs1 | [| B1 f1] [ rhoc |] | ]; try contradiction;
    destruct (get (b l) H2) as [[c2 vs2 | [| B2 f2] [ rhoc2 |] | ] |]; try contradiction.
    - destruct Hres as [Heq2 Hall].
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
      destruct Hres as [Henv _]. subst.
      specialize (Henv j (Nat.lt_succ_diag_r j)).
      eapply cc_approx_clos_post_n_cc. eassumption.
      rewrite post_Singleton; eauto. 
      edestruct Henv as (Heql & rhoc' & c & vs & FLS & Heq & Hnd & Hget' & Hget'' & Hall); try eassumption.
      subst. 
      simpl in Hin'. rewrite Union_Empty_set_neut_l in Hin'. inv Hin'.
      destruct Hin' as [x' [Hgetx Hinx]].
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
*)

  Lemma cc_approx_val_reach_cc1 (k : nat) v1 v2 H1 H2 l2 :
    (forall j, Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b ) Res (v2, H2)) ->
    l2 \in reach' H2 (val_loc v2) ->
    (exists l1, l1 \in reach' H1 (val_loc v1) /\
           b l1 = l2 /\
           ((forall j, Res (Loc l1, H1) ≺ ^ (k; j; GIP ; GP; b) Res (Loc (b l1), H2)) \/
            (forall j, (l1, H1) << ^ (k; j; GIP; GP; b) (l2, H2)))).
  Proof. 
    intros Hres Hrin.
    assert (Hrin2 := Hrin).
    eapply cc_approx_val_image_eq in Hrin2; [ | eassumption ].  
    destruct Hrin2 as [l1' [Heq Hind]]; subst.
    eexists. split. eassumption.
    split. reflexivity. 
    eapply cc_approx_val_reach_cc. eassumption. eassumption.
  Qed.

  (** *  The logical relation implies well-formedness *)

  Lemma cc_approx_val_well_formed_post1 (k j : nat) v1 v2 H1 H2 :
    Res (v1, H1) ≺ ^ (k; j + 1; GIP ; GP; b) Res (v2, H2) ->
    well_formed (((post H1) ^ j) (val_loc v1)) H1.
  Proof.
    intros Hcc l1 b1 Hin Hget l Hdom.
    assert (Hp : (post H1 ^ S j) (val_loc v1) l).
    { simpl. do 2 eexists. split. eassumption. 
      split; eassumption. }
    eapply cc_approx_val_post_n_cc with (j := 0) in Hp.
    inv Hp. 
    eapply cc_approx_val_dom1. eassumption.
    reflexivity.
    eapply cc_approx_clos_dom1. eassumption.
    eapply cc_approx_val_j_monotonic. eassumption. omega.
  Qed.

  Lemma cc_approx_val_well_formed_reach1 (k : nat) v1 v2 H1 H2 :
    (forall j, Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b) Res (v2, H2)) ->
    well_formed (reach' H1 (val_loc v1)) H1.
  Proof.
    intros Hcc l1 b1 [n [_ Hin]] Hget l Hdom.
    eapply cc_approx_val_well_formed_post1. now eapply Hcc.
    eassumption. eassumption. eassumption.
  Qed.

  Lemma cc_approx_val_well_formed_reach2 (k : nat) v1 v2 H1 H2 :
    (forall j, Res (v1, H1) ≺ ^ (k; j; GIP ; GP; b) Res (v2, H2)) ->
    well_formed (reach' H2 (val_loc v2)) H2.
  Proof.
    intros Hcc l1 b1 Hin Hget l Hdom.
    assert (Hr : In loc (reach' H2 (val_loc v2)) l). 
    { rewrite reach'_idempotent. eapply Included_post_reach'.
      do 2 eexists; split; eauto. }
    
    eapply cc_approx_val_reach_cc1 in Hr; [ | eassumption ]. 
    destruct Hr as
        [l1' [Hr1 [Hbeq [Hes | Hclo ]]]].
    + subst.
      eapply cc_approx_val_dom2 with (j := 0).
      eapply Hes. reflexivity. 
    + subst. 
      eapply cc_approx_clos_dom2. eapply Hclo with (j := 0).
  Qed.
  

  Lemma cc_approx_env_P_well_formed_reach1 (R : Ensemble var) (k : nat)
        rho1 rho2 H1 H2 :
    (forall j, (H1, rho1) ⋞ ^ ( R ; k ; j ; GIP ; GP ; b) (H2, rho2)) ->
    well_formed (reach' H1 (env_locs rho1 R)) H1.  
  Proof.
    clear LIP LP.
    intros Henv l1 b1 [n [_ Hin]] Hget l Hlocs.
    edestruct post_n_exists_Singleton as [l1' [Hin' Hp]]. eassumption. 
    edestruct Hin' as [y [Hiny Heqy]].
    destruct (M.get y rho1) as [[l1'' |] |] eqn:Hgety; try contradiction.
    inv Heqy. eapply Henv with (j := n + 1) in Hgety; [| eassumption ].
    edestruct Hgety as [l2 [Hgetyl1 Hres]]. 
    assert (Hr : In loc ((post H1 ^ (S n)) [set l1']) l). 
    { do 2 eexists; split. eassumption. split; eauto. }
    
    eapply cc_approx_val_post_n_cc with (v1 := Loc l1') (j := 0) in Hr.
    inv Hr. 
    eapply cc_approx_val_dom1. eassumption. reflexivity.
    eapply cc_approx_clos_dom1. eassumption.
    eapply cc_approx_val_j_monotonic. eassumption. omega.
  Qed.
  
  Lemma cc_approx_env_P_well_formed_reach2 (R : Ensemble var) (k : nat)
        rho1 rho2 H1 H2 :
    (forall j, (H1, rho1) ⋞ ^ ( R ; k ; j ; GIP ; GP ; b ) (H2, rho2)) ->
    binding_in_map R rho1 ->
    well_formed (reach' H2 (env_locs rho2 R)) H2.  
  Proof.
    intros Hcc Hbin l1 b1 Hin Hget l Hdom.
    assert (Hr : In loc (reach' H2 (env_locs rho2 R)) l). 
    { rewrite reach'_idempotent. eapply Included_post_reach'.
      do 2 eexists; split; eauto. }
    edestruct Hin as [m [_ Hpost]].
    edestruct post_n_exists_Singleton as [l1' [Hin' Hp]]. eassumption. 
    edestruct Hin' as [y [Hiny Heqy]].
    destruct (M.get y rho2) as [[l1'' |] |] eqn:Hgety; try contradiction.
    inv Heqy. 
    edestruct Hbin as [l2 Hgety1]. eassumption. 
    eapply cc_approx_val_well_formed_reach2; [| | eassumption | eassumption ]. 
    + intros i.  
      edestruct (Hcc i) as [l2' [Hgety' Hcc']]. eassumption.
      eassumption. repeat subst_exp. eassumption. 
    + exists m. split. now constructor. eassumption.
  Qed. 

  Lemma cc_approx_clos_well_formed_reach1 (k : nat)
        (H1 H2 : heap block) l1 l2 :
    (forall j, (l1, H1) << ^ (k; j; GIP; GP; b) (l2, H2)) ->
    well_formed (reach' H1 [set l1]) H1.
  Proof.
    intros Henv l1' b1 [m [_ Hr]] Hget1 l Hdom.
    assert (Hp : (post H1 ^ S m) [set l1] l).
    { simpl. do 2 eexists. split. eassumption. 
      split; eassumption. }
    eapply cc_approx_clos_post_n_cc with (j := 0) in Hp. 
    inv Hp. 
    eapply cc_approx_val_dom1. eassumption.
    reflexivity.
    eapply cc_approx_clos_dom1. eassumption. now eauto. 
  Qed.
  
  Lemma cc_approx_clos_well_formed_reac2 (k : nat)
        (H1 H2 : heap block) rho1 l2 :
    (forall j, (rho1, H1) << ^ (k; j; GIP; GP; b) (l2, H2)) ->  
    well_formed (reach' H2 [set l2]) H2.
  Proof.
    intros Henv l1 b1 [m [_ Hr]] Hget1.
    edestruct (Henv (m+1)) as (Hleq & rhoc & c & vs & FLS & Heq1 & Hnd & Hget1' & Hget2 & Hall). 
    intros l3 Hlocs. 

    assert (Hin : reach' H2 (Union_list (map val_loc vs)) l3).
    { destruct m as [ | m ].
      - eexists 0. split. now constructor. inv Hr. repeat subst_exp.
        eassumption.
      - replace (Datatypes.S m) with (m + 1) in Hr by omega.
        rewrite app_plus in Hr. unfold compose in Hr; simpl in Hr.
        eapply proper_post_n in Hr;
        [| erewrite post_Singleton; eauto; reflexivity ].
        exists (1 + m). split. now constructor.
        simpl. do 2 eexists. split. eassumption.
        split; eauto. }

    destruct Hin as [n [_ Hr']].
    edestruct post_n_exists_Singleton as [l1' [Hin' Hp]]. eassumption. 
    edestruct (@Union_lists_exists loc) as [R [Hin3 Hin2]]. eassumption.
    edestruct (list_in_map_inv _ _ _ Hin3) as [l3' [Heql Hinl]]; subst.
    destruct l3' as [l3' |]; inv Hin2.
    edestruct (@Forall2_exists_r loc) with (x := Loc l1')
      as [y [Hgety Hcc]]; try eassumption.
    destruct Hcc as [l' [Hgetl1 Hval]].
    rewrite cc_approx_val_eq in Hval. repeat subst_exp.
    eapply cc_approx_val_loc_eq in Hval. inv Hval. 
    
    assert (Hval' : forall j, Res (Loc l', H1) ≺ ^ (k; j; GIP; GP; b) Res (Loc (b l'), H2)).
    { intros j. 
      edestruct (Henv j) as (Hleq' & rhoc' & c' & vs' & FLS' & Heq1' & Hnd' & Hget1'' & Hget2'' & Hall').
      repeat subst_exp. 
      edestruct (@Forall2_exists loc) with (x := y)
        as [z [Hgetz Hcc]];  [| now apply Hall' |].
      eapply Heq1'. eapply Heq1. eassumption.
      simpl in Hcc. destruct Hcc as [l2' [Hgetl4' Hval'']].
      rewrite cc_approx_val_eq in Hval''. repeat subst_exp.
      assert (Hval2 := Hval'').
      destruct z; try contradiction. destruct Hval'' as [Heq' _].
      subst. eassumption. }
    
    assert (Hval := Hval').
    eapply cc_approx_val_well_formed_reach2 in Hval'.
    eapply reachable_in_dom. eassumption.
    simpl. eapply Singleton_Included.
    eapply cc_approx_val_dom2.
    eapply (Hval 0). reflexivity.
    simpl. eexists n. split.
    now constructor. 
    eassumption. 
  Qed.

  
  Lemma Forall2_reach1 (k : nat) (H1 H2 : heap block)
        vs1 vs2 :
    Forall2 (fun v1 v2 => forall j, (Res (v1, H1)) ≺ ^ (k; j; GIP ; GP ; b)
                                                 (Res (v2, H2)))
            vs1 vs2 ->
    well_formed (reach' H1 (Union_list (map val_loc vs1))) H1.  
  Proof.
    intros Hall. induction Hall; simpl.
    - rewrite reach'_Empty_set. eapply well_formed_Empty_set.
    - rewrite reach'_Union. eapply well_formed_Union; [| eassumption ].
      eapply cc_approx_val_well_formed_reach1; eauto.
  Qed.

   
  Lemma Forall2_reach2 (k : nat) (β : Inj) (δ : EInj) (H1 H2 : heap block)
        vs1 vs2 :
    Forall2 (fun v1 v2 => forall j, (Res (v1, H1)) ≺ ^ (k; j; GIP ; GP ; b)
                            (Res (v2, H2)))
            vs1 vs2 ->
    well_formed (reach' H2 (Union_list (map val_loc vs2))) H2.  
  Proof.
    intros Hall. induction Hall; simpl.
    - rewrite reach'_Empty_set. eapply well_formed_Empty_set.
    - rewrite reach'_Union. eapply well_formed_Union; [| eassumption ].
      eapply cc_approx_val_well_formed_reach2; eauto.
  Qed.

  (** * cc_approx_heap *)
    Lemma cc_approx_env_cc_approx_heap (S : Ensemble var) (β1 β2 : loc -> loc)
        (H1 H2 : heap block) (rho1 rho2 : env) k :
      (forall j, (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b ) (H2, rho2)) ->
      (forall j, (reach' H1 (env_locs rho1 S)) |- H1 ≼ ^ (k; j; GIP; GP; b) H2 ).
  Proof.     
    intros Heq j x [m [_ Hin]].
    edestruct post_n_exists_Singleton as [l3' [Hin1 Hinp3]]; try eassumption.
    destruct Hin1 as [y [Hin1 Hgetx]]. edestruct (M.get y rho1) as [[l1 | ] | ] eqn:Hgety; try inv Hgetx.
    edestruct (Heq (m + j)) as [v' [Hgety' Hcc]]; try eassumption.
    eapply cc_approx_val_post_n_cc. eassumption.
    eassumption. 
  Qed.

  (** * The logical relation respects heap equivalences *)

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

  

  Lemma cc_approx_val_res_eq (k j : nat) (b' b1 b2 : Inj) (H1 H2 H1' H2' : heap block)
        (v1 v2 v1' v2' : value) :
    (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b') (Res (v2, H2)) ->

    (v1, H1) ≈_(id, b1) (v1', H1') ->
    injective_subdomain (reach' H1' (val_loc v1')) b1 ->

    (v2, H2) ≈_(b2, id) (v2', H2') ->
    injective_subdomain (reach' H2 (val_loc v2)) b2 ->
    
    (Res (v1', H1')) ≺ ^ (k ; j ; GIP ; GP ; b2 ∘ b' ∘ b1) (Res (v2', H2')).
  Proof with now eauto with Ensembles_DB.
    clear LIP LP b.
    revert j b' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'.
    induction k as [k IHk] using lt_wf_rec1. intros j.
    induction j as [j IHj] using lt_wf_rec1.
    intros b' b1 b2 v1 v2 v1' v2' H1 H2 H1' H2'. 
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    intros [Heq Hcc] (* Hwf1 Hwf2 Hl1 Hl2 *) Hres1 Hr1 Hres2 Hr2. 
    destruct (get l1 H1) as [[c1 vs1 | [? | B1 f1] [ env_loc1 |] | ] | ] eqn:Hget1;
      destruct (get l2 H2) as [[c2 vs2 | | ] | ] eqn:Hget2; try contradiction.
    + rewrite res_equiv_eq in Hres1, Hres2.
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
      split. unfold compose. rewrite <- Heqi1. unfold id. rewrite Heqi2. reflexivity.
      split; eauto.
         
      intros i Hlt. specialize (Hall i Hlt).
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
      
      destruct b1' as [c1' vs1' | | ]; try contradiction.
      destruct b2' as [c2' vs2' | | ]; try contradiction.
 
      destruct Hall as [Hceq Hall]. subst. destruct Henv1 as [Henv1 Henv2].
      rewrite res_equiv_eq in Henv1; rewrite res_equiv_eq in Henv2.
      destruct v as [l3' | lf3' f3']; try contradiction.
      destruct v0 as [l4' | lf4' f4']; try contradiction.
      
      destruct Henv1 as [Heq1 Heq2]. subst.
      destruct Henv2 as [Heq1 Henv2]. unfold id in *. subst.
      inv Hall. inv H5. inv H7.
      rewrite res_equiv_eq in *.  
      destruct y as [l5' | lf5' f5']; destruct y0 as [l6' | lf6' f6']; try contradiction.
      destruct Hcc as [Henv' Hcc].
      destruct H4 as [Heq H4']. subst.
      destruct H3 as [Heq1 Heq2]. subst. split.

      (* rewrite Heq; reflexivity. *)
      
      * intros i Hlt.
        
        edestruct (Henv' i) as (Hleq & rhoc & c & vs & FLS & Heq & Hnd & Hget1'' & Hget2'' & Hall); try eassumption.
        subst. 
        rewrite Hget2'' in H4'. rewrite Hget1'' in Henv2. 
        destruct (get (b2 (b' (b1 l4'))) H2') as [b2'|] eqn:Hgetb2'; try contradiction.
        destruct b2' as [c' vs'| | ]; try contradiction.

        destruct (get l4' H1') as [b1'|] eqn:Hgetb1'; try contradiction.
        destruct b1' as [c'' vs''| | ]; try contradiction.

        unfold id in *. repeat subst_exp. subst.
        simpl in H4'. destruct H4' as [Hceq Hall4]. subst. 

        simpl in Henv2. subst.
        
        clear Hcc.
        
        split. reflexivity.
        do 4 eexists. split. now rewrite heap_env_equiv_key_set in Heq; eauto.
        split. eassumption. split. eassumption.
        split. eassumption.
        
        eapply Forall2_vertical_strong with (R2 := fun x y => x = y); [| eassumption | | ].
        
        intros x y z w Hin1 Hin2 Hin3 Hin4 Hr1' Hr2' Hr3'. 
        destruct Hr1' as [l2 [Hgetl2 Hr1']]. simpl in Hr1'.
        rewrite cc_approx_val_eq in Hr1'.  subst.
        edestruct heap_env_equiv_env_get as [l2' [Hgetl2' Hres']].
        eassumption. eassumption. now constructor.
        destruct l2' as [l2' |]; try (rewrite res_equiv_eq in Hres'; contradiction).
        eexists. split. subst. eassumption. rewrite cc_approx_val_eq.
        eapply IHj. eassumption. now apply Hr1'.
        eassumption.

        eapply injective_subdomain_antimon. eassumption. 
        rewrite (reach_unfold H1' (val_loc (Loc l1'))). eapply Included_Union_preserv_r.
        rewrite (reach_unfold H1' (post H1' _)). eapply Included_Union_preserv_r.
        eapply  reach'_set_monotonic. simpl post. rewrite post_Singleton; eauto.
        simpl. rewrite Union_Empty_set_neut_l. rewrite post_Singleton; eauto.
        eapply Singleton_Included. 
        eapply get_In_env_locs; try eassumption. now constructor. reflexivity.
        
        now apply Hr3'.

        eapply injective_subdomain_antimon. eassumption.
        rewrite (reach_unfold H2 [set b' (b1 l1')]). eapply Included_Union_preserv_r.
        rewrite (reach_unfold H2 (post H2 [set b' (b1 l1')])). eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. rewrite post_Singleton; eauto. simpl.
        rewrite Union_Empty_set_neut_r, Union_Empty_set_neut_l.
        rewrite post_Singleton; eauto. simpl.
        eapply In_Union_list. eapply in_map. eassumption. 
        
        eapply Forall2_refl; eauto.

        eapply block_equiv_Constr_r with (c2 := c2'). simpl. split; [| eassumption ].
        reflexivity.
      * intros b1' b2' el tc1 tc2 tc3 H3' H3'' H4'' env_loc1' xs1 ft
             e1 vs1 vs2 Hres1 Hinj1 Hres2 hinj2 Hgetl Hfind Hdef Hset Hlen.
       repeat subst_exp. 
       
       { edestruct Hcc with (env_loc1' := el)
           as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi)                 
         ; [| | | | eassumption |  | eassumption | eassumption | eassumption |  ].
         * eapply res_equiv_f_compose; [| eassumption ].
           rewrite compose_id_neut_r.
           rewrite res_equiv_eq.  split. reflexivity. eassumption. 
         * eapply injective_subdomain_compose. eassumption.
           eapply injective_subdomain_antimon. eassumption.
           rewrite (reach_unfold H1' (val_loc (Loc l1'))).
           eapply Included_Union_preserv_r.
           simpl. rewrite post_Singleton; eauto. simpl.
           rewrite Union_Empty_set_neut_l.
           rewrite (res_equiv_image_reach b1' id) with (v1 := Loc el);
           [| symmetry; eassumption ].
           rewrite image_id. reflexivity.
         * symmetry. eapply res_equiv_f_compose.
           symmetry. rewrite compose_id_neut_r.
           eassumption.
           symmetry. rewrite res_equiv_eq. split. reflexivity. eassumption.
         * eapply injective_subdomain_compose.
           eapply injective_subdomain_antimon. eassumption.
           rewrite (reach_unfold H2 [set (b' _)]).
           eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
           simpl. rewrite post_Singleton; eauto. simpl...
           rewrite (res_equiv_image_reach b2 id) with (v1 := Loc env_loc2) (v2 := Loc (b2 env_loc2)).
           simpl. 
           rewrite image_id. eassumption.
           rewrite res_equiv_eq. split. reflexivity. eassumption.
         * eassumption.
         * exists xs2, e2, rho2'. repeat (split; eauto). }
  Qed.
  

  (* Lemma cc_approx_val_heap_eq (k j : nat) (β β1 β2 : Inj) (δ : EInj) *)
  (*       (H1 H2 H1' H2' : heap block) *)
  (*       (v1 v2 : value) : *)
  (*   (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β ; δ) (Res (v2, H2)) -> *)
  (*   (val_loc v1) |- H1 ≃_(id, β1) H1' -> *)
  (*   injective_subdomain (reach' H1' (val_loc v1)) β1 -> *)
  (*   (val_loc v2) |- H2 ≃_(β2, id) H2' -> *)
  (*   injective_subdomain (reach' H2 (val_loc v2)) β2 -> *)
  (*   (Res (v1, H1')) ≺ ^ (k ; j ; GIP ; GP ; β2 ∘ β ∘ β1 ; lift β2 ∘ δ ∘ β1) (Res (v2, H2')). *)
  (* Proof with now eauto with Ensembles_DB. *)
  (*   intros. *)
  (*   eapply cc_approx_val_res_eq; try eassumption. *)
  (*   eapply heap_equiv_res_equiv; try eassumption. reflexivity. *)
  (*   eapply heap_equiv_res_equiv; try eassumption. reflexivity. *)
  (* Qed. *)

  Lemma cc_approx_var_env_heap_env_equiv (S1 S2 : Ensemble var) (k j : nat)
        (β β1 β2 : Inj)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 rho1' rho2' : env) (x1 x2 : var) :
    cc_approx_var_env k j GIP GP β H1 rho1 H2 rho2 x1 x2 ->
    S1 |- (H1, rho1) ⩪_(id, β1) (H1', rho1') ->
    injective_subdomain (reach' H1' (env_locs rho1' S1)) β1 -> 
    S2 |- (H2, rho2) ⩪_(β2, id) (H2', rho2') ->
    injective_subdomain (reach' H2 (env_locs rho2 S2)) β2 ->
    x1 \in S1 -> x2 \in S2 ->
    cc_approx_var_env k j GIP GP (β2 ∘ β ∘ β1)
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

  Lemma cc_approx_env_heap_env_equiv (S S1 S2 : Ensemble var) (k j : nat)
        (β1 β2 : Inj)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 rho1' rho2' : env) :
    (H1, rho1) ⋞ ^ (S; k; j; GIP; GP; b ) (H2, rho2) ->
    S1 |- (H1, rho1) ⩪_(id, β1) (H1', rho1') ->
    injective_subdomain (reach' H1' (env_locs rho1' S1)) β1 -> 
    S2 |- (H2, rho2) ⩪_(β2, id) (H2', rho2') ->
    injective_subdomain (reach' H2 (env_locs rho2 S2)) β2 ->
    S \subset S1 -> S \subset S2 ->
    (H1', rho1') ⋞ ^ (S; k; j; GIP; GP; (β2 ∘ b ∘ β1)) (H2', rho2').
  Proof.
    intros Henv Heq1 Hinj1 Heq2 Hinj2 Hin1 Hin2 v1' Hget1'.
    eapply cc_approx_var_env_heap_env_equiv; try eassumption;
    now eauto.
  Qed.

  
  (* Lemma cc_approx_heap_env_equiv (S : Ensemble var) (k j : nat) (β β1 β2 : Inj) *)
  (*       (δ : EInj) (H1 H2 H1' H2' : heap block)  : *)
  (*   S |- H1 ≼ ^ (k; j; GIP; GP; β ; δ) H2 -> *)
  (*   S |- H1 ≃_(id, β1) H1' -> *)
  (*   injective_subdomain (reach' H1' S) β1 ->  *)
  (*   image β S |- H2 ≃_(β2, id) H2' -> *)
  (*   injective_subdomain (reach' H2 (image β S)) β2 -> *)
  (*   S |- H1' ≼ ^ (k; j; GIP; GP; β2 ∘ β ∘ β1; (lift β2 ∘ δ ∘ β1)) H2'. *)
  (* Proof. *)
  (*   intros Henv [Heq1 Heq1'] Hinj1 [Heq2 Heq2'] Hinj2 x HS. *)
  (*   assert (Heqb : (β2 ∘ β ∘ β1) x = β x). *)
  (*   { specialize (Henv _ HS). *)
  (*     specialize (Heq1 _ HS). destruct Heq1 as [Heq1 _]. *)
  (*     assert (HS' : image β S (β x)). *)
  (*     { eexists; split; eauto. }  *)
  (*     specialize (Heq2 _ HS'). destruct Heq2 as [Heq2 _]. *)
  (*     unfold compose, id in *. rewrite <- Heq1, Heq2. *)
  (*     reflexivity. } *)
  (*   specialize (Henv _ HS). eapply cc_approx_val_heap_eq. *)
    
  (*   rewrite Heqb. eassumption. *)

  (*   eapply heap_equiv_antimon. split; eassumption. *)
  (*   eapply Singleton_Included. eassumption. *)

  (*   eapply injective_subdomain_antimon. eassumption. *)
  (*   eapply reach'_set_monotonic. eapply Singleton_Included. *)
  (*   eassumption. *)
    
  (*   rewrite Heqb.   *)
  (*   try eassumption. eapply heap_equiv_antimon. split; eassumption. *)
  (*   eapply Singleton_Included. now eexists; split; eauto. *)

  (*   rewrite Heqb.   *)
  (*   eapply injective_subdomain_antimon. eassumption. *)
  (*   eapply reach'_set_monotonic. eapply Singleton_Included. *)
  (*   now eexists; split; eauto. *)
  (* Qed. *)
    
  Lemma cc_approx_clos_heap_env_equiv (S : Ensemble var) (k j : nat) (β β1 β2 : Inj)
        (δ : EInj) (H1 H2 H1' H2' : heap block) l1 l1' l2 l2' :
    (l1, H1) << ^ (k; j; GIP; GP; β) (l2, H2) ->
    (Loc l1, H1) ≈_(id, β1) (Loc l1', H1') ->
    injective_subdomain (reach' H1' [set l1']) β1 ->
    
    (Loc l2, H2) ≈_(β2, id) (Loc l2', H2') ->
    injective_subdomain (reach' H2 [set l2]) β2 ->
    (l1', H1') << ^ (k; j; GIP; GP; β2 ∘ β ∘ β1) (l2', H2').
  Proof.
    intros Henv Heq1 Hin1 Heq2 Hinj2.
    edestruct Henv as (Hleq & rhoc & c & vs & FLS & Heq & Hnd & Hget1'' & Hget2'' & Hall); try eassumption.
    subst.
    rewrite res_equiv_eq in *. destruct Heq1 as [Heq1 Hres1].
    destruct Heq2 as [Heq2 Hres2]. unfold id in *. subst. 
    rewrite Hget2'' in Hres2. rewrite Hget1'' in Hres1. 
    destruct (get (β2 (β (β1 l1'))) H2') as [b2'|] eqn:Hgetb2'; try contradiction.
    destruct b2' as [c' vs'| | ]; try contradiction.
    
    destruct (get l1' H1') as [b1'|] eqn:Hgetb1'; try contradiction.
    destruct b1' as [c'' vs''| | ]; try contradiction.
    
    split. reflexivity.
    do 4 eexists. split. now rewrite heap_env_equiv_key_set in Heq; eauto.
    split. eassumption. split. eassumption.
    split. eassumption.
    
    eapply Forall2_vertical_strong with (R2 := fun x y => x = y); [| eassumption | | ].
    
    intros x y z w Hin1' Hin2' Hin3 Hin4 Hr1' Hr2' Hr3'. 
    destruct Hr1' as [l2 [Hgetl2 Hr1']]. simpl in Hr1'.
    rewrite cc_approx_val_eq in Hr1'.  subst.
    edestruct heap_env_equiv_env_get as [l2' [Hgetl2' Hres']].
    eassumption. eassumption. now constructor.
    destruct l2' as [l2' |]; try (rewrite res_equiv_eq in Hres'; contradiction).
    eexists. split. eassumption.
    rewrite cc_approx_val_eq. eapply cc_approx_val_res_eq.
    eassumption. eassumption.
    
    eapply injective_subdomain_antimon. eassumption. 
    rewrite (reach_unfold H1' (val_loc (Loc l1'))). eapply Included_Union_preserv_r.
    simpl post. rewrite post_Singleton; eauto.
    simpl. eapply reach'_set_monotonic. 
    eapply get_In_env_locs with (v := Loc l2'); try eassumption. now constructor.
    now eapply Hr3'.
    
    eapply injective_subdomain_antimon. eassumption.
    rewrite (reach_unfold H2 [set β (β1 l1')]). eapply Included_Union_preserv_r.
    rewrite post_Singleton; eauto. simpl.
    eapply reach'_set_monotonic. 
    eapply In_Union_list. eapply in_map. eassumption.
    
    eapply Forall2_refl; eauto.
    
    eapply block_equiv_Constr_r with (c2 := c'). eassumption.
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
      eexists. split; simpl; eauto. rewrite Hget. rewrite Heq. reflexivity.
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
  
  Lemma cc_approx_var_env_getlist_all (k : nat)
        (rho1 rho2 : env) (β : Inj) (H1 H2 : heap block)
        xs ys vs1 :
    Forall2 (fun x1 x2 =>
               forall j, cc_approx_var_env k j GIP GP β H1 rho1 H2 rho2 x1 x2
            ) xs ys ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist ys rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => forall j, (Res (v1, H1)) ≺ ^ (k; j; GIP ; GP ; β )
                                                   (Res (v2, H2)))
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

  Lemma cc_approx_env_P_getlist_l_all (S : Ensemble var) (k : nat)
        (rho1 rho2 : env)
        (H1 H2 : heap block) (xs : list var) (vs1 : list value) :
    (forall j, (H1, rho1) ⋞ ^ ( S ; k ; j ; GIP ; GP ; b) (H2, rho2)) ->
    (FromList xs) \subset S ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist xs rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => forall j,  (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; b) (Res (v2, H2)))
              vs1 vs2.
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
        destruct v; [| contradiction ]. 
        eapply cc_approx_val_loc_eq in Hyp2. subst. 
        assert (Hyp2 := Hyp2').
        eapply cc_approx_val_loc_eq in Hyp2. subst. 
        eassumption. 

        eassumption.
  Qed.

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
   

   Lemma cc_approx_val_heap_monotonic (k : nat) (H1 H2 H1' H2' : heap block)
       (v1 v2 : value):
      H1 ⊑ H1' -> H2 ⊑ H2' ->
     (forall j, Res (v1, H1) ≺ ^ (k ; j; GIP ; GP ; b) Res (v2, H2)) ->
     (forall j, Res (v1, H1') ≺ ^ (k ; j; GIP ; GP; b) Res (v2, H2')).
   Proof with (now eauto with Ensembles_DB).
     clear LIP LP.
     intros Hsub1 Hsub2 Hcc j.
     assert (Hwf1 := cc_approx_val_well_formed_reach1 _ _ _ _ _ Hcc). 
     assert (Hwf2 := cc_approx_val_well_formed_reach2 _ _ _ _ _ Hcc). 
     assert (Hin1 := cc_approx_val_dom1 _ _ _ _ _ _ (Hcc 1)).
     assert (Hin2 := cc_approx_val_dom2 _ _ _ _ _ _ (Hcc 1)).
     specialize (Hcc j).
     revert j v1 v2 Hwf1 Hwf2 Hin1 Hin2 Hcc. induction k as [k IHk] using lt_wf_rec1;
     induction j as [j IHj] using lt_wf_rec1.
     intros v1 v2  Hwf1 Hwf2 Hin1 Hin2 Hcc.
     
     destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
     try (now intros; contradiction); try (now simpl; eauto).
     simpl in Hcc. destruct Hcc as [Heq Hcc]; split; eauto.
     destruct (get l1 H1) as [b1|] eqn:Hget1; destruct (get l2 H2) as [b2|] eqn:Hget2;
     try contradiction; try (now destruct b1 as [c1 vs1 | [? | B1 f1 ] env_loc1 ]; contradiction).
     eapply Hsub1 in Hget1. eapply Hsub2 in Hget2. rewrite Hget1, Hget2.    
     destruct b1 as [c1 vs1 | [? | B1 f1 ] [ env_loc1 |] | ];
       destruct b2 as [c2 vs2 | | ]; try contradiction.  
     + subst.
       edestruct Hin1 as [b1 Hget1']. reflexivity.
       assert (Hget1'' := Hget1'). eapply Hsub1 in Hget1''.
       subst_exp.
       edestruct Hin2 as [b2 Hget2']. reflexivity.
       assert (Hget2'' := Hget2'). eapply Hsub2 in Hget2''.
       subst_exp. destruct Hcc as [Heq' Hall].
       split; eauto.
       intros i Hleq. simpl.
       eapply Forall2_monotonic_strong; [| eapply Hall; eassumption ].
       intros x1 x2 Hinx1 Hinx2 Hr.
       assert (Hr1 : val_loc x1 \subset post H1 (val_loc (Loc l1))).
       { simpl. rewrite post_Singleton; [| eassumption ].
         simpl. eapply In_Union_list.
         eapply in_map. eassumption. }
       assert (Hr2 : val_loc x2 \subset post H2 (val_loc (Loc (b l1)))).
       { simpl. rewrite post_Singleton; [| eassumption ].
         simpl. eapply In_Union_list.
         eapply in_map. eassumption. }
       rewrite cc_approx_val_eq. eapply IHj; try eassumption.
       * eapply well_formed_antimon; [| eassumption ].
         rewrite (reach_unfold _ (val_loc (Loc l1))).
         eapply Included_Union_preserv_r.
         eapply reach'_set_monotonic. eassumption.
       * eapply well_formed_antimon; [| eassumption ].
         rewrite (reach_unfold _ (val_loc (Loc (b l1)))).
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
       simpl. destruct Hcc as [Henv Hcc]. split; eauto.
       clear Hcc. intros i Hlt. 
       edestruct (Henv i Hlt) as (Heql & rhoc & c & vs
                                       & FVs & Heqfv & Hnd & Hget3 & Hgetl & Hall); try eassumption.
       
       split. eassumption.

       do 4 eexists. split. eassumption. split. eassumption.
       split. now erewrite <- Hsub1; eauto.
       split. now erewrite <- Hsub2; eauto.
       eapply Forall2_monotonic_strong; [| eapply Hall; eassumption ].
       intros x1 x2 Hinx1 Hinx2 [l1' [Hgetl1 Hr]].
       eexists; split; eauto.
       rewrite cc_approx_val_eq in *. 
       assert (Heqx : x2  = Loc (b l1')).
       { destruct x2; try contradiction. destruct Hr. subst. 
         reflexivity. }
       subst.
       assert (Hr1 : val_loc (Loc l1') \subset reach' H1 (val_loc (Loc l1))).
       { intros l Hin. inv Hin. simpl.
         eexists 2. split. now constructor. simpl. do 2 eexists. split.
         rewrite post_Singleton; eauto. simpl. now right. 
         split. eassumption. simpl. eapply get_In_env_locs.
         now constructor. eassumption. reflexivity. }
       assert (Hr2 : val_loc (Loc (b l1')) \subset reach' H2 (val_loc (Loc (b l1)))).
       { simpl. eapply Singleton_Included. simpl. rewrite reach_unfold. right.
         rewrite post_Singleton; eauto. simpl.
         eapply Included_post_reach'. 
         simpl. rewrite Union_Empty_set_neut_l, Union_Empty_set_neut_r, post_Singleton; eauto.
         simpl. eapply In_Union_list.
         eapply in_map with (f := val_loc). eassumption. reflexivity. }
       { eapply IHj; try eassumption.
         * eapply well_formed_antimon; [| eassumption ].
           rewrite (reach'_idempotent _ (val_loc (Loc l1))).
           eapply reach'_set_monotonic. eassumption.
         * eapply well_formed_antimon; [| eassumption ].
           rewrite (reach'_idempotent _ (val_loc (Loc (b l1)))).
           eapply reach'_set_monotonic. eassumption.
         * eapply Included_trans; [| eapply reachable_in_dom ]; try eassumption.
         * eapply Included_trans; [| eapply reachable_in_dom ]; try eassumption. }
       
         
       intros b1 b2 el tc1 tc2 tc3  H3 H3' H4' env_loc xs1 ft e1 vs1 vs2
              Heq1 Hinj1 Heq2 Hinj2 Hget Hfind Hdef Hset Hlen. 
       edestruct Hcc
         as (xs2 & e2 & rho2' & Hget' & Hfind' & Hset').
       * eapply Equivalence_Transitive; [| now apply Heq1 ].
         eapply subheap_res_equiv; try eassumption.
         eapply Included_trans; [| now eapply Included_post_reach' ].
         edestruct Hin2 as [b2' Hget2'']. reflexivity.
         eexists. eexists.  split; [| split; [ eassumption |]].
         reflexivity. eapply Hsub2 in Hget2''. subst_exp.
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
       * eassumption. 
       * do 3 eexists; split; [ | split ]; try (now eauto).
     + destruct b1; try contradiction.
       destruct v; try contradiction.
       destruct v0; try contradiction.
   Qed.

   Lemma cc_approx_var_env_heap_monotonic (k : nat) (H1 H2 H1' H2' : heap block)
       (rho1 rho2 : env) x y:
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     (forall j, cc_approx_var_env k j GIP GP b H1 rho1 H2 rho2 x y) ->
     (forall j, cc_approx_var_env k j GIP GP b H1' rho1 H2' rho2 x y).
   Proof.
     intros Hs1 Hs2 Hres j v Hget.
     edestruct (Hres j) as [l2 [Hget2 Hres2]]; eauto.
     eexists; split; eauto.
     eapply cc_approx_val_heap_monotonic; try eassumption.
     intros j'.
     edestruct (Hres j') as [l2' [Hget2' Hres2']]; eauto.
     repeat subst_exp.
     eassumption.
   Qed.
   
   Lemma cc_approx_env_heap_monotonic S (k : nat)
         (H1 H2 H1' H2' : heap block)
       (rho1 rho2 : env):
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     (forall j, (H1, rho1) ⋞ ^ (S ; k ; j; GIP ; GP ; b) (H2, rho2)) ->
     (forall j, (H1', rho1) ⋞ ^ (S ; k ; j; GIP ; GP; b) (H2', rho2)).
   Proof.
     intros Hs1 Hs2 Hres j x Hin.
     eapply cc_approx_var_env_heap_monotonic; try eassumption.
     intros j'. eapply Hres. eassumption.
   Qed.
  
  Lemma cc_approx_clos_heap_monotonic (k : nat)
        (H1 H2 H1' H2' : heap block) l1 l2 :
    H1 ⊑ H1' -> H2 ⊑ H2' ->
    (forall j, (l1, H1) << ^ (k; j; GIP; GP; b) (l2, H2)) ->
    (forall j, (l1, H1') << ^ (k; j; GIP; GP; b) (l2, H2')).
  Proof.
    intros Hs1 Hs2 Henv j.
    edestruct (Henv 0) as (el & rhoc & c & vs & FLS & Heq & Hnd & Hget & Hegt' & Hall); try eassumption.
    split. eassumption. do 4 eexists. split.
    eassumption. split. eassumption. split. erewrite <- Hs1. reflexivity.
    eassumption. split. 
    erewrite <- Hs2. reflexivity. eassumption.

    eapply Forall2_monotonic_strong; [| eapply Hall; eassumption ].

    intros x1 x2 Hin1 Hin2 [l3 [Hgetl3 Hcc]]. 
    eexists. split. eassumption.
    rewrite cc_approx_val_eq in *. 
    eapply cc_approx_val_heap_monotonic; try eassumption.
    intros j'.
    edestruct (Henv j') as (el' & rhoc' & c' & vs' & FLS' & Heq' & Hnd' & Hget' & Hegt'' & Hall');
      try eassumption.
    repeat subst_exp.
    eapply Heq in Hin1. eapply Heq' in Hin1.
    edestruct (Forall2_exists _ FLS' vs' x1 Hin1 Hall')  as [x' [Hin2' [l1' [Hgetl1' Hres']]]].
    repeat subst_exp. rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_loc_eq in Hcc. subst.
    assert (Hr := Hres').
    eapply cc_approx_val_loc_eq in Hr. subst.

    eassumption.
  Qed. 

  (* Lemma cc_approx_heap_heap_monotonic (S : Ensemble loc) (k : nat) *)
  (*       (H1 H2 H1' H2' : heap block)  : *)
  (*   H1 ⊑ H1' -> H2 ⊑ H2' -> *)
  (*   (forall j, S |- H1 ≼ ^ (k; j; GIP; GP; b ) H2) -> *)
  (*   (forall j, S |- H1' ≼ ^ (k; j; GIP; GP; b ) H2'). *)
  (* Proof. *)
  (*   intros Hs1 Hs2 Hres j x HS. eapply (Hres j) in Hin. inv Hin.  *)
  (*   eapply cc_approx_val_heap_monotonic; try eassumption. *)
  (*   intros j'. eapply Hres. eassumption. *)
  (* Qed.  *)

   
  Lemma cc_approx_env_set_alloc_Constr S (k j : nat)
        c vs1 vs2 l1 l2  (H1 H2 H1' H2' : heap block)
        (rho1 rho2 : env) x:

    (forall j, (H1, rho1) ⋞ ^ (S \\ [set x]; k; j; GIP; GP; b) (H2, rho2)) ->
     
     alloc (Constr c vs1) H1 = (l1, H1') ->
     alloc (Constr c vs2) H2 = (l2, H2') ->  

     b l1 = l2 ->
     (forall j, Forall2 (fun v1 v2 => Res (v1, H1) ≺ ^ (k; j; GIP; GP; b) Res (v2, H2)) vs1 vs2) ->
     
     (H1', M.set x (Loc l1) rho1) ⋞ ^ (S; k; j; GIP; GP; b) (H2', M.set x (Loc l2) rho2).
   Proof with (now eauto with Ensembles_DB).
     intros Henv Ha1 Ha2 Hb Hres. assert (Hres' := Hres). 
     eapply cc_approx_env_P_set; try eassumption.
     eapply cc_approx_env_heap_monotonic; try eassumption.
     eapply HL.alloc_subheap; eassumption.
     eapply HL.alloc_subheap; eassumption.
     simpl. erewrite !gas; eauto.
     split. eassumption.
     simpl. split; eauto. intros i Hlt.
     specialize (Hres i).
     eapply Forall2_monotonic_strong; [| eassumption ].
     intros x1 x2 Hin1 Hin2 Heq.
     rewrite cc_approx_val_eq.
     eapply cc_approx_val_heap_monotonic; try eassumption.

     eapply HL.alloc_subheap; eassumption.
     eapply HL.alloc_subheap; eassumption.

     intros j'.
     specialize (Hres' j').
     edestruct (Forall2_exists _ vs1 vs2 x1 Hin1 Hres')  as [x' [Hinx2 Hr']].
     repeat subst_exp.
     destruct x1; try contradiction.
     apply cc_approx_val_loc_eq in Heq. subst.
     assert (Hr := Hr').
     eapply cc_approx_val_loc_eq in Hr. subst.
     eassumption.
   Qed.

   Lemma cc_approx_val_rename_ext  β β' k j H1 H2 v1 v2:
     (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β' ) (Res (v2, H2)) ->
     f_eq_subdomain (reach' H1 (val_loc v1)) β β' ->
     (Res (v1, H1)) ≺ ^ (k ; j ; GIP ; GP ; β ) (Res (v2, H2)).
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
    destruct b1' as [c1 vs1 | [? | B1 f1] [ env_loc1 |] | ]; try contradiction;
    destruct b2' as [c2 vs2 | | ]; try contradiction. 
    + simpl in Hbeq'. destruct Hbeq' as [ceq Hi]. split; eauto. subst.
      subst. intros i Hlt. simpl.
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
      destruct Hbeq' as [Henv Hcc].
      simpl. split.

      intros i Hlt.
      edestruct (Henv i Hlt) as (el & rhoc & c & vs & FVs & Heqfv & Hnd & Hget & Hget' & Hall); try eassumption.
      split; eauto. rewrite Hfeq. eassumption.
      eapply Included_post_reach'. simpl. rewrite post_Singleton; eauto. simpl...
      do 4 eexists. split. eassumption. split. eassumption. split. eassumption.
      split. eassumption. 
      eapply Forall2_monotonic_strong; [| eapply Hall; eassumption ].
      intros x1 x2 Hinx1 Hinx2 [l1' [Hgetx Hr]].
      assert (Hr1 : val_loc (Loc l1') \subset reach' H1 (val_loc (Loc l1))).
      { intros l Hin. inv Hin. simpl. eexists 2. split. constructor.
        simpl. do 2 eexists. split.
        rewrite post_Singleton; eauto. simpl. right. reflexivity.
        split; eauto. eapply get_In_env_locs. now constructor.
        eassumption. reflexivity. }
      { eexists; split; eauto.
        rewrite cc_approx_val_eq in *.
        eapply IHj; try eassumption.
         * eapply f_eq_subdomain_antimon; [| eassumption ].
           rewrite (reach'_idempotent _ (val_loc (Loc l1))).
           eapply reach'_set_monotonic. eassumption. }

       intros b1' b2' el tc1 tc2 tc3 H3 H3' H4' env_loc' xs1 ft
       e1 vs1 vs2 Hres1 Hinj1 Hres2 hinj2 Hget Hfind Hdef Hset Hlen.
       edestruct Hcc as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi)
       ; [| |  | | | eassumption | eassumption | eassumption | eassumption | ];
       try eassumption.
       exists xs2, e2, rho2'. split; [| split ]; eauto. intros. 
       eapply Hi; try eassumption. 
       eapply Equivalence_Transitive; [| eassumption ].
       eapply f_eq_subdomain_compose_compat. reflexivity.
       eapply f_eq_subdomain_compose_compat; [| reflexivity ].
       eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].

       eapply Included_trans. eapply image_monotonic with (S' := (reach' H3 (val_loc (Loc el)))).
       reflexivity.
       rewrite res_equiv_image_reach; [| symmetry; eassumption ].
       rewrite image_id.
       rewrite (reach_unfold H1 (val_loc (Loc l1))). eapply Included_Union_preserv_r.
       simpl. rewrite post_Singleton; eauto. simpl.
       eapply reach'_set_monotonic...
    + destruct Hres as [Hres1 Hres2]. destruct b1'; try contradiction.
      destruct v; destruct v0; contradiction. 
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
    intros Henv Heq Heq' x Hin.
    eapply cc_approx_var_env_rename_ext. now eauto.
    eapply f_eq_subdomain_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply env_locs_monotonic.
    eapply Singleton_Included. eassumption.
  Qed.

  (* Lemma cc_approx_heap_rename_ext (S : Ensemble loc) (k j : nat) (β β' : Inj) *)
  (*       (H1 H2 : heap block)  : *)
  (*    S |- H1 ≼ ^ (k; j; GIP; GP; β ) H2 -> *)
  (*    f_eq_subdomain (reach' H1 S) β β' -> *)
  (*    S |- H1 ≼ ^ (k; j; GIP; GP; β' ) H2. *)
  (* Proof. *)
  (*   intros Hres Hfeq1 x HS. *)
  (*   eapply cc_approx_val_rename_ext; eauto. *)
    
  (*   rewrite <- Hfeq1. now eauto. *)
  (*   eapply reach'_extensive. eassumption. *)

  (*   symmetry; eapply f_eq_subdomain_antimon; [| eassumption ]. *)
  (*   eapply reach'_set_monotonic. *)
  (*   eapply Singleton_Included. eassumption. *)
  (* Qed.  *)
    
  Lemma cc_approx_clos_rename_ext (S : Ensemble var) (k j : nat) (β β': Inj)
        (H1 H2 : heap block) l1 l2 :
    (l1, H1) << ^ (k; j; GIP; GP; β) (l2, H2) ->
    f_eq_subdomain (reach' H1 [set l1]) β β' ->
    (l1, H1) << ^ (k; j; GIP; GP; β') (l2, H2).
  Proof.
    intros Henv Hfeq1.
    edestruct Henv as (Heql & rhoc & c & vs & FLS & Heq & Hnd & Hget & Hget' & Hall); try eassumption.
    split. rewrite <- Hfeq1. eassumption. now eapply reach'_extensive.
    do 4 eexists. split. eassumption.
    split. eassumption. 
    split. eassumption.
    split. eassumption.
    
    eapply Forall2_monotonic_strong; [| eapply Hall; eassumption ].
    intros x1 x2 Hinx1 Hinx2 [l1' [Hgetl1 Hr]].
    eexists; split; eauto.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_rename_ext; try eassumption.
    * eapply f_eq_subdomain_antimon; [| symmetry; eassumption ].
      rewrite (reach'_idempotent _ [set l1]).
      eapply reach'_set_monotonic. eapply Singleton_Included.
      eapply Included_post_reach'. rewrite post_Singleton; eauto.
      simpl. eexists; split; eauto. now constructor. rewrite Hgetl1.
      reflexivity.
  Qed.

  End LogRelLemmas.

    (** * Proper Instances *)

  
  Global Instance cc_approx_env_proper_set :
    Proper (Same_set var ==> Logic.eq ==>  Logic.eq ==> Logic.eq ==> Logic.eq ==>
            Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           cc_approx_env_P.
  Proof.
    intros s1 s2 [H1 H2]; split; intros Hpre;
    subst; eapply cc_approx_env_P_antimon; subst; eauto. 
  Qed.

  Global Instance Proper_cc_approx_heap :
    Proper (Same_set _ ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
           cc_approx_heap.
  Proof.
    intros s1 s2 Hseq; constructor; subst;
    intros Hcc z Hin; eapply Hcc; eapply Hseq; eauto.
  Qed.



  Lemma def_closures_cc_approx_env Scope k GIP GP b B1 B2 envc rho1 H1 rho1' H1' rho2 H2 :
    (forall j, (H1, rho1) ⋞ ^ (Scope; k; j; GIP; GP; b) (H2, rho2)) ->
    def_closures B1 B2 rho1 H1 envc = (H1', rho1') ->
    (forall j, (H1', rho1') ⋞ ^ (Scope \\ name_in_fundefs B1; k; j; GIP; GP; b) (H2, rho2)).
  Proof with (now eauto with Ensembles_DB).
    revert H1 rho1 H1' rho1'.
    induction B1; intros H1 rho1 H1' rho1' Hcc Hdef j.
    - simpl in Hdef.
      destruct (def_closures B1 B2 rho1 H1) as (H1'', rho1'') eqn:Hdef'.
      destruct (alloc (Clos _ _) H1'') as [la H1a] eqn:Hal.
      inv Hdef. 
      eapply cc_approx_env_P_set_not_in_P_l.
      assert (Hdef := Hdef').
      + eapply cc_approx_env_P_antimon. 
        eapply cc_approx_env_heap_monotonic; [ | | eapply IHB1 ].
        * eapply HL.alloc_subheap. eassumption.
        * eapply HL.subheap_refl.
        * eassumption.
        * eassumption.
        * now eauto with Ensembles_DB.
      + intros Hc; inv Hc. eapply H0; now left.
    - rewrite Setminus_Empty_set_neut_r.
      inv Hdef. now eauto.
  Qed.


  Lemma def_funs_cc_approx_env Scope k j GIP GP b B1 B2 rho1 H1 rho2 H2 :
    (H1, rho1) ⋞ ^ (Scope; k; j; GIP; GP; b) (H2, rho2) ->
    (H1, rho1) ⋞ ^ (Scope \\ name_in_fundefs B1; k; j; GIP; GP; b) (H2, def_funs B1 B2 rho2).
  Proof with (now eauto with Ensembles_DB).
    induction B1; intros Hcc.
    - simpl def_funs.
      eapply cc_approx_env_P_set_not_in_P_r.
      eapply cc_approx_env_P_antimon.
      eapply IHB1. eassumption.
      now eauto with Ensembles_DB.
      intros Hc; inv Hc. eapply H0; now left.
    - simpl name_in_fundefs.
      rewrite Setminus_Empty_set_neut_r. eassumption.
  Qed.

End CC_log_rel.
