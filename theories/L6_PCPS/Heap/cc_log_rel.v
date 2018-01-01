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
  Definition GIInv := relation (heap block * env * exp).

  (** * Final conditions *)
  
  (** Local final conditions. Holds for the result of the execution of the expressions being related. *)
  Definition Inv := relation (nat * nat).

  (** Global final conditions. Holds for the result of future execution of the result *)
  Definition GInv := relation (nat * nat).
  
  
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
    
    Variable (cc_approx_val : nat -> IInv -> GInv -> ans -> ans -> Prop). 
    
    (** * Expression relation *)
    
    Definition cc_approx_exp (k : nat) (IIL : IInv) (IIG : GIInv) (IL : Inv) (IG : GInv)
               (p1 p2 : exp * env * heap block) : Prop :=
      let '(e1, rho1, H1) := p1 in
      let '(e2, rho2, H2) := p2 in
      forall (H1' H2' : heap block) (rho1' rho2' : env) (r1 : ans) (c1 m1 : nat),
        (occurs_free e1) |- (H1, rho1) ⩪ (H1', rho1') ->
        (occurs_free e2) |- (H2, rho2) ⩪ (H2', rho2') ->
        IIL (H1', rho1', e1) (H2', rho2', e2) ->
        c1 <= k ->
        big_step_GC H1' rho1' e1 r1 c1 m1 ->
        not_stuck H1' rho1' e1 ->
        exists (r2 : ans) (c2 m2 : nat),
          big_step_GC_cc H2' rho2' e2 r2 c2 m2 /\
          (* extra invariants for costs *)
          IL (c1, m1) (c2, m2) /\
          cc_approx_val (k - c1) IIG IG r1 r2.
    
  End cc_approx.
  
  (** * Value relation *)
  
  Fixpoint cc_approx_val (k : nat) (IP : IInv) (P : GInv) (r1 r2 : ans) {struct k} : Prop :=
    match r1, r2 with
      | OOT, OOT => True (* Both programs timeout *)
      | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
        match v1, v2 with
          | Loc l1, Loc l2 =>
            match get l1 H1, get l2 H2 with
              | Some (Constr c1 vs1), Some (Constr c2 vs2) =>
                    c1 = c2 /\
                    (forall i,
                       (i < k)%nat ->
                       match k with
                         | 0 => True
                         | S k =>
                           let R l1 l2 := cc_approx_val (k - (k - i)) IP P (Res (l1, H1)) (Res (l2, H2)) in
                           Forall2 R vs1 vs2
                       end)
              | Some (Clos (FunPtr B1 f1) (Loc env_loc1)), Some (Constr c [FunPtr B2 f2; Loc env_loc2]) =>
                forall (rho_clo1 rho_clo2 rho_clo3 : env) (H1' H1'' H2' : heap block) (env_loc1' env_loc2' : loc)
                  (xs1 : list var) (ft : fTag) (e1 : exp) (vs1 vs2 : list value),
                  (Loc env_loc1, H1) ≈ (Loc env_loc1', H1') ->
                  (Loc env_loc2, H2) ≈ (Loc env_loc2', H2') ->

                  get env_loc1' H1' = Some (Env rho_clo1) ->
                  find_def f1 B1 = Some (ft, xs1, e1) ->

                  def_closures B1 B1 rho_clo1 H1' env_loc1' =  (H1'', rho_clo2) ->
                  setlist xs1 vs1 rho_clo2 = Some rho_clo3 ->

                  exists (xs2 : list var) (e2 : exp) (rho2' : env),
                    find_def f2 B2 = Some (ft, xs2, e2) /\
                    Some rho2' = setlist xs2 ((Loc env_loc2') :: vs2) (def_funs B2 B2 (M.empty _)) /\
                    (forall i,
                       (i < k)%nat ->
                       match k with
                         | 0 => True
                         | S k =>
                           let R v1 v2 := cc_approx_val (k - (k - i)) IP P (Res (v1, H1'')) (Res (v2, H2')) in
                           Forall2 R vs1 vs2 ->
                           cc_approx_exp cc_approx_val
                                         (k - (k - i))
                                         IP IP P P 
                                         (e1, rho_clo3, H1'') (e2, rho2', H2')
                       end)
              | _, _ => False
            end
          | _, _ => False
        end
      | _, _ => False
    end.
  
  
  (** Notations for approximation relation *)
  Notation "p1 ⪯ ^ ( k ; P1 ; P2 ; P3 ; P4 ) p2" :=
    (cc_approx_exp cc_approx_val k P1 P2 P3 P4 p1 p2)
      (at level 70, no associativity).
  
  Definition cc_approx_block (k : nat) (IP : IInv) (P : GInv) (b1 : block) (H1 : heap block)
             (b2 : block) (H2 : heap block) : Prop :=

    match b1, b2 with
      | Constr c1 vs1, Constr c2 vs2 =>
        c1 = c2 /\
        (forall i,
           (i < k)%nat ->
           let R l1 l2 := cc_approx_val i IP P (Res (l1, H1)) (Res (l2, H2)) in
           Forall2 R vs1 vs2)
      | Clos (FunPtr B1 f1) (Loc env_loc1), Constr c [FunPtr B2 f2; Loc env_loc2] =>
        forall (rho_clo1 rho_clo2 rho_clo3 : env) (H1' H1'' H2' : heap block) (env_loc1' env_loc2' : loc)
          (xs1 : list var) (ft : fTag) (e1 : exp) (vs1 vs2 : list value),
          (Loc env_loc1, H1) ≈ (Loc env_loc1', H1') ->
          (Loc env_loc2, H2) ≈ (Loc env_loc2', H2') ->
          
          get env_loc1' H1' = Some (Env rho_clo1) ->
          find_def f1 B1 = Some (ft, xs1, e1) ->
          
          def_closures B1 B1 rho_clo1 H1' env_loc1' =  (H1'', rho_clo2) ->
          setlist xs1 vs1 rho_clo2 = Some rho_clo3 ->
          
          exists (xs2 : list var) (e2 : exp) (rho2' : env),
            find_def f2 B2 = Some (ft, xs2, e2) /\
            Some rho2' = setlist xs2 ((Loc env_loc2') :: vs2) (def_funs B2 B2 (M.empty _)) /\
            (forall i,
               (i < k)%nat ->
               let R v1 v2 := cc_approx_val i IP P (Res (v1, H1'')) (Res (v2, H2')) in
               (* env_locs rho_clo3 (occurs_free e1) |- H1' ≃ H1'' -> *)
               (* env_locs rho2' (occurs_free e2) |- H2 ≃ H2' -> *)
               Forall2 R vs1 vs2 ->
               cc_approx_exp cc_approx_val
                             i
                             IP IP P P 
                             (e1, rho_clo3, H1'') (e2, rho2', H2'))
      | _, _ => False
    end.
  
  (** Unfold the recursion. A more compact definition of the value relation. *)
  Definition cc_approx_val' (k : nat) (IP : IInv) (P : GInv) (r1 r2 : ans) : Prop :=
    match r1, r2 with
      | OOT, OOT => True (* Both programs timeout *)
      | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
        match v1, v2 with
          | Loc l1, Loc l2 =>
            match get l1 H1, get l2 H2 with
              | Some b1, Some b2 => cc_approx_block k IP P b1 H1 b2 H2
              | _, _ => False
            end
          | _, _ => False
        end
      | _, _ => False
    end.
  
  (** Correspondence of the two definitions *)
  Lemma cc_approx_val_eq (k : nat) IP P (v1 v2 : ans) :
    cc_approx_val k IP P v1 v2 <-> cc_approx_val' k IP P v1 v2.
  Proof.
    destruct k as [ | k ];
    destruct v1 as [[[l1 | lf1 f1] H1] | |]; destruct v2 as [[[l2 | lf2 f2] H2] | |];
    try (now split; intros; contradiction);
    try (now simpl; eauto). 
    - split; simpl; unfold cc_approx_block;
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + now firstorder.
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros Hyp tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset. 
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & _); eauto.
          do 3 eexists; split; [ | split ]; try now eauto. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; eauto. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + now firstorder.
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros Hyp tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset. 
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & _); eauto.
          do 3 eexists; split; [ | split ]; now eauto. }
      { contradiction. }
    - split; unfold cc_approx_block; simpl;
      destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + intros [Heq Hi]; split; [ eassumption |].
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : k - (k - i) = i) by omega. rewrite !Heqi in Hap.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros Hyp tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          simpl. intros i Hleq Hall.
          assert (Heqi : k - (k - i) = i) by omega.
          setoid_rewrite <- Heqi. eapply Hi; eauto.
          eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap. rewrite Heqi. eassumption. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; eauto. }
      { destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
        + intros [Heq Hi]; split; [ eassumption |].
          intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap.
          assert (Heqi : k - (k - i) = i) by omega. rewrite !Heqi.
          eassumption. 
        + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
          intros Hyp tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset.
          edestruct Hyp
            as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
          do 3 eexists; split; [ | split ]; try (now eauto).
          intros i Hleq Hall.
          assert (Heqi : k - (k - i) = i) by omega.
          setoid_rewrite Heqi. eapply Hi; eauto.
          eapply Forall2_monotonic; [| now eauto ].
          intros x1 x2 Hap. rewrite <- Heqi. eassumption. }
      { contradiction. }
  Qed.
  
  Opaque cc_approx_val.
  
  (** * Environment relations *)
  
  (** Environment relation for a single point (i.e. variable) : 
   * ρ1 ~_k^x ρ2 iff ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition cc_approx_var_env (k : nat) IP P (H1 : heap block) (rho1 : env)
             (H2 : heap block) (rho2 : env) (x y : var) : Prop :=
    forall l1, 
      M.get x rho1 = Some l1 -> 
      exists l2, M.get y rho2 = Some l2 /\
            cc_approx_val' k IP P (Res (l1, H1)) (Res (l2, H2)).
  
  (** Environment relation for a set of points (i.e. predicate over variables) :
    * ρ1 ~_k^S ρ2 iff 
    *  forall x, S x -> ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition cc_approx_env_P (S : Ensemble var) k IP P (c1 c2 : heap block * env) :=
    let (H1, rho1) := c1 in
    let (H2, rho2) := c2 in
    forall (x : var), S x -> cc_approx_var_env k IP P H1 rho1 H2 rho2 x x.
  
  Notation "p1 ≺ ^ ( k ; IP ; P ) p2" := (cc_approx_val' k IP P p1 p2)
                                      (at level 70, no associativity).

  Notation "p1 ⋞ ^ ( R ; k ; IP ; P ) p2" := (cc_approx_env_P R k IP P p1 p2)
                                          (at level 70, no associativity).
  
  
  (** Environment relation for the whole domain of definition :
    * ρ1 ~_k ρ2 iff forall x, ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
  Definition cc_approx_env (k : nat) IP P c1 c2 : Prop :=
    c1 ⋞ ^ (Full_set _; k; IP;  P) c2.
  
  (** * Environment Invariants for Closure Conversion *)
  
  (** Naming conventions in the following :

     [Scope] : The set of variables currently in scope.
 
     [Funs]  : The set of variables in the current block of mutually recursive
               functions.

     [FVs]   : The list of free variables (needs to be ordered).

     [Γ]     : The formal parameter of the environment after closure conversion. *)
  
  (** Invariant about the free variables *) 
  Definition FV_inv (k : nat) (IP : IInv) (P : GInv)
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
        (Res (v, H1)) ≺ ^ ( k ; IP ; P ) (Res (v', H2)).
  
  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv (k : nat) (IP : IInv) (P : GInv)
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
          (Res (vf1, H1)) ≺ ^ ( k ; IP ; P ) (Res (Loc l_clo, H2)).
  
  Section LogRelLemmas.
    
    Context (LIP : IInv)
            (GIP : IInv)
            (LP : Inv)
            (GP : GInv).
    
  (** * Monotonicity Properties *)

  (** The environment relation is antimonotonic in the set of free variables *) 
  Lemma cc_approx_env_P_antimon (S1 S2 : Ensemble var) (k : nat)
        (c1 c2 : (heap block) * env) :
    c1 ⋞ ^ ( S2 ; k ; GIP ; GP) c2 ->
    S1 \subset S2 ->
    c1 ⋞ ^ ( S1 ; k ; GIP ; GP) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre Hin x Hin'. eapply Hpre; eapply Hin; eauto.
  Qed.
  
  (** The expression relation is monotonic in the local invariant *)
  Lemma cc_approx_exp_rel_mon k LIP1 GIP1 (LP1 LP2 : Inv) (GP1 : GInv)
        (p1 p2 : exp * env * heap block) :
    p1 ⪯ ^ ( k ; LIP1 ; GIP1 ; LP1 ; GP1 ) p2 ->
    inclusion _ LP1 LP2 ->
    p1 ⪯ ^ ( k ; LIP1 ; GIP1 ; LP2 ; GP1 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2].
    intros Hcc Hin H1' H2' rho1' rho2' v1 c1 m1 HH1 HH2 Hip Hleq Hstep Hstuck.
    edestruct Hcc as [v2 [c2 [m2 [Hstep' [HInv Hval]]]]]; eauto.
    repeat eexists; eauto.
  Qed.
  
  (** The logical relation respects equivalence of the global invariant *)
  
  Lemma cc_approx_exp_same_rel_IH k LIP1 GIP1 LP1 (GP1 GP2 : GInv) p1 p2 :
    (forall m r1 r2,
       m <= k ->
       r1 ≺ ^ (m ; GIP1 ; GP1) r2 ->
       r1 ≺ ^ (m ; GIP1 ; GP2) r2) ->
    p1 ⪯ ^ ( k ; LIP1 ; GIP1 ; LP1 ; GP1 ) p2 ->
    same_relation _ GP1 GP2 ->
    p1 ⪯ ^ ( k ; LIP1 ; GIP1 ; LP1 ; GP2 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2].
    intros IH Hcc Hin H1' H2' rho1' rho2' v1 c1 m1 HH1 HH2 Hip Hleq Hstep Hstuck.
    edestruct Hcc as [v2 [c2 [m2 [Hstep2 [HP Hval]]]]]; eauto.
    repeat eexists; eauto.
    rewrite cc_approx_val_eq.
    eapply IH; eauto. omega.
    rewrite <- cc_approx_val_eq; eauto.    
  Qed.
  
  Opaque cc_approx_exp.
  
  Lemma cc_approx_val_same_rel (k : nat) (GP1 GP2 : GInv) r1 r2 :
    r1 ≺ ^ (k ; GIP ; GP1) r2 ->
    same_relation _ GP1 GP2 ->
    r1 ≺ ^ (k ; GIP ; GP2) r2.
  Proof.
    revert GP1 GP2 r1 r2. induction k as [k IHk] using lt_wf_rec1.
    intros GP1 GP2 r1 r2.
    destruct k as [ | k ];
    destruct r1 as [[[l1 | lf1 f1] H1] | |]; destruct r2 as [[[l2 | lf2 f2] H2] | |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    - destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
      destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
      + intros [Heq Hi] HR; split; [ eassumption |].
        intros i Hleq. omega.
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        intros Hyp HR tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset.
        edestruct Hyp
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
    - destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
      destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
      + intros [Heq Hi] HR; split; [ eassumption |].
        intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHk; try eassumption.
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        intros Hyp HR tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset.
        edestruct Hyp
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        simpl. intros i Hleq Hall.
        eapply cc_approx_exp_same_rel_IH with (GP1 := GP1); try eassumption.
        * intros; eapply IHk. omega. eassumption. eassumption.
        * destruct HR as [Hi1 Hi2]. 
          eapply cc_approx_exp_rel_mon; [| eassumption ]. eapply Hi; eauto.
          eapply Forall2_monotonic; [| eassumption ].
          intros. rewrite cc_approx_val_eq.
          eapply IHk; eauto. now rewrite <- cc_approx_val_eq; simpl in *; eauto.
          split; eassumption.
  Qed.
  
  Transparent cc_approx_exp.

  Lemma cc_approx_exp_same_rel (P : relation nat) k (GP' : GInv)
        p1 p2 :
    p1 ⪯ ^ ( k ; LIP ; GIP ; LP ; GP ) p2 ->
    same_relation _ GP GP' ->
    p1 ⪯ ^ ( k ; LIP ; GIP ; LP ; GP' ) p2.
  Proof.
    intros Hcc Hin. eapply cc_approx_exp_same_rel_IH; try eassumption.
    intros. eapply cc_approx_val_same_rel; eauto.
  Qed.
  
  (** The value relation is monotonic in the step index *)
  Lemma cc_approx_val_monotonic (k m : nat) (r1 r2 : ans) :
    r1 ≺ ^ (k; GIP ; GP) r2 ->
    m <= k ->
    r1 ≺ ^ (m; GIP ; GP) r2.
  Proof.
    revert k r1 r2. induction m as [m IHk] using lt_wf_rec1.
    intros k r1 r2.
    destruct m as [ | m ];
    destruct r1 as [[[l1 | lf1 f1] H1] | |]; destruct r2 as [[[l2 | lf2 f2] H2] | |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    - destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
      destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
      + intros [Heq Hi] Hleq; split; [ eassumption |].
        intros i Hleq'. omega.
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        intros Hyp HR tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset. 
        edestruct Hyp
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
    - destruct (get l1 H1) as [b1|]; destruct (get l2 H2) as [b2|]; eauto.
      destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
        destruct b2 as [c2 vs2 | | ]; eauto.
      + intros [Heq Hi] HR; split; [ eassumption |].
        intros i Hleq. eapply Forall2_monotonic; [| now eauto ].
        intros x1 x2 Hap.
        rewrite cc_approx_val_eq in *. eapply IHk; try eassumption.
        omega. 
      + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
        intros Hyp HR tc1 tc2 tc3 H1' H1'' H2' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset. 
        edestruct Hyp
          as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
        do 3 eexists; split; [ | split ]; try (now eauto).
        intros i Hleq Hall.
        eapply Hi; try eassumption. omega.
  Qed.
  
  (** The expression relation is anti-monotonic in the step index *)
  Lemma cc_approx_exp_monotonic (k j : nat) p1 p2 :
    p1 ⪯ ^ ( k ; LIP ; GIP ; LP ; GP ) p2 ->
    j <= k ->
    p1 ⪯ ^ ( j ; LIP ; GIP ; LP ; GP ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1]; destruct p2 as [[e2 H2] rho2].
    intros Hpre Hleq H1' H2' rho1' rho2' v1 c1 m1 HH1 HH2 HIP Hleq' Hstep Hstuck.
    edestruct (Hpre H1' H2' rho1' rho2' v1 c1)
      as [v2 [c2 [m2 [Hstep2 [Hleq2 H3]]]]]; eauto.
    omega. do 3 eexists; repeat split; eauto.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_monotonic; eauto. omega.
  Qed.
  
  
  (** The environment relations are anti-monotonic in the step index *)
  Lemma cc_approx_env_P_monotonic (R : Ensemble var) (k j : nat)
        c1 c2 :
    c1 ⋞ ^ ( R ; k ; GIP ; GP ) c2 ->
    j <= k ->
    c1 ⋞ ^ ( R ; j ; GIP ; GP ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hcc Hleq x HP v Hget.
    edestruct Hcc as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.
  
  Lemma cc_approx_env_monotonic (k j : nat) c1 c2 :
    cc_approx_env k GIP GP c1 c2 ->
    j <= k ->
    cc_approx_env j GIP GP c1 c2.
  Proof.
    intros Hleq H. eapply cc_approx_env_P_monotonic; eauto.
  Qed.
  
  (** * Set lemmas *)
  
  Lemma cc_approx_env_Empty_set (k : nat) c1 c2 :
    c1 ⋞ ^ ( Empty_set var ; k ; GIP ; GP ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    firstorder.
  Qed.
  
  Lemma cc_approx_env_P_union (P1 P2 : Ensemble var) (k : nat) c1 c2 :
    c1 ⋞ ^ ( P1 ; k ; GIP ; GP) c2 ->
    c1 ⋞ ^ ( P2 ; k ; GIP ; GP ) c2 ->
    c1 ⋞ ^ ( P1 :|: P2 ; k ; GIP ; GP ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre1 Hpre2 x HP2. inv HP2; eauto.
  Qed.
  
  Lemma cc_approx_env_P_inter_l (P1 P2 : Ensemble var) (k : nat) c1 c2 :
    c1 ⋞ ^ ( P1 ; k ; GIP ; GP ) c2 ->
    c1 ⋞ ^ ( P1 :&: P2 ; k ; GIP ; GP ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre x HP2. inv HP2; eauto.
  Qed.
  
  Lemma cc_approx_env_P_inter_r (P1 P2 : Ensemble var) (k : nat) c1 c2 :
    c1 ⋞ ^ ( P2 ; k ; GIP ; GP) c2 ->
    c1 ⋞ ^ ( P1 :&: P2 ; k ; GIP ; GP ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre x HP2. inv HP2; eauto.
  Qed.
  
  (** * Preservation under enviroment extension lemmas *)
  
  Lemma cc_approx_var_env_set_eq :
    forall (k : nat) (rho1 rho2 : env) (H1 H2 : heap block)
      (x y : var) (v1 v2 : value),
      (Res (v1, H1)) ≺ ^ (k ; GIP ; GP) (Res (v2, H2)) ->
      cc_approx_var_env k GIP GP H1 (M.set x v1 rho1) H2 (M.set y v2 rho2) x y.
  Proof.
    intros rho1 rho2 H1 H2 k x y v1 v2 Hval x' Hget.
    rewrite M.gss in Hget. inv Hget. eexists.
    rewrite M.gss. split; eauto.
  Qed.
  
  Lemma cc_approx_var_env_set_neq :
    forall (k : nat)  (rho1 rho2 : env) (H1 H2 : heap block)
      (x1 x2 y1 y2 : var) (v1 v2 : value),
      cc_approx_var_env k GIP GP H1 rho1 H2 rho2 y1 y2 ->
      y1 <> x1 -> y2 <> x2 ->
      cc_approx_var_env k GIP GP H1 (M.set x1 v1 rho1) H2 (M.set x2 v2 rho2) y1 y2.
  Proof. 
    intros k rho1 rho2 H1 H2 x1 x2 y1 y2 v1 v2 Hval Hneq Hneq' x' Hget.
    rewrite M.gso in *; eauto.
  Qed.
  
  Lemma cc_approx_var_env_set :
    forall (k : nat)  (rho1 rho2 : env) (H1 H2 : heap block)
      (x y : var) (v1 v2 : value),
      cc_approx_var_env k GIP GP H1 rho1 H2 rho2 y y ->
      (Res (v1, H1)) ≺ ^ (k; GIP ; GP) (Res (v2, H2)) ->
      cc_approx_var_env k GIP GP H1 (M.set x v1 rho1) H2 (M.set x v2 rho2) y y.
  Proof.
    intros k rho1 rho2 H1 H2 x y v1 v2 Hvar Hval.
    destruct (peq y x); subst.
    - apply cc_approx_var_env_set_eq; eauto.
    - apply cc_approx_var_env_set_neq; eauto.
  Qed.
  
  (** Extend the related environments with a single point *)
  Lemma cc_approx_env_P_set (S : Ensemble var) (k : nat)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v1 v2 : value) :
      (H1, rho1) ⋞ ^ ( S \\ [set x] ; k ; GIP ; GP ) (H2, rho2) ->
      (Res (v1, H1)) ≺ ^ (k; GIP ; GP) (Res (v2, H2)) ->
      (H1, M.set x v1 rho1) ⋞ ^ ( S; k ; GIP ; GP ) (H2, M.set x v2 rho2).
  Proof.
    intros Henv Hval x' HP v1' Hget.
    rewrite M.gsspec in Hget. destruct (peq x' x); subst.
    - inv Hget. eexists. rewrite M.gss. split; eauto.
    - apply Henv in Hget; eauto. destruct Hget as [v2' [Heq Hpre]].
      eexists; split; eauto. rewrite M.gso; eauto. constructor; eauto.
      intros Hin. inv Hin. congruence.
  Qed.
  
  (** Extend the related environments with a list *)
  Lemma cc_approx_env_P_setlist_l (S : Ensemble var) (k : nat)
        (rho1 rho2 rho1' rho2' : env) (H1 H2 : heap block) xs (vs1 vs2 : list value) :
    (H1, rho1) ⋞ ^ ( S \\ (FromList xs) ; k ; GIP ; GP ) (H2, rho2) ->
    Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k ; GIP ; GP ) (Res (v2, H2))) vs1 vs2 ->
    setlist xs vs1 rho1 = Some rho1' ->
    setlist xs vs2 rho2 = Some rho2' ->
    (H1, rho1') ⋞ ^ ( S ; k ; GIP ; GP ) (H2, rho2').
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
  
  Lemma cc_approx_env_P_set_not_in_P_l (S : Ensemble var) (k : nat) 
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v : value) :
    (H1, rho1) ⋞ ^ ( S ; k ; GIP ; GP ) (H2, rho2) ->
    ~ x \in S ->
    (H1, M.set x v rho1) ⋞ ^ ( S; k ; GIP ; GP ) (H2, rho2).
  Proof. 
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    destruct (peq y x); subst.
    - contradiction.
    - rewrite M.gso in Hget; eauto.
  Qed.
  
  Lemma cc_approx_env_P_set_not_in_P_r (S : Ensemble var) (k : nat)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v : value) :
    (H1, rho1) ⋞ ^ ( S ; k ; GIP ; GP ) (H2, rho2) ->
    ~ x \in S ->
    (H1, rho1) ⋞ ^ ( S ; k ; GIP ; GP ) (H2, M.set x v rho2).
  Proof. 
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    exists v''. rewrite M.gsspec.
    destruct (peq y x); subst.
    - contradiction.
    - eauto.
  Qed.

  (** * The logical relation respects heap equivalences *)

  (* TODO move *)
  Lemma Forall_vertical_l {A B} (R1 R1' : A -> B -> Prop) (R2 : A -> A -> Prop) l1 l2 l3 :
    (forall x y z, R1 x y -> R2 x z -> R1' z y) ->
    Forall2 R1 l1 l2 ->
    Forall2 R2 l1 l3 ->
    Forall2 R1' l3 l2.
  Proof.
    intros Hr Hall1. revert l3. induction Hall1; intros l3 Hall2.
    - inv Hall2. constructor.
    - inv Hall2. constructor; eauto. 
  Qed.


  Lemma Forall_vertical_r {A B} (R1 R1' : A -> B -> Prop) (R2 : B -> B -> Prop) l1 l2 l3 :
    (forall x y z, R1 x y -> R2 y z -> R1' x z) ->
    Forall2 R1 l1 l2 ->
    Forall2 R2 l2 l3 ->
    Forall2 R1' l1 l3.
  Proof.
    intros Hr Hall1. revert l3. induction Hall1; intros l3 Hall2.
    - inv Hall2. constructor.
    - inv Hall2. constructor; eauto. 
  Qed.
  
  Lemma cc_approx_val_res_eq (k : nat)  (H1 H2 H1' H2' : heap block)
        (v1 v2 v1' v2' : value) :
    (Res (v1, H1)) ≺ ^ (k ; GIP ; GP) (Res (v2, H2)) ->
    (v1, H1) ≈ (v1', H1') ->
    (v2, H2) ≈ (v2', H2') ->
    (Res (v1', H1')) ≺ ^ (k ; GIP ; GP) (Res (v2', H2')).
  Proof with now eauto with Ensembles_DB.
    revert v1 v2 v1' v2' H1 H2 H1' H2'. induction k as [k IHk] using lt_wf_rec1.
    intros v1 v2 v1' v2' H1 H2 H1' H2'.
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    destruct (get l1 H1) as [b1|] eqn:Hget1; destruct (get l2 H2) as [b2|] eqn:Hget2; try contradiction;
    destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ]; try contradiction;
    destruct b2 as [c2 vs2 | | ]; try contradiction.
    + intros [Heq Hi] Hres1 Hres2.
      rewrite res_equiv_eq in Hres1, Hres2.
      destruct v1' as [l1' | lf1' f1']; destruct v2' as [l2' | lf2' f2']; try contradiction.
      simpl in Hres1, Hres2.
      rewrite Hget1 in Hres1. rewrite Hget2 in Hres2. 
      destruct (get l1' H1') as [b1'|] eqn:Hget1'; try contradiction.
      destruct (get l2' H2') as [b2'|] eqn:Hget2'; try contradiction.
      destruct b1' as [c1' vs1' | | ]; try contradiction.
      destruct b2' as [c2' vs2' | | ]; try contradiction.
      destruct Hres1 as [Heqc1 Heqb1].
      destruct Hres2 as [Heqc2 Heqb2]. subst.
      split; [ reflexivity |].
      intros i Hleq.
      eapply Forall_vertical_l; [| | eassumption ].
      * simpl. intros. rewrite cc_approx_val_eq in *. eapply IHk.
        eassumption. eassumption.
        eassumption. reflexivity.
      * eapply Forall_vertical_r; [| | eassumption ].
        simpl. intros. rewrite cc_approx_val_eq in *. eapply IHk.
        eassumption. eassumption.
        reflexivity. eassumption.
        eapply Hi. eassumption.
    + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; try contradiction.
      intros Hyp Hres1 Hres2. rewrite res_equiv_eq in *.
      destruct v1' as [l1' | lf1' f1']; destruct v2' as [l2' | lf2' f2']; try contradiction.
      simpl in Hres1, Hres2.
      rewrite Hget1 in Hres1. rewrite Hget2 in Hres2. 
      destruct (get l1' H1') as [b1'|] eqn:Hget1'; try contradiction.
      destruct (get l2' H2') as [b2'|] eqn:Hget2'; try contradiction.
      destruct b1' as [c1' vs1' | | ]; try contradiction.
      destruct b2' as [c2' vs2' | | ]; try contradiction.
      destruct Hres1 as [Hptr1 Henv1].
      destruct Hres2 as [Heqc2 Hall]. subst.
      rewrite res_equiv_eq in *.
      destruct v as [l3' | lf3' f3']; destruct v0 as [l4' | lf4' f4']; try contradiction.
      inv Hall. inv H5. inv H7.
      rewrite res_equiv_eq in *.
      destruct y as [l5' | lf5' f5']; destruct y0 as [l6' | lf6' f6']; try contradiction.
      inv H3. inv Hptr1.
      intros tc1 tc2 tc3 H3 H3' H4' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset.
      rewrite <- res_equiv_eq in *.
      (* simpl in Henv1. rewrite Hget in Henv1. *)
      (* destruct (get env_loc1 H1) as [[| | rho ] |]; try contradiction. *)
      edestruct Hyp as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi).
      * eapply Equivalence_Transitive; eassumption.
      * eapply Equivalence_Transitive; eassumption.
      * eassumption.
      * eassumption.
      * eassumption.
      * eassumption.
      * exists xs2, e2, rho2'. repeat split; eauto.
  Qed.

  Lemma cc_approx_val_heap_eq (k : nat) (H1 H2 H1' H2' : heap block)
        (v1 v2 : value) :
    (Res (v1, H1)) ≺ ^ (k ; GIP ; GP) (Res (v2, H2)) ->
    (val_loc v1) |- H1 ≃ H1' ->
    (val_loc v2) |- H2 ≃ H2' ->
    (Res (v1, H1')) ≺ ^ (k ; GIP ; GP) (Res (v2, H2')).
  Proof with now eauto with Ensembles_DB.
    intros.
    eapply cc_approx_val_res_eq. eassumption. 
    eapply heap_equiv_res_equiv. eassumption. reflexivity.
    eapply heap_equiv_res_equiv. eassumption. reflexivity.
  Qed.

  Lemma cc_approx_var_env_heap_env_equiv (S1 S2 : Ensemble var) (k : nat)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 rho1' rho2' : env) (x1 x2 : var) :
    cc_approx_var_env k GIP GP H1 rho1 H2 rho2 x1 x2 ->
    S1 |- (H1, rho1) ⩪ (H1', rho1') ->
    S2 |- (H2, rho2) ⩪ (H2', rho2') ->
    x1 \in S1 -> x2 \in S2 ->
    cc_approx_var_env k GIP GP H1' rho1' H2' rho2' x1 x2.
  Proof.
    intros Henv Heq1 Heq2 Hin1 Hin2 v1' Hget1'.
    eapply Heq1 in Hget1'; [| eassumption ].
    destruct Hget1' as [v1 [Hget1 Hequiv1]].
    eapply Henv in Hget1.
    destruct Hget1 as [v2 [Hget2 Hval]]; eauto.
    eapply Heq2 in Hget2; [| eassumption ].
    destruct Hget2 as [v2' [Hget2' Hequiv2]]; eauto.
    eexists. split; eauto.
    eapply cc_approx_val_res_eq. eassumption.
    now symmetry. eassumption.
  Qed.
  
  Lemma cc_approx_env_P_heap_eq (S : Ensemble var) (k : nat) (P : GInv)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 rho1' rho2' : env) :
    (H1, rho1) ⋞ ^ (S; k; GIP; GP) (H2, rho2) ->
    S |- (H1, rho1) ⩪ (H1', rho1') ->
    S |- (H2, rho2) ⩪ (H2', rho2') ->
    (H1', rho1') ⋞ ^ (S; k; GIP; GP) (H2', rho2').
  Proof.
    intros Henv Heq1 Heq2 x HS.
    eapply cc_approx_var_env_heap_env_equiv; eauto.
  Qed.


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
  
  Lemma cc_approx_var_env_getlist (k : nat)
        (rho1 rho2 : env) (H1 H2 : heap block) xs ys vs1 :
    Forall2 (cc_approx_var_env k GIP GP H1 rho1 H2 rho2) xs ys ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist ys rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k; GIP ; GP) (Res (v2, H2))) vs1 vs2.
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
  
  Lemma cc_approx_env_P_getlist_l (S : Ensemble var) (k : nat)
        (rho1 rho2 : env) (H1 H2 : heap block) (xs : list var) (vs1 : list value) :
    (H1, rho1) ⋞ ^ ( S ; k ; GIP ; GP ) (H2, rho2) ->
    (FromList xs) \subset S ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist xs rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k; GIP ; GP) (Res (v2, H2))) vs1 vs2.
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

  (*  Lemma cc_approx_exp_heap_env_equiv (k : nat) (H1 H2 H1' H2' : heap block) *)
  (*        (rho1 rho2 rho1' rho2' : env) (e1 e2 : exp) : *)
  (*   (e1, rho1, H1) ⪯ ^ (k; IP ; LP; GP) (e2, rho2, H2) -> *)
  (*   (occurs_free e1) |- (H1, rho1) ⩪ (H1', rho1') -> *)
  (*   (occurs_free e2) |- (H2, rho2) ⩪ (H2', rho2') -> *)
  (*   (IP (H1', rho1', e1) (H2', rho2', e2) -> IP (H1, rho1, e1) (H2, rho2, e2)) -> *)
  (*   (e1, rho1', H1') ⪯ ^ (k; IP; LP; GP) (e2, rho2', H2'). *)
  (* Proof with now eauto with Ensembles_DB. *)
  (*   intros Hexp Heq1 Heq2 Hinv H1'' H2'' rho1'' rho2'' r1 c1 m1 Heq1' Heq2' HIP Hleq Hbs Hns. *)
  (*   eapply Hexp; [| | | | eassumption | ]; eauto; *)
  (*   eapply Equivalence_Transitive; try eassumption. *)
  (* Qed. *)

   
   Lemma cc_approx_exp_heap_monotonic (k : nat) (H1 H2 H1' H2' : heap block)
         (rho1 rho2 : env) (e1 e2 : exp) :
     well_formed (reach' H1 (env_locs rho1 (occurs_free e1))) H1 ->
     well_formed (reach' H2 (env_locs rho2 (occurs_free e2))) H2 ->
     (env_locs rho1 (occurs_free e1)) \subset dom H1 ->
     (env_locs rho2 (occurs_free e2)) \subset dom H2 ->
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     (e1, rho1, H1)  ⪯ ^ ( k ; LIP ; GIP ; LP ; GP ) (e2, rho2, H2) ->
     (e1, rho1, H1') ⪯ ^ ( k ; LIP ; GIP ; LP ; GP ) (e2, rho2, H2').
   Proof.
     intros Hwf1 Hwf22 Hs1 Hs2 Hsub1 Hsub2 Hyp H3 H4 rho1' rho2' r1 c1 m1 Heq1 Heq2 HIP Hleq Hstep Hns.
     eapply Hyp; [ | | eassumption | eassumption | eassumption | eassumption ].
     edestruct Equivalence_heap_env_equiv with (S := (occurs_free e1)). (* ? *)
     eapply Equivalence_Transitive.
     eapply subheap_heap_env_equiv; try eassumption. now eapply reach'_extensive.
     eassumption.
     edestruct Equivalence_heap_env_equiv with (S := (occurs_free e2)). (* ? *)
     eapply Equivalence_Transitive.
     eapply subheap_heap_env_equiv; try eassumption. now eapply reach'_extensive.
     eassumption. 
   Qed.

   Lemma cc_approx_val_heap_monotonic  (k : nat) (H1 H2 H1' H2' : heap block)
       (v1 v2 : value):
     well_formed (reach' H1 (val_loc v1)) H1 ->
     well_formed (reach' H2 (val_loc v2)) H2 ->
     val_loc v1 \subset dom H1 ->
     val_loc v2 \subset dom H2 ->
     H1 ⊑ H1' -> H2 ⊑ H2' ->
     Res (v1, H1) ≺ ^ (k ; GIP ; GP) Res (v2, H2) ->
     Res (v1, H1') ≺ ^ (k ; GIP ; GP) Res (v2, H2').
   Proof.
     revert v1 v2. induction k as [k IHk] using lt_wf_rec1.
     intros v1 v2 Hwf1 Hwf2 Hin1 Hin2 Hsub1 Hsub2 Hcc.
     destruct k as [ | k ];
       destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2]; simpl;
       try (now intros; contradiction); try (now simpl; eauto).
     - simpl in Hcc.
       destruct (get l1 H1) as [b1|] eqn:Hget1; destruct (get l2 H2) as [b2|] eqn:Hget2; try contradiction.
       eapply Hsub1 in Hget1. eapply Hsub2 in Hget2. rewrite Hget1, Hget2.
       destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
         destruct b2 as [c2 vs2 | | ]; try contradiction.
       + destruct Hcc as [Heq Hi]. subst. split; [ reflexivity |].
         intros i Hleq. omega.
       + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
         intros tc1 tc2 tc3 H3 H3' H4' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset.
         edestruct Hcc
           as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
         * eapply Equivalence_Transitive; [| eassumption ].
           eapply subheap_res_equiv; try eassumption.
           eapply Included_trans; [| now eapply Included_post_reach' ].
           edestruct Hin1 as [b1 Hget1']. reflexivity.
           eexists. eexists.  split; [| split; [ eassumption |]].
           reflexivity. eapply Hsub1 in Hget1'. subst_exp.
           simpl. right. eassumption. 
         * eapply Equivalence_Transitive; [| eassumption ].
           eapply subheap_res_equiv; try eassumption.
           eapply Included_trans; [| now eapply Included_post_reach' ].
           edestruct Hin2 as [b2 Hget2']. reflexivity.
           eexists. eexists.  split; [| split; [ eassumption |]].
           reflexivity. eapply Hsub2 in Hget2'. subst_exp.
           simpl. right. left. eassumption. 
         * do 3 eexists; split; [ | split ]; try (now eauto).
     - simpl in Hcc.
       destruct (get l1 H1) as [b1|] eqn:Hget1; destruct (get l2 H2) as [b2|] eqn:Hget2; try contradiction.
       eapply Hsub1 in Hget1. eapply Hsub2 in Hget2. rewrite Hget1, Hget2.
       destruct b1 as [c1 vs1 | [? | B1 f1] [env_loc1 |] | ];
         destruct b2 as [c2 vs2 | | ]; try contradiction.
       + destruct Hcc as [Heq Hi]. subst. split; [ reflexivity |].
         edestruct Hin1 as [b1 Hget1']. reflexivity.
         assert (Hget1'' := Hget1'). eapply Hsub1 in Hget1''.
         subst_exp.
         edestruct Hin2 as [b2 Hget2']. reflexivity.
         assert (Hget2'' := Hget2'). eapply Hsub2 in Hget2''.
         subst_exp.
         intros i Hleq. simpl.
         eapply Forall2_monotonic_strong; [| eapply Hi; eassumption ].
         intros x1 x2 Hinx1 Hinx2 Hr.
         assert (Hr1 : val_loc x1 \subset post H1 (val_loc (Loc l1))).
         { simpl. rewrite post_Singleton; [| eassumption ].
           simpl. eapply In_Union_list.
           eapply in_map. eassumption. }
         assert (Hr2 : val_loc x2 \subset post H2 (val_loc (Loc l2))).
         { simpl. rewrite post_Singleton; [| eassumption ].
           simpl. eapply In_Union_list.
           eapply in_map. eassumption. }
         rewrite cc_approx_val_eq. eapply IHk; try eassumption.
         * eapply well_formed_antimon; [| eassumption ].
           rewrite (reach_unfold _ (val_loc (Loc l1))).
           eapply Included_Union_preserv_r.
           eapply reach'_set_monotonic. eassumption.
         * eapply well_formed_antimon; [| eassumption ].
           rewrite (reach_unfold _ (val_loc (Loc l2))).
           eapply Included_Union_preserv_r.
           eapply reach'_set_monotonic. eassumption.
         * eapply Included_trans; [| eapply reachable_in_dom ]; try eassumption.
           eapply Included_trans; [| eapply Included_post_reach']; eassumption.
         * eapply Included_trans; [| eapply reachable_in_dom ]; try eassumption.
           eapply Included_trans; [| eapply Included_post_reach']; eassumption.
         * rewrite <- cc_approx_val_eq. eassumption.
       + destruct vs2 as [ | [| B2 f2] [| [env_loc2 |] [|]] ]; eauto.
         intros tc1 tc2 tc3 H3 H3' H4' env_loc1' env_loc2' xs1 ft e1 vs1 vs2 Heq1 Heq2 Hget Hfind Hdef Hset.
         edestruct Hcc
           as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi); eauto.
         * eapply Equivalence_Transitive; [| eassumption ].
           eapply subheap_res_equiv; try eassumption.
           eapply Included_trans; [| now eapply Included_post_reach' ].
           edestruct Hin1 as [b1 Hget1']. reflexivity.
           eexists. eexists.  split; [| split; [ eassumption |]].
           reflexivity. eapply Hsub1 in Hget1'. subst_exp.
           simpl. right. eassumption. 
         * eapply Equivalence_Transitive; [| eassumption ].
           eapply subheap_res_equiv; try eassumption.
           eapply Included_trans; [| now eapply Included_post_reach' ].
           edestruct Hin2 as [b2 Hget2']. reflexivity.
           eexists. eexists.  split; [| split; [ eassumption |]].
           reflexivity. eapply Hsub2 in Hget2'. subst_exp.
           simpl. right. left. eassumption.  
         * do 3 eexists; split; [ | split ]; try (now eauto).
   Qed.
   
  End LogRelLemmas.



  (** * Proper Instances *)

  
  Global Instance cc_approx_env_proper_set :
    Proper (Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           cc_approx_env_P.
  Proof.
    intros s1 s2 [H1 H2]; split; intros Hpre;
    subst; eapply cc_approx_env_P_antimon; subst; eauto. 
  Qed.


  (** * Compatibility lemmas *)


  (** Apply a closure converted function *)
  (** TODO move *)
   Definition AppClo f t xs f' Γ :=
    Eproj f' clo_tag 0%N f
          (Eproj Γ clo_tag 1%N f
                 (Eapp f' t (Γ :: xs))).


  Section Compat.

    (** Conditions *)

    Variable (IG : GInv). (* Final global *)
    Variable (ILi : nat -> Inv). (* Final local indexed by a natural number indicating the amount of time units already spent for evaluation of the RHS program *) 
    Variable (IIG : GIInv). (* Global initial *)
    Variable (IIL1 IIL2 : IInv). (* Local initial *)
    
    Variable (F : nat). (* A constant factor*)
    
    Variable
      (InvCostTimeout :
         forall (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp) (k c : nat),
           IIL1 (H1, rho1, e1) (H2, rho2, e2) ->
           ILi k (c, size_heap H1) (c - k, size_heap H2)).
    
    Variable
      (InvCostBase :
         forall (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp) (k c : nat),
           c >= 1 ->
           IIL1 (H1, rho1, e1) (H2, rho2, e2) ->
           ILi k (c, size_heap H1) (c, size_heap H2)).
    
    
    (** * Compatibility properties for local conditions *)

    Variable
      (InvCompat_str :
         forall (k1 k2 c1 c2 c1' c2' m1 m2 : nat),
           
           ILi k2 (c1 - c1', m1) (c2 - c2', m2) -> 

           c1' <= c2' + (k1 - k2) <= c1' + F*c1' ->

           ILi k1 (c1, m1) (c2, m2)).
    
    Variable
      (InvTransfer :
         forall (k c1 c2 c m1 m2 : nat),
           ILi (k + c) (c1, m1) (c2, m2) ->
           ILi k (c1, m1) (c2 + c, m2)).
    
    (** Constructor compatibility *)
    Lemma cc_approx_exp_constr_compat (k : nat)
          (H1 H2 : heap block)  (rho1 rho2 : env)
          (x1 x2 : var) (t : cTag) (ys1 ys2 : list var) (e1 e2 : exp) (r1 r2 : nat) (a1 a2 : nat)
          
          (IInvConstrCompat :
             forall (H1 H2 H1' H2' : heap block) (rho1 rho2 : env)
               (b1 b2 : block) (l1 l2 : loc),
               IIL1 (H1, rho1, Econstr x1 t ys1 e1) (H2, rho2, Econstr x2 t ys2 e2) ->
               alloc b1 H1 = (l1, H1') -> 
               alloc b2 H2 = (l2, H2') ->
               size_val b1 = size_val b2 ->
               locs b1 \subset reach' H1 (env_locs rho1 (occurs_free (Econstr x1 t ys1 e1))) ->
               locs b2 \subset reach' H2 (env_locs rho2 (occurs_free (Econstr x2 t ys2 e2))) ->
               IIL2 (H1', M.set x1 (Loc l1) rho1, e1) (H2', M.set x2 (Loc l2) rho2, e2)) : 

      well_formed (reach' H1 (env_locs rho1 (occurs_free (Econstr x1 t ys1 e1)))) H1 ->
      well_formed (reach' H2 (env_locs rho2 (occurs_free (Econstr x2 t ys2 e2)))) H2 ->
      (env_locs rho1 (occurs_free (Econstr x1 t ys1 e1))) \subset dom H1 ->
      (env_locs rho2 (occurs_free (Econstr x2 t ys2 e2))) \subset dom H2 ->

      Forall2 (cc_approx_var_env k IIG IG H1 rho1 H2 rho2) ys1 ys2 ->

      (r1 - r2) <= F*(cost (Econstr x1 t ys1 e1)) ->

      (forall i vs1 vs2 l1 l2 H1' H2',
         i < k ->
         (* allocate a new location for the constructed value *)
         alloc (Constr t vs1) H1 = (l1, H1') ->
         alloc (Constr t vs2) H2 = (l2, H2') ->
         Forall2 (fun l1 l2 => (Res (l1, H1)) ≺ ^ (i ; IIG ; IG) (Res (l2, H2))) vs1 vs2 ->
         (e1, M.set x1 (Loc l1) rho1, H1') ⪯ ^ (i ; IIL2 ; IIG ; ILi r2 ; IG)
         (e2, M.set x2 (Loc l2) rho2, H2')) ->
      
      (Econstr x1 t ys1 e1, rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi r1 ; IG) (Econstr x2 t ys2 e2, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hwf1 Hwf2 Hdom1 Hdom2 Hall Hleq Hpre H1' H2' rho1' rho2' v1 c1 m1
             Heq1 Heq2 HII Hleq1 Hstep1 Hstuck1.
      inv Hstep1.
      (* Timeout! *)
      - { exists OOT, (c1 - r1). eexists. repeat split. 
          - econstructor. simpl. erewrite <- Forall2_length; [| eassumption ].
            simpl in Hcost. omega. reflexivity.
          - eapply InvCostTimeout. eassumption.
          - now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { edestruct (cc_approx_var_env_getlist IIG IG k rho1' rho2') as [vs2 [Hget' Hpre']];
          [| eauto |]; eauto. 
          eapply Forall2_monotonic_strong; [| eassumption ].
          intros x1' x2' Hin1 Hin2 Hvar.
          eapply cc_approx_var_env_heap_env_equiv; try eassumption.
          normalize_occurs_free... normalize_occurs_free...
          edestruct heap_env_equiv_env_getlist as [vs1' [Hget1' Hall1]]; [| symmetry; now apply Heq1 | |]; try eassumption.
          normalize_occurs_free...
          edestruct heap_env_equiv_env_getlist as [vs2' [Hget2' Hall2]]; [| symmetry; now apply Heq2 | |]; try eassumption.
          normalize_occurs_free...
          destruct (alloc (Constr t vs1') H1) as [l1 H1''] eqn:Hal1.
          destruct (alloc (Constr t vs2) H2') as [l2 H''] eqn:Hal2'.
          destruct (alloc (Constr t vs2') H2) as [l2' H2''] eqn:Hal2.
          eapply Forall2_length in Hall.
          assert (Hlen : @length M.elt ys1 = @length M.elt ys2).
          { erewrite (@getlist_length_eq value ys1 vs); [| eassumption ].
            erewrite (@getlist_length_eq value ys2 vs2); [| eassumption ].
            eapply Forall2_length. eassumption. }
          edestruct Hpre with (i := k - (cost (Econstr x1 t ys1 e1)))
            as [v2 [c2 [m2 [Hstep [HS Hval]]]]];
            [ | eassumption | eassumption | | | | | | eassumption | | ].
          - simpl in Hcost. simpl. omega.
          - eapply Forall_vertical_l; [| | eassumption ].
            intros x y z Hr Hres.
            eapply cc_approx_val_res_eq. now apply Hr. now apply Hres.
            reflexivity.
            eapply Forall_vertical_r; [| | eassumption ].
            intros x y z Hr Hres.
            eapply cc_approx_val_res_eq. now apply Hr. reflexivity. now apply Hres.
            eapply Forall2_monotonic_strong; [| eassumption ]. intros ? ? ? ? H.
            eapply cc_approx_val_monotonic.
            now eapply H. omega.
          - eapply heap_env_equiv_alloc; [| | | | | | | eassumption | eassumption | ].
            + eapply reach'_closed. eassumption. eassumption.
            + eapply reach'_closed.
              eapply well_formed_respects_heap_env_equiv.
              now apply Hwf1. eassumption.
              eapply env_locs_in_dom; eassumption.
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
            + eapply heap_env_equiv_antimon. eassumption.
              normalize_occurs_free...
            + simpl. split. reflexivity.
              eapply Forall2_symm_strong; [| eassumption ].
              intros. symmetry; eauto.
          - eapply heap_env_equiv_alloc; [| | | | | | | now apply Hal2 | now apply Hal2' | ].
            + eapply reach'_closed. eassumption. eassumption.
            + eapply reach'_closed.
              eapply well_formed_respects_heap_env_equiv.
              now apply Hwf2. eassumption.
              eapply env_locs_in_dom; eassumption.
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
            + eapply heap_env_equiv_antimon. eassumption.
              normalize_occurs_free...
            + simpl. split. reflexivity.
              eapply Forall2_symm_strong; [| eassumption ].
              intros. symmetry; eauto.
          - eapply IInvConstrCompat; [ eassumption | eassumption | eassumption | | | ].
            simpl.
            eapply getlist_length_eq in Hget.
            eapply getlist_length_eq in Hget'. congruence.
            eapply Included_trans; [| now eapply reach'_extensive ].
            normalize_occurs_free. rewrite env_locs_Union.
            eapply Included_Union_preserv_l. rewrite env_locs_FromList.
            simpl. reflexivity. eassumption.
            eapply Included_trans; [| now eapply reach'_extensive ].
            normalize_occurs_free. rewrite env_locs_Union.
            eapply Included_Union_preserv_l. rewrite env_locs_FromList.
            simpl. reflexivity. eassumption.
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
            + simpl. eapply InvCompat_str with (c2' := S (length ys1)).
              replace (length ys2) with (length ys1).
              replace (c2 + S (length ys1) - S (length ys1)) with c2 by omega.
              eassumption. simpl. simpl in Hleq. omega.
            + rewrite cc_approx_val_eq. eapply cc_approx_val_monotonic.
              rewrite <- cc_approx_val_eq. eassumption. omega. }
    Qed.
    
    (** Projection compatibility *)
    Lemma cc_approx_exp_proj_compat (k : nat) (H1 H2 : heap block) (rho1 rho2 : env)
          (x1 x2 : var) (t : cTag) (n : N) (y1 y2 : var) (e1 e2 : exp) (r1 r2 : nat)

          (IInvProjCompat :
             forall (H1 H2 : heap block) (rho1 rho2 : env) (v1 v2 : value),
               IIL1 (H1, rho1, Eproj x1 t n y1 e1) (H2, rho2, Eproj x2 t n y2 e2) ->
               val_loc v1 \subset reach' H1 (env_locs rho1 (occurs_free (Eproj x1 t n y1 e1))) ->
               val_loc v2 \subset reach' H2 (env_locs rho2 (occurs_free (Eproj x2 t n y2 e2))) ->
               IIL2 (H1, M.set x1 v1 rho1, e1) (H2, M.set x2 v2 rho2, e2)) :

      cc_approx_var_env k IIG IG H1 rho1 H2 rho2 y1 y2 ->

      r1 - r2 <= F*(cost (Eproj x1 t n y1 e1)) ->

      (forall i v1 v2,
         i < k ->
         (Res (v1, H1)) ≺ ^ (i ; IIG ; IG) (Res (v2, H2)) ->
         (e1, M.set x1 v1 rho1, H1) ⪯ ^ (i ; IIL2 ; IIG ; ILi r2 ; IG) (e2, M.set x2 v2 rho2, H2)) ->
      
      (Eproj x1 t n y1 e1, rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi r1 ; IG) (Eproj x2 t n y2 e2, rho2, H2).
    Proof.
      intros Hall Hleq Hpre H1' H2' rho1' rho2' v1 c1 m1
             Heq1' Heq2' HII Hleq1 Hstep1 Hstuck. inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost. exists OOT, (c1 - r1). eexists. repeat split. 
          - econstructor. simpl; omega. reflexivity. 
          - eapply InvCostTimeout. eassumption.
          - now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { pose (cost1 := cost (Eproj x1 t n y1 e1)).
          pose (cost2 := costCC (Eproj x2 t n y2 e2)).
          assert (Hall' := Hall).
          
          eapply (cc_approx_var_env_heap_env_equiv
                    _ _
                    (occurs_free (Eproj x1 t n y1 e1))
                    (occurs_free (Eproj x2 t n y2 e2))) in Hall;
          [| eassumption | eassumption
           | normalize_occurs_free; now eauto with Ensembles_DB | normalize_occurs_free; now eauto with Ensembles_DB ].
          edestruct Hall as [l2 [Hget' Hcc']]; eauto.
          destruct l2 as [l' | l' f]; [| contradiction ].
          simpl in Hcc'. rewrite Hgetl in Hcc'.
          destruct (get l' H2') as [[ t2 vs' | | ] |] eqn:Hgetl'; try contradiction.
          destruct Hcc' as [Hteq Hcc']. subst.
          
          edestruct heap_env_equiv_env_get as [l1 [Hgetl1 Hres1]]; [ now apply Hgety | | | ].
          symmetry. eassumption. now eauto.
          edestruct heap_env_equiv_env_get as [l2 [Hgetl2 Hres2]]; [ now apply Hget' | | | ].
          symmetry. eassumption. now eauto.

          edestruct Hall' as [l2' [Hgetl2'' Hcc]]; eauto. repeat subst_exp. 
          
          rewrite res_equiv_eq in Hres1, Hres2.
          destruct l1 as [l1 |]; try contradiction.
          destruct l2' as [l2 |]; try contradiction.
          
          simpl in Hres1, Hres2. rewrite Hgetl in Hres1. rewrite Hgetl' in Hres2.
          destruct (get l1 H1) as [b1 |] eqn:Hgetl1'; try contradiction.
          destruct (get l2 H2) as [b2 |] eqn:Hgetl2'; try contradiction.
          destruct b1 as [t1 vs1 | | ]; try contradiction. destruct Hres1 as [Hteq Hallvs1]; subst.
          destruct b2 as [t2 vs2 | | ]; try contradiction. destruct Hres2 as [Hteq Hallvs2]; subst.

          simpl in Hcc. rewrite Hgetl1' in Hcc. rewrite Hgetl2' in Hcc.
          destruct Hcc as [Hteq Hcc]. subst.

          edestruct (Forall2_nthN _ _ _ _ _ Hallvs1 Hnth) as [v1' [Hnth' Hv1]].
          edestruct (Forall2_nthN (fun l1 l2 => cc_approx_val (k - cost1) IIG IG (Res (l1, H1)) (Res (l2, H2))) vs1)
            as [l3' [Hnth'' Hval']]; eauto. eapply Hcc. unfold cost1. simpl. simpl in Hcost. omega.
          
          edestruct (Forall2_nthN (fun v1 v2 : value => (v1, H2) ≈ (v2, H2'))) as [v2' [Hnth2' Hv2]].
          eapply Forall2_symm_strong; [| eassumption ]. intros. now symmetry; eauto. eassumption.
          
          edestruct Hpre with (i := k - cost1) (c1 := c1 - cost1) as [v2 [c2 [m2 [Hstep [HS Hres]]]]]. 
          - unfold cost1. simpl. simpl in Hcost. omega.
          - rewrite <- cc_approx_val_eq. eassumption.
          - eapply heap_env_equiv_set.
            eapply heap_env_equiv_antimon. eassumption.
            normalize_occurs_free... now eauto with Ensembles_DB.
            symmetry. eassumption. 
          - eapply heap_env_equiv_set.
            eapply heap_env_equiv_antimon. eassumption.
            normalize_occurs_free... now eauto with Ensembles_DB.
            eassumption.
          - eapply IInvProjCompat. eassumption.
            eapply Included_trans; [| eapply Included_post_reach' ].
            normalize_occurs_free. rewrite env_locs_Union, post_Union. eapply Included_Union_preserv_l.
            rewrite env_locs_Singleton; eauto. simpl. erewrite post_Singleton; eauto.
            simpl. eapply In_Union_list. eapply in_map. eapply nthN_In. eassumption.
            eapply Included_trans; [| eapply Included_post_reach' ].
            normalize_occurs_free. rewrite env_locs_Union, post_Union. eapply Included_Union_preserv_l.
            rewrite env_locs_Singleton; eauto. simpl. erewrite post_Singleton; eauto.
            simpl. eapply In_Union_list. eapply in_map. eapply nthN_In. eassumption.
          - omega.
          - eassumption.
          - intros i. edestruct (Hstuck (i + cost1)) as [r' [m' Hstep']].
            inv Hstep'.
            * unfold cost1 in Hcost0. omega.
            * simpl in Hbs0. rewrite NPeano.Nat.add_sub in Hbs0.
              repeat subst_exp.
              do 2 eexists. eassumption.
          - repeat eexists; eauto. eapply Eval_proj_per_cc with (c := c2 + cost2); try eassumption.
            unfold cost2. simpl; omega. simpl. rewrite NPeano.Nat.add_sub.
            eassumption.
            eapply InvCompat_str with (c2' := cost1).
            unfold cost1, cost2. simpl. rewrite NPeano.Nat.add_sub. eassumption. 
            simpl; simpl in Hleq; omega.
            rewrite cc_approx_val_eq in *.
            eapply cc_approx_val_monotonic. eassumption.
            unfold cost1, cost2. simpl. simpl in Hcost. omega. }
    Qed.
    

    (** Case compatibility *)
    Lemma cc_approx_exp_case_nil_compat (k : nat) (H1 H2 : heap block) (rho1 rho2 : env) (x1 x2 : var) (c : nat) :
      c <= F * (cost (Ecase x1 [])) -> 
      (Ecase x1 [], rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi c ; IG) (Ecase x2 [], rho2, H2).
    Proof.
      intros Hleq H1' H2' rho1' rho2' v1 c1 m1 Heq1 Heq2 HII Hleq1 Hstep1 Hns. inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost. exists OOT, (c1 - c). eexists. repeat split. 
          - econstructor. simpl; omega. reflexivity. 
          - eapply InvCostTimeout.
            eassumption.
          - now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { simpl in Htag. discriminate. }
    Qed.
    
    Lemma cc_approx_exp_case_compat (k : nat) (H1 H2 : heap block) (rho1 rho2 : env) (x1 x2 : var) (t : cTag)
          (e1 e2 : exp) (Pats1 Pats2 : list (cTag * exp)) (r1 r2 : nat)
 
      (IInvCaseHdCompat :
         forall (H1 H2 : heap block) (rho1 rho2 : env),
           IIL1 (H1, rho1, Ecase x1 ((t, e1) :: Pats1)) (H2, rho2, Ecase x2 ((t, e2) :: Pats2)) ->
           IIL2 (H1, rho1, e1) (H2, rho2, e2))

      (IInvCaseTlCompat :
         forall (H1 H2 : heap block) (rho1 rho2 : env),
           IIL1 (H1, rho1, Ecase x1 ((t, e1) :: Pats1)) (H2, rho2, Ecase x2 ((t, e2) :: Pats2)) ->
           IIL1 (H1, rho1, Ecase x1 Pats1) (H2, rho2, Ecase x2 Pats2)) :
        
      cc_approx_var_env k IIG IG H1 rho1 H2 rho2 x1 x2 ->

      (r1 - r2) <= F * (cost (Ecase x1 Pats1)) -> 

      (forall i H1 H2 rho1 rho2,
         i < k -> 
         (e1, rho1, H1) ⪯ ^ (i ; IIL2 ; IIG ; ILi r2 ; IG) (e2, rho2, H2)) ->

      (Ecase x1 Pats1, rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi r1 ; IG) (Ecase x2 Pats2, rho2, H2) ->

      (Ecase x1 ((t, e1) :: Pats1), rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi r1 ; IG) (Ecase x2 ((t, e2) :: Pats2), rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hvar Hleq Hexp_hd Hexp_tl H1' H2' rho1' rho2' v1 c1 m1 Heq1 Heq2 HII Hleq1 Hstep1 Hstuck1.
      inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost. exists OOT, (c1 - r1). eexists. repeat split. 
          - econstructor. simpl; omega. reflexivity. 
          - eapply InvCostTimeout. eassumption.
          - now rewrite cc_approx_val_eq. }
      - { pose (cost1 := cost (Ecase x1 ((t, e1) :: Pats1))).
          pose (cost2 := costCC (Ecase x2 ((t, e2) :: Pats2))).
          eapply (cc_approx_var_env_heap_env_equiv
                    _ _
                    (occurs_free (Ecase x1 ((t, e1) :: Pats1)))
                    (occurs_free (Ecase x2 ((t, e2) :: Pats2)))) in Hvar;
          [| eassumption | eassumption
           | normalize_occurs_free; now eauto with Ensembles_DB | normalize_occurs_free; now eauto with Ensembles_DB ].
          edestruct Hvar as [l' [Hgety' Hcc]]; eauto.
          destruct l' as [l' |l' f ]; [| contradiction ].
          simpl in Hcc. rewrite Hgetl in Hcc.
          destruct (get l' H2') as [[ t' vs' | | ] |] eqn:Hgetl'; try contradiction.
          destruct Hcc as [Heq Hall']; subst. simpl in Hall', Hcost.
          simpl in Htag. destruct (M.elt_eq t t') eqn:Heq; subst.
          - inv Htag.
            edestruct Hexp_hd with (i := k - cost1) (c1 := c1 - cost1) as [v2 [c2 [m2 [Hstep [HS Hres]]]]]. 
            + unfold cost1; simpl; omega.
            + eapply heap_env_equiv_antimon. now eapply Heq1.
              normalize_occurs_free...
            + eapply heap_env_equiv_antimon. now eapply Heq2.
              normalize_occurs_free...
            + eapply IInvCaseHdCompat; eassumption.
            + unfold cost1. simpl; omega.
            + eassumption.
            + intros i. edestruct (Hstuck1 (i + cost1)) as [r' [m'' Hstep']].
              inv Hstep'.
              * exists OOT. eexists. econstructor; eauto. unfold cost1 in Hcost0.
               omega. 
              * repeat subst_exp.
                simpl in Htag; rewrite Heq in Htag; inv Htag.
                simpl in Hbs0. rewrite NPeano.Nat.add_sub in Hbs0.
                do 2 eexists. eassumption.
            + repeat eexists; eauto.
              * eapply Eval_case_per_cc with (c := c2 + cost2)
                ; [ | | | | rewrite NPeano.Nat.add_sub ]; try eassumption.
                unfold cost2. omega. now simpl; rewrite Heq. 
              * simpl. eapply InvCompat_str with (c2' := cost1).
                unfold cost2, cost1. simpl. rewrite NPeano.Nat.add_sub.
                eassumption. simpl; simpl in Hleq; omega.
              * rewrite cc_approx_val_eq. eapply cc_approx_val_monotonic.
                rewrite <- cc_approx_val_eq. eassumption. unfold cost1. simpl. omega.
          - edestruct Hexp_tl as [v2 [c2 [m2 [Hstep2 [HS Hpre2]]]]];
               [ | | | | now econstructor; eauto | | ].
            + eapply heap_env_equiv_antimon; [ eassumption |].
              normalize_occurs_free...
            + eapply heap_env_equiv_antimon; [ eassumption |].
              normalize_occurs_free...
            + eapply IInvCaseTlCompat; eassumption.
            + simpl in Hcost. omega.
            + intros i. edestruct (Hstuck1 i) as [r' [m'' Hstep']].
              inv Hstep'.
              * exists OOT. eexists. econstructor; eauto.
              * repeat subst_exp.
                simpl in Htag0; rewrite Heq in Htag0. repeat subst_exp.
                simpl in Hbs0.
                do 2 eexists. eapply Eval_case_gc.
                simpl in Hcost0. simpl. omega.
                eassumption. eassumption. eassumption. eassumption.
            + inv Hstep2.
              * (* Timeout! *)
                { simpl in Hcost0. exists OOT, c2. eexists. repeat split.
                  - econstructor. simpl. eassumption. reflexivity. 
                  - eassumption.
                  - eassumption. }
              * (* termination *)
                { repeat eexists; eauto.
                  - eapply Eval_case_per_cc with (c := c2); eauto.
                    simpl. repeat subst_exp.
                    rewrite Heq. eassumption.
                } }
    Qed.
    
    (** Halt compatibility *)
    Lemma cc_approx_exp_halt_compat (k : nat) (H1 H2 : heap block) (rho1 rho2 : env) (x1 x2 : var) (r : nat) :
      r <= F * (cost (Ehalt x1)) -> 
          
      cc_approx_var_env k IIG IG H1 rho1 H2 rho2 x1 x2 ->
      
      (Ehalt x1, rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi r ; IG) (Ehalt x2, rho2, H2).
    Proof.
      intros Hleq Hvar H1' H2' rho1' rho2' v1 c1 m1 HII Heq1 Heq2 Hleq1 Hstep1 Hstuck1.
      inv Hstep1.
      - (* Timeout! *)
        { simpl in Hcost. exists OOT, (c1 - r). eexists. repeat split. 
          - econstructor; eauto. simpl. omega.
          - rewrite <- plus_n_O. eapply InvCostTimeout.
            eassumption.
          - now rewrite cc_approx_val_eq. }
      - pose (cost1 := cost (Ehalt x1)).
        pose (cost2 := cost (Ehalt x2)).
        eapply (cc_approx_var_env_heap_env_equiv
                  _ _
                  (occurs_free (Ehalt x1))
                  (occurs_free (Ehalt x2))) in Hvar;
          [| eassumption | eassumption | now constructor | now constructor ]. 
        edestruct Hvar as [l' [Hgety' Hcc]]; eauto.
        eexists. exists c1. repeat eexists.
        * eapply Eval_halt_per_cc. simpl. simpl in Hcost. omega. eassumption.
          reflexivity.
        * eapply InvCostBase. eassumption. eassumption.
        * rewrite cc_approx_val_eq in *.
          eapply cc_approx_val_monotonic. eassumption.
          omega.
    Qed.

    (** XXX move/name *)
    Lemma heap_env_equiv_def_funs' (S : Ensemble var) (H1 H2 : heap block) 
          (rho1 rho2 : M.t value) (B B' : fundefs) : 
      S \\ (name_in_fundefs B) |- (H1, rho1) ⩪ (H2, rho2) ->
      S |- (H1, def_funs B B' rho1) ⩪ (H2, def_funs B B' rho2).
    Proof with now eauto with Ensembles_DB.
      revert S. induction B; simpl; intros S Heq.
      - eapply heap_env_equiv_set.
        + eapply IHB. eapply heap_env_equiv_antimon...
        + rewrite res_equiv_eq. simpl. split; eauto.
      - eapply heap_env_equiv_antimon...
    Qed.

    (** Abstraction compatibility *)
    Lemma cc_approx_exp_fun_compat (k : nat) rho1 rho2 H1 H2 B1 e1 B2 e2 r1 r2
          (IInvFunCompat :
             forall H1 H1' H1''  H2  rho1 rho1' rho1'' rho2 env_loc, 
               IIL1 (H1, rho1, Efun B1 e1) (H2, rho2, Efun B2 e2) ->
               restrict_env (fundefs_fv B1) rho1 = rho1' ->
               alloc (Env rho1') H1 = (env_loc, H1') ->
               def_closures B1 B1 rho1 H1' env_loc = (H1'', rho1'') ->
               IIL2 (H1'', rho1'', e1) (H2, def_funs B2 B2 rho2, e2)) :

      well_formed (reach' H1 (env_locs rho1 (occurs_free (Efun B1 e1)))) H1 ->
      (env_locs rho1 (occurs_free (Efun B1 e1))) \subset dom H1 ->
      

      fundefs_num_fv B1 <= (r1 - r2) <= F*(cost (Efun B1 e1)) -> 

      (forall i  H1 H1' H1'' rho1' rho_clo env_loc,
         i < k ->
         
         restrict_env (fundefs_fv B1) rho1 = rho_clo ->
         alloc (Env rho_clo) H1 = (env_loc, H1') ->

         def_closures B1 B1 rho1 H1' env_loc = (H1'', rho1') ->

         (e1, rho1', H1'') ⪯ ^ (i; IIL2 ; IIG ; ILi r2 ; IG)
         (e2, def_funs B2 B2 rho2, H2)) ->
      (Efun B1 e1, rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi r1 ; IG) (Efun B2 e2, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hwf Hdom Hleq Hpre H1' H2' rho1' rho2' v1 c1
             m1 Heq1 Heq2 HII Hleq1 Hstep1 Hstuck1.
      inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost. exists OOT, (c1 - r1).
          - eexists. repeat split. econstructor. simpl.
            omega. reflexivity.
            eapply InvCostTimeout. eassumption.
            now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { destruct (alloc (Env (restrict_env (fundefs_fv B1) rho1)) H1)
            as [env_loc3 H3] eqn:Ha3.
          destruct (def_closures B1 B1 rho1 H3 env_loc3)
            as [H3' rho3] eqn:Hdef3.
          edestruct Hpre with (i := k - cost (Efun B1 e1)) as [v2 [c2 [m2 [Hstep [HS Hval]]]]]
          ; [ | reflexivity | now apply Ha3 | now apply Hdef3 | | | | | eassumption | | ].
          - simpl in Hcost. simpl. omega.
          - assert (Hequiv : occurs_free_fundefs B1 :|: occurs_free e1 \\ name_in_fundefs B1 |- (H', rho1') ⩪ (H3, rho1)).
            { eapply heap_env_equiv_weaking_cor.
              * eapply well_formed_antimon;
                [| eapply well_formed_respects_heap_env_equiv; [ now apply Hwf | eassumption ] ].
                eapply reach'_set_monotonic.
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic.
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply Included_trans; [| eapply env_locs_in_dom; [ eassumption |]].
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
                eassumption.
              * eapply Included_trans; [| eassumption ].
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply heap_env_equiv_antimon. symmetry. eassumption.
                normalize_occurs_free. rewrite Setminus_Union_distr...
              * eapply HL.alloc_subheap. eassumption.
              * eapply HL.alloc_subheap. eassumption. }
            eapply heap_env_equiv_antimon with (S1 := occurs_free_fundefs B1 :|: occurs_free e1);
            [| now eauto with Ensembles_DB ].
            setoid_rewrite <- Hdef3. setoid_rewrite <- Hfuns. (* strange *)
            symmetry.
            eapply heap_env_equiv_def_funs. 
            + eapply closed_alloc'; [| | eassumption ].
              * eapply reach'_closed.
                eapply well_formed_respects_heap_env_equiv. now apply Hwf.
                eassumption.
                eapply env_locs_in_dom; eassumption.
              * eapply Included_trans; [| now eapply reach'_extensive ].
                simpl. eapply Included_trans.
                eapply restrict_env_env_locs.
                eapply restrict_env_correct.
                eapply fundefs_fv_correct.
                eapply env_locs_monotonic. normalize_occurs_free...
            + eapply closed_alloc'; [| | eassumption ].
              * eapply reach'_closed; eassumption.
              * eapply Included_trans; [| now eapply reach'_extensive ].
                simpl.
                simpl. eapply Included_trans.
                eapply restrict_env_env_locs.
                eapply restrict_env_correct.
                eapply fundefs_fv_correct.
                eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [| now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free.
              rewrite Setminus_Union_distr...
            + eapply Included_trans; [| now eapply reach'_extensive ].
              eapply env_locs_monotonic. normalize_occurs_free.
              rewrite Setminus_Union_distr...
            + eapply gas. eassumption.
            + eapply gas. eassumption.
            + eapply Included_trans; [| now eapply reach'_extensive ].
              simpl. eapply Included_trans.
              eapply restrict_env_env_locs.
              eapply restrict_env_correct.
              eapply fundefs_fv_correct.
              eapply env_locs_monotonic. normalize_occurs_free...
            + eapply Included_trans; [| now eapply reach'_extensive ].
              simpl. eapply Included_trans.
              eapply restrict_env_env_locs.
              eapply restrict_env_correct.
              eapply fundefs_fv_correct.
              eapply env_locs_monotonic. normalize_occurs_free...
            + rewrite Setminus_Union_distr, Setminus_Disjoint.
              now eauto with Ensembles_DB.
              eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
            + rewrite res_equiv_eq.
              simpl. erewrite !gas; try eassumption. simpl. 
              eapply heap_env_equiv_restrict_env with (S' := occurs_free_fundefs B1).
              * eapply heap_env_equiv_antimon. now apply Hequiv.
                rewrite Setminus_Union_distr, Setminus_Disjoint.
                eapply Included_Union_preserv_l. reflexivity.
                eapply Disjoint_sym. eapply occurs_free_fundefs_name_in_fundefs_Disjoint.
              * reflexivity.
              * eapply restrict_env_correct.
                eapply fundefs_fv_correct.
              * eapply restrict_env_correct.
                eapply fundefs_fv_correct.
            + eapply heap_env_equiv_weaking_cor.
              * eapply well_formed_antimon;
                [| eapply well_formed_respects_heap_env_equiv; [ now apply Hwf | eassumption ] ].
                eapply reach'_set_monotonic.
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply well_formed_antimon; [| eassumption ].
                eapply reach'_set_monotonic.
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply Included_trans; [| eapply env_locs_in_dom; [ eassumption |]].
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
                eassumption.
              * eapply Included_trans; [| eassumption ].
                eapply env_locs_monotonic. normalize_occurs_free.
                rewrite Setminus_Union_distr...
              * eapply heap_env_equiv_antimon. symmetry. eassumption.
                normalize_occurs_free. rewrite Setminus_Union_distr...
              * eapply HL.alloc_subheap. eassumption.
              * eapply HL.alloc_subheap. eassumption.
          - eapply heap_env_equiv_def_funs'.
            eapply heap_env_equiv_antimon. eassumption.
            normalize_occurs_free...
          - eapply IInvFunCompat; eauto.
          - simpl; omega.
          - intros i. edestruct (Hstuck1 (i + cost (Efun B1 e1))) as [r' [m' Hstep']].
            inv Hstep'.
            * omega.
            * rewrite NPeano.Nat.add_sub in Hbs0. repeat subst_exp.
              repeat eexists. eassumption.
          - repeat eexists; eauto.
            + eapply Eval_fun_per_cc with (c := c2 + costCC (Efun B2 e2)); try eassumption.
              simpl. omega. reflexivity. simpl.
              rewrite NPeano.Nat.add_sub. eassumption.
            + simpl. eapply InvCompat_str with (c2' := 1).
              rewrite NPeano.Nat.add_sub. eassumption.
              simpl. simpl in Hleq. omega. 
            + rewrite cc_approx_val_eq in *. 
              eapply cc_approx_val_monotonic. eassumption.
              simpl. simpl in Hcost. omega. }
    Qed.
    

    Variable
      (InvCompat1_str_gc :
         forall (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp)
           (k1 k2 c1 c2 c1' c2' m1 m2 : nat),

           IIL2 (H1, rho1, e1) (H2, rho2, e2) ->

           ILi k2 (c1 - c1', m1) (c2 - c2', m2) -> 

           c1' <= c2' + (k1 - k2) <= c1' + F*c1' ->

           ILi k1 (c1, max m1 (size_heap H1)) (c2, max m2 (size_heap H2))).
    
    Variable
      (IGinILi : inclusion _ IG (ILi 0)).

    Variable
      (IIL2inIIG : inclusion _ IIL2 IIG).

    Variable
      (II_gc :
         forall (H1 H2 H1' H2' : heap block) (rho1 rho2 : env) (e1 e2 : exp),
           IIL2 (H1, rho1, e1) (H2, rho2, e2) ->
           live (env_locs rho1 (occurs_free e1)) H1 H1' ->
           live (env_locs rho2 (occurs_free e2)) H2 H2' ->
           IIL2 (H1', rho1, e1) (H2', rho2, e2)).
    
    (** Application compatibility *)
    Lemma cc_approx_exp_app_compat (k : nat) (H1 H2 : heap block) (rho1 rho2 : env) (f1 : var) (xs1 : list var)
          (f2 f2' Γ : var) (xs2 : list var) (t : fTag) (c : nat)
          (IInvAppCompat :
             forall (H1 H2 H1' : heap block) (rho1 rho_clo rho_clo1 rho_clo2 rho2 rho2' : env)
               (B1 : fundefs) (f1 f1' : var) (ct1 : cTag) 
               (xs1 xs1' : list var) (e1 : exp) (l1 env_loc1 : loc)
               (vs1 : list value) 

               (B2 : fundefs) (f2 f3 : var) (c ct2 : cTag) (xs2 xs2' : list var) 
               (e2 : exp) (l2 env_loc2 : loc) (vs2 : list value),
               IIL1 (H1, rho1, Eapp f1 t xs1) (H2, rho2, AppClo f2 t xs2 f2' Γ) ->
               (* not exactly classy.... Can we make it a bit more abstract? *)
               M.get f1 rho1 = Some (Loc l1) ->
               get l1 H1 = Some (Clos (FunPtr B1 f1') (Loc env_loc1)) ->
               get env_loc1 H1 = Some (Env rho_clo) ->
               find_def f1' B1 = Some (ct1, xs1', e1) ->
               getlist xs1 rho1 = Some vs1 ->
               def_closures B1 B1 rho_clo H1 env_loc1 = (H1', rho_clo1) ->
               setlist xs1' vs1 rho_clo1 = Some rho_clo2 ->

               M.get f2 rho2 = Some (Loc l2) ->
               getlist xs2 rho2 = Some vs2 ->
               get l2 H2 = Some (Constr c [FunPtr B2 f3; Loc env_loc2]) ->
               Some rho2' =
               setlist xs2' (Loc env_loc2 :: vs2) (def_funs B2 B2 (M.empty value)) ->
               find_def f3 B2 = Some (ct2, xs2', e2) ->

               IIL2 (H1', rho_clo2, e1) (H2, rho2', e2)) :
      
      well_formed (reach' H1 (env_locs rho1 (occurs_free (Eapp f1 t xs1)))) H1 ->
      well_formed (reach' H2 (env_locs rho2 (occurs_free (AppClo f2 t xs2 f2' Γ)))) H2 ->
      (env_locs rho1 (occurs_free (Eapp f1 t xs1))) \subset dom H1 ->
      (env_locs rho2 (occurs_free (AppClo f2 t xs2 f2' Γ))) \subset dom H2 ->
      
      ~ Γ \in (f2 |: FromList xs2) ->
      ~ f2' \in (f2 |: FromList xs2) ->
      Γ <> f2' ->

      c + 3 <= F * (cost (Eapp f1 t xs1)) -> 
      length xs1 = length xs2 ->

      cc_approx_var_env k IIG IG H1 rho1 H2 rho2 f1 f2 ->
      Forall2 (cc_approx_var_env k IIG IG H1 rho1 H2 rho2) xs1 xs2 ->
      (* II (H1, rho1, Eapp f1 t xs1) (H2, rho2, AppClo f2 t xs2 f2' Γ)  -> *)
      (Eapp f1 t xs1, rho1, H1) ⪯ ^ (k ; IIL1 ; IIG ; ILi c ; IG) (AppClo f2 t xs2 f2' Γ, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hwf1 Hwf2 Hs1 Hs2 Hnin1 Hnin2 Hneq Hleqc Hlen Hvar Hall
             H1' H2' rho1' rho2' v1 c1 m1 Heq1 Heq2 HII Hleq1 Hstep1 Hstuck1.
      eapply (cc_approx_var_env_heap_env_equiv
                    _ _
                    (occurs_free (Eapp f1 t xs1))
                    (occurs_free (AppClo f2 t xs2 f2' Γ))) in Hvar;
          [| eassumption | eassumption 
           | normalize_occurs_free; now eauto with Ensembles_DB
           | unfold AppClo; normalize_occurs_free; now eauto with Ensembles_DB ].
      inv Hstep1.
      (* Timeout! *)
      - { simpl in Hcost.
          edestruct (Hstuck1 (cost (Eapp f1 t xs1))) as [v1 [m1 Hstep1]].
          inv Hstep1; [ omega | ].
          exists OOT, (c1 - c). destruct (lt_dec (c1 - c) 1).
          - eexists. repeat split. now constructor; eauto.
            rewrite <- plus_n_O.
            eapply InvCostTimeout.
            eassumption.
            now rewrite cc_approx_val_eq.
          - edestruct Hvar as [l2 [Hget' Hcc]]; eauto.
            simpl in Hcc. rewrite Hgetl in Hcc. destruct l2 as [l2 | ]; [| contradiction ]. 
            destruct (get l2 H2') as [v |] eqn:Hget2; try contradiction.
            simpl in Hcc.
            destruct v as [ ? [| [| B2 f3 ] [| [ env_loc' |] [|] ]] | | ]; try contradiction.
            edestruct Hcc with (vs2 := vs) as (xs2' & e2 & rho2'' & Hfind' & Hset' & Hi'); try eassumption.
            reflexivity. reflexivity.
            destruct (lt_dec (c1 - c - 1) 1).
            + eexists. repeat split. unfold AppClo.
              eapply Eval_proj_per_cc; eauto.
              simpl. omega. reflexivity.
              now econstructor; simpl; eauto.
              rewrite <- !plus_n_O.
              eapply InvCostTimeout. eassumption.
              now rewrite cc_approx_val_eq.
            + eexists. repeat split. unfold AppClo.
              eapply Eval_proj_per_cc; eauto.
              simpl. omega. reflexivity.
              eapply Eval_proj_per_cc; eauto.
              simpl. omega.
              rewrite M.gso. eassumption.
              intros Heq; subst. now eauto with Ensembles_DB.
              reflexivity.
              econstructor; simpl; eauto.
              erewrite <- Forall2_length; [| eassumption ]. omega.
              rewrite <- !plus_n_O.
              eapply InvCostTimeout. eassumption.
              now rewrite cc_approx_val_eq. }
      (* Termination *) 
      - { simpl in Hcost.
          eapply Forall2_monotonic_strong in Hall; (* yiiiiiikes *)
            [| intros x1 x2 Hin1 Hin2 Hyp;
               eapply (cc_approx_var_env_heap_env_equiv
                         _ _
                         (occurs_free (Eapp f1 t xs1))
                         (occurs_free (AppClo f2 t xs2 f2' Γ))) in Hyp;
               [ now eapply Hyp | eassumption | eassumption 
                 | normalize_occurs_free; now eauto with Ensembles_DB
                 | unfold AppClo; repeat normalize_occurs_free; rewrite FromList_cons ];
             right; constructor;
             [ right; constructor;
               [ now eauto with Ensembles_DB
               | now intros Hc; inv Hc; eapply Hnin1; eauto ]
             | now intros Hc; inv Hc; eapply Hnin2; eauto ] ].
          edestruct (cc_approx_var_env_getlist IIG IG k rho1' rho2') as [vs2 [Hgetl' Hcc']];
            [ eassumption | now eauto |].
          edestruct Hvar as [l2 [Hget' Hcc]]; eauto.
          simpl in Hcc. rewrite Hgetl in Hcc. destruct l2 as [l2 | ]; [| contradiction ]. 
          destruct (get l2 H2') as [v |] eqn:Hget2; try contradiction.
          simpl in Hcc.
          destruct v as [ ? [| [| B2 f3 ] [| [ env_loc' |] [|] ]] | | ]; try contradiction.
          edestruct Hcc as (xs2' & e2 & rho2'' & Hfind' & Hset' & Hi'); try eassumption.
          reflexivity. reflexivity.
          edestruct (live_exists (env_locs rho2'' (occurs_free e2)) H2') as [H2'' Hgc'].
          eapply Decidable_env_locs. now eauto with typeclass_instances. 
          edestruct Hi' with (i := k - cost (Eapp f1 t xs1)) as [r2 [c2 [m2 [Hbs2 [Hig Hcc2]]]]];
            [ | | | | | | eassumption | | ]. 
          + simpl. omega.
          + eapply Forall2_monotonic_strong; [| eassumption ].
            intros v v' Hinv Hinv' Heq. rewrite cc_approx_val_eq.
            eapply cc_approx_val_monotonic with (k := k).
            assert (Hrv : val_loc v \subset env_locs rho1' (occurs_free (Eapp f1 t xs1))).
            { normalize_occurs_free. rewrite env_locs_Union.
              eapply Included_Union_preserv_l. rewrite env_locs_FromList.
              simpl. eapply In_Union_list.
              eapply in_map. eassumption. eassumption. }
            assert (Hrv' : val_loc v' \subset env_locs rho2' (occurs_free (AppClo f2 t xs2 f2' Γ))).
            { unfold AppClo. repeat normalize_occurs_free.
              rewrite FromList_cons, !Setminus_Union_distr, !env_locs_Union.
              do 2 eapply Included_Union_preserv_r.
              eapply Included_Union_preserv_l. eapply Included_Union_preserv_r.
              rewrite !Setminus_Disjoint.
              rewrite env_locs_FromList.
              simpl. eapply In_Union_list.
              eapply in_map. eassumption. eassumption. 
              now eapply Disjoint_Singleton_r; intros Hc; eapply Hnin1; eauto.
              now eapply Disjoint_Singleton_r; intros Hc; inv Hc; eapply Hnin2; eauto. }
            eapply cc_approx_val_heap_monotonic;
              [ | | | | | now eapply HL.subheap_refl | ].
            * eapply well_formed_respects_heap_env_equiv in Hwf1; [| eassumption ].
              eapply well_formed_antimon; [| now apply Hwf1 ].
              now eapply reach'_set_monotonic.
            * eapply well_formed_respects_heap_env_equiv in Hwf2; [| eassumption ].
              eapply well_formed_antimon; [| now apply Hwf2 ].
              now eapply reach'_set_monotonic.
            * eapply Included_trans; [| eapply reachable_in_dom; try eassumption ].
              eapply Included_trans; [| now eapply reach'_extensive ].
              eassumption.
              eapply well_formed_respects_heap_env_equiv in Hwf1; [| eassumption ].
              eassumption.
              eapply env_locs_in_dom; eassumption.
            * eapply Included_trans; [| eapply reachable_in_dom; try eassumption ].
              eapply Included_trans; [| now eapply reach'_extensive ].
              eassumption.
              eapply well_formed_respects_heap_env_equiv in Hwf2; [| eassumption ].
              eassumption.
              eapply env_locs_in_dom; eassumption.
            * eapply def_funs_subheap. eauto.
            * eassumption.
            * simpl; omega.
          + eapply heap_env_equiv_heap_equiv.
            destruct Hgc as [? [? ?]]. eassumption.
          + eapply heap_env_equiv_heap_equiv.
            destruct Hgc' as [? [? ?]]. eassumption.
          + eapply IIL2inIIG.  
            eapply II_gc; [| eassumption | eassumption ].
            eapply IInvAppCompat; try eassumption.
          + simpl; omega.
          + intros i. edestruct (Hstuck1 (i + cost (Eapp f1 t xs1))) as [r' [m' Hstep']].
            inv Hstep'.
            * omega.
            * rewrite NPeano.Nat.add_sub in Hbs0. repeat subst_exp.
              eapply live_deterministic in Hgc0; [| now apply Hgc ].
              edestruct big_step_gc_heap_env_equiv as [r1 [m1 [Hgc1 _]]]. eassumption.
              eapply heap_env_equiv_heap_equiv. symmetry. eassumption.
              do 2 eexists. eassumption.
          + repeat eexists.
            * eapply Eval_proj_per_cc with (c := c2 + 1 + 1 + costCC (Eapp f2' t (Γ :: xs2))).
              simpl; omega.
              eassumption. eassumption. reflexivity.
              eapply Eval_proj_per_cc. simpl; omega.
              rewrite M.gso. eassumption.
              intros Hc. subst. eapply Hnin2. now left; eauto.
              eassumption. reflexivity.
              eapply Eval_app_per_cc. omega.
              rewrite M.gso. rewrite M.gss. reflexivity.
              now intros Hc; subst; eauto.
              eassumption.
              simpl. rewrite M.gss.
              rewrite !getlist_set_neq. now rewrite Hgetl'.
              intros Hc. eapply Hnin2. now eauto.
              intros Hc. eapply Hnin1. now eauto.
              now eauto. eassumption. reflexivity.
              replace (c2 + 1 + 1 + costCC (Eapp f2' t (Γ :: xs2))
                        - 1 - 1 - costCC (Eapp f2' t (Γ :: xs2))) with c2.
              eassumption. omega.
            * simpl.
              eapply InvCompat1_str_gc with (c2' := 1 + 1 + S (S (length xs2)));
                [ | | ].
              eapply IInvAppCompat; eassumption.
              replace (c2 + 1 + 1 + S (S (length xs2)) - (1 + 1 + S (S (length xs2)))) with c2 by omega. 
              eapply IGinILi. eassumption. simpl. rewrite <- !Hlen. simpl in Hleqc.
              omega.
            * rewrite cc_approx_val_eq in *. eapply cc_approx_val_monotonic.
              eassumption. simpl. omega. }
    Qed.
    
    Require Import L6.ctx.

    Fixpoint costCC_ctx_full (c : exp_ctx) : nat :=
      match c with
        | Econstr_c x t ys c => 1 + length ys + costCC_ctx_full c
        | Eproj_c x t n y c => 1 + costCC_ctx_full c
        | Efun1_c B c => 1 + costCC_ctx_full c (* XXX maybe revisit *)
        | Eprim_c x p ys c => 1 + length ys + costCC_ctx_full c
        | Hole_c => 0
        | Efun2_c _ _ => 0 (* maybe fix but not needed for now *)
        | Ecase_c _ _ _ _ _ => 0
      end.
    
    Fixpoint costCC_ctx (c : exp_ctx) : nat :=
      match c with
        | Econstr_c x t ys c => 1 + length ys
        | Eproj_c x t n y c => 1 
        | Efun1_c B c => 1
        | Eprim_c x p ys c => 1 + length ys
        | Hole_c => 0
        | Efun2_c _ _ => 0 (* maybe fix but not needed for now *)
        | Ecase_c _ _ _ _ _ => 0
      end.
    
   
    (* Interpretation of a context as a heap and an environment *) 
    Inductive ctx_to_heap_env : exp_ctx -> heap block -> env -> heap block -> env -> nat -> Prop :=
    | Hole_c_to_heap_env :
        forall H rho,
          ctx_to_heap_env Hole_c H rho H rho 0
    | Econstr_c_to_rho :
        forall H H' H'' rho rho' x t ys C vs l c,
          getlist ys rho = Some vs ->
          alloc (Constr t vs) H = (l, H') ->
          
          ctx_to_heap_env C H' (M.set x (Loc l) rho)  H'' rho'  c -> 
          
          ctx_to_heap_env (Econstr_c x t ys C) H rho H'' rho' (c + costCC_ctx (Econstr_c x t ys C))

    | Eproj_c_to_rho :
        forall H H' rho rho' x N t y C vs v t' l c,
          
          M.get y rho = Some (Loc l) ->
          get l H = Some (Constr t' vs) ->
          nthN vs N = Some v ->
          
          ctx_to_heap_env C H (M.set x v rho)  H' rho'  c -> 
          
          ctx_to_heap_env (Eproj_c x t N y C) H rho H' rho' (c + costCC_ctx (Eproj_c x t N y C)).


    Lemma comp_ctx_f_Hole_c C :
      comp_ctx_f C Hole_c = C
    with comp_f_ctx_f_Hole_c f : 
     comp_f_ctx_f f Hole_c = f.
    Proof.
      - destruct C; simpl; eauto;
        try (rewrite comp_ctx_f_Hole_c; reflexivity). 
        rewrite comp_f_ctx_f_Hole_c. reflexivity.
      - destruct f; simpl; eauto.
        rewrite comp_ctx_f_Hole_c; reflexivity.
        rewrite comp_f_ctx_f_Hole_c. reflexivity.
    Qed.
    

    Lemma cc_approx_exp_right_ctx_compat 
          (k : nat) rho1 rho2 rho2' H1 H2 H2' e1 C C' e2 c c' (II : exp_ctx -> IInv)
          (IInvCtxCompat :
             forall H1 H2 H2' rho1 rho2 rho2' e1 e2 C C' c, 
               II C' (H1, rho1, e1) (H2, rho2, C |[ e2 ]|) ->
               ctx_to_heap_env C H2 rho2 H2' rho2' c ->
               II (comp_ctx_f C' C) (H1, rho1, e1) (H2', rho2', e2)) :

      well_formed (reach' H1 (env_locs rho1 (occurs_free e1))) H1 ->
      well_formed (reach' H2 (env_locs rho2 (occurs_free (C |[ e2 ]|)))) H2 ->
      (env_locs rho1 (occurs_free e1)) \subset dom H1 ->
      (env_locs rho2 (occurs_free (C |[ e2 ]|))) \subset dom H2 ->

      ctx_to_heap_env C H2 rho2 H2' rho2' c' ->
      (e1, rho1, H1) ⪯ ^ (k; II (comp_ctx_f C' C) ; IIG ; ILi (c' + c) ; IG) (e2, rho2', H2') ->
      (e1, rho1, H1) ⪯ ^ (k ; II C' ; IIG ; ILi c ; IG) (C |[ e2 ]|, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hwf1 Hwf2 Henv1 Henv2 Hctx. revert c C'. induction Hctx; intros c1 C' Hpre.
      - intros ? ? ? ? ? ? ? ? ? ? ? ? ?. eapply Hpre; eauto.
        rewrite comp_ctx_f_Hole_c. eassumption.
      - rewrite <- plus_assoc in Hpre.
        replace (Econstr_c x t ys C) with (comp_ctx_f (Econstr_c x t ys Hole_c) C) in Hpre by reflexivity.
        rewrite <- comp_ctx_f_assoc with (c2 := Econstr_c x t ys Hole_c) in Hpre. 
        eapply IHHctx in Hpre.
        intros H1' H2' rho1' rho2' v1 k1 m1 Heq1 Heq2 HII Hleq1 Hstep1 Hstuck1.
        edestruct heap_env_equiv_env_getlist as [vs' [Hlst Hall]]; try eassumption.
        simpl. normalize_occurs_free...
        destruct (alloc (Constr t vs') H2') as [l2 H2''] eqn:Halloc.
        specialize (Hpre H1' H2'' rho1' (M.set x (Loc l2) rho2')).
        edestruct Hpre as [r1 [c3 [m2 [Hstep2 [Hinv Hccr]]]]]. 
        + eassumption.
        + eapply heap_env_equiv_alloc;
          [ | | | | | | | now apply H2 | now apply Halloc | ].
          eapply reach'_closed; try eassumption.
          eapply reach'_closed.
          eapply well_formed_respects_heap_env_equiv; eassumption.
          eapply env_locs_in_dom; eassumption.
          eapply Included_trans; [| now eapply reach'_extensive ].
          simpl. normalize_occurs_free.
          eapply env_locs_monotonic...
          eapply Included_trans; [| now eapply reach'_extensive ].
          simpl. normalize_occurs_free.
          eapply env_locs_monotonic...
          simpl.
          eapply Included_trans; [| now eapply reach'_extensive ].
          normalize_occurs_free. rewrite env_locs_Union.
          eapply Included_Union_preserv_l. rewrite env_locs_FromList.
          reflexivity. eassumption.
          simpl.
          eapply Included_trans; [| now eapply reach'_extensive ].
          normalize_occurs_free. rewrite env_locs_Union.
          eapply Included_Union_preserv_l. rewrite env_locs_FromList.
          reflexivity. eassumption.
          eapply heap_env_equiv_antimon. eassumption.
          simpl. normalize_occurs_free...
          split. reflexivity. eassumption.
        + eapply IInvCtxCompat with (C := Econstr_c x t ys Hole_c). eassumption. 
          econstructor. eassumption. eassumption. econstructor.
        + eassumption.
        + eassumption.
        + eassumption.
        + eexists. eexists (c3 + costCC (Econstr x t ys (C |[ e2 ]|))).
          eexists. split. simpl. eapply Eval_constr_per_cc; try eassumption.
          simpl. omega. simpl. rewrite NPeano.Nat.add_sub. eassumption.
          split; [| eassumption ].
          simpl. eapply InvTransfer. rewrite plus_comm.
          eassumption.
        + eapply well_formed_antimon with
          (S2 := reach' H' (env_locs (M.set x (Loc l) rho) (FromList ys :|: occurs_free (C |[ e2 ]|)))).
          eapply reach'_set_monotonic. eapply env_locs_monotonic...
          eapply well_formed_reach_alloc'; try eassumption.
          eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply env_locs_monotonic. 
          simpl. normalize_occurs_free... 
          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic. 
          simpl. normalize_occurs_free...
          eapply Included_trans; [| now eapply reach'_extensive ].
          rewrite env_locs_Union. 
          eapply Included_Union_preserv_l. rewrite env_locs_FromList.
          simpl. reflexivity. eassumption.
        + eapply Included_trans.
          eapply env_locs_set_Inlcuded'.
          rewrite HL.alloc_dom; try eassumption.
          eapply Included_Union_compat. reflexivity.
          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic. simpl. normalize_occurs_free...
      - rewrite <- plus_assoc in Hpre.
        replace (Eproj_c x t N y C) with (comp_ctx_f (Eproj_c x t N y Hole_c) C) in Hpre by reflexivity.
        rewrite <- comp_ctx_f_assoc with (c2 := Eproj_c x t N y Hole_c) in Hpre. 
        eapply IHHctx in Hpre.
        intros H1' H2' rho1' rho2' v1 k1 m1 Heq1 Heq2 HII Hleq1 Hstep1 Hstuck1.
        eapply Heq2 in H0; [| now constructor ].
        edestruct H0 as [l' [Hget' Heql]].
        rewrite res_equiv_eq in Heql. destruct l' as[l' |]; try contradiction.
        simpl in Heql. rewrite H2 in Heql. 
        destruct (get l' H2') eqn:Hgetl'; try contradiction.
        destruct b as [c' vs'| | ]; try contradiction.
        destruct Heql as [Heqt Hall]; subst.
        edestruct (Forall2_nthN _ vs vs' _ _ Hall H3) as [v' [Hnth' Hv]].
        specialize (Hpre H1' H2' rho1' (M.set x v' rho2')).
        edestruct Hpre as [r1 [c3 [m2 [Hstep2 [Hinv Hccr]]]]]. 
        + eassumption.
        + eapply heap_env_equiv_set; try eassumption.
          eapply heap_env_equiv_antimon. eassumption.
          simpl. normalize_occurs_free...
        + eapply IInvCtxCompat with (C := Eproj_c x t N y Hole_c). eassumption. 
          econstructor. eassumption. eassumption. eassumption. econstructor.
        + eassumption.
        + eassumption.
        + eassumption.
        + eexists. eexists (c3 + costCC_ctx (Eproj_c x t N y C)).
          eexists. split. simpl. eapply Eval_proj_per_cc; try eassumption.
          simpl. omega. simpl. rewrite NPeano.Nat.add_sub. eassumption.
          split; [| eassumption ].
          simpl. eapply InvTransfer. rewrite plus_comm. eassumption.
        + eapply well_formed_antimon with
          (S2 := reach' H (env_locs (M.set x v rho) ([set y] :|: occurs_free (C |[ e2 ]|)))).
          eapply reach'_set_monotonic. eapply env_locs_monotonic...
          eapply well_formed_reach_set'.
          eapply well_formed_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply env_locs_monotonic. 
          simpl. normalize_occurs_free...
          rewrite env_locs_Union, reach'_Union.
          eapply Included_Union_preserv_l. rewrite env_locs_Singleton; eauto.
          eapply Included_trans; [| eapply Included_post_reach' ].
          simpl. rewrite post_Singleton; eauto. simpl.
          eapply In_Union_list. eapply in_map.
          eapply nthN_In; eassumption.
        + eapply Included_trans.
          eapply env_locs_set_Inlcuded'.
          eapply Union_Included.
          eapply Included_trans; [| eapply reachable_in_dom; eassumption ].
          simpl. normalize_occurs_free. rewrite env_locs_Union, reach'_Union.
          eapply Included_Union_preserv_l. rewrite env_locs_Singleton; eauto.
          eapply Included_trans; [| eapply Included_post_reach' ].
          simpl. rewrite post_Singleton; eauto. simpl.
          eapply In_Union_list. eapply in_map.
          eapply nthN_In; eassumption.
          eapply Included_trans; [| eassumption ].
          eapply env_locs_monotonic. simpl. normalize_occurs_free...
    Qed.
    
    Definition size_reachable (S : Ensemble loc) (H1 : heap block) (s : nat ) : Prop :=
      exists H2, live S H1 H2 /\ size H2 = s. 


  End Compat.

End CC_log_rel.