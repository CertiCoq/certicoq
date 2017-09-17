(* Step-indexed logical relation for L6 closure conversion.
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2017
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util
                       List_util Heap.heap Heap.heap_defs Heap.space_sem.
From compcert Require Import lib.Coqlib.

Import ListNotations.

Module CC_log_rel (H : Heap).

  Module Sem := SpaceSem H.

  Import H Sem.Defs Sem.

  (** Global invariant *)
  Definition GInv :=
    nat -> (* The step index *)
    relation (heap block * env * exp * nat * nat).
  
  (** Local invariant *)
  (* XXX Same type as the GInv. Merge them at some point *)
  Definition Inv :=
    nat -> (* The step index *)
    relation (heap block * env * exp * nat * nat).

  (** Initial invariant *)
  Definition IInv :=
    relation (heap block * env * exp).
  
  (** Tag for closure records *)
  Variable (clo_tag : cTag). 
  
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
    
    Variable (cc_approx_val : nat -> GInv -> ans -> ans -> Prop). 

    (** * Expression relation *)

    Definition cc_approx_exp (k : nat) (P1 : Inv) (P2 : GInv)
               (p1 p2 : exp * env * heap block) : Prop :=
      let '(e1, rho1, H1) := p1 in
      let '(e2, rho2, H2) := p2 in
      forall (H1' H2' : heap block) (r1 : ans) (c1 m1 : nat),
        reach' H1 (env_locs rho1 (occurs_free e1)) |- H1 ≡ H1' ->
        reach' H2 (env_locs rho2 (occurs_free e2)) |- H2 ≡ H2' ->
        c1 <= k ->
        big_step_perfect_GC H1' rho1 e1 r1 c1 m1 ->
        exists (r2 : ans) (c2 m2 : nat),
          big_step_perfect_GC H2' rho2 e2 r2 c2 m2 /\
          (* extra invariants for costs *)
          P1 k (H1', rho1, e1, c1, m1) (H2', rho2, e2, c2, m2) /\
          cc_approx_val (k - c1) P2 r1 r2.
   
  End cc_approx.
  
  (** * Value relation *)

  Fixpoint cc_approx_val (k : nat) (P : GInv) (r1 r2 : ans) {struct k} : Prop :=
    match r1, r2 with
      | OOT, OOT => True (* Both programs timeout *)
      | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
        match v1, v2 with
          | Loc l1, Loc l2 =>
            exists c (vs1 vs2 : list value),
              get l1 H1 = Some (Vconstr c vs1) /\
              get l2 H2 = Some (Vconstr c vs2) /\
              match k with
                | 0 => True
                | S k =>
                  let R l1 l2 := cc_approx_val k P (Res (l1, H1)) (Res (l2, H2)) in
                  Forall2 R vs1 vs2
              end
          | FunPtr lf1 f1, Loc l2 =>
            exists rho1 B1 lf2 f2 venv rho2 B2,
              get lf1 H1 = Some (Vfun rho1 B1) /\
              get l2 H2 = Some (Vconstr clo_tag [(FunPtr lf2 f2) ; venv]) /\
              get lf2 H2 = Some (Vfun rho2 B2) /\
              forall (xs1 : list var) (ft : fTag) (e1 : exp)
                (rho1' : env) (vs1 vs2 : list value) (j : nat),
                find_def f1 B1 = Some (ft, xs1, e1) ->
                length vs1 = length vs2 ->
                Some rho1' = setlist xs1 vs1 (def_funs B1 lf1 rho1) ->
                exists (xs2 : list var) (e2 : exp) (rho2' : env),
                  find_def f2 B2 = Some (ft, xs2, e2) /\
                  Some rho2' = setlist xs2 (venv :: vs2) (def_funs B2 lf2 rho2) /\
                  match k with
                    | 0 => True
                    | S k =>
                      j < S k ->
                      (forall H1' H2',
                         let R v1 v2 := cc_approx_val (k - (k - j)) P (Res (v1, H1')) (Res (v2, H2')) in
                         reach' H1 [set lf1] |- H1 ≡ H1' ->
                         reach' H2 [set l2] |- H2 ≡ H2' ->
                         Forall2 R vs1 vs2 ->
                         cc_approx_exp cc_approx_val
                                       (k - (k - j))
                                       P P 
                                       (e1, rho1', H1') (e2, rho2', H2'))
                  end
          | _, _ => False
        end
      | _, _ => False
    end.
  

  (** Notations for approximation relation *)
  Notation "p1 ⪯ ^ ( k ; P1 ; P2 ) p2" :=
    (cc_approx_exp cc_approx_val k P1 P2 p1 p2)
      (at level 70, no associativity).


  (** Unfold the recursion. A more compact definition of the value relation. *)
  Definition cc_approx_val' (k : nat) (P : GInv) (r1 r2 : ans) : Prop :=
    match r1, r2 with
      | OOT, OOT => True (* Both programs timeout *)
      | Res (v1, H1), Res (v2, H2) => (* Both programs terminate *)
        match v1, v2 with
          | Loc l1, Loc l2 =>
            exists (c : cTag) (vs1 vs2 : list value),
              get l1 H1 = Some (Vconstr c vs1) /\
              get l2 H2 = Some (Vconstr c vs2) /\
              match k with
                | 0 => True
                | S k =>
                  let R l1 l2 := cc_approx_val k P (Res (l1, H1)) (Res (l2, H2)) in
                  Forall2 R vs1 vs2
              end
          | FunPtr lf1 f1, Loc l2 =>
            exists rho1 B1 lf2 f2 v_env rho2 B2,
              get lf1 H1 = Some (Vfun rho1 B1) /\
              get l2 H2 = Some (Vconstr clo_tag [(FunPtr lf2 f2) ; v_env]) /\
              get lf2 H2 = Some (Vfun rho2 B2) /\
              forall (xs1 : list var) (ft : fTag) (e1 : exp)
                (rho1' : env) (vs1 vs2 : list value) (j : nat),
                find_def f1 B1 = Some (ft, xs1, e1) ->
                length vs1 = length vs2 ->
                Some rho1' = setlist xs1 vs1 (def_funs B1 lf1 rho1) ->
                exists (xs2 : list var) (e2 : exp) (rho2' : env),
                  find_def f2 B2 = Some (ft, xs2, e2) /\
                  Some rho2' = setlist xs2 (v_env :: vs2) (def_funs B2 lf2 rho2) /\
                  (j < k ->
                   forall H1' H2',
                     reach' H1 [set lf1] |- H1 ≡ H1' ->
                     reach' H2 [set l2] |- H2 ≡ H2' ->
                     Forall2 (fun v1 v2 => cc_approx_val j P (Res (v1, H1')) (Res (v2, H2'))) vs1 vs2 ->
                     (e1, rho1', H1') ⪯ ^ (j ; P ; P) (e2, rho2', H2'))
          | _, _ => False

        end
      | _, _ => False
    end.
  
  (** Correspondence of the two definitions *)
  Lemma cc_approx_val_eq (k : nat) P (v1 v2 : ans) :
    cc_approx_val k P v1 v2 <-> cc_approx_val' k P v1 v2.
  Proof.
    destruct k as [ | k ];
    destruct v1 as [[[l1 | lf1 f1] H1] | |]; destruct v2 as [[[l2 | lf2 f2] H2] | |];
    try (now split; intros; contradiction);
    try (now simpl; eauto).
    - split;
      (intros Hyp;
       destruct Hyp
         as (rho1 & B1 & lf2 & f2 & v_env & rho2 & B2 & Hget & Hgetl2 & Hgetlf2  & Hyp');
       do 7 eexists; split; [ | split; [| split ] ]; (try now eauto);
       intros xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset;
       destruct (Hyp' xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset)
         as (xs2 & e2 & rho2' & Hfind' & Hset' & HT);
       do 3 eexists; repeat split; now eauto). 
    - split;
      (intros Hyp;
       destruct Hyp
         as (rho1 & B1 & lf2 & f2 & v_env & rho2 & B2 & Hget & Hgetl2 & Hgetlf2  & Hyp');
       do 7 eexists; split; [ | split; [| split ] ]; (try now eauto);
       intros xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset;
       destruct (Hyp' xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset)
         as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi);
       do 3 eexists; repeat split; try now eauto).
      intros Hlt H1' H2' HH1 HH2 Hall.
      assert (Heq : k - (k - j) = j) by omega. rewrite !Heq in Hi.
      eapply Hi. omega. eassumption. eassumption. eassumption.
      intros Hlt H1' H2' R HH1 HH2 Hall.
      assert (Heq : k - (k - j) = j) by omega. unfold R in *. rewrite !Heq in *.
      eapply Hi. omega. eassumption. eassumption. eassumption.
  Qed.
  
  Opaque cc_approx_val.
  
  (** * Environment relations *)
  
  (** Environment relation for a single point (i.e. variable) : 
   * ρ1 ~_k^x ρ2 iff ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition cc_approx_var_env (k : nat) P (H1 : heap block) (rho1 : env)
             (H2 : heap block) (rho2 : env) (x y : var) : Prop :=
    forall l1, 
      M.get x rho1 = Some l1 -> 
      exists l2, M.get y rho2 = Some l2 /\
            cc_approx_val' k P (Res (l1, H1)) (Res (l2, H2)).
  
  (** Environment relation for a set of points (i.e. predicate over variables) :
    * ρ1 ~_k^S ρ2 iff 
    *  forall x, S x -> ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition cc_approx_env_P (S : Ensemble var) k P (c1 c2 : heap block * env) :=
    let (H1, rho1) := c1 in
    let (H2, rho2) := c2 in
    forall (x : var), S x -> cc_approx_var_env k P H1 rho1 H2 rho2 x x.
  
  Notation "p1 ≺ ^ ( k ; P ) p2" := (cc_approx_val' k P p1 p2)
                                      (at level 70, no associativity).

  Notation "p1 ⋞ ^ ( R ; k ; P ) p2" := (cc_approx_env_P R k P p1 p2)
                                          (at level 70, no associativity).

  
  (** Environment relation for the whole domain of definition :
    * ρ1 ~_k ρ2 iff forall x, ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
  Definition cc_approx_env (k : nat) P c1 c2 : Prop :=
    c1 ⋞ ^ (Full_set _; k; P) c2.

  (** * Environment Invariants for Closure Conversion *)
  
  (** Naming conventions in the following :

     [Scope] : The set of variables currently in scope.
 
     [Funs]  : The set of variables in the current block of mutually recursive
               functions.

     [FVs]   : The list of free variables (needs to be ordered).

     [Γ]     : The formal parameter of the environment after closure conversion. *)
  
  (** Invariant about the free variables *) 
  Definition FV_inv (k : nat) (P : GInv)
             (rho1 : env) (H1 : heap block) (rho2 : env) (H2 : heap block)
             (Scope Funs : Ensemble var) (c : cTag) (Γ : var) (FVs : list var) : Prop :=
    forall (x : var) N (v : value),
      ~ In _ Scope x ->
      ~ In _ Funs x -> 
      nthN FVs N = Some x ->
      M.get x rho1 = Some v ->
      exists (vs : list value) (l : loc) (v' : value),
        M.get Γ rho2 = Some (Loc l) /\
        get l H2 = Some (Vconstr c vs) /\
        nthN vs N = Some v' /\
        (Res (v, H1)) ≺ ^ ( k ; P ) (Res (v', H2)).
  
  (** Invariant about the functions in the current function definition *)
  Definition Fun_inv (k : nat) (P : GInv)
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
          get l_clo H1 = Some (Vconstr c (vf1 :: venv :: vs)) ->
          (Res (vf1, H1)) ≺ ^ ( k ; P ) (Res (Loc l_clo, H2)).
  
  (** * Monotonicity Properties *)

  (** The environment relation is antimonotonic in the set of free variables *) 
  Lemma cc_approx_env_P_antimon (S1 S2 : Ensemble var) (k : nat)
        (P : GInv) (c1 c2 : (heap block) * env) :
    c1 ⋞ ^ ( S2 ; k ; P ) c2 ->
    S1 \subset S2 ->
    c1 ⋞ ^ ( S1 ; k ; P ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre Hin x Hin'. eapply Hpre; eapply Hin; eauto.
  Qed.
  
  (** The expression relation is monotonic in the local invariant *)
  Lemma cc_approx_exp_rel_mon k (P1 P1' : Inv) (P2 : GInv) p1 p2 :
    p1 ⪯ ^ ( k ; P1 ; P2 ) p2 ->
    (forall i, inclusion _ (P1 i) (P1' i)) ->
    p1 ⪯ ^ ( k ; P1' ; P2 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2].
    intros Hcc Hin H1' H2' v1 c1 m1 HH1 HH2 Hleq Hstep.
    edestruct Hcc as [v2 [c2 [m2 [Hstep' [HInv Hval]]]]]; eauto.
    repeat eexists; eauto. eapply Hin. eassumption.
  Qed.
  
  (** The logical relation respects equivalence of the global invariant *)
  
  Lemma cc_approx_exp_same_rel_IH k (P1 : Inv) (P2 P2' : GInv) p1 p2 :
    (forall m r1 r2,
       m <= k ->
       r1 ≺ ^ (m; P2) r2 ->
       r1 ≺ ^ (m; P2') r2) ->
    p1 ⪯ ^ ( k ; P1 ; P2 ) p2 ->
    (forall n, same_relation _ (P2 n) (P2' n)) ->
    p1 ⪯ ^ ( k ; P1 ; P2' ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2].
    intros IH Hcc Hin H1' H2' v1 c1 m1 HH1 HH2 Hleq Hstep.
    edestruct Hcc as [v2 [c2 [m2 [Hstep2 [HP Hval]]]]]; eauto.
    repeat eexists; eauto.
    rewrite cc_approx_val_eq.
    eapply IH; eauto. omega.
    rewrite <- cc_approx_val_eq; eauto.    
  Qed.
  
  Opaque cc_approx_exp.

  Lemma cc_approx_val_same_rel (k : nat) (P1 P2 : GInv) r1 r2 :
    r1 ≺ ^ (k; P1) r2 ->
    (forall n, same_relation _ (P1 n) (P2 n)) ->
    r1 ≺ ^ (k; P2) r2.
  Proof.
    revert k P1 P2 r1 r2. induction k as [k IHk] using lt_wf_rec1.
    intros P1 P2 r1 r2 Hyp HR.
    destruct k as [ | k ];
    destruct r1 as [[[l1 | lf1 f1] H1] | |]; destruct r2 as [[[l2 | lf2 f2] H2] | |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    - destruct Hyp
        as (rho1 & B1 & lf2 & f2 & v_env & rho2 & B2 & Hget & Hgetl2 & Hgetlf2  & Hyp');
      do 7 eexists; split; [ | split; [| split ] ]; (try now eauto);
      intros xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset;
      destruct (Hyp' xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset)
        as (xs2 & e2 & rho2' & Hfind' & Hset' & HT);
      do 3 eexists; repeat split; now eauto.
    - destruct Hyp as [c [vs1 [vs2 [Hget1 [Hget2 Hall]]]]]; repeat eexists; eauto.
      eapply Forall2_monotonic; [| eassumption ].
      intros. rewrite cc_approx_val_eq in *. eapply IHk; eauto. 
    - destruct Hyp
        as (rho1 & B1 & lf2 & f2 & v_env & rho2 & B2 & Hget & Hgetl2 & Hgetlf2 & Hyp');
      do 7 eexists; split; [ | split; [| split ] ]; (try now eauto);
      intros xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset;
      destruct (Hyp' xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset)
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi);
      do 3 eexists; repeat split; try now eauto.
      intros Hlt H1' H2' HH1 HH2 Hall.
      eapply cc_approx_exp_same_rel_IH with (P2 := P1) (P2' := P2);
        try eassumption. 
      + intros; eapply IHk. omega. eassumption. eassumption.
      + eapply cc_approx_exp_rel_mon. eapply Hi; eauto.
        eapply Forall2_monotonic; [| eassumption ].
        intros. rewrite cc_approx_val_eq.
        eapply IHk; eauto. now rewrite <- cc_approx_val_eq; simpl in *; eauto.
        now intros n; destruct (HR n); split; eauto.
        intros i [[[[? ?] ?] ?] ?] [[[[? ?] ?] ?] ?] HP1. eapply HR.
        eassumption.
  Qed.
  
  Transparent cc_approx_exp.

  Lemma cc_approx_exp_same_rel (P : relation nat) k (P1 : Inv) (P2 P2' : GInv)
        p1 p2 :
    p1 ⪯ ^ ( k ; P1 ; P2 ) p2 ->
    (forall n, same_relation _ (P2 n) (P2' n)) ->
    p1 ⪯ ^ ( k ; P1 ; P2' ) p2.
  Proof.
    intros Hcc Hin. eapply cc_approx_exp_same_rel_IH; try eassumption.
    intros. eapply cc_approx_val_same_rel; eauto.
  Qed.
  
  (** The value relation is monotonic in the step index *)
  Lemma cc_approx_val_monotonic (k m : nat) (P : GInv) (r1 r2 : ans) :
    r1 ≺ ^ (k; P) r2 ->
    m <= k ->
    r1 ≺ ^ (m; P) r2.
  Proof.
    revert m P r1 r2. induction k as [k IHk] using lt_wf_rec1.
    intros m P r1 r2 Hyp Hrel.
    destruct k as [ | k ];
    destruct r1 as [[[l1 | lf1 f1] H1] | |]; destruct r2 as [[[l2 | lf2 f2] H2] | |]; simpl;
    try (now intros; contradiction); try (now simpl; eauto).
    - destruct Hyp as [c [vs1 [vs2 [Hget1 [Hget2 Hall]]]]];
      repeat eexists; eauto. destruct m; eauto. omega.
    - destruct Hyp
        as (rho1 & B1 & lf2 & f2 & v_env & rho2 & B2 & Hget & Hgetl2 & Hgetlf2  & Hyp');
      do 7 eexists; split; [ | split; [| split ] ]; (try now eauto);
      intros xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset;
      destruct (Hyp' xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset)
        as (xs2 & e2 & rho2' & Hfind' & Hset' & HT);
      do 3 eexists; repeat split; try now eauto.
      intros. omega.
    - destruct Hyp as [c [vs1 [vs2 [Hget1 [Hget2 Hall]]]]];
      repeat eexists; eauto.
      destruct m; [ now eauto | ]. eapply Forall2_monotonic; [| eassumption ].
      intros. rewrite cc_approx_val_eq in *. eapply IHk; [| eassumption |]; omega. 
    - destruct Hyp
        as (rho1 & B1 & lf2 & f2 & v_env & rho2 & B2 & Hget & Hgetl2 & Hgetlf2 & Hyp');
      do 7 eexists; split; [ | split; [| split ] ]; (try now eauto);
      intros xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset;
      destruct (Hyp' xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset)
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi);
      do 3 eexists; repeat split; try now eauto.
      intros Hlt' HH Hall; intros.
      eapply Hi; eauto. omega.
  Qed.

  Section IndexMon.

    Variable (P1 : Inv).
    Variable (P2 : GInv).

    (** The invariants are antimonotonic in the step index *)
    Variable (InvIndMon : forall n m, m <= n -> inclusion _ (P1 n) (P1 m)).
    Variable (GInvIndMon : forall n m, m <= n -> inclusion _ (P1 n) (P1 m)).
    
    (** The expression relation is anti-monotonic in the step index *)
    Lemma cc_approx_exp_monotonic (k j : nat) p1 p2 :
      p1 ⪯ ^ ( k ; P1 ; P2 ) p2 ->
      j <= k ->
      p1 ⪯ ^ ( j ; P1 ; P2 ) p2.
    Proof.
      destruct p1 as [[e1 H1] rho1]; destruct p2 as [[e2 H2] rho2].
      intros Hpre Hleq H1' H2' v1 c1 m1 HH1 HH2 Hleq' Hstep.
      edestruct (Hpre H1' H2' v1 c1)
        as [v2 [c2 [m2 [Hstep2 [Hleq2 H3]]]]]; eauto.
      omega. do 3 eexists; repeat split; eauto.
      eapply InvIndMon; [| eassumption ]. omega.
      rewrite cc_approx_val_eq in *.
      eapply cc_approx_val_monotonic; eauto. omega.
    Qed.

  End IndexMon.

  (** The environment relations are anti-monotonic in the step index *)
  Lemma cc_approx_env_P_monotonic (R : Ensemble var) (k j : nat) (P : GInv)
        c1 c2 :
    c1 ⋞ ^ ( R ; k ; P ) c2 ->
    j <= k ->
    c1 ⋞ ^ ( R ; j ; P ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hcc Hleq x HP v Hget.
    edestruct Hcc as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto.
    eapply cc_approx_val_monotonic; eauto.
  Qed.
  
  Lemma cc_approx_env_monotonic (k j : nat) (P : GInv) c1 c2 :
    cc_approx_env k P c1 c2 ->
    j <= k ->
    cc_approx_env j P c1 c2.
  Proof.
    intros Hleq H. eapply cc_approx_env_P_monotonic; eauto.
  Qed.
  
  (** * Proper Instances *)

  Global Instance cc_approx_env_proper_set :
    Proper (Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           cc_approx_env_P.
  Proof.
    intros s1 s2 [H1 H2]; split; intros Hpre;
    eapply cc_approx_env_P_antimon; subst; eauto.
  Qed.

  (** * Set lemmas *)

  Lemma cc_approx_env_Empty_set (k : nat) (P : GInv) c1 c2 :
    c1 ⋞ ^ ( Empty_set var ; k ; P ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    firstorder.
  Qed.

  Lemma cc_approx_env_P_union (P1 P2 : Ensemble var) (k : nat) (P : GInv) c1 c2 :
    c1 ⋞ ^ ( P1 ; k ; P ) c2 ->
    c1 ⋞ ^ ( P2 ; k ; P ) c2 ->
    c1 ⋞ ^ ( P1 :|: P2 ; k ; P ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre1 Hpre2 x HP2. inv HP2; eauto.
  Qed.
  
  Lemma cc_approx_env_P_inter_l (P1 P2 : Ensemble var) (k : nat) (P : GInv) c1 c2 :
    c1 ⋞ ^ ( P1 ; k ; P ) c2 ->
    c1 ⋞ ^ ( P1 :&: P2 ; k ; P ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre x HP2. inv HP2; eauto.
  Qed.
  
  Lemma cc_approx_env_P_inter_r (P1 P2 : Ensemble var) (k : nat) (P : GInv) c1 c2 :
    c1 ⋞ ^ ( P2 ; k ; P ) c2 ->
    c1 ⋞ ^ ( P1 :&: P2 ; k ; P ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre x HP2. inv HP2; eauto.
  Qed.
  
  (** * Preservation under enviroment extension lemmas *)

  Lemma cc_approx_var_env_set_eq :
    forall (k : nat) (P : GInv) (rho1 rho2 : env) (H1 H2 : heap block)
      (x y : var) (v1 v2 : value),
      (Res (v1, H1)) ≺ ^ (k; P) (Res (v2, H2)) ->
      cc_approx_var_env k P H1 (M.set x v1 rho1) H2 (M.set y v2 rho2) x y.
  Proof.
    intros rho1 rho2 H1 H2 k P x y v1 v2 Hval x' Hget.
    rewrite M.gss in Hget. inv Hget. eexists.
    rewrite M.gss. split; eauto.
  Qed.
  
  Lemma cc_approx_var_env_set_neq :
    forall (k : nat) (P : GInv)  (rho1 rho2 : env) (H1 H2 : heap block)
      (x1 x2 y1 y2 : var) (v1 v2 : value),
      cc_approx_var_env k P H1 rho1 H2 rho2 y1 y2 ->
      y1 <> x1 -> y2 <> x2 ->
      cc_approx_var_env k P H1 (M.set x1 v1 rho1) H2 (M.set x2 v2 rho2) y1 y2.
  Proof. 
    intros k P rho1 rho2 H1 H2 x1 x2 y1 y2 v1 v2 Hval Hneq Hneq' x' Hget.
    rewrite M.gso in *; eauto.
  Qed.
  
  Lemma cc_approx_var_env_set :
    forall (k : nat) (P : GInv)  (rho1 rho2 : env) (H1 H2 : heap block)
      (x y : var) (v1 v2 : value),
      cc_approx_var_env k P H1 rho1 H2 rho2 y y ->
      (Res (v1, H1)) ≺ ^ (k; P) (Res (v2, H2)) ->
      cc_approx_var_env k P H1 (M.set x v1 rho1) H2 (M.set x v2 rho2) y y.
  Proof.
    intros k P rho1 rho2 H1 H2 x y v1 v2 Hvar Hval.
    destruct (peq y x); subst.
    - apply cc_approx_var_env_set_eq; eauto.
    - apply cc_approx_var_env_set_neq; eauto.
  Qed.
  
  (** Extend the related environments with a single point *)
  Lemma cc_approx_env_P_set (S : Ensemble var) (k : nat) (P : GInv)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v1 v2 : value) :
      (H1, rho1) ⋞ ^ ( S \\ [set x] ; k ; P ) (H2, rho2) ->
      (Res (v1, H1)) ≺ ^ (k; P) (Res (v2, H2)) ->
      (H1, M.set x v1 rho1) ⋞ ^ ( S; k ; P ) (H2, M.set x v2 rho2).
  Proof.
    intros Henv Hval x' HP v1' Hget.
    rewrite M.gsspec in Hget. destruct (peq x' x); subst.
    - inv Hget. eexists. rewrite M.gss. split; eauto.
    - apply Henv in Hget; eauto. destruct Hget as [v2' [Heq Hpre]].
      eexists; split; eauto. rewrite M.gso; eauto. constructor; eauto.
      intros Hin. inv Hin. congruence.
  Qed.
  
  (** Extend the related environments with a list *)
  Lemma cc_approx_env_P_setlist_l (S : Ensemble var) (k : nat) (P : GInv)
        (rho1 rho2 rho1' rho2' : env) (H1 H2 : heap block) xs (vs1 vs2 : list value) :
    (H1, rho1) ⋞ ^ ( S \\ (FromList xs) ; k ; P ) (H2, rho2) ->
    Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k; P) (Res (v2, H2))) vs1 vs2 ->
    setlist xs vs1 rho1 = Some rho1' ->
    setlist xs vs2 rho2 = Some rho2' ->
    (H1, rho1') ⋞ ^ ( S ; k ; P ) (H2, rho2').
  Proof.
    intros Hcc Hall Hset1 Hset2 x HP v Hget.
    destruct (in_dec var_dec x xs).
    - edestruct (@setlist_Forall2_get value) as [v1 [v2 [Hget1 [Hget2 HP']]]];
      try eassumption.
      rewrite Hget in Hget1. inv Hget1. repeat eexists; eauto.
    - erewrite <- setlist_not_In in Hget; eauto.
      edestruct Hcc as [v2 [Hget' Hpre']]; eauto.
      constructor; eauto. repeat eexists; eauto.
      erewrite <- setlist_not_In; eauto.
  Qed.
  
  Lemma cc_approx_env_P_set_not_in_P_l (S : Ensemble var) (k : nat) (P : GInv)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v : value) :
    (H1, rho1) ⋞ ^ ( S ; k ; P ) (H2, rho2) ->
    ~ x \in S ->
    (H1, M.set x v rho1) ⋞ ^ ( S; k ; P ) (H2, rho2).
  Proof. 
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    destruct (peq y x); subst.
    - contradiction.
    - rewrite M.gso in Hget; eauto.
  Qed.
  
  Lemma cc_approx_env_P_set_not_in_P_r (S : Ensemble var) (k : nat) (P : GInv)
        (rho1 rho2 : env) (H1 H2 : heap block) (x : var) (v : value) :
    (H1, rho1) ⋞ ^ ( S ; k ; P ) (H2, rho2) ->
    ~ x \in S ->
    (H1, rho1) ⋞ ^ ( S ; k ; P ) (H2, M.set x v rho2).
  Proof. 
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    exists v''. rewrite M.gsspec.
    destruct (peq y x); subst.
    - contradiction.
    - eauto.
  Qed.
  
  (** * The logical relation respects heap equality *)

  Lemma cc_approx_val_heap_eq (k : nat) (P : GInv) (H1 H2 H1' H2' : heap block)
        (v1 v2 : value) :
    (Res (v1, H1)) ≺ ^ (k; P) (Res (v2, H2)) ->
    reach' H1 [set (val_loc v1)] |- H1 ≡ H1' ->
    reach' H2 [set (val_loc v2)] |- H2 ≡ H2' ->
    (Res (v1, H1')) ≺ ^ (k; P) (Res (v2, H2')).
  Proof with now eauto with Ensembles_DB.
    revert P H1 H2 H1' H2' v1 v2. induction k as [k IHk] using lt_wf_rec1.
    intros P H1 H2 H1' H2' v1 v2 Hyp Heq1 Heq2.
    destruct k as [ | k ];
    destruct v1 as [l1 | lf1 f1]; destruct v2 as [l2 | lf2 f2];
    try (now intros; contradiction).
    - destruct Hyp as [c [vs1 [vs2 [Hget1 [Hget2 Hall]]]]].
      rewrite Heq1 in Hget1; [| now apply reach'_extensive ].
      repeat eexists; eauto.
      rewrite <- Heq2; [ eassumption | now apply reach'_extensive ].
    - destruct Hyp
        as (rho1 & B1 & lf2 & f2 & v_env & rho2 & B2 & Hget & Hgetl2 & Hgetlf2 & Hyp').
      rewrite Heq1 in Hget; [| now apply reach'_extensive ].
      do 7 eexists; split; [ | split; [| split] ]; (try now eauto).
      rewrite <- Heq2; [ eassumption | now apply reach'_extensive ].
      rewrite <- Heq2; [ eassumption | ].
      rewrite reach_unfold. right. eapply reach'_extensive.
      repeat eexists; eauto. simpl. rewrite FromList_cons...
      intros xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset;
      destruct (Hyp' xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset)
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi).
      do 3 eexists; repeat split; try now eauto.
    - destruct Hyp as [c [vs1 [vs2 [Hget1 [Hget2 Hall]]]]].
      rewrite Heq1 in Hget1; [| now apply reach'_extensive ].
      repeat eexists; eauto.
      rewrite <- Heq2; [ eassumption | now apply reach'_extensive ].
      eapply Forall2_monotonic_strong; [| eassumption ].
      intros. rewrite cc_approx_val_eq in *. eapply IHk; try eassumption.
      omega.
      eapply heap_eq_antimon; [| eassumption ]. rewrite (reach_unfold _ [set l1]).
      eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
      eapply Singleton_Included. repeat eexists; eauto. simpl.
      rewrite Heq1; [ eassumption | now apply reach'_extensive ].
      simpl. rewrite FromList_map_image_FromList. now eexists; split; eauto.
      eapply heap_eq_antimon; [| eassumption ]. rewrite (reach_unfold _ [set l2]).
      eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
      eapply Singleton_Included. repeat eexists; eauto. simpl.
      rewrite FromList_map_image_FromList. now eexists; split; eauto.
    - destruct Hyp
        as (rho1 & B1 & lf2 & f2 & v_env & rho2 & B2 & Hget & Hgetl2 & Hgetlf2 & Hyp').
      rewrite Heq1 in Hget; [| now apply reach'_extensive ].
      do 7 eexists; split; [ | split; [| split] ]; (try now eauto).
      rewrite <- Heq2; [ eassumption | now apply reach'_extensive ].
      rewrite <- Heq2; [ eassumption | ].
      rewrite reach_unfold. right. eapply reach'_extensive.
      repeat eexists; eauto. simpl. rewrite FromList_cons...
      intros xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset;
      destruct (Hyp' xs1 ft e1 rho1' vs1 vs2 j Hfind Hlen Hset)
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi).
      do 3 eexists; repeat split; try now eauto.
      assert (Hr1 : reach' H1 (env_locs rho1 (occurs_free_fundefs B1)) |- H1 ≡ H1').
      { eapply heap_eq_antimon; [| eassumption ].
        rewrite (reach_unfold _ [set lf1]). eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. intros l1 Henv.
        repeat eexists; try eassumption.
        rewrite Heq1; [ eassumption | now apply reach'_extensive ].
        eassumption. }
      assert (Hr2 : reach' H2 (env_locs rho2 (occurs_free_fundefs B2)) |- H2 ≡ H2').
      { eapply heap_eq_antimon; [| eassumption ].
        rewrite (reach_unfold _ [set l2]). eapply Included_Union_preserv_r.
        rewrite (reach_unfold _ (post H2 [set l2])).
        eapply Included_Union_preserv_r. eapply reach'_set_monotonic.
        intros l1 Henv. 
        repeat eexists; try eassumption. simpl. rewrite FromList_cons... }
      intros Hlt H1'' H2'' HH1 HH2. eapply Hi. omega.
      rewrite <- reach'_heap_eq in HH1; try eassumption.
      eapply Equivalence_Transitive; eassumption.
      rewrite <- reach'_heap_eq in HH2; try eassumption.
      eapply Equivalence_Transitive; eassumption.
  Qed.

  Lemma cc_approx_var_env_heap_eq (k : nat) (P : GInv)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 : env) (x y : var):
    cc_approx_var_env k P H1 rho1 H2 rho2 x y ->
    reach' H1 (env_locs rho1 [set x]) |- H1 ≡ H1' ->
    reach' H2 (env_locs rho2 [set y]) |- H2 ≡ H2' ->
    cc_approx_var_env k P H1' rho1 H2' rho2 x y.
  Proof.
    intros Henv Heq1 Heq2 v Hget.
    edestruct Henv as [v2 [Hget' Hval]]; eauto.
    eexists; split; eauto. eapply cc_approx_val_heap_eq.
    eassumption.
    eapply heap_eq_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply Singleton_Included.
    eexists; split; eauto. rewrite Hget. reflexivity.
    eapply heap_eq_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply Singleton_Included.
    eexists; split. eauto. rewrite Hget'. reflexivity.
  Qed.

  Lemma cc_approx_env_P_heap_eq (S : Ensemble var) (k : nat) (P : GInv)
        (H1 H2 H1' H2' : heap block) (rho1 rho2 : env) :
    (H1, rho1) ⋞ ^ (S; k; P) (H2, rho2) ->
    reach' H1 (env_locs rho1 S) |- H1 ≡ H1' ->
    reach' H2 (env_locs rho2 S) |- H2 ≡ H2' ->
    (H1', rho1) ⋞ ^ (S; k; P) (H2', rho2).
  Proof.
    intros Henv Heq1 Heq2 x HS v Hget.
    edestruct Henv as [l2 [Hget' Hval]]; eauto.
    eexists; split; eauto. eapply cc_approx_val_heap_eq.
    eassumption.
    eapply heap_eq_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply Singleton_Included.
    eexists; split; eauto. rewrite Hget. reflexivity.
    eapply heap_eq_antimon; [| eassumption ].
    eapply reach'_set_monotonic. eapply Singleton_Included.
    eexists; split. eassumption. rewrite Hget'. reflexivity.
  Qed.
    
  (** * Preservation under allocation lemmas *)
  
  Lemma cc_approx_val_alloc_Vconstr_set (k : nat) (P : GInv)
        (H1 H2 H1' H2' : heap block) (v1 v2 : value) (l1 l2 : loc)
        (c : cTag) (vs1 vs2 : list value) :
    well_formed (reach' H1 [set (val_loc v1)]) H1 ->
    (val_loc v1) \in dom H1 ->
    well_formed (reach' H2 [set (val_loc v2)]) H2 ->
    (val_loc v2) \in dom H2 ->
    (Res (v1, H1))  ≺ ^ (k; P) (Res (v2, H2)) ->
    alloc (Vconstr c vs1) H1 = (l1, H1') ->
    alloc (Vconstr c vs2) H2 = (l2, H2') ->
    Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k - 1; P) (Res (v2, H2))) vs1 vs2 ->
    (Res (v1, H1'))  ≺ ^ (k; P) (Res (v2, H2')).
  Proof with now eauto with Ensembles_DB.
    revert P H1 H2 H1' H2' v1 v2. induction k as [k IHk] using lt_wf_rec1.
    intros P H1 H2 H1' H2' v1 v2 Hwf1 Hsub1 Hwf2 Hsub2 Hyp Ha1 Ha2 Hall.
    destruct k as [ | k ];
    destruct v1 as [l1' | lf1 f1]; destruct v2 as [l2' | lf2 f2];
    try (now intros; contradiction).
    - destruct Hyp as [c' [vs1' [vs2' [Hget1 [Hget2 Hall']]]]].
      repeat eexists; eauto; erewrite gao; eauto.
      intros Hc; subst. erewrite alloc_fresh in Hget1; eauto. congruence.
      intros Hc; subst. erewrite alloc_fresh in Hget2; eauto. congruence.
    - destruct Hyp
        as (rho1 & B1 & lf2 & f2 & v_env & rho2 & B2 & Hget & Hgetl2 & Hgetlf2 & Hyp').
      do 7 eexists; split; [ | split; [| split] ]; (try now eauto).
      erewrite gao; try eassumption.
      intros Hc; subst. erewrite alloc_fresh in Hget; eauto. congruence.
      erewrite gao; try eassumption.
      intros Hc; subst. erewrite alloc_fresh in Hgetl2; eauto. congruence.
      erewrite gao; try eassumption.
      intros Hc; subst. erewrite alloc_fresh in Hgetlf2; eauto. congruence.
      intros xs1 ft e1 rho1' vs3 vs4 j Hfind Hlen Hset;
      destruct (Hyp' xs1 ft e1 rho1' vs3 vs4 j Hfind Hlen Hset)
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi).
      do 3 eexists; repeat split; try now eauto.
    - destruct Hyp as [c' [vs1' [vs2' [Hget1 [Hget2 Hall']]]]].
      repeat eexists; try eassumption; try erewrite gao; eauto.
      intros Hc; subst. erewrite alloc_fresh in Hget1; eauto. congruence.
      intros Hc; subst. erewrite alloc_fresh in Hget2; eauto. congruence.
      eapply Forall2_monotonic_strong; [| eassumption ].
      intros. rewrite cc_approx_val_eq in *.
      eapply IHk; try eassumption.
      + omega.
      + eapply well_formed_antimon; [| eassumption ].
        rewrite (reach_unfold _ [set val_loc (Loc l1')]).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. eapply Singleton_Included.
        repeat eexists; eauto. simpl. rewrite FromList_map_image_FromList.
        eapply In_image. eassumption.
      + eapply Hwf1; [| now apply Hget1 |].
        eapply reach'_extensive. reflexivity.
        simpl. rewrite FromList_map_image_FromList.
        eexists; split; eauto.
      + eapply well_formed_antimon; [| eassumption ].
        rewrite (reach_unfold _ [set val_loc (Loc l2')]).
        eapply Included_Union_preserv_r.
        eapply reach'_set_monotonic. eapply Singleton_Included.
        repeat eexists; eauto. simpl. rewrite FromList_map_image_FromList.
        eexists; split; eauto.
      + eapply Hwf2; [| now apply Hget2 |].
        eapply reach'_extensive. reflexivity.
        simpl. rewrite FromList_map_image_FromList.
        eapply In_image. eassumption.
      + eapply Forall2_monotonic; [| eassumption ]. intros.
        eapply cc_approx_val_monotonic. now apply H4. omega.
    - destruct Hyp
        as (rho1 & B1 & lf2 & f2 & v_env  & rho2 & B2 & Hget & Hgetl2 & Hgetlf2 & Hyp').
      do 7 eexists; split; [ | split; [| split] ]; (try now eauto).
      erewrite gao; try eassumption.
      intros Hc; subst. erewrite alloc_fresh in Hget; eauto. congruence.
      erewrite gao; try eassumption.
      intros Hc; subst. erewrite alloc_fresh in Hgetl2; eauto. congruence.
      erewrite gao; try eassumption.
      intros Hc; subst. erewrite alloc_fresh in Hgetlf2; eauto. congruence.
      intros xs1 ft e1 rho1' vs3 vs4 j Hfind Hlen Hset;
      destruct (Hyp' xs1 ft e1 rho1' vs3 vs4 j Hfind Hlen Hset)
        as (xs2 & e2 & rho2' & Hfind' & Hset' & Hi).
      do 3 eexists; repeat split; try now eauto.
      intros Hlt H1'' H2'' HH1 HH2. eapply Hi.
      + omega.
      + eapply Equivalence_Transitive; try eassumption.
        * eapply heap_eq_antimon; [|  eapply subheap_heap_eq ].
          eapply reachable_in_dom. eassumption.
          eapply Singleton_Included.
          now repeat eexists; eauto. eapply alloc_subheap. eassumption.
        * eapply heap_eq_antimon; [| eassumption ].
          eapply reach'_heap_monotonic. eapply alloc_subheap. eassumption.
      + eapply Equivalence_Transitive.
        * eapply heap_eq_antimon; [|  eapply subheap_heap_eq ].
          eapply reachable_in_dom. eassumption.
          eapply Singleton_Included.
          now repeat eexists; eauto. eapply alloc_subheap. eassumption.
        * eapply heap_eq_antimon; [| eassumption ].
          eapply reach'_heap_monotonic. eapply alloc_subheap. eassumption.
  Qed.
  
  (** * Getlist lemmas *)
  
  Lemma cc_approx_var_env_getlist (k : nat) (P : GInv)
        (rho1 rho2 : env) (H1 H2 : heap block) xs ys vs1 :
    Forall2 (cc_approx_var_env k P H1 rho1 H2 rho2) xs ys ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist ys rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k; P) (Res (v2, H2))) vs1 vs2.
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
  
  Lemma cc_approx_env_P_getlist_l (S : Ensemble var) (k : nat) (P : GInv)
        (rho1 rho2 : env) (H1 H2 : heap block) (xs : list var) (vs1 : list value) :
    (H1, rho1) ⋞ ^ ( S ; k ; P ) (H2, rho2) ->
    (FromList xs) \subset S ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist xs rho2 = Some vs2 /\
      Forall2 (fun v1 v2 => (Res (v1, H1)) ≺ ^ (k; P) (Res (v2, H2))) vs1 vs2.
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


  (** * heap_eq respects cc_approx *)

   Lemma cc_approx_exp_heap_eq (k : nat) (P1 : Inv) (P2 : GInv) (H1 H2 H1' H2' : heap block)
         (rho1 rho2 : env) (e1 e2 : exp) :
    (e1, rho1, H1) ⪯ ^ (k; P1; P2) (e2, rho2, H2) ->
    reach' H1 (env_locs rho1 (occurs_free e1)) |- H1 ≡ H1' ->
    reach' H2 (env_locs rho2 (occurs_free e2)) |- H2 ≡ H2' ->
    (e1, rho1, H1') ⪯ ^ (k; P1; P2) (e2, rho2, H2').
   Proof with now eauto with Ensembles_DB.
     intros Hexp Heq1 Heq2 H1'' H2'' r1 c1 m1 Heq1' Heq2'.
     eapply Hexp.
     eapply Equivalence_Transitive. eassumption.
     rewrite reach'_heap_eq; eassumption.
     eapply Equivalence_Transitive. eassumption.
     rewrite reach'_heap_eq; eassumption.
   Qed.

  (** * Compatibility lemmas *)
   
  (** Apply a closure converted function *)
  (** TODO move *)
  Definition AppClo f t xs f' Γ :=
    Eproj f' clo_tag 0%N f
          (Eproj Γ clo_tag 1%N f
                 (Eapp f' t (Γ :: xs))).

  Section Compat.
    
    Variable (IG : GInv). (* Global Invariant *)
    Variable (IL1 IL2 IL: Inv). (* Local Invariants *)
    Variable (II : IInv). (* Initial Invariant *)
    
    (** The initial invariant should respect heap equality *)
    Variable
      (InitInvRespectsHeapEq :
         forall (H1 H2 H1' H2' : heap block) (rho1 rho2 : env) (e1 e2 : exp),
           reach' H1 (env_locs rho1 (occurs_free e1)) |- H1 ≡ H1' ->
           reach' H2 (env_locs rho2 (occurs_free e2)) |- H2 ≡ H2' ->
           II (H1, rho1, e1) (H2, rho2, e2) ->
           II (H1', rho1, e1) (H2', rho2, e2)).

    Variable
      (InvCostRefl :
         forall (H1 H2 : heap block) (rho1 rho2 : env) (e1 e2 : exp) (c k : nat),
           II (H1, rho1, e1) (H2, rho2, e2) ->
           
           IL k (H1, rho1, e1, c, size_heap H1) (H2, rho2, e2, c, size_heap H2)).
    

    (** * Compatibility properties for the local invariants *)
    
    (** Constructor compatibility *)
    Variable
      (InvConstrCompat :
         forall (H1 H2 H1' H2' H1'' H2'': heap block) (rho1 rho2 : env)
           (x1 x2 : var) (t : cTag) (ys1 ys2 : list var) (e1 e2 : exp)
           (c1 c2 m1 m2 c k i : nat) (l1 l2 : loc) (b1 b2 : block),

           alloc b1 H1 = (l1, H1') ->
           live (env_locs (M.set x1 (Loc l1) rho1) (occurs_free e1)) H1' H1'' ->

           alloc b2 H2 = (l2, H2') ->
           live (env_locs (M.set x2 (Loc l2) rho2) (occurs_free e2)) H2' H2'' ->

           i < k ->
           
           IL1 i (H1'', M.set x1 (Loc l1) rho1, e1, c1 - c, m1) (H2'', M.set x2 (Loc l2) rho2, e2, c2 - c, m2) -> 

           II (H1, rho1, Econstr x1 t ys1 e1) (H2, rho2, Econstr x2 t ys2 e2) ->

           IL k (H1, rho1, Econstr x1 t ys1 e1, c1, max m1 (size_heap H1 + c))
              (H2, rho2, Econstr x2 t ys2 e2, c2, max m2 (size_heap H2 + c))).
    
    (** Projection compatibility *)
    Variable
      (InvProjCompat :
         forall (H1 H2 H1' H2' : heap block) (rho1 rho2 : env)
           (x1 x2 : var) (t : cTag) (n : N) (y1 y2 : var) (e1 e2 : exp)
           (c1 c2 m1 m2 c k i : nat) (v1 v2 : value),

           live (env_locs (M.set x1 v1 rho1) (occurs_free e1)) H1 H1' ->

           live (env_locs (M.set x2 v2 rho2) (occurs_free e2)) H2 H2' ->

           i < k ->

           IL1 i (H1', M.set x1 v1 rho1, e1, c1 - c, m1) (H2', M.set x2 v2 rho2, e2, c2 - c, m2) -> 

           II (H1, rho1, Eproj x1 t n y1 e1) (H2, rho2, Eproj x2 t n y2 e2) ->

           IL k (H1, rho1, Eproj x1 t n y1 e1, c1, max m1 (size_heap H1))
              (H2, rho2, Eproj x2 t n y2 e2, c2, max m2 (size_heap H2))).

    (** Case compatibility *)
    Variable
      (InvCaseHdCompat :
         forall (H1 H2 H1' H2' : heap block) (rho1 rho2 : env)
           (y1 y2 : var) (t : cTag) (e1 e2 : exp) (P1 P2 : list (cTag * exp))
           (c1 c2 m1 m2 c i k : nat),

           live (env_locs rho1 (occurs_free e1)) H1 H1' ->

           live (env_locs rho2 (occurs_free e2)) H2 H2' ->

           i < k ->

           IL1 i (H1', rho1, e1, c1 - c, m1) (H2', rho2, e2, c2 - c, m2) -> 

           II (H1, rho1, Ecase y1 ((t, e1) :: P1)) (H2, rho2, Ecase y2 ((t, e2) :: P2)) ->

           IL k (H1, rho1, Ecase y1 ((t, e1) :: P1), c1, max m1 (size_heap H1))
              (H2, rho2, Ecase y2 ((t, e2) :: P2), c2, max m2 (size_heap H2))).

    Variable
      (InvCaseTlCompat :
         forall (H1 H2 : heap block) (rho1 rho2 : env)
           (y1 y2 : var) (t : cTag) (e1 e2 : exp) (P1 P2 : list (cTag * exp))
           (c1 c2 m1 m2 c k : nat),
            
           IL2 k (H1, rho1, Ecase y1 P1, c1, m1)
               (H2, rho2, Ecase y2 P2, c2, m2) -> 

           II (H1, rho1, Ecase y1 ((t, e1) :: P1)) (H2, rho2, Ecase y2 ((t, e2) :: P2)) ->

           IL k (H1, rho1, Ecase y1 ((t, e1) :: P1), c1, m1)
              (H2, rho2, Ecase y2 ((t, e2) :: P2), c2, m2)).
    
    (** Halt compatibility *)
    Variable
      (InvHaltCompat :
         forall (H1 H2 : heap block) (rho1 rho2 : env)
           (x1 x2 : var) (c k : nat),

           II (H1, rho1, Ehalt x1) (H2, rho2, Ehalt x2) ->

           IL k (H1, rho1, Ehalt x1, c, size_heap H1) (H2, rho2, Ehalt x2, c, size_heap H2)).
    
    (** App compatibility *)
    (* Messy compat assumption :( *)
    Variable
      (InvAppCompat :
         forall (H1 H2 H1' H2' : heap block)
           (rho1 rho2 rho1' rho2' rho1'' rho2'' : env)
           (f1 f2 f1' f2' f2'' Γ : var) (t : cTag) (xs1 xs2 ys1 ys2 : list var) (e1 e2 : exp)
           (B1 B2 : fundefs) (lf1 lc2 lf2 : loc) (venv : value)
           (c1 c2 m1 m2 c i k : nat) (vs1 vs2 : list value),
           
           M.get f1 rho1 = Some (FunPtr lf1 f1') ->
           get lf1 H1 = Some (Vfun rho1' B1) ->
           getlist xs1 rho1 = Some vs1 ->
           find_def f1' B1 = Some (t, ys1, e1) ->
           setlist ys1 vs1 (def_funs B1 lf1 rho1') = Some rho1'' ->
           live (env_locs rho1'' (occurs_free e1)) H1 H1' ->

           M.get f2 rho2 = Some (Loc lc2) ->
           get lc2 H2 = Some (Vconstr clo_tag [(FunPtr lf2 f2') ; venv]) ->
           get lf2 H2 = Some (Vfun rho2' B2) ->
           getlist xs2 rho2 = Some vs2 ->
           find_def f2' B2 = Some (t, ys2, e2) ->
           setlist ys2 (venv :: vs2) (def_funs B2 lf2 rho2') = Some rho2'' ->
           live (env_locs rho1'' (occurs_free e1)) H1 H1' ->

           i < k ->

           IG i (H1', rho1'', e1, c1, m1) (H2', rho2'', e2, c2, m2) -> 
           
           II (H1, rho1, Eapp f1 t xs1) (H2, rho2, AppClo f2 t xs2 f2'' Γ) ->

           IL k (H1, rho1, Eapp f1 t xs1, c1 + c, max m1 (size_heap H1))
              (H2, rho2, AppClo f2 t xs2 f2'' Γ, c2 + c + 3, max m2 (size_heap H2))).
    
    (** Abstraction compatibility *)
    Variable
      (InvFunCompat :
         forall (H1 H2 H1' H2' H1'' H2'': heap block) (rho1 rho2 : env)
           (B1 B2 : fundefs) (e1 e2 : exp) (c1 c2 m1 m2 s c k i : nat) (l1 l2 : loc),

           alloc (Vfun rho1 B1) H1 = (l1, H1') ->
           live (env_locs (def_funs B1 l1 rho1) (occurs_free e1)) H1' H1'' ->
           
           alloc (Vfun rho2 B2) H2 = (l2, H2') ->
           live (env_locs (def_funs B2 l2 rho2) (occurs_free e2)) H2' H2'' ->

           i < k ->

           IL1 i (H1'', def_funs B1 l1 rho1, e1, c1 - cost (Efun B1 e1), m1)
               (H2'', def_funs B2 l2 rho2, e2, c2 - cost (Efun B2 e2), m2) ->
           
           II (H1, rho1, Efun B1 e1) (H2, rho2, Efun B2 e2) ->

           IL k (H1, rho1, Efun B1 e1, c1, max m1 (size_heap H1 + s))
              (H2, rho2, Efun B2 e2, c2, max m2 (size_heap H2 + s))).

    (** Constructor compatibility *)
    Lemma cc_approx_exp_constr_compat (k : nat)
          rho1 rho2 H1 H2 x1 x2 t ys1 ys2 e1 e2 :

      Forall2 (cc_approx_var_env k IG H1 rho1 H2 rho2) ys1 ys2 ->

      II (H1, rho1, Econstr x1 t ys1 e1) (H2, rho2, Econstr x2 t ys2 e2) ->
      
      (forall i vs1 vs2 l1 l2 H1' H2' H1'' H2'',
         i < k ->
         (* quantify over all equal heaps *)
         reach' H1 (env_locs rho1 (occurs_free (Econstr x1 t ys1 e1))) |- H1 ≡ H1' ->
         reach' H2 (env_locs rho2 (occurs_free (Econstr x2 t ys2 e2))) |- H2 ≡ H2' ->
         (* allocate a new location for the constructed value *)
         alloc (Vconstr t vs1) H1' = (l1, H1'') ->
         alloc (Vconstr t vs2) H2' = (l2, H2'') ->
         Forall2 (fun l1 l2 => (Res (l1, H1')) ≺ ^ (i; IG) (Res (l2, H2'))) vs1 vs2 ->
         (e1, M.set x1 (Loc l1) rho1, H1'') ⪯ ^ (i; IL1; IG)
         (e2, M.set x2 (Loc l2) rho2, H2'')) ->
      
      (Econstr x1 t ys1 e1, rho1, H1) ⪯ ^ (k; IL; IG) (Econstr x2 t ys2 e2, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hall Hinit Hpre H1' H2' v1 c1 m1 Heq1 Heq2 Hleq1 Hstep1.
      inv Hstep1.
      (* Timeout! *)
      - { simpl in H0. exists OOT, c1. eexists. repeat split. 
          - econstructor. simpl. erewrite <- Forall2_length. eassumption.
            eassumption. reflexivity.
          - eapply InvCostRefl. eapply InitInvRespectsHeapEq; eassumption.
          - now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { edestruct (cc_approx_var_env_getlist k IG rho1 rho2) as [ls2 [Hget' Hpre']];
          [| eauto |]; eauto.
          destruct (alloc (Vconstr t ls2) H2') as [l' H2''] eqn:Ha.
          edestruct (live_exists (env_locs (M.set x2 (Loc l') rho2) (occurs_free e2)) H2'')
            as [H2''' Hl2].
          eapply Decidable_env_locs; eauto with typeclass_instances.
          eapply Forall2_length in Hall.
          assert (Hlen : @length M.elt ys1 = @length M.elt ys2).
          { erewrite (@getlist_length_eq value ys1 vs); [| eassumption ].
            erewrite (@getlist_length_eq value ys2 ls2); [| eassumption ].
            eapply Forall2_length. eassumption. }
          edestruct Hpre with (i := k - (cost (Econstr x1 t ys1 e1))) as [v2 [c2 [m2 [Hstep [HS Hval]]]]];
            [ |  eassumption | eassumption | eassumption | eassumption | | | | | eassumption | ].
          - simpl in H6. simpl. omega.
          - eapply Forall2_monotonic_strong; [| eassumption ]. intros ? ? ? ? H.
            eapply cc_approx_val_monotonic.
            eapply cc_approx_val_heap_eq. now apply H.
            eapply heap_eq_antimon; [| eassumption ]. eapply reach'_set_monotonic.
            eapply Singleton_Included. eapply FromList_env_locs. eassumption.
            normalize_occurs_free... rewrite FromList_map_image_FromList.
            eapply In_image; eassumption.
            eapply heap_eq_antimon; [| eassumption ]. eapply reach'_set_monotonic.
            eapply Singleton_Included. eapply FromList_env_locs. eassumption.
            normalize_occurs_free... rewrite FromList_map_image_FromList.
            eapply In_image; eassumption. omega.
          - eapply collect_heap_eq. eapply live_collect. eassumption.
          - eapply collect_heap_eq. eapply live_collect. eassumption.
          - simpl. simpl in H6. omega.
          - repeat eexists; eauto.
            + eapply Eval_constr_per with (c := c2 + cost (Econstr x2 t ys2 e2))
              ; [ | | | | | | rewrite NPeano.Nat.add_sub ]; try eassumption.
              omega. reflexivity. 
            + simpl. rewrite <- Hall.
              unfold size_heap. 
              erewrite (size_with_measure_alloc _ _ _ H1' H'); [| reflexivity | eassumption ].
              erewrite size_with_measure_alloc with (H' := H2''); [| reflexivity | eassumption ].
              simpl.
              erewrite <- (getlist_length_eq ys1 vs); [| eassumption ].
              replace (length ls2) with (length ys1).
              eapply InvConstrCompat; try eassumption.
              Focus 2. replace (c2 + S (length ys1) - S (length ys1)) with c2 by omega.
              eassumption. simpl. simpl in H6. omega.
              eapply InitInvRespectsHeapEq; eassumption.
              erewrite <- (getlist_length_eq _ ls2); [| eassumption ]. eassumption.
            + rewrite cc_approx_val_eq. eapply cc_approx_val_monotonic.
              rewrite <- cc_approx_val_eq. eassumption. omega. }
    Qed.

    (** Projection compatibility *)
    Lemma cc_approx_exp_proj_compat (k : nat) rho1 rho2 H1 H2 x1 x2 t n y1 y2 e1 e2 :

      cc_approx_var_env k IG H1 rho1 H2 rho2 y1 y2 ->

      II (H1, rho1, Eproj x1 t n y1 e1) (H2, rho2, Eproj x2 t n y2 e2) ->

      (forall i v1 v2 H1' H2',
         i < k ->
         (* quantify over all equal heaps *)
         reach' H1 (env_locs rho1 (occurs_free (Eproj x1 t n y1 e1))) |- H1 ≡ H1' ->
         reach' H2 (env_locs rho2 (occurs_free (Eproj x2 t n y2 e2))) |- H2 ≡ H2' ->
                                                                                                                         (Res (v1, H1)) ≺ ^ (i; IG) (Res (v2, H2)) ->
                                                                                                                         (e1, M.set x1 v1 rho1, H1') ⪯ ^ (i ; IL1; IG) (e2, M.set x2 v2 rho2, H2')) ->
      
      (Eproj x1 t n y1 e1, rho1, H1) ⪯ ^ (k ; IL; IG) (Eproj x2 t n y2 e2, rho2, H2).
    Proof.
      intros Hall Hi Hpre H1' H2' r1 c1 m1 Heq1' Heq2' Hleq1 Hstep1. inv Hstep1.
      (* Timeout! *)
      - { simpl in H0. exists OOT, c1. eexists. repeat split. 
          - econstructor. eassumption. reflexivity. 
          - eapply InvCostRefl. eapply InitInvRespectsHeapEq; eassumption.
          - now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { edestruct Hall as [l2 [Hget' Hcc']]; eauto.
          destruct l2 as [l' | l' f]; [| contradiction ].
          destruct Hcc' as [c' [vs1 [vs2 [Hget1 [Hget2' Hk]]]]].
          rewrite Heq1' in Hget1; [
            | now eapply reach'_extensive; repeat eexists; eauto; rewrite H8; eauto ].
          rewrite Heq2' in Hget2'; [
            | now eapply reach'_extensive; repeat eexists; eauto; rewrite Hget'; eauto ]. 
          rewrite Hget1 in H11; inv H11.
          destruct k; simpl in H7; try omega.
          edestruct (Forall2_nthN (fun l1 l2 => cc_approx_val k IG (Res (l1, H1)) (Res (l2, H2))) vs)
            as [l2' [Hnth Hval]]; eauto.
          edestruct (live_exists (env_locs (M.set x2 l2' rho2) (occurs_free e2)) H2')
            as [H2'' Hl2].
          eapply Decidable_env_locs; eauto with typeclass_instances.
          edestruct Hpre with (i := k) as [r2 [c2 [m2 [Hstep [HS Hres]]]]];
            [omega | eassumption | eassumption | | | | | eassumption | ].
          - rewrite cc_approx_val_eq in *. eassumption.
          - eapply collect_heap_eq. eapply live_collect. eassumption.
          - eapply collect_heap_eq. eapply live_collect. eassumption.
          - omega.
          - repeat eexists; eauto. eapply Eval_proj_per with (c := c2 + 1); try eassumption.
            simpl; omega. reflexivity. rewrite NPeano.Nat.add_sub.
            eassumption.
            eapply InvProjCompat with (c := 1) (i := k);
              [ eassumption | eassumption | omega | | ].
            rewrite NPeano.Nat.add_sub. eassumption. 
            eapply InitInvRespectsHeapEq; eassumption.
            rewrite cc_approx_val_eq in *.
            eapply cc_approx_val_monotonic. eassumption. omega. }
    Qed.


    (** Case compatibility *)
    Lemma cc_approx_exp_case_nil_compat (k : nat) rho1 rho2 H1 H2 x1 x2 :
      II (H1, rho1, Ecase x1 []) (H2, rho2, Ecase x2 []) ->
      (Ecase x1 [], rho1, H1) ⪯ ^ (k ; IL; IG) (Ecase x2 [], rho2, H2).
    Proof.
      intros HII H1' H2' v1 c1 m1 Hleq1 Hstep1 Hleq Hstep. inv Hstep.
      (* Timeout! *)
      - { simpl in H0. exists OOT, c1. eexists. repeat split. 
          - econstructor. eassumption. reflexivity. 
          - eapply InvCostRefl.
            eapply InitInvRespectsHeapEq; eassumption.
          - now rewrite cc_approx_val_eq. }
      (* Termination *)
      - { simpl in H7. discriminate. }
    Qed.
    
    Lemma cc_approx_exp_case_compat (k : nat) rho1 rho2 H1 H2 x1 x2 t e1 e2 Pats1 Pats2 :
      
      cc_approx_var_env k IG H1 rho1 H2 rho2 x1 x2 ->

      II (H1, rho1, Ecase x1 ((t, e1) :: Pats1)) (H2, rho2, Ecase x2 ((t, e2) :: Pats2)) ->

      (forall i H1' H2',
         i < k ->
         (* quantify over all equal heaps *)
         reach' H1 (env_locs rho1 (occurs_free (Ecase x1 ((t, e1) :: Pats1)))) |- H1 ≡ H1' ->
         reach' H2 (env_locs rho2 (occurs_free (Ecase x2 ((t, e2) :: Pats2)))) |- H2 ≡ H2' ->

         (e1, rho1, H1') ⪯ ^ (i ; IL1; IG) (e2, rho2, H2')) ->

      (Ecase x1 Pats1, rho1, H1) ⪯ ^ (k ; IL2; IG) (Ecase x2 Pats2, rho2, H2) ->

      (Ecase x1 ((t, e1) :: Pats1), rho1, H1) ⪯ ^ (k ; IL; IG) (Ecase x2 ((t, e2) :: Pats2), rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hap HI Hexp_hd Hexp_tl H1' H2' r1 c1 m1 Heq1 Heq2 Hleq1 Hstep1.
      inv Hstep1.
      (* Timeout! *)
      - { simpl in H0. exists OOT, c1. eexists. repeat split. 
          - econstructor. eassumption. reflexivity. 
          - eapply InvCostRefl.
            eapply InitInvRespectsHeapEq; eassumption.
          - now rewrite cc_approx_val_eq. }
      -  { edestruct Hap as [l2 [Hget' Hcc']]; eauto.
           destruct l2 as [l' |l' f ]; [| contradiction ].
           destruct Hcc' as [c' [vs1 [vs2 [Hget1 [Hget2' Hk]]]]].
           rewrite Heq1 in Hget1; [
             | now eapply reach'_extensive; repeat eexists; eauto; rewrite H5; eauto ].
           rewrite Heq2 in Hget2'; [
             | now eapply reach'_extensive; repeat eexists; eauto; rewrite Hget'; eauto ]. 
           rewrite Hget1 in H6; inv H6.
           destruct k. simpl in H4; try omega.
           simpl in H7. destruct (M.elt_eq t t0) eqn:Heq; subst.
           - inv H7.
             edestruct (live_exists (env_locs rho2 (occurs_free e2)) H2')
               as [H2'' Hl2].
             eapply Decidable_env_locs; typeclasses eauto.
             edestruct Hexp_hd with (i := k) as [v2 [c2 [m2 [Hstep2 [HS Hpre2]]]]];
               [| eassumption | eassumption | | | | eassumption | ].
             + omega.
             + eapply collect_heap_eq; eapply live_collect; eassumption.
             + eapply collect_heap_eq; eapply live_collect; eassumption.
             + simpl; omega. 
             + repeat eexists; eauto.
               * eapply Eval_case_per with (c := c2 + cost (Ecase x2 ((t0, e2) :: Pats2)));
                 try eassumption.
                 simpl; omega. 
                 simpl. rewrite Heq. reflexivity.
                 reflexivity. simpl.
                 rewrite NPeano.Nat.add_sub. eassumption. 
               * eapply InvCaseHdCompat with (i := k) (c := 1);
                 try eassumption.
                 omega.
                 simpl. rewrite NPeano.Nat.add_sub. eassumption. 
                 eapply InitInvRespectsHeapEq; eassumption.
               * rewrite cc_approx_val_eq in *.
                 eapply cc_approx_val_monotonic. eassumption.
                 simpl in H4. simpl; destruct c1; omega.
           - edestruct Hexp_tl as [v2 [c2 [m2 [Hstep2 [HS Hpre2]]]]];
               [ | |  eassumption | now econstructor; eauto | ].
             + eapply heap_eq_antimon; [| eassumption ].
               eapply reach'_set_monotonic. eapply env_locs_monotonic.
               normalize_occurs_free...
             + eapply heap_eq_antimon; [| eassumption ].
               eapply reach'_set_monotonic. eapply env_locs_monotonic.
               normalize_occurs_free...
             + inv Hstep2.
               * (* Timeout! *)
                 { simpl in H0. exists OOT, c2. eexists. repeat split.
                   - econstructor. simpl. eassumption. reflexivity. 
                   - eapply InvCaseTlCompat; eauto.
                     rewrite <- plus_n_O in HS. eassumption. 
                   - eassumption. }
               * (* termination *)
                 { repeat eexists; eauto.
                   - eapply Eval_case_per with (c := c2); eauto.
                     simpl.
                     rewrite H9 in Hget'; inv Hget'. rewrite H10 in Hget2'; inv Hget2'.
                     rewrite Heq. eassumption.
                   - rewrite <- plus_n_O in *; eauto. } }
    Qed.

    (** Halt compatibility *)
    Lemma cc_approx_exp_halt_compat (k : nat) rho1 rho2 H1 H2 x1 x2 :
      cc_approx_var_env k IG H1 rho1 H2 rho2 x1 x2 ->

      II (H1, rho1, Ehalt x1) (H2, rho2, Ehalt x2) ->

      (Ehalt x1, rho1, H1) ⪯ ^ (k ; IL; IG) (Ehalt x2, rho2, H2).
    Proof.
      intros Henv Hi H1' H2' v1 c1 m1 Heq1 Heq2 Hleq1 Hstep1. inv Hstep1.
      - (* Timeout! *)
        { simpl in H0. exists OOT, c1. eexists. repeat split. 
          - econstructor. eassumption. reflexivity. 
          - eapply InvCostRefl.
            eapply InitInvRespectsHeapEq; eassumption.
          - now rewrite cc_approx_val_eq. }
      - edestruct Henv as [v' [Hget Hpre]]; eauto.
        repeat eexists.
        * now econstructor; eauto.
        * rewrite <- plus_n_O in *; eauto.
        * rewrite cc_approx_val_eq in *.
          eapply cc_approx_val_heap_eq.
          eapply cc_approx_val_monotonic. eassumption.
          omega.
          eapply heap_eq_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply Singleton_Included. repeat eexists; eauto.
          now rewrite H4; eauto.
          eapply heap_eq_antimon; [| eassumption ].
          eapply reach'_set_monotonic.
          eapply Singleton_Included. repeat eexists; eauto.
          now rewrite Hget; eauto.
    Qed.

(*

    (** Abstraction compatibility *)
    Lemma cc_approx_exp_fun_compat (k : nat) rho1 rho2 H1 H2 B1 e1 B2 e2 :
      II (H1, rho1, Efun B1 e1) (H2, rho2, Efun B2 e2)  ->
      (forall i l1 l2 H1' H2' H1'' H2'',
         i < k ->
         (* quantify over all equal heaps *)
         reach' H1 (env_locs rho1 (occurs_free (Efun B1 e1))) |- H1 ≡ H1' ->
         reach' H2 (env_locs rho2 (occurs_free (Efun B2 e2))) |- H2 ≡ H2' ->
         (* allocate a new location for the abstraction *)
         alloc (Vfun rho1 B1) H1' = (l1, H1'') ->
         alloc (Vfun rho2 B2) H2' = (l2, H2'') ->
         (e1, def_funs B1 l1 rho1, H1'') ⪯ ^ (i; IL1; IG)
         (e2, def_funs B2 l2 rho2, H2'')) ->
      (Efun B1 e1, rho1, H1) ⪯ ^ (k ; IL; IG) (Efun B2 e2, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hinit Hpre H1' H2' v1 c1 m1 Heq1 Heq2 Hleq1 Hstep1.
      inv Hstep1.
      - (* Timeout! *)
        { simpl in H0. exists OOT, c1. eexists. repeat split. 
          - econstructor. simpl. admit.
            reflexivity.
          - eapply InvCostRefl. eapply InitInvRespectsHeapEq; eassumption.
          - now rewrite cc_approx_val_eq. }
      - { destruct (alloc (Vfun rho2 B2) H2') as [l' H2''] eqn:Ha.
          edestruct (live_exists (env_locs (def_funs B2 l' rho2) (occurs_free e2)) H2'')
            as [H2''' Hl2].
          eapply Decidable_env_locs; eauto with typeclass_instances.

          edestruct Hpre with (i := k - 1) as [v2 [c2 [m2 [Hstep [HS Hval]]]]];
            [ |  eassumption | eassumption | eassumption | eassumption | | | | eassumption | ].
          - simpl in H4. omega.
          - eapply collect_heap_eq. eapply live_collect. eassumption.
          - eapply collect_heap_eq. eapply live_collect. eassumption.
          - simpl in H4. simpl. omega.
          - repeat eexists; eauto.
            + eapply Eval_fun_per with (c := c2 + cost (Efun B2 e2)); try eassumption.
              omega. reflexivity.
              rewrite NPeano.Nat.add_sub. eassumption.
            + unfold size_heap. 
              erewrite (size_with_measure_alloc _ _ _ H1' H'); [| reflexivity | eassumption ].
              erewrite size_with_measure_alloc with (H' := H2''); [| reflexivity | eassumption ].
              eapply InvFunCompat with (i := k - 1); try eassumption.
              simpl in H4. omega.
              rewrite NPeano.Nat.add_sub. eassumption.
              now eauto.
            + rewrite cc_approx_val_eq in *.
              eapply cc_approx_val_monotonic. eassumption. simpl.
              simpl in H4. omega.
    Qed.

    (** Application compatibility *)
    Lemma cc_approx_exp_app_compat (k : nat) rho1 rho2 H1 H2 t f1 xs1 f2 f2' Γ xs2 :
      ~ Γ \in (f2 |: FromList xs2) ->
      ~ f2' \in (f2 |: FromList xs2) ->
      Γ <> f2' ->
      cc_approx_var_env k IG H1 rho1 H2 rho2 f1 f2 ->
      Forall2 (cc_approx_var_env k IG H1 rho1 H2 rho2) xs1 xs2 ->
      II (H1, rho1, Eapp f1 t xs1) (H2, rho2, AppClo f2 t xs2 f2' Γ)  ->
      (Eapp f1 t xs1, rho1, H1) ⪯ ^ (k ; IL; IG) (AppClo f2 t xs2 f2' Γ, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hnin1 Hnin2 Hneq Henv Hall Hi H1' H2' v1 c1 m1 Heq1 Heq2 Hleq1 Hstep1.
      inv Hstep1.
      (* weaken the hypotheses *)
      eapply cc_approx_var_env_heap_eq in Henv;
        try now (eapply heap_eq_antimon; [| eassumption ];
                 eapply reach'_set_monotonic; eapply env_locs_monotonic;
                 eapply Singleton_Included; eauto).
      eapply Forall2_monotonic_strong in Hall;
        [| intros ? ? ? ? Hval;
           eapply cc_approx_var_env_heap_eq; [ now apply Hval | |];
           (eapply heap_eq_antimon; [| eassumption ]);
           eapply reach'_set_monotonic; eapply env_locs_monotonic;
           eapply Singleton_Included; eauto
        ].
      - edestruct Henv as [l' [Hget' Hcc']]; eauto. unfold AppClo in *.
        edestruct (cc_approx_var_env_getlist k IG rho1 rho2) as [vs2 [Hgetl' Hcc'']];
          [| now eauto |]; eauto.
        simpl in Hcc'. destruct l' as [l' | ]; [| contradiction ]. 
        destruct Hcc'
          as (rho1' & B1 & lf2 & f2'' & venv & rho2' & B2 & Hgetl & Hgetl'' & Hgetlf & HBs).
        rewrite Hgetl in H6; inv H6.
        edestruct HBs with (j := k - 1) (vs1 := vs) (vs2 := vs2)
          as (xs2' & e2 & rho2'' & Hf2'' & Hset & Hj); eauto.
        eapply Forall2_length. eassumption.
        (* first GC *)
        edestruct (live_exists (env_locs (M.set f2' (FunPtr lf2 f2'') rho2)
                                         (occurs_free (Eproj Γ clo_tag 1 f2 (Eapp f2' t (Γ :: xs2))))) H2')
          as [H21 Hl2].
        eapply Decidable_env_locs; eauto with typeclass_instances.
        (* second GC *)
        edestruct (live_exists (env_locs (M.set Γ venv (M.set f2' (FunPtr lf2 f2'') rho2))
                                         (occurs_free (Eapp f2' t (Γ :: xs2)))) H21)
          as [H22 Hl2'].
        eapply Decidable_env_locs; eauto with typeclass_instances.
        (* third GC *)
        edestruct (live_exists (env_locs rho2'' (occurs_free e2)) H22)
          as [H23 Hl2''].
        eapply Decidable_env_locs; eauto with typeclass_instances.
        
        assert (Hlocs_eq :
                  reach' H2' (env_locs (M.set Γ venv (M.set f2' (FunPtr lf2 f2'') rho2))
                                       (occurs_free (Eapp f2' t (Γ :: xs2)))) \subset
                         reach' H2' (env_locs (M.set f2' (FunPtr lf2 f2'') rho2)
                                              (occurs_free (Eproj Γ clo_tag 1 f2 (Eapp f2' t (Γ :: xs2)))))).
        { normalize_occurs_free. rewrite !occurs_free_Eapp at 1. rewrite !FromList_cons at 1.
          rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l. 
          rewrite !Setminus_Disjoint. rewrite !env_locs_set_In; eauto. 
          rewrite !Setminus_Union_distr, !Setminus_Same_set_Empty_set, Union_Empty_set_neut_r. 
          rewrite (Setminus_Union [set f2'] [set Γ] [set f2']), (Union_commut [set Γ] [set f2']).
          rewrite <- Setminus_Union, !Setminus_Same_set_Empty_set, !Setminus_Empty_set_abs_r,
          Union_Empty_set_neut_r, Union_Empty_set_neut_l.
          rewrite !Setminus_Disjoint, env_locs_Union, !reach'_Union.
          rewrite (Union_assoc (reach' H2' [set val_loc venv])).
          rewrite (Union_commut (reach' H2' [set val_loc venv])), <- Union_assoc.
          simpl.
          rewrite (reach_unfold _ (env_locs rho2 [set f2])).
          rewrite !env_locs_Singleton at 1; [ | now eauto | now eauto]. simpl.
          rewrite post_Singleton; [| now eauto ]. simpl. rewrite !FromList_cons at 1.
          rewrite !reach'_Union...
          eapply Disjoint_Singleton_r. intros Hc. eapply Hnin2. now right.
          eapply Disjoint_Singleton_r. intros Hc. inv Hc. eapply Hnin2. now left.
          eapply Disjoint_Singleton_r. intros Hc. eapply Hnin1. now right.
          eapply Disjoint_Singleton_r. intros Hc. inv Hc. eapply Hnin2. now right.
          constructor. now eauto. intros Hc; inv Hc; congruence.
          eapply Disjoint_Singleton_r. intros Hc. inv Hc. congruence.
          eapply Disjoint_Singleton_r. intros Hc. eapply Hnin1. now right. }
        assert (Hlocs_eq' :
                  reach' H2' (env_locs rho2'' (occurs_free e2)) \subset
                         reach' H2' (env_locs (M.set Γ venv (M.set f2' (FunPtr lf2 f2'') rho2))
                                              (occurs_free (Eapp f2' t (Γ :: xs2))))).
        { normalize_occurs_free. rewrite !FromList_cons at 1.
          rewrite !env_locs_set_In; eauto. eapply Included_trans.
          eapply reach'_set_monotonic. eapply Included_trans.
          eapply env_locs_monotonic.
          eapply occurs_free_in_fun. eapply find_def_correct. eassumption.
          eapply Included_trans.
          rewrite Union_commut. eapply env_locs_setlist_Included. now eauto.
          eapply Included_Union_compat. rewrite Union_commut. now eapply env_locs_def_funs_Included. 
          simpl. rewrite FromList_cons. reflexivity. simpl.
          rewrite !reach'_Union. eapply Union_Included.
          eapply Union_Included. eapply Included_Union_preserv_r.
          eapply Included_Union_preserv_l.
          rewrite (reach'_idempotent _ [set lf2]).
          eapply reach'_set_monotonic.
          intros l1 Hin. exists 1. split. now constructor.
          exists lf2. eexists; split; [ | split; try eassumption ].
          reflexivity. now eauto with Ensembles_DB.
          eapply Union_Included. now eauto with Ensembles_DB.
          do 2 eapply Included_Union_preserv_r.
          eapply reach'_set_monotonic. eapply FromList_env_locs.
          eassumption.
          rewrite !Setminus_Union_distr, Setminus_Same_set_Empty_set; eauto. 
          eapply Included_Union_preserv_l. eapply Included_Union_preserv_r.
          rewrite !Setminus_Disjoint. reflexivity.
          eapply Disjoint_Singleton_r. intros Hc. eapply Hnin1. now right.
          eapply Disjoint_Singleton_r. intros Hc. inv Hc. eapply Hnin2. now right.
          constructor. now eauto. intros Hc; inv Hc. congruence. }
        assert (Heap1 :
                  reach' H2'
                         (env_locs (M.set f2' (FunPtr lf2 f2'') rho2)
                                   (occurs_free (Eproj Γ clo_tag 1 f2 (Eapp f2' t (Γ :: xs2))))) |- H2' ≡ H21).
        { eapply collect_heap_eq; eapply live_collect; eassumption. }
        assert (Heap2 :
                  reach' H2'
                         (env_locs (M.set Γ venv (M.set f2' (FunPtr lf2 f2'') rho2))
                                   (occurs_free (Eapp f2' t (Γ :: xs2)))) |- H21 ≡ H22).
        { eapply heap_eq_antimon; [| eapply collect_heap_eq; eapply live_collect; eassumption ].
          rewrite reach'_heap_eq. reflexivity.
          eapply heap_eq_antimon; [| eassumption ]. eassumption. }
        assert (Heap3 :
                  reach' H2' (env_locs rho2'' (occurs_free e2)) |- H22 ≡ H23).
        { eapply heap_eq_antimon; [| eapply collect_heap_eq; eapply live_collect; eassumption ].
          rewrite reach'_heap_eq. reflexivity.
          eapply Equivalence_Transitive.
          eapply heap_eq_antimon; [| eassumption ]. eapply Included_trans; eassumption.
          eapply heap_eq_antimon; [| eassumption ]. eassumption. }
        edestruct Hj with (H1' := H') (H2' := H23) as (r2 & c2 & m2 & Hstep & Hinv & Hval);
          [ omega | reflexivity | reflexivity |  | | | | eassumption | ].
        + eapply Forall2_monotonic; [| eassumption ].
          intros ? ? Hval. rewrite !cc_approx_val_eq in *.
          eapply cc_approx_val_monotonic. now apply Hval. omega.
        + eapply collect_heap_eq; eapply live_collect; eassumption.
        + eapply Equivalence_Transitive; [| eapply Equivalence_Transitive ].
          * (* H2' = H21  *)
            eapply heap_eq_antimon; [| eassumption ].
            eapply Included_trans; eassumption.
          * (* H21 = H22 *)
            eapply heap_eq_antimon; eassumption. 
          * (* H22 = H23 *)
            eassumption.
        + omega.
        + repeat eexists.
          * econstructor. eassumption. eassumption. reflexivity.
            eassumption. reflexivity.
            econstructor; eauto.
            rewrite M.gso. eassumption. intros Hc.
            subst. eapply Hnin2. now left; eauto.
            rewrite <- Heap1. eassumption.
            eapply reach'_extensive. eapply env_locs_monotonic with (S1 := [set f2]).
            normalize_occurs_free...
            eexists; split; eauto. rewrite M.gso. now rewrite Hget'.
            now intros Hc; subst; eauto.
            reflexivity.
            econstructor. exact 0. (* XXX extra nat in the semantics *)
            rewrite M.gso. rewrite M.gss. reflexivity.
            now intros Hc; subst; eauto.
            rewrite <- Heap2, <- Heap1. eassumption.
            eapply reach'_extensive. eapply env_locs_monotonic with (S1 := [set f2']).
            eapply Singleton_Included. repeat normalize_occurs_free.
            right. constructor; eauto. intros Hc; inv Hc; congruence.
            eexists; split; eauto. rewrite M.gss. reflexivity.
            eapply reach'_extensive. eapply env_locs_monotonic with (S1 := [set f2']).
            eapply Singleton_Included. repeat normalize_occurs_free...
            eexists; split; eauto. rewrite M.gso. rewrite M.gss. reflexivity.
            now eauto. simpl. rewrite M.gss.
            rewrite !getlist_set_neq. now rewrite Hgetl'.
            intros Hc. eapply Hnin2. now eauto.
            intros Hc. eapply Hnin1. now eauto.
            eassumption. now eauto. eassumption. reflexivity.
            eassumption.
          * rewrite <- plus_n_O. simpl.
            replace (c2 + 1 + S (length xs2) + 1 + 1) with (c2 + (S (length xs2)) + 3) by omega.
            replace (c + 1 + length xs1) with (c + S (length xs1)) by omega. 
            rewrite <- !Max.max_assoc, (Max.max_r (size_heap H22)), (Max.max_r (size_heap H21)).
            erewrite Forall2_length; eauto.
            eapply InvAppCompat; try eassumption. now eauto. omega. now eauto.
            eapply size_with_measure_subheap. now destruct Hl2.
            eapply le_trans; [| now apply NPeano.Nat.le_max_l ].
            eapply size_with_measure_subheap. now destruct Hl2'.
          * rewrite cc_approx_val_eq in *. eapply cc_approx_val_monotonic.
            eassumption.  omega.
      - unfold AppClo. repeat normalize_occurs_free.
        right. constructor. right. constructor. left.
        rewrite FromList_cons...
        intros Hc; inv Hc; eapply Hnin1. now right.
        intros Hc; inv Hc; eapply Hnin2. now right.
      - eapply heap_eq_antimon; [| eassumption ].
        eapply reach'_set_monotonic. eapply env_locs_monotonic.
        eapply Singleton_Included. unfold AppClo.
        repeat normalize_occurs_free. eauto.
    Qed.

    (** Abstraction compatibility *)
    Lemma cc_approx_exp_fun_compat (k : nat) rho1 rho2 H1 H2 B1 e1 B2 e2 :
      II (H1, rho1, Efun B1 e1) (H2, rho2, Efun B2 e2)  ->
      (forall i l1 l2 H1' H2' H1'' H2'',
         i < k ->
         (* quantify over all equal heaps *)
         reach' H1 (env_locs rho1 (occurs_free (Efun B1 e1))) |- H1 ≡ H1' ->
         reach' H2 (env_locs rho2 (occurs_free (Efun B2 e2))) |- H2 ≡ H2' ->
         (* allocate a new location for the abstraction *)
         alloc (Vfun rho1 B1) H1' = (l1, H1'') ->
         alloc (Vfun rho2 B2) H2' = (l2, H2'') ->
         (e1, def_funs B1 l1 rho1, H1'') ⪯ ^ (i; IL1; IG)
         (e2, def_funs B2 l2 rho2, H2'')) ->
      (Efun B1 e1, rho1, H1) ⪯ ^ (k ; IL; IG) (Efun B2 e2, rho2, H2).
    Proof with now eauto with Ensembles_DB.
      intros Hinit Hpre H1' H2' v1 c1 m1 Heq1 Heq2 Hleq1 Hstep1.
      inv Hstep1.
      destruct (alloc (Vfun rho2 B2) H2') as [l' H2''] eqn:Ha.
      edestruct (live_exists (env_locs (def_funs B2 l' rho2) (occurs_free e2)) H2'')
        as [H2''' Hl2].
      eapply Decidable_env_locs; eauto with typeclass_instances.

      edestruct Hpre with (i := k - 1) as [v2 [c2 [m2 [Hstep [HS Hval]]]]];
        [ |  eassumption | eassumption | eassumption | eassumption | | | | eassumption | ].
      - omega.
      - eapply collect_heap_eq. eapply live_collect. eassumption.
      - eapply collect_heap_eq. eapply live_collect. eassumption.
      - omega.
      - repeat eexists; eauto.
        + now econstructor; eauto.
        + rewrite <- plus_n_O.
          unfold size_heap. 
          erewrite (size_with_measure_alloc _ _ _ H1' H'); [| reflexivity | eassumption ].
          erewrite size_with_measure_alloc with (H' := H2''); [| reflexivity | eassumption ].
          eapply InvFunCompat; try eassumption.
          omega. now eauto.
        + rewrite cc_approx_val_eq in *.
          eapply cc_approx_val_monotonic. eassumption. omega.
    Qed.
*)
  End Compat.

End CC_log_rel.