(* Step-indexed logical relation for L6 closure conversion.
 * Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2017
 *)

From Coq Require Import NArith.BinNat Relations.Relations MSets.MSets
                        MSets.MSetRBT Lists.List omega.Omega Sets.Ensembles.
From L6 Require Import functions cps eval cps_util identifiers ctx Ensembles_util
                       List_util Heap.heap Heap.heap_defs Heap.space_sem.
From Libraries Require Import Coqlib.

Module CC_log_rel (H : Heap).

  Module Sem := SpaceSem H.

  Import H Sem.Defs Sem.

  (* Global invariant *)
  Definition GInv :=
    nat -> (* The step index *)
    relation (exp * env * heap val * nat * nat).
  
  (* Local invariant *)
  Definition Inv :=
    relation (nat * nat).
  
  (* Tag for closure records *)
  Variable (clo_tag : cTag). 

  Inductive fundefs_Forall2
            (R : var -> fTag -> list var -> exp -> var -> fTag -> list var -> exp -> Prop)
  : fundefs -> fundefs -> Prop :=
  | Forall2_Fcons :
      forall f1 ft1 xs1 e1 B1 f2 ft2 xs2 e2 B2, 
        fundefs_Forall2 R B1 B2 ->
        R f1 ft1 xs1 e1 f2 ft2 xs2 e2 ->
        fundefs_Forall2 R (Fcons f1 ft1 xs1 e1 B1) (Fcons f2 ft2 xs2 e2 B2)
  | Forall2_Fnil :
      fundefs_Forall2 R Fnil Fnil.

  (** step-indexed relation on cps terms. Relates cps-terms with closure-converted terms  *)
  (* Expression relation : 
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
  Fixpoint cc_approx_val (k : nat) (P : GInv) (r1 r2 : res) {struct k} : Prop :=
    let cc_approx_exp (k : nat) (p1 p2 : exp * env * heap val) : Prop :=
        let '(e1, rho1, H1) := p1 in
        let '(e2, rho2, H2) := p2 in
        forall r1 c1 m1,
          c1 <= k ->
          big_step_perfect_GC H1 rho1 e1 r1 c1 m1 ->
          exists r2 c2 m2,
            big_step_perfect_GC H2 rho2 e2 r2 c2 m2 /\
            P k (e1, rho1, H1, c1, m1) (e2, rho2, H2, c2, m2) /\
            cc_approx_val (k - c1) P r1 r2
    in
    let '(l1, H1) := r1 in
    let '(l2, H2) := r2 in 
    match get l1 H1 with
      | Some v1 =>
        match get l2 H2 with
          | Some v2 =>
            match v1, v2 with
              | Vfun rho1 defs1,
                Vconstr tag (l_clo :: l_env :: l)  =>
                exists rho2 defs2, 
                  get l_clo H2 = Some (Vfun rho2 defs2) /\
                  fundefs_Forall2
                    (fun f1 ft1 xs1 e1 f2 ft2 xs2 e2 =>
                       forall (ls1 ls2 : list loc) (j : nat) (rho1' : env),
                         length ls1 = length ls2 ->
                         Some rho1' = setlist xs1 ls1 (def_funs defs1 l1 rho1) ->
                         exists (rho2' : env),
                           tag = clo_tag /\
                           Some rho2' = setlist xs2 (l_env :: ls2)
                                                (def_funs defs2 l2 rho2) /\
                           match k with
                             | 0 => True
                             | S k =>
                               let R l1 l2 := cc_approx_val (k - (k-j)) P (l1, H1) (l2, H2) in
                               j < S k ->
                               Forall2 R ls1 ls2 ->
                               cc_approx_exp (k - (k - j)) (e1, rho1', H1) (e2, rho2', H2)
                           end
                    ) defs1 defs2
              | Vconstr t1 ls1, Vconstr t2 ls2 =>
                t1 = t2 /\ 
                match k with
                  | 0 => True
                  | S k =>
                    let R l1 l2 := cc_approx_val k P (l1, H1) (l2, H2) in
                    Forall2 R ls1 ls2
                end
              | _, _ => False
            end
          | None => False
        end
      | None => get l2 H2 = None (* ? *)
    end.

  Definition cc_approx_exp (k : nat) (P1 : Inv) (P2 : GInv)
             (p1 p2 : exp * env * heap val) : Prop :=
    let '(e1, rho1, H1) := p1 in
    let '(e2, rho2, H2) := p2 in
    forall r1 c1 m1,
      c1 <= k ->
      big_step_perfect_GC H1 rho1 e1 r1 c1 m1 ->
      exists r2 c2 m2,
        big_step_perfect_GC H2 rho2 e2 r2 c2 m2 /\
        (* extra invariants for costs *)
        P1 (c1, m1) (c2, m2) /\
        cc_approx_val (k - c1) P2 r1 r2.
  
  (** More compact definition of the value relation *)
  Definition cc_approx_val' (k : nat) (P : GInv) (r1 r2 : res) : Prop :=
    let '(l1, H1) := r1 in
    let '(l2, H2) := r2 in 
    match get l1 H1 with
      | Some v1 =>
        match get l2 H2 with
          | Some v2 =>
            match v1, v2 with
              | Vfun rho1 defs1, Vconstr tag (l_clo :: l_env :: l) =>
                exists rho2 defs2, 
                  get l_clo H2 = Some (Vfun rho2 defs2) /\
                  fundefs_Forall2
                    (fun f1 ft1 xs1 e1 f2 ft2 xs2 e2 =>
                       forall (ls1 ls2 : list loc) (j : nat) (rho1' : env),
                         length ls1 = length ls2 ->
                         Some rho1' = setlist xs1 ls1 (def_funs defs1 l1 rho1) ->
                         exists (rho2' : env),
                           tag = clo_tag /\
                           Some rho2' = setlist xs2 (l_env :: ls2)
                                                (def_funs defs2 l2 rho2) /\
                           (j < k ->
                            Forall2 (fun l1 l2 => cc_approx_val j P (l1, H1) (l2, H2))
                                    ls1 ls2 ->
                            cc_approx_exp j (fun p1 p2 =>
                                               let '(c1, m1) := p1 in
                                               let '(c2, m2) := p2 in
                                               P j
                                                 (e1, rho1', H1, c1, m1)
                                                 (e2, rho2', H2, c2, m2))
                                          P (e1, rho1', H1) (e2, rho2', H2))
                    ) defs1 defs2
              | Vconstr t1 ls1, Vconstr t2 ls2 =>
                t1 = t2 /\ 
                match k with
                  | 0 => True
                  | S k =>
                    let R l1 l2 := cc_approx_val k P (l1, H1) (l2, H2) in
                    Forall2 R ls1 ls2
                end
              | _, _ => False
            end
          | None => False
        end
      | None => get l2 H2 = None
    end.

  Lemma fundefs_Forall2_monotonic
        (R1 R2 : var -> fTag -> list var -> exp -> var -> fTag -> list var -> exp -> Prop) B1 B2:
    (forall f1 ft1 xs1 e1 f2 ft2 xs2 e2,
       R1 f1 ft1 xs1 e1 f2 ft2 xs2 e2 -> R2 f1 ft1 xs1 e1 f2 ft2 xs2 e2) ->
    fundefs_Forall2 R1 B1 B2 ->
    fundefs_Forall2 R2 B1 B2.
  Proof.
    intros Hyp Hdefs. induction Hdefs; constructor; eauto.
  Qed.

  (** Correspondence of the two definitions *)
  Lemma cc_approx_val_eq (k : nat) P (v1 v2 : res) :
    cc_approx_val k P v1 v2 <-> cc_approx_val' k P v1 v2.
  Proof.
    destruct k as [ | k ]; destruct v1 as (l1, H1); destruct v2 as (l2, H2). simpl.
    - destruct (get l1 H1) as [v1 | ] eqn:Hget1;
      destruct (get l2 H2) as [v2 | ] eqn:Hget2; try now firstorder.
      destruct v1; destruct v2;
      eauto; try (split; intros H; (now simpl in H; inv H)).
      + destruct l; [ now firstorder |].
        destruct l0; [ now firstorder |].
        split; intros [rho2 [defs2 [Hget Hyp]]]; do 2 eexists; (split; [ eassumption |  ]).
        * eapply fundefs_Forall2_monotonic; [| eassumption ].
          intros. edestruct H as [? [? [? ?]]]; eauto.
          eexists; repeat split; eauto. intros; omega.
        * eapply fundefs_Forall2_monotonic; [| eassumption ].
          intros ? ? ? ? ? ? ? ? H ? ? ? ? ? ?.
          edestruct H with (j := 0) as [? [? [? ? ]]]; eauto.
    - simpl; destruct (get l1 H1) as [v1 | ] eqn:Hget1;
      destruct (get l2 H2) as [v2 | ] eqn:Hget2; try now firstorder.
      destruct v1; destruct v2;
      eauto; try (split; intros H; (now simpl in H; inv H)). 
      + destruct l; [ now firstorder |].
        destruct l0; [ now firstorder |].
        split; intros [rho2 [defs2 [Hget Hyp]]]; do 2 eexists; (split; [ eassumption |  ]).
        * eapply fundefs_Forall2_monotonic; [| eassumption ].
          intros. edestruct H with (j := j) as [? [? [? Hyp']]]; eauto.
          subst.
          eexists x; repeat split; eauto. intros.
          assert (Heq : k - (k - j) = j) by omega. rewrite <- Heq.
          eapply Hyp'; eauto; [| omega ]. rewrite Heq. eassumption.
        *  eapply fundefs_Forall2_monotonic; [| eassumption ].
          intros. edestruct H with (j := j) as [? [? [? Hyp']]]; eauto.
          subst. eexists x; repeat split; eauto. intros.
          assert (Heq : k - (k - j) = j) by omega. rewrite Heq.
          eapply Hyp'; eauto; [| omega ]. rewrite <- Heq. eassumption.
  Qed.

  Opaque cc_approx_val.

  (** Environment relation for a single point (i.e. variable) : 
   * ρ1 ~_k^x ρ2 iff ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition cc_approx_var_env (k : nat) P (H1 : heap val) (rho1 : env)
             (H2 : heap val) (rho2 : env) (x y : var) : Prop :=
    forall l1, 
      M.get x rho1 = Some l1 -> 
      exists l2, M.get y rho2 = Some l2 /\
            cc_approx_val' k P (l1, H1) (l2, H2).

  (** Environment relation for a set of points (i.e. predicate over variables) :
    * ρ1 ~_k^S ρ2 iff 
    *  forall x, S x -> ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition cc_approx_env_P (S : Ensemble var) k P (c1 c2 : heap val * env) :=
    let (H1, rho1) := c1 in
    let (H2, rho2) := c2 in
    forall (x : var), S x -> cc_approx_var_env k P H1 rho1 H2 rho2 x x.
  
  (** Environment relation for the whole domain of definition :
    * ρ1 ~_k ρ2 iff forall x, ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
  Definition cc_approx_env (k : nat) P c1 c2 : Prop :=
    cc_approx_env_P (fun _ => True) k P c1 c2.

  (** Notations for approximation relations *)

  Notation "p1 ⪯ ^ ( k ; P1 ; P2 ) p2" := (cc_approx_exp k P1 P2 p1 p2)
                                            (at level 70, no associativity).
  

  Notation "p1 ≺ ^ ( k ; P ) p2" := (cc_approx_val' k P p1 p2)
                              (at level 70, no associativity).
  
  Notation "p1 ⋞ ^ ( R ; k ; P ) p2" := (cc_approx_env_P R k P p1 p2)
                                          (at level 70, no associativity).
  
  (** * Monotonicity Properties *)

  (** The environment relation is antimonotonic in the set of free variables *) 
  Lemma cc_approx_env_P_antimon (S1 S2 : Ensemble var) (k : nat)
        (P : GInv) (c1 c2 : (heap val) * env) :
    c1 ⋞ ^ ( S2 ; k ; P ) c2 ->
    S1 \subset S2 ->
    c1 ⋞ ^ ( S1 ; k ; P ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hpre Hin x Hin'. eapply Hpre; eapply Hin; eauto.
  Qed.
  
  (** The expression relation is monotonic in the local invariant *)
  Lemma cc_approx_exp_rel_mon k (P1 P1' : Inv) P2 p1 p2 :
    p1 ⪯ ^ ( k ; P1 ; P2 ) p2 ->
    inclusion _ P1 P1' ->
    p1 ⪯ ^ ( k ; P1' ; P2 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1].
    destruct p2 as [[e2 H2] rho2].
    intros Hcc Hin v1 c1 m1 Hleq Hstep.
    edestruct Hcc as [v2 [c2 [m2 [Hstep' [HInv Hval]]]]]; eauto.
    repeat eexists; eauto.
  Qed.
  
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
    intros IH Hcc Hin v1 c1 m1 Hleq Hstep.
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
    revert k P1 P2 r1 r2.
    induction k using lt_wf_rec1.
    intros P1 P2 r1 r2 Hv1 Hrel.
    destruct r1 as (l1, H1); destruct r2 as (l2, H2).
    destruct k; simpl in *.
    - destruct (get l1 H1) as [v1 | ] eqn:Hget1;
      destruct (get l2 H2) as [v2 | ] eqn:Hget2;
      try congruence.
      destruct v1; destruct v2;
      eauto; try (split; intros H; (now simpl in H; inv H)).
      destruct l; [ now firstorder |].
      destruct l0; [ now firstorder |].
      destruct Hv1 as [rho2 [defs2 [Hget Hyp]]];
        do 2 eexists; (split; [ eassumption |  ]).
      eapply fundefs_Forall2_monotonic; [| eassumption ].
      intros. edestruct H0 with (j := 0)as [? [? [? ?]]]; eauto.
      eexists; repeat split; eauto. intros; omega.
    - destruct (get l1 H1) as [v1 | ] eqn:Hget1;
      destruct (get l2 H2) as [v2 | ] eqn:Hget2;
      try congruence.
      destruct v1; destruct v2;
      eauto; try (split; intros H; (now simpl in H; inv H)).
      + destruct Hv1 as [Heq Hall]; subst.
        split; eauto. eapply Forall2_monotonic; [| eassumption ].
        intros; eauto. rewrite cc_approx_val_eq.
        eapply H; eauto. rewrite <- cc_approx_val_eq; eauto.
      + destruct l; [ now firstorder |].
        destruct l0; [ now firstorder |].
        destruct Hv1 as [rho2 [defs2 [Hget Hyp]]];
          do 2 eexists; (split; [ eassumption |  ]).
        eapply fundefs_Forall2_monotonic; [| eassumption ]. simpl.
        intros ? ? ? ? ? ? ? ? Hypj. intros.
        edestruct Hypj with (j := j) as [? [? [? Hval]]]; eauto.
        eexists; repeat split; eauto. intros ? ?. 
        eapply cc_approx_exp_same_rel_IH with (P2 := P1) (P2' := P2). 
        intros; eapply H. omega. eassumption. eassumption.
        eapply cc_approx_exp_rel_mon. eapply Hval; eauto.
        eapply Forall2_monotonic; [| eassumption ].
        intros. rewrite cc_approx_val_eq.
        eapply H; eauto. now rewrite <- cc_approx_val_eq; simpl in *; eauto.
        intros. now firstorder.
        intros [? ?] [? ?]. now firstorder. now firstorder.
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
  Lemma cc_approx_val_monotonic (k j : nat) (P : GInv) (r1 r2 : res) :
    r1 ≺ ^ (k; P) r2 ->
    j <= k ->
    r1 ≺ ^ (j; P) r2.
  Proof.
    revert j P r1 r2. induction k as [k IHk] using lt_wf_rec1.
    intros j P [l1 H1] [l2 H2] Hv1 Hleq.
    simpl in *;
      destruct (get l1 H1) as [v1 | ] eqn:Hget1;
      destruct (get l2 H2) as [v2 | ] eqn:Hget2;
    try congruence.
    destruct v1; destruct v2;
    eauto; try (split; intros H; (now simpl in H; inv H)).
    - destruct Hv1 as [Heq Hall].
      destruct j as [| j]; eauto. destruct k as [| k]; try omega.
      split; eauto. eapply Forall2_monotonic; [| eassumption ].
      intros. rewrite cc_approx_val_eq in *.
      simpl in H. eapply IHk; [| eassumption |]; omega.
    - destruct l; [ now firstorder |].
      destruct l0; [ now firstorder |].
      destruct Hv1 as [rho2 [defs2 [Hget Hyp]]];
      do 2 eexists; (split; [ eassumption |  ]).
      eapply fundefs_Forall2_monotonic; [| eassumption ].
      intros.
      edestruct H with (j := j0) as [rho2' [? [? Hypj]]]; eauto.
      eexists; repeat split; eauto. intros.
      edestruct Hypj as [r2 [c2 [m2 [Hbs [HP Hcc]]]]]; eauto.
      omega. repeat eexists; eauto.
  Qed.

  (** The expression relation is monotonic in the step index *)
  Lemma cc_approx_exp_monotonic (k j : nat) (P1 : Inv) (P2 : GInv)
        p1 p2 :
    p1 ⪯ ^ ( k ; P1 ; P2 ) p2 ->
    j <= k ->
    p1 ⪯ ^ ( j ; P1 ; P2 ) p2.
  Proof.
    destruct p1 as [[e1 H1] rho1]; destruct p2 as [[e2 H2] rho2].
    intros Hpre Hleq v1 c1 m1 Hleq' Hstep.
    edestruct (Hpre v1 c1) as [v2 [c2 [m2 [Hstep2 [Hleq2 H3]]]]]; eauto.
    omega. do 3 eexists; repeat split; eauto.
    rewrite cc_approx_val_eq in *. eapply cc_approx_val_monotonic; eauto. omega.
  Qed.
  
  (** The environment relations are monotonic in the step index *)
  Lemma cc_approx_env_P_monotonic (R : Ensemble var) (k j : nat) (P : GInv)
        c1 c2 :
    c1 ⋞ ^ ( R ; k ; P ) c2 ->
    j <= k ->
    c1 ⋞ ^ ( R ; j ; P ) c2.
  Proof.
    destruct c1 as [H1 rho1]; destruct c2 as [H2 rho2].
    intros Hcc Hleq x HP v Hget.
    edestruct Hcc as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto. eapply cc_approx_val_monotonic; eauto.
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

  Lemma cc_approx_var_env_extend_eq :
    forall  (k : nat) (P : GInv) (rho1 rho2 : env) (H1 H2 : heap val)
       (x y : var) (l1 l2 : loc),
      (l1, H1) ≺ ^ (k; P) (l2, H2) ->
      cc_approx_var_env k P H1 (M.set x l1 rho1) H2 (M.set y l2 rho2) x y.
  Proof.
    intros rho1 rho2 H1 H2 k P x y v1 v2 Hval x' Hget.
    rewrite M.gss in Hget. inv Hget. eexists.
    rewrite M.gss. split; eauto.
  Qed.
  
  Lemma cc_approx_var_env_extend_neq :
    forall (k : nat) (P : GInv)  (rho1 rho2 : env) (H1 H2 : heap val)
      (x1 x2 y1 y2 : var) (l1 l2 : loc),
      cc_approx_var_env k P H1 rho1 H2 rho2 y1 y2 ->
      y1 <> x1 -> y2 <> x2 ->
      cc_approx_var_env k P H1 (M.set x1 l1 rho1) H2 (M.set x2 l2 rho2) y1 y2.
  Proof. 
    intros k P rho1 rho2 H1 H2 x1 x2 y1 y2 v1 v2 Hval Hneq Hneq' x' Hget.
    rewrite M.gso in *; eauto.
  Qed.
   
  Lemma cc_approx_var_env_extend :
    forall (k : nat) (P : GInv)  (rho1 rho2 : env) (H1 H2 : heap val)
      (x y : var) (l1 l2 : loc),
      cc_approx_var_env k P H1 rho1 H2 rho2 y y ->
      (l1, H1) ≺ ^ (k; P) (l2, H2) ->
      cc_approx_var_env k P H1 (M.set x l1 rho1) H2 (M.set x l2 rho2) y y.
  Proof.
    intros k P rho1 rho2 H1 H2 x y v1 v2 Hvar Hval.
    destruct (peq y x); subst.
    - apply cc_approx_var_env_extend_eq; eauto.
    - apply cc_approx_var_env_extend_neq; eauto.
  Qed.

  (** Extend the related environments with a single point *)
  Lemma cc_approx_env_P_extend (S : Ensemble var) (k : nat) (P : GInv)
        (rho1 rho2 : env) (H1 H2 : heap val) x l1 l2 :
      (H1, rho1) ⋞ ^ ( S \\ [set x] ; k ; P ) (H2, rho2) ->
      (l1, H1) ≺ ^ (k; P) (l2, H2) ->
      (H1, M.set x l1 rho1) ⋞ ^ ( S; k ; P ) (H2, M.set x l2 rho2).
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
        (rho1 rho2 rho1' rho2' : env) (H1 H2 : heap val) xs ls1 ls2 :
    (H1, rho1) ⋞ ^ ( S \\ (FromList xs) ; k ; P ) (H2, rho2) ->
    Forall2 (fun l1 l2 => (l1, H1) ≺ ^ (k; P) (l2, H2)) ls1 ls2 ->
    setlist xs ls1 rho1 = Some rho1' ->
    setlist xs ls2 rho2 = Some rho2' ->
    (H1, rho1') ⋞ ^ ( S ; k ; P ) (H2, rho2').
  Proof.
    intros Hcc Hall Hset1 Hset2 x HP v Hget.
    destruct (in_dec var_dec x xs).
    - edestruct (@setlist_Forall2_get loc) as [v1 [v2 [Hget1 [Hget2 HP']]]];
      try eassumption.
      rewrite Hget in Hget1. inv Hget1. repeat eexists; eauto.
    - erewrite <- setlist_not_In in Hget; eauto.
      edestruct Hcc as [v2 [Hget' Hpre']]; eauto.
      constructor; eauto. repeat eexists; eauto.
      erewrite <- setlist_not_In; eauto.
  Qed.

  (** * Getlist lemmas *)
  
  Lemma cc_approx_var_env_getlist (k : nat) (P : GInv)
        (rho1 rho2 : env) (H1 H2 : heap val) xs ys ls1 :
    Forall2 (cc_approx_var_env k P H1 rho1 H2 rho2) xs ys ->
    getlist xs rho1 = Some ls1 ->
    exists ls2,
      getlist ys rho2 = Some ls2 /\
      Forall2 (fun l1 l2 => (l1, H1) ≺ ^ (k; P) (l2, H2)) ls1 ls2.
  Proof.
    revert ys ls1. induction xs as [| x xs IHxs]; intros ys ls1 Hall Hget.
    - destruct ys; inv Hall. inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget.
      destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (getlist xs rho1) eqn:Heq2; try discriminate. inv Hget.
      destruct ys as [| y ys]; inv Hall. 
      destruct (IHxs ys l0 H6 eq_refl) as [vs2 [Hget HAll]].
      destruct (H4 _ Heq1) as [v2 [Heq Hpre]].
      eexists. split; simpl; eauto. rewrite Hget, Heq. eauto.
  Qed.

  Lemma cc_approx_env_P_getlist_l (S : Ensemble var) (k : nat) (P : GInv)
        (rho1 rho2 : env) (H1 H2 : heap val) (xs : list var) (ls1 : list loc) :
    (H1, rho1) ⋞ ^ ( S ; k ; P ) (H2, rho2) ->
    (FromList xs) \subset S ->
    getlist xs rho1 = Some ls1 ->
    exists ls2,
      getlist xs rho2 = Some ls2 /\
      Forall2 (fun l1 l2 => (l1, H1) ≺ ^ (k; P) (l2, H2)) ls1 ls2.
  Proof.
    intros Henv. revert ls1.
    induction xs as [| x xs IHxs]; intros ls1 Hp Hget.
    - inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget. destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (getlist xs rho1) eqn:Heq2; try discriminate. inv Hget.
      edestruct (IHxs l0) as  [vs2 [Hget HAll]]; eauto.
      + intros x' Hin. eapply Hp. constructor 2; eauto.
      + eapply Henv in Heq1. destruct Heq1 as [v2 [Hyp1 Hyp2]].
        eexists. split; simpl; eauto. rewrite Hyp1. rewrite Hget.
        constructor. apply Hp. now constructor.
  Qed.

  Lemma cc_approx_env_P_set_not_in_P_l (S : Ensemble var) (k : nat) (P : GInv)
        (rho1 rho2 : env) (H1 H2 : heap val) (x : var) (l : loc) :
    (H1, rho1) ⋞ ^ ( S ; k ; P ) (H2, rho2) ->
    ~ x \in S ->
    (H1, M.set x l  rho1) ⋞ ^ ( S; k ; P ) (H2, rho2).
  Proof. 
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    destruct (peq y x); subst.
    - contradiction.
    - rewrite M.gso in Hget; eauto.
  Qed.

  Lemma cc_approx_env_P_set_not_in_P_r (S : Ensemble var) (k : nat) (P : GInv)
        (rho1 rho2 : env) (H1 H2 : heap val) (x : var) (l : loc) :
    (H1, rho1) ⋞ ^ ( S ; k ; P ) (H2, rho2) ->
    ~ x \in S ->
    (H1, rho1) ⋞ ^ ( S; k ; P ) (H2, M.set x l rho2).
  Proof. 
    intros Hcc Hnin y Py v' Hget.
    edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
    exists v''. rewrite M.gsspec.
    destruct (peq y x); subst.
    - contradiction.
    - eauto.
  Qed.
  
  (** * Compatibility lemmas *)

  Open Scope fun_scope.
  
  Lemma live_collect S H1 H2 :
    live S H1 H2 ->
    collect S H1 H2.
  Proof.
    firstorder.
  Qed.

  Definition HInv := relation nat.

  Lemma cc_approx_exp_constr_compat (k : nat) (P : GInv) (P1 P2 : Inv) (Ph : HInv)
        rho1 rho2 H1 H2 x1 x2 t ys1 ys2 e1 e2 :
    Forall2 (cc_approx_var_env k P H1 rho1 H2 rho2) ys1 ys2 ->
    (* Cost invariant compatibility property *)
    (forall c1 m1 m1' c2 m2 m2',
       P1 (c1, m1) (c2, m2) ->
       Ph m1' m2' ->
       P2 (c1 + 1 + length ys1, max m1 m1') (c2 + 1 + length ys1, max m2 m2')) ->
    Ph (size_heap H1 + (1 + length ys1)) (size_heap H2 + (1 + length ys1)) ->
    (forall ls1 ls2 l1 l2 H1' H2' H1'' H2'',
       (* allocate a new location for the constructed value *)
       alloc (Vconstr t ls1) H1 = (l1, H1') ->
       alloc (Vconstr t ls2) H2 = (l2, H2') ->
       (* garbage collect *)
       reach' H1' (env_locs (M.set x1 l1 rho1) (occurs_free e1)) |- H1' ≡ H1'' ->
       reach' H2' (env_locs (M.set x2 l2 rho2) (occurs_free e2)) |- H2' ≡ H2'' ->
       Forall2 (fun l1 l2 => (l1, H1) ≺ ^ (k; P) (l2, H2)) ls1 ls2 ->
       (e1, M.set x1 l1 rho1, H1'') ⪯ ^ (k ; P1; P) 
       (e2, M.set x2 l2 rho2, H2'')) ->
    (Econstr x1 t ys1 e1, rho1, H1) ⪯ ^ (k ; P2; P) (Econstr x2 t ys2 e2, rho2, H2).
  Proof.
    intros Hall Hyp Hi Hpre v1 c1 m1 Hleq1 Hstep1. inv Hstep1.
    edestruct (cc_approx_var_env_getlist k P rho1 rho2) as [ls2 [Hget' Hpre']];
      [| eauto |]; eauto.
    destruct (alloc (Vconstr t ls2) H2) as [l' H2'] eqn:Ha.
    edestruct (live_exists (env_locs (M.set x2 l' rho2) (occurs_free e2)) H2') as [H2'' Hl2].
    eapply Decidable_env_locs; eauto with typeclass_instances.
    eapply Forall2_length in Hall. rewrite Hall.
    edestruct Hpre as [v2 [c2 [m2 [Hstep [HS Hval]]]]];
      [ eassumption | eassumption | | | eassumption | | eassumption |  ].
    eapply collect_heap_eq; eapply live_collect; eassumption.
    eapply collect_heap_eq; eapply live_collect; eassumption.
    omega.
    repeat eexists; eauto. econstructor; eauto.
    rewrite <- Hall. eapply Hyp. eassumption.
    rewrite cc_approx_val_eq in *.
    unfold size_heap. erewrite size_with_measure_alloc; [| reflexivity | eassumption ].
    erewrite size_with_measure_alloc with (H' := H2'); [| reflexivity | eassumption ].
    simpl. rewrite <- plus_n_O. erewrite <- getlist_length_eq; [| eassumption ].
    replace (length ls2) with (length ys1). eassumption.
    erewrite <- (getlist_length_eq _ ls2); [| eassumption ]. eassumption.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_monotonic. eassumption. omega.
  Qed.

  Lemma cc_approx_exp_proj_compat (k : nat) (P : GInv) (P1 P2 : Inv) (Ph : HInv)
        rho1 rho2 H1 H2 x1 x2 t n y1 y2 e1 e2 :
    cc_approx_var_env k P H1 rho1 H2 rho2 y1 y2 ->
    (* Cost invariant compatibility property *)
    (forall c1 m1 m1' c2 m2 m2',
       P1 (c1, m1) (c2, m2) ->
       Ph m1' m2' ->
       P2 (c1 + 1, max m1 m1') (c2 + 1, max m2 m2')) ->
    Ph (size_heap H1) (size_heap H2) ->
    (forall i l1 l2 H1' H2',
       i <= k ->
       (* garbage collect *)
       reach' H1 (env_locs (M.set x1 l1 rho1) (occurs_free e1)) |- H1 ≡ H1' ->
       reach' H2 (env_locs (M.set x2 l2 rho2) (occurs_free e2)) |- H2 ≡ H2' ->
       (l1, H1) ≺ ^ (i; P) (l2, H2) ->
       (e1, M.set x1 l1 rho1, H1') ⪯ ^ (i ; P1; P) 
       (e2, M.set x2 l2 rho2, H2')) ->
    (Eproj x1 t n y1 e1, rho1, H1) ⪯ ^ (k ; P2; P) (Eproj x2 t n y2 e2, rho2, H2).
  Proof.
    intros Hall Hyp Hi Hpre r1 c1 m1 Hleq1 Hstep1. inv Hstep1.
    edestruct Hall as [l2 [Hget' Hcc']]; eauto.
    simpl in Hcc'. rewrite H10 in Hcc'. destruct (get l2 H2) eqn:Hget2; try contradiction.
    destruct v; try contradiction. destruct Hcc' as [Heq Hcc']. subst.
    destruct k; try omega.
    edestruct (Forall2_nthN (fun l1 l2 => cc_approx_val k P (l1, H1) (l2, H2)) ls)
      as [l2' [Hnth Hval]]; eauto.
    edestruct (live_exists (env_locs (M.set x2 l2' rho2) (occurs_free e2)) H2)
      as [H2' Hl2].
    eapply Decidable_env_locs; eauto with typeclass_instances.
    edestruct Hpre with (i := k) as [r2 [c2 [m2 [Hstep [HS Hres]]]]];
      [omega | | | | | eassumption |].
    eapply collect_heap_eq; eapply live_collect; eassumption.
    eapply collect_heap_eq; eapply live_collect; eassumption.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_monotonic. eassumption. omega.
    omega.
    repeat eexists; eauto. econstructor; eauto.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_monotonic. eassumption. omega.
  Qed.
  
  Import ListNotations.

  Lemma cc_approx_exp_case_nil_compat (k : nat) (P : GInv) (P1 P2 : Inv) (Ph : HInv)
        rho1 rho2 H1 H2 x1 x2 :
    (Ecase x1 [], rho1, H1) ⪯ ^ (k ; P2; P) (Ecase x2 [], rho2, H2).
  Proof.
    intros v1 c1 m1 Hleq1 Hstep1. inv Hstep1. inv H6.
  Qed.
  

  Lemma cc_approx_exp_case_compat (k : nat) (P : GInv) (P1 P2 P3 : Inv) (Ph : HInv)
        rho1 rho2 H1 H2 x1 x2 t e1 e2 Pats1 Pats2 :
    
    cc_approx_var_env k P H1 rho1 H2 rho2 x1 x2 ->
    
    (* Cost invariant compatibility properties *)
    (forall c1 m1 m1' c2 m2 m2',
       P1 (c1, m1) (c2, m2) ->
       Ph m1' m2' ->
       P3 (c1 + 1, max m1 m1') (c2 + 1, max m2 m2')) ->
    inclusion  _ P2 P3 ->

    Ph (size_heap H1) (size_heap H2) ->

    (forall i H1' H2',
       i < k ->
       (* garbage collect *)
       reach' H1 (env_locs rho1 (occurs_free e1)) |- H1 ≡ H1' ->
       reach' H2 (env_locs rho2 (occurs_free e2)) |- H2 ≡ H2' ->
       (e1, rho1, H1') ⪯ ^ (i ; P1; P) (e2, rho2, H2')) ->

    (Ecase x1 Pats1, rho1, H1) ⪯ ^ (k ; P2; P) (Ecase x2 Pats2, rho2, H2) ->

    (Ecase x1 ((t, e1) :: Pats1), rho1, H1) ⪯ ^ (k ; P3; P) (Ecase x2 ((t, e2) :: Pats2), rho2, H2).
  Proof.
    intros Hap Hyp1 Hyp2 Hyp3 Hexp_hd Hexp_tl r1 c1 m1 Hleq1 Hstep1.
    inv Hstep1.
    edestruct Hap as [l2 [Hget' Hcc']]; eauto.
    simpl in Hcc'. rewrite H5 in Hcc'.
    destruct (get l2 H2) eqn:Hget2; try contradiction.
    destruct v; try contradiction. destruct Hcc' as [Heq Hcc'].
    subst. destruct k; try omega.
    simpl in H6. destruct (peq t c0); subst.
    - rewrite peq_true in H6. inv H6.
      edestruct (live_exists (env_locs rho2 (occurs_free e2)) H2)
        as [H2' Hl2].
      eapply Decidable_env_locs; typeclasses eauto.
      edestruct Hexp_hd with (i := k) as [v2 [c2 [m2 [Hstep2 [HS Hpre2]]]]];
        [| | | | eassumption | ].
      omega.
      eapply collect_heap_eq; eapply live_collect; eassumption.
      eapply collect_heap_eq; eapply live_collect; eassumption.
      omega. 
      repeat eexists. econstructor; eauto; try now constructor; eauto.
      simpl. rewrite peq_true. reflexivity.
      eapply Hyp1. eassumption. rewrite <- plus_n_O. eassumption.
      rewrite cc_approx_val_eq in *.
      eapply cc_approx_val_monotonic. eassumption. omega.
    - rewrite peq_false in H6; eauto. 
      edestruct Hexp_tl as [v2 [c2 [m2 [Hstep2 [HS Hpre2]]]]];
        [eassumption | now econstructor; eauto | ]. inv Hstep2.
      repeat eexists.
      + econstructor; eauto. simpl. rewrite peq_false. eassumption.
        rewrite H8 in Hget'; inv Hget'. rewrite H9 in Hget2; inv Hget2.
        eassumption.
      + eapply Hyp2. rewrite <- plus_n_O in *. eassumption.
      + rewrite cc_approx_val_eq in *.
        eapply cc_approx_val_monotonic. eassumption. omega.
  Qed.
  
  Lemma cc_approx_exp_halt_compat (k : nat) (P : GInv) (P1 : Inv) (Ph : HInv)
        rho1 rho2 H1 H2 x1 x2 :
    cc_approx_var_env k P H1 rho1 H2 rho2 x1 x2 ->
    (forall m1 m2, Ph m1 m2 -> P1 (1, m1) (1, m2)) ->
    Ph (size_heap H1) (size_heap H2) ->
    (Ehalt x1, rho1, H1) ⪯ ^ (k ; P1; P) (Ehalt x2, rho2, H2).
  Proof.
    intros Henv Hc Hi v1 c1 m1 Hleq1 Hstep1. inv Hstep1.
    edestruct Henv as [v' [Hget Hpre]]; eauto.
    repeat eexists; eauto. now econstructor; eauto.
    rewrite cc_approx_val_eq in *.
    eapply cc_approx_val_monotonic. eassumption. omega.
  Qed.

  Lemma cc_approx_exp_app_compat (k : nat) (P : GInv) (P1 : Inv) (Ph : HInv)
        rho1 rho2 H1 H2 t f1 xs1 f2 f2' Γ xs2 :
    cc_approx_var_env k P H1 rho1 H2 rho2 f1 f2 ->
    Forall2 (cc_approx_var_env k P H1 rho1 H2 rho2) xs1 xs2 ->
    (forall m1 m2, Ph m1 m2 -> P1 (1 + length xs1, m1) (1 + length xs1, m2)) ->
    Ph (size_heap H1) (size_heap H2) ->
    (Eapp f1 t xs1, rho1, H1) ⪯ ^ (k ; P1; P)
    (Eproj f2' clo_tag 0%N f2
           (Eproj Γ clo_tag 1%N f2
                  (Eapp f2' t (Γ :: xs2))), rho2, H2).
  Proof.
    intros Henv Hall Hc Hi v1 c1 m1 Hleq1 Hstep1. inv Hstep1.
    edestruct Henv as [l' [Hget' Hcc']]; eauto.
    edestruct (cc_approx_var_env_getlist k P rho1 rho2) as [ls2 [Hgetl' Hcc'']];
      [| eauto |]; eauto.
    simpl in Hcc'. rewrite H6 in Hcc'.
    destruct (get l' H2) eqn:Hget2; try contradiction.
    destruct v; try contradiction. destruct l0; try contradiction.
    destruct l1; try contradiction.
    destruct Hcc' as [rho2' [B' [Hget HallB]]].
  Abort.

End  CC_log_rel.