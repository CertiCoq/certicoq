(* Step-indexed logical relations for L6.  Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles.
Require Import L6.cps L6.eval L6.cps_util L6.identifiers L6.ctx
        L6.Ensembles_util L6.List_util L6.size_cps L6.tactics L6.set_util.
Require Import compcert.lib.Coqlib.

Import ListNotations.

Close Scope Z_scope.

Section Log_rel.

  Variable (pr : prims).
  Variable (cenv : ctor_env).
  
  (* Tag for closure records *)
  Variable (clo_tag : ctor_tag). 
  
  (** step-indexed preorder on cps terms *)
  (* Expression relation : 
   * ---------------------
   *  (e1, ρ1) ~_k (e2, ρ2) iff 
   *    forall c1 <= k, 
   *      ρ1 |- e1 ->^c1 v1 -> 
   *      exists v2, p2 |- e2 -> v2 /\ v1 ~_(k-c1) v2 
   * Value relation :
   * ----------------
   * Integers: (n1 ~_k n2) iff n1 = n2
   * Constructors: [v_1, .., v_n] ~_k [v'_1, .., v'_m] iff
                     n <= m /\ v_1 ~_k v'_1 /\ ... /\ v_n ~_k v'_n'
   * Closures: (\f1 x1. e1, ρ1) ~_k (\f2 x2. e2, ρ2) iff 
   *              \forall v1 v2 i < k, v1 ~_j v2 => 
   *                (e1, ρ1[x1 -> v1, f1 -> (\f1 x1. e1, ρ1)]) ~_j 
   *                (e2, ρ2[x2 -> v2, f2 -> (\f2 x2. e2, ρ2)])
   *)
  Fixpoint preord_val (k : nat) (P : nat -> relation (exp * env *  nat)) (v1 v2 : val) {struct k} : Prop :=
    let preord_exp (k : nat) (p1 p2 : exp * env) : Prop :=
        let '(e1, rho1) := p1 in
        let '(e2, rho2) := p2 in
        forall v1 c1,
           c1 <= k -> bstep_cost pr cenv rho1 e1 v1 c1 ->
           exists v2 c2, bstep_cost pr cenv rho2 e2 v2 c2 /\
                    P k (e1, rho1, c1) (e2, rho2, c2) /\
                    preord_val (k - c1) P v1 v2
    in
    let fix preord_val_aux (v1 v2 : val) {struct v1} : Prop :=
        let fix Forall2_aux vs1 vs2 :=
            match vs1, vs2 with
              | [], _ => True
              | v1 :: vs1, v2 :: vs2 =>
                preord_val_aux v1 v2 /\ Forall2_aux vs1 vs2
              | _, _ => False
            end
        in
        match v1, v2 with
          | Vfun rho1 defs1 f1, Vfun rho2 defs2 f2 =>
            forall (vs1 vs2 : list val) (j : nat) (t : fun_tag) 
              (xs1 : list var) (e1 : exp) (rho1' : env),
              List.length vs1 = List.length vs2 ->
              find_def f1 defs1 = Some (t, xs1, e1) ->
              Some rho1' = set_lists xs1 vs1 (def_funs defs1 defs1 rho1 rho1) ->
              exists (xs2 : list var) (e2 : exp) (rho2' : env),
                find_def f2 defs2 = Some (t, xs2, e2) /\
                Some rho2' = set_lists xs2 vs2 (def_funs defs2 defs2 rho2 rho2) /\
                match k with
                  | 0 => True
                  | S k =>
                    let R := preord_val (k - (k-j)) P in
                    j < S k ->
                    Forall2 R vs1 vs2 ->
                    preord_exp (k - (k - j)) (e1, rho1') (e2, rho2')
                end
          | Vconstr t1 vs1, Vconstr t2 vs2 =>
            t1 = t2 /\ Forall2_aux vs1 vs2
          | Vint n1, Vint n2 => n1 = n2
          | _, _ => False
        end
    in preord_val_aux v1 v2.
           
  Definition preord_exp (k : nat)
             (P1 : relation nat) (P2 : nat -> relation (exp * env * nat)) 
             (p1 p2 : exp * env) : Prop :=
    let '(e1, rho1) := p1 in
    let '(e2, rho2) := p2 in
    forall v1 c1,
      c1 <= k -> bstep_cost pr cenv rho1 e1 v1 c1 ->
      exists v2 c2, bstep_cost pr cenv rho2 e2 v2 c2 /\
               P1 c1 c2 /\
               preord_val (k - c1) P2 v1 v2.
  
  (** a more compact definition of the value preorder *)
  Definition preord_val' (k : nat) (P : nat -> relation (exp * env * nat))
             (v1 v2 : val) : Prop :=
    match v1, v2 with
      | Vfun rho1 defs1 f1, Vfun rho2 defs2 f2 =>
        forall (vs1 vs2 : list val) j (t : fun_tag) (xs1 : list var)
          (e1 : exp) (rho1' : env),
          List.length vs1 = List.length vs2 -> 
          find_def f1 defs1 = Some (t, xs1, e1) ->
          Some rho1' = set_lists xs1 vs1 (def_funs defs1 defs1 rho1 rho1) ->
          exists (xs2 : list var) (e2 : exp) (rho2' : env),
            find_def f2 defs2 = Some (t, xs2, e2) /\
            Some rho2' = set_lists xs2 vs2 (def_funs defs2 defs2 rho2 rho2) /\
            (j < k -> Forall2 (preord_val j P) vs1 vs2 ->
             preord_exp j (fun c1 c2 => P j (e1, rho1', c1) (e2, rho2', c2)) P
                        (e1, rho1') (e2, rho2'))
      | Vconstr t1 vs1, Vconstr t2 vs2 =>
        t1 = t2 /\ Forall2_asym (preord_val k P) vs1 vs2
      | Vint n1, Vint n2 => n1 = n2
      | _, _ => False
    end.

  (** correspondence of the two definitions *)
  Lemma preord_val_eq (k : nat) P (v1 v2 : val) :
    preord_val k P v1 v2 <-> preord_val' k P v1 v2.
  Proof.
    destruct k as [ | k ]; destruct v1; destruct v2;
    eauto; try (split; intros H; (now simpl in H; inv H)).
    - split.
      * revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        try (now intros [H1 H2]; split; eauto; inv H2).
        intros H; split; destruct H as [H1 [H2 H3]]; eauto.
        constructor; [ now eauto | now eapply IHxs ].
      * revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        try (now intros [H1 H2]; split; eauto; inv H2).
        intros H; split; inv H; eauto. inv H1.
        split; [ now eauto | now eapply IHxs ].
    - split; intros Hpre; simpl; intros; 
      edestruct (Hpre vs1 vs2 0) as [xs2 [e2 [rho' [H1' [H2' H3']]]]];
      eauto; do 4 eexists; repeat split; eauto; intros Hc; exfalso; omega.
    - revert l0; induction l as [| x xs IHxs];
      intros l2; destruct l2 as [| y ys ];
      split; intros H; try (now simpl in H; inv H); try now (simpl; eauto).
      + destruct H as [Heq [H1 H2]]; subst.  
        constructor; eauto. constructor; eauto. eapply IHxs.
        constructor; eauto.
      + inv H. inv H1. split. reflexivity.
        split. now eauto. eapply IHxs. split; eauto. 
    - split; intros Hpre; simpl; intros;
        try now (edestruct Hpre as [xs2 [e2 [rho' [H1' [H2' H3']]]]]; eauto;
                 do 3 eexists; do 2 (split; eauto); intros Hleq Hf v1 c1 Hleq' Hstep;
                 (assert (Heq : k - (k - j) = j) by omega); rewrite Heq in *;
                 eapply H3'; eauto). 
  Qed.

  Global Opaque preord_val.
  

  (** Environment relation for a single point (i.e. variable) : 
    * ρ1 ~_k^(x, y) ρ2 iff ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition preord_var_env (k : nat) PG (rho1 rho2 : env) (x y : var) : Prop :=
    forall v1, 
      M.get x rho1 = Some v1 -> 
      exists v2, M.get y rho2 = Some v2 /\ preord_val k PG v1 v2.
    
  (** Environment relation for a set of points (i.e. predicate over variables) : 
    * ρ1 ~_k^S ρ2 iff 
    *   forall x, S x -> ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
  Definition preord_env_P (S : Ensemble var) k PG rho1 rho2 :=
    forall (x : var), S x -> preord_var_env k PG rho1 rho2 x x.

  (** Environment relation for the whole domain of definition :
    * ρ1 ~_k ρ2 iff forall x, ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
  Definition preord_env (k : nat) PG (rho1 rho2 : env) : Prop :=
    preord_env_P (fun _ => True) k PG rho1 rho2.
  
  Open Scope ctx_scope.

  (** Context relation. *)
  Definition preord_ctx (k : nat) P PG (rho1 rho2 : env)
             (p1 p2 : exp_ctx * env) :=
    let '(c1, rho1') := p1 in
    let '(c2, rho2') := p2 in
    forall e1 e2, preord_exp k P PG (e1, rho1) (e2, rho2) ->
             preord_exp k P PG (c1 |[ e1 ]|, rho1')
                        (c2 |[ e2 ]|, rho2').

  Section PostCond.
    
    (* Postcondition parameter *)
    Context (P : relation nat) (* Local *)
            (PG : nat -> relation (exp * env * nat)). (* Global *)           

  (** Lemmas about extending the environment *)
  Lemma preord_var_env_extend_eq :
    forall (rho1 rho2 : env) (k : nat) (x : var) (v1 v2 : val),
      preord_val k PG v1 v2 ->
      preord_var_env k PG (M.set x v1 rho1) (M.set x v2 rho2) x x.
  Proof.
    intros rho1 rho2 k x v1 v2 Hval x' Hget.
    rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss. split; eauto.
  Qed.
  
  Lemma preord_var_env_extend_neq :
    forall (rho1 rho2 : env) (k : nat) (x y : var) (v1 v2 : val),
      preord_var_env k PG rho1 rho2 y y ->
      y <> x ->
      preord_var_env k PG (M.set x v1 rho1) (M.set x v2 rho2) y y.
  Proof.
    intros rho1 rho2 k x  y v1 v2 Hval Hneq x' Hget.
    rewrite M.gso in *; eauto.
  Qed.

  Lemma preord_var_env_extend :
    forall (rho1 rho2 : env) (k : nat) (x y : var) (v1 v2 : val),
      preord_var_env k PG rho1 rho2 y y ->
      preord_val k PG v1 v2 ->
      preord_var_env k PG (M.set x v1 rho1) (M.set x v2 rho2) y y.
  Proof.
    intros rho1 rho2 k x y v1 v2 Henv Hval.
    destruct (peq y x); subst.
    - apply preord_var_env_extend_eq; eauto.
    - apply preord_var_env_extend_neq; eauto.
  Qed.

  (** The environment relation is antimonotonic in the set
    * of free variables *) 
  Lemma preord_env_P_antimon (P1 P2 : var -> Prop) k rho1 rho2 :
    preord_env_P P2 k PG rho1 rho2 ->
    (Included var P1 P2) ->
    preord_env_P P1 k PG rho1 rho2.
  Proof.
    intros Hpre Hin x HP2. eapply Hpre; eapply Hin; eauto.
  Qed.

  (** Lemmas about the sets that index the environment relation *)
  Lemma preord_env_Empty_set k (rho1 rho2 : env) :
    preord_env_P (Empty_set var) k PG rho1 rho2.
  Proof.
    intros x H. inv H.
  Qed.
  
  Lemma preord_env_P_union (P1 P2 : var -> Prop) k rho1 rho2 :
    preord_env_P P1 k PG rho1 rho2 ->
    preord_env_P P2 k PG rho1 rho2 ->
    preord_env_P (Union var P1 P2) k PG rho1 rho2.
  Proof.
    intros Hpre1 Hpre2 x HP2. inv HP2; eauto.
  Qed.

  Lemma preord_env_P_inter_l (P1 P2 : var -> Prop) k rho1 rho2 :
    preord_env_P P1 k PG rho1 rho2 ->
    preord_env_P (Intersection var P1 P2) k PG rho1 rho2.
  Proof.
    intros Hpre x HP2. inv HP2; eauto.
  Qed.

  Lemma preord_env_P_inter_r (P1 P2 : var -> Prop) k rho1 rho2 :
    preord_env_P P2 k PG rho1 rho2 ->
    preord_env_P (Intersection var P1 P2) k PG rho1 rho2.
  Proof.
    intros Hpre x HP2.
    inv HP2; eauto.
  Qed.

  (** Extend the related environments with a single point *)
  Lemma preord_env_P_extend :
    forall P (rho1 rho2 : env) (k : nat) (x : var) (v1 v2 : val),
      preord_env_P (Setminus var P (Singleton var x)) k PG rho1 rho2 ->
      preord_val k PG v1 v2 ->
      preord_env_P P k PG (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros S rho1 rho2 k x v1 v2 Henv Hval x' HP v1' Hget.
    rewrite M.gsspec in Hget. destruct (peq x' x); subst.
    - inv Hget. eexists. rewrite M.gss. split; eauto.
    - apply Henv in Hget; eauto. destruct Hget as [v2' [Heq Hpre]].
      eexists; split; eauto. rewrite M.gso; eauto. constructor; eauto.
      intros Hin. inv Hin. congruence.
  Qed.

  (** Extend the related environments with a list *)
  Lemma preord_env_P_set_lists_l:
    forall (P1 P2 : var -> Prop) (rho1 rho2 rho1' rho2' : env)
      (k : nat) (xs : list var) (vs1 vs2 : list val),
      preord_env_P P1 k PG rho1 rho2 ->
      (forall x, ~ List.In x xs -> P2 x -> P1 x) ->
      Forall2 (preord_val k PG) vs1 vs2 ->
      set_lists xs vs1 rho1 = Some rho1' ->
      set_lists xs vs2 rho2 = Some rho2' ->
      preord_env_P P2 k PG rho1' rho2'.
  Proof. 
    intros P1 P2 rho1' rho2' rho1 rho2 k xs vs1 vs2 Hpre Hyp Hall Hset1 Hset2
           x HP v Hget.
    destruct (in_dec var_dec x xs).
    - edestruct (@set_lists_Forall2_get val) as [v1 [v2 [Hget1 [Hget2 HP']]]]; eauto.
      rewrite Hget in Hget1. inv Hget1. repeat eexists; eauto.
    - erewrite <- set_lists_not_In in Hget; eauto.
      edestruct Hpre as [v2 [Hget' Hpre']]; eauto.
      repeat eexists; eauto. erewrite <- set_lists_not_In; eauto.
  Qed.

  
  Lemma preord_var_env_get_list (rho1 rho2 : env) (k : nat)
        (xs ys : list var) (vs1 : list val) :
    Forall2 (preord_var_env k PG rho1 rho2) xs ys ->
    get_list xs rho1 = Some vs1 ->
    exists vs2,
      get_list ys rho2 = Some vs2 /\ Forall2 (preord_val k PG) vs1 vs2.
  Proof.
    revert ys vs1. induction xs as [| x xs IHxs]; intros ys vs2 Hall Hget.
    - destruct ys; inv Hall. inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget.
      destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (get_list xs rho1) eqn:Heq2; try discriminate. inv Hget.
      destruct ys as [| y ys]; inv Hall. 
      destruct (IHxs ys l H4 eq_refl) as [vs2 [Hget HAll]].
      destruct (H2 _ Heq1) as [v2 [Heq Hpre]].
      eexists. split; simpl; eauto. rewrite Hget, Heq. eauto.
  Qed.

  Lemma preord_env_P_get_list_l (S : var -> Prop) (rho1 rho2 : env) (k : nat)
        (xs : list var) (vs1 : list val) :
    preord_env_P S k PG rho1 rho2 ->
    Included _ (FromList xs) S ->
    get_list xs rho1 = Some vs1 ->
    exists vs2,
      get_list xs rho2 = Some vs2 /\ Forall2 (preord_val k PG) vs1 vs2.
  Proof.
    intros Henv. revert vs1.
    induction xs as [| x xs IHxs]; intros vs1 Hp Hget.
    - inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget. destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (get_list xs rho1) eqn:Heq2; try discriminate. inv Hget.
      edestruct (IHxs l) as  [vs2 [Hget HAll]]; eauto.
      + intros x' Hin. eapply Hp. constructor 2; eauto.
      + eapply Henv in Heq1. destruct Heq1 as [v2 [H1 H2]].
        eexists. split; simpl; eauto. rewrite H1. rewrite Hget.
        constructor. apply Hp. now constructor.
  Qed.
  
  Corollary preord_env_get_list_l (rho1 rho2 : env) (k : nat)
        (xs : list var) (vs1 : list val) :
    preord_env k PG rho1 rho2 ->
    get_list xs rho1 = Some vs1 ->
    exists vs2,
      get_list xs rho2 = Some vs2 /\ Forall2 (preord_val k PG) vs1 vs2.
  Proof.
    intros. eapply preord_env_P_get_list_l; eauto.
    intros x H'; simpl; eauto.
  Qed.

  Corollary preord_env_extend (rho1 rho2 : env) (k : nat)
        (x : var) (v1 v2 : val) :
    preord_env k PG rho1 rho2 ->
    preord_val k PG v1 v2 ->
    preord_env k PG (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros H1 Hval. apply preord_env_P_extend; eauto.
    eapply preord_env_P_antimon; eauto. intros x' H; simpl; eauto.
  Qed.

  Lemma preord_env_refl k :
    Reflexive (preord_val k PG) ->
    Reflexive (preord_env k PG).
  Proof.
    intros H r. intros; eexists; eauto.
  Qed.

  Corollary preord_env_set_lists_l (rho1 rho2 rho1' rho2' : env) (k : nat)
        (xs : list var) (vs1 vs2 : list val) :
    preord_env k PG rho1 rho2 ->
    Forall2 (preord_val k PG) vs1 vs2 ->
    set_lists xs vs1 rho1 = Some rho1' ->
    set_lists xs vs2 rho2 = Some rho2' ->
    preord_env k PG rho1' rho2'.
  Proof.
    intros. eapply preord_env_P_set_lists_l; eauto.
  Qed.

  (** * Index Anti-Monotonicity Properties *)

  (** The value relation is anti-monotonic in the step index *)
  Lemma preord_val_monotonic (k : nat) :
    (forall v1 v2 j,
       preord_val k PG v1 v2 -> j <= k -> preord_val j PG v1 v2).
  Proof.
    intros v1 v2 h Hpre Hleq. try rewrite preord_val_eq in *.
    revert v2 Hpre; induction v1 using val_ind'; intros v2 Hpre;
    destruct v2; try (simpl; contradiction); eauto.
    - destruct l; try now inv Hpre.
    - inv Hpre. inv H0.
      split; auto. constructor; eauto; rewrite preord_val_eq in *.
      eapply IHv1; eauto.
      destruct (IHv0 ((Vconstr c l'))) as [Heq Hpre']; eauto.
      simpl. split; eauto.
    - intros vs1 vs2 j t1 xs e1 rho1' Hlen Hf Heq.
      edestruct Hpre as [xs2 [e2 [rho2' [H1 [H2 H3]]]]]; eauto.
      do 3 eexists; split; eauto. split; eauto. intros Hleq' Hall. 
      eapply H3; eauto. omega. 
  Qed.
  
  (** The expression relation is anti-monotonic in the step index *)
  Lemma preord_exp_monotonic (k : nat) :
    (forall rho1 e1 rho2 e2 j,
       preord_exp k P PG (rho1, e1) (rho2, e2) ->
       j <= k -> preord_exp j P PG (rho1, e1) (rho2, e2)).
  Proof.
    intros rho1 e1 rho2 e2 j Hpre Hleq v1 c1 Hlt Hstep.
    edestruct (Hpre v1 c1) as [v2 [c2 [H1 [H2 H3]]]]; eauto. omega.
    do 2 eexists; split; eauto. split; eauto.
    eapply preord_val_monotonic. eassumption. omega.
  Qed.

  (** The environment relations are monotonic in the step index *)
  Lemma preord_env_P_monotonic :
    forall S (k j : nat) (rho1 rho2 : env),
      j <= k -> preord_env_P S k PG rho1 rho2 -> preord_env_P S j PG rho1 rho2.
  Proof.
    intros S k j rho1 rho2 Hleq Hpre x HP v Hget.
    edestruct Hpre as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto. eapply preord_val_monotonic; eauto.
  Qed.
  
  Lemma preord_env_monotonic k j rho1 rho2 :
    j <= k -> preord_env k PG rho1 rho2 -> preord_env j PG rho1 rho2.
  Proof.
    intros Hleq H. eapply preord_env_P_monotonic; eauto.
  Qed.

  End PostCond.

  (** * Compatibility Properties of Post-conditions *)

  Definition Post := relation nat.
  Definition PostG := nat -> relation (exp * env * nat).
      
  Definition post_compat (P1 P2 : Post) :=
    forall c1 c2 a, P1 c1 c2 -> P2 (c1 + a) (c2 + a).        

  Definition post_refl (P1 : Post) :=
    forall c, P1 c c.
  
  Definition post_app_compat (PG : PostG) (P1 : Post) :=
    (* Maybe for certain postconditions we'll need to strengthen the assumptions here *)
    forall k e1 e2 rho1 rho2 c1 c2 a,
      PG k (e1, rho1, c1) (e2, rho2, c2) ->
      P1 (c1 + a) (c2 + a).

  Definition post_letapp_compat (PG : PostG) (P1 P2 : Post) :=
    (* Maybe for certain postconditions we'll need to strengthen the assumptions here *)
    forall k e1 e2 rho1 rho2 c1 c2 c1' c2' a,
      PG (k - 1) (e1, rho1, c1) (e2, rho2, c1') ->
      P1 c2 c2' ->
      P2 (c1 + c2 + a) (c1' + c2' + a).

  Section Compat.
    Context (P1 P2 : relation nat) (* Local *)
            (PG : nat -> relation (exp * env * nat)) (* Global *)           
            (HPost : post_compat P1 P2)
            (HPostApp : post_app_compat PG P1)
            (HPostLetApp : post_letapp_compat PG P1 P2)
            (HPostRefl : post_refl P1).
    
    
  (** * Compatibility Properties *)

    Lemma preord_exp_const_compat k rho1 rho2 x x' t ys1 ys2 e1 e2 :
      Forall2 (preord_var_env k PG rho1 rho2) ys1 ys2 ->
      (forall vs1 vs2 : list val,
          Forall2 (preord_val k PG) vs1 vs2 ->
          preord_exp k P1 PG (e1, M.set x (Vconstr t vs1) rho1)
                     (e2, M.set x' (Vconstr t vs2) rho2)) ->
      preord_exp k P2 PG (Econstr x t ys1 e1, rho1) (Econstr x' t ys2 e2, rho2).
    Proof.
      intros Hall Hpre v1 c1 Hleq1 Hstep1. inv Hstep1.
      edestruct (preord_var_env_get_list PG rho1 rho2) as [vs2' [Hget' Hpre']];
        [| eauto |]; eauto.
      edestruct Hpre as [v2 [c2 [Hstep [Hpost Hval]]]]; [| | eassumption | ]; eauto.
      omega. 
      repeat eexists. now econstructor; eauto.
      rewrite <- !plus_assoc.
      erewrite get_list_length_eq; [| eassumption ]. 
      erewrite get_list_length_eq; [| eassumption ]. 
      erewrite Forall2_length; [| eassumption ]. 
      eapply HPost. eassumption.
      eapply preord_val_monotonic. eassumption. omega.
    Qed.

    Lemma preord_exp_proj_compat k rho1 rho2 x x' tau n y1 y2 e1 e2 :
      preord_var_env k PG rho1 rho2 y1 y2 ->
      (forall v1 v2,
          preord_val k PG v1 v2 -> 
          preord_exp k P1 PG (e1, M.set x v1 rho1)
                     (e2, M.set x' v2 rho2)) ->
      preord_exp k P2 PG (Eproj x tau n y1 e1, rho1) (Eproj x' tau n y2 e2, rho2).
    Proof.
      intros Henv Hexp v1 c1 Hleq1 Hstep1. inv Hstep1.
      edestruct Henv as [v' [Hget Hpre]]; eauto.
      destruct v'; rewrite preord_val_eq in Hpre; simpl in Hpre; try contradiction.
      inv Hpre.
      edestruct (Forall2_asym_nthN (preord_val k PG) vs l) as [v2 [Hnth Hval]];
        try eassumption.
      edestruct Hexp as [v2' [c2 [Hstep [Hpost Hval']]]]; [ | | eassumption | ]; eauto.
      omega.
      repeat eexists; eauto. 
      econstructor; eauto.
      eapply preord_val_monotonic. eassumption. omega.
    Qed.

    Lemma Forall2_Forall2_asym_included {A} R (l1 l2 : list A) :
      Forall2 R l1 l2 ->
      Forall2_asym R l1 l2.
    Proof.
      intros H. induction H; eauto.
    Qed.    
    
    Lemma preord_exp_app_compat k rho1 rho2 x1 x2 ft ys1 ys2 :
      preord_var_env k PG rho1 rho2 x1 x2 ->
      Forall2 (preord_var_env k PG rho1 rho2) ys1 ys2 ->
      preord_exp k P1 PG (Eapp x1 ft ys1, rho1) (Eapp x2 ft ys2, rho2).
    Proof.
      intros Hvar Hall v1 c1 Hleq1 Hstep1. inv Hstep1.
      edestruct Hvar as [v2' [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v2'; try (now simpl in Hpre; contradiction).
      edestruct preord_var_env_get_list as [vs2 [Hget' Hpre']]; eauto.
      edestruct (Hpre vs vs2 (k-1)) as [xs2 [e2 [rho2' [Hf [Hset H']]]]]; eauto.
      now eapply Forall2_length; eauto.
      edestruct H' with (c1 := c) as [v2 [c2 [Hstep' [Hpost' Hpre'']]]];
        eauto; try omega.
      - eapply Forall2_monotonic; [| now eauto ].
        intros. eapply (preord_val_monotonic PG k); [ now eauto | omega ].
      - repeat eexists. econstructor 4; eauto.
        erewrite get_list_length_eq; [| eassumption ]. 
        erewrite get_list_length_eq; [| eassumption ]. 
        erewrite Forall2_length; [| eassumption ].
        rewrite <- !plus_assoc. eapply HPostApp. eassumption.
        eapply preord_val_monotonic. eassumption. omega.
    Qed.

    Lemma preord_exp_letapp_compat k rho1 rho2 x x' f1 f2 ft ys1 ys2 e1 e2 :
      preord_var_env k PG rho1 rho2 f1 f2 ->
      Forall2 (preord_var_env k PG rho1 rho2) ys1 ys2 ->
      (forall m v1 v2,
          m <= k ->
          preord_val m PG v1 v2 -> 
          preord_exp m P1 PG (e1, M.set x v1 rho1)
                     (e2, M.set x' v2 rho2)) ->
      preord_exp k P2 PG (Eletapp x f1 ft ys1 e1, rho1) (Eletapp x' f2 ft ys2 e2, rho2).
    Proof.
      intros Henv Hall Hexp v1 c1 Hleq1 Hstep1. inv Hstep1.
      edestruct Henv as [v' [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v'; try (now simpl in Hpre; contradiction).
      edestruct preord_var_env_get_list as [vs2 [Hget' Hpre']]; eauto.
      edestruct (Hpre vs vs2 (k-1)) as [xs2 [e2' [rho2' [Hf [Hset H']]]]]; eauto.
      now eapply Forall2_length; eauto.
      edestruct H' with (c1 := c) as [v2 [c2 [Hstep' [Hpost' Hpre'']]]].
      omega.
      eapply Forall2_monotonic; [| eassumption ]. intros. eapply preord_val_monotonic.
      eassumption. omega. 
      omega. eassumption.
      edestruct Hexp as [v2' [c3 [Hstep [Hpost Hval']]]]; [ | eassumption | | eassumption | ]; eauto.
      omega. omega. 
      repeat eexists. 
      now econstructor; eauto.
      erewrite get_list_length_eq; [| eassumption ]. 
      erewrite get_list_length_eq; [| eassumption ]. 
      erewrite Forall2_length; [| eassumption ].
      rewrite <- !(plus_assoc _ 1 _).
      eapply HPostLetApp. eassumption. eassumption.
      eapply preord_val_monotonic. eassumption. omega.
    Qed.

    Lemma preord_exp_halt_compat k rho1 rho2 x1 x2  :
      preord_var_env k PG rho1 rho2 x1 x2 ->
      preord_exp k P1 PG (Ehalt x1, rho1) (Ehalt x2, rho2).
    Proof.
      intros Hvar v1 c1 Hleq1 Hstep1. inv Hstep1.
      edestruct Hvar as [v2' [Hget Hpre]]; eauto.
      repeat eexists. now econstructor; eauto. now eapply HPostRefl.
      eapply preord_val_monotonic. eassumption. omega.
    Qed.
    
    Lemma preord_exp_case_nil_compat k rho1 rho2 x1 x2 :
      preord_exp k P1 PG (Ecase x1 [], rho1) (Ecase x2 [], rho2).
    Proof.
      intros v1 c1 Hleq1 Hstep1. inv Hstep1. inv H4.
    Qed.

    Lemma preord_exp_case_cons_compat k rho1 rho2 x1 x2 c e1 e2 D1 D2:
      post_compat P2 P2 -> 
      Forall2 (fun p p' => fst p = fst p') D1 D2 ->
      preord_var_env k PG rho1 rho2 x1 x2 ->
      preord_exp k P1 PG (e1, rho1) (e2, rho2) ->
      preord_exp k P2 PG (Ecase x1 D1, rho1)
                 (Ecase x2 D2, rho2) ->
      preord_exp k P2 PG (Ecase x1 ((c, e1) :: D1), rho1)
                 (Ecase x2 ((c, e2) :: D2), rho2).
    Proof.
      intros HPost2 Hall Henv Hexp_hd Hexp_tl v1 c1 Hleq1 Hstep1. inv Hstep1.
      destruct (M.elt_eq c t) eqn:Heq; subst.
      - inv H4; subst; [| contradiction ].
        edestruct Hexp_hd as [v2 [c2 [Hstep2 [Hpost Hpre2]]]]; [ | eassumption | ]; eauto. omega.
        edestruct Henv as [v2' [Hget Hpre]]; eauto.
        rewrite preord_val_eq in Hpre.
        destruct v2'; try (now simpl in Hpre; contradiction). inv Hpre. 
        repeat eexists. econstructor; eauto.
        
        eapply caseConsistent_same_ctor_tags;
          [ econstructor; [ | eassumption ] | eassumption ].
        simpl; reflexivity.
        constructor.
        eapply HPost. eassumption.
        eapply preord_val_monotonic. eassumption. omega.
      - inv H4. contradiction. inv H2. 
        edestruct Hexp_tl with (c1 := c0 + n1) as [v2 [c2 [Hstep2 [Hpost2 Hpre2]]]].
        + omega. 
        + econstructor; eauto. 
        + inv Hstep2.
          eapply Henv in H1. destruct H1 as [v2' [Hgetx2 Hval]].
          rewrite Hgetx2 in H2. inv H2. rewrite preord_val_eq in Hval. inv Hval.
          repeat eexists. 
          eapply BStepc_case. eassumption.
          econstructor; eassumption.
          constructor; eassumption. 
          eassumption.
          (* assert (Heqn1 : n1 = n) *)
          (*   by (eapply find_tag_nth_same_tags with (n := n1); eauto). *)
          rewrite !plus_assoc. eapply HPost2. eassumption.
          eapply preord_val_monotonic. eassumption. omega.
    Qed.


    Axiom Prim_axiom :
      forall f f' v1,
        M.get f pr = Some f' ->
        forall k vs1 vs2,
          Forall2 (preord_val k PG) vs1 vs2 ->
          f' vs1 = Some v1 ->
          exists v2,
            f' vs2 = Some v2 /\                      
            preord_val k PG v1 v2.
    
    Lemma preord_exp_prim_compat k rho1 rho2 x1 x2 f ys1 ys2 e1 e2 :
      Forall2 (preord_var_env k PG rho1 rho2) ys1 ys2 ->
      (forall v1 v2,
          preord_val k PG v1 v2 -> 
          preord_exp k P1 PG (e1, M.set x1 v1 rho1)
                     (e2, M.set x2 v2 rho2)) ->
      preord_exp k P2 PG (Eprim x1 f ys1 e1, rho1) (Eprim x2 f ys2 e2, rho2).
    Proof.
      intros Henv Hexp v1 c1 Hleq1 Hstep1. inv Hstep1.
      edestruct preord_var_env_get_list as [vs2 [Hget' Hpre']]; eauto.
      edestruct Prim_axiom as [v2 [Heq Hprev2]]; eauto.
      edestruct Hexp as [v2' [c2 [Hstepv2' [Hpost2 Hprev2']]]]; [ | | eassumption | ]; eauto.
      omega. repeat eexists. econstructor; eauto.
      erewrite get_list_length_eq; [| eassumption ]. 
      erewrite get_list_length_eq; [| eassumption ]. 
      erewrite Forall2_length; [| eassumption ].
      rewrite <- !plus_assoc. eapply HPost. eassumption.
      eapply preord_val_monotonic. eassumption. omega.
    Qed.

    Lemma preord_exp_fun_compat k rho1 rho2 B B' e1 e2 :
      (forall c1 c2, P1 c1 c2 -> P2 (c1 + (1 + numOf_fundefs B + PS.cardinal (fundefs_fv B)))
                              (c2 + (1 + numOf_fundefs B' + PS.cardinal (fundefs_fv B')))) ->
      preord_exp k P1 PG (e1, def_funs B B rho1 rho1)
                 (e2, def_funs B' B' rho2 rho2) ->
      preord_exp k P2 PG (Efun B e1, rho1) (Efun B' e2, rho2).
    Proof.
      intros Hyp Hexp v1 c1 Hleq1 Hstep1. inv Hstep1.
      edestruct Hexp as [v2' [c2 [Hstepv2' [Hprev2' Hpost]]]];
        [ | eassumption | ]; eauto. omega.
      repeat eexists. now econstructor; eauto.
      eapply Hyp. eassumption.
      eapply preord_val_monotonic. eassumption. omega.
    Qed.
    
  End Compat.
  
  Global Instance preord_env_proper  :
    Proper (Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
           preord_env_P.
  Proof.
    intros s1 s2 [H1 H2]; split; intros Hpre; subst; 
    eapply preord_env_P_antimon; subst; eauto. 
  Qed.



  Lemma preord_exp_post_monotonic k P1 P2 PG e1 rho1 e2 rho2 :
    inclusion _ P1 P2 ->
    preord_exp k P1 PG (e1, rho1) (e2, rho2) ->
    preord_exp k P2 PG (e1, rho1) (e2, rho2).
  Proof.
    intros Hyp Hexp v1 c2 Hleq Hstep.
    edestruct Hexp as [v2 [c2' [Hstep2 [Hp Hv]]]]; try eassumption.
    do 2 eexists; repeat split; eauto.
  Qed.

  
  Section Refl.

    (* PostCondition parameter for the reflexivity proof *)
    Context (P1 : relation nat) (* Local *)
            (PG : nat -> relation (exp * env * nat)) (* Global *)           
            (HPost : post_compat P1 P1)
            (HPostApp : post_app_compat PG P1)
            (HPostLetApp : post_letapp_compat PG P1 P1)
            (HPostRefl : post_refl P1)

            (* This asserts that the local post condition implies the global and it is
               useful for the function case. However is somewhat restrictive since it
               forces the global post to be independent from the terms and the environments.
               This simplification is OK for now since all L6 transformations seem to
               have a constant upper bound for time.
               If we want to go around this issue, we must give expressions and parameters
               to the local relation, which makes the statement of the compat requirements
               more complicated.
             *)
            (HGPost : forall m e1 e2 rho rho' c1 c2, P1 c1 c2 -> PG m (e1, rho, c1) (e2, rho', c2)).

   (** * Reflexivity Properties *)

    (** Un-nesting the function case of the reflexivity proof *)
    Lemma preord_env_P_def_funs_pre k B rho rho' B' e :
      (* The inductive hypothesis on expressions *)
      (forall m e (rho rho' : env),
          m <  k ->
          preord_env_P (occurs_free e) m PG rho rho' ->
          preord_exp m P1 PG (e, rho) (e, rho')) ->
      (* Environments are related at FV(Efun B' e) *) 
      preord_env_P (occurs_free (Efun B' e)) k PG rho rho' ->
      preord_env_P (Union _ (occurs_free (Efun B' e)) (name_in_fundefs B))
                   k PG (def_funs B' B rho rho) (def_funs B' B rho' rho').
    Proof with eauto 6 with Ensembles_DB.
      revert B rho rho' e B'.
      induction k as [ k IH' ] using lt_wf_rec1. intros B rho rho' e B'.
      induction B; intros Hyp Hpre.
      - simpl. apply preord_env_P_extend.
        + eapply preord_env_P_antimon; [ now eapply IHB; eauto | ]...
        + rewrite preord_val_eq.
          intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
          edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
          exists xs1. exists e1. exists rho2'. split; eauto.
          split; [ now eauto |]. intros Hleq Hpre'. 
          eapply preord_exp_post_monotonic.
          intros n1 n2 HP. eapply HGPost. eassumption.
          eapply Hyp. omega.
          eapply preord_env_P_set_lists_l; [| | eauto | eauto | eauto]. 
          * apply IH'; eauto. intros. apply Hyp. omega. eauto.
            eapply (preord_env_P_monotonic PG _ k); eauto. omega.
          * intros x Hin Hfr. simpl.
            apply find_def_correct in Hf; eauto.
            specialize (occurs_free_in_fun _ _ _ _ _ Hf x Hfr); intros H1.
            inv H1; eauto; try contradiction. inv H.
            now right; eauto. now left; eauto.
      - simpl. intros x HP. inv HP. inv H. apply Hpre; eauto.
        apply Hpre; eauto. inv H.
    Qed.
    
  Lemma preord_exp_refl k e rho rho' :
    preord_env_P (occurs_free e) k PG rho rho' ->
    preord_exp k P1 PG (e, rho) (e, rho').
  Proof with eauto with Ensembles_DB.
    revert e rho rho'.
    (* Well founded induction on the step-index *)
    induction k as [ k IH ] using lt_wf_rec1.
    (* Induction on e *) 
    intros e. revert k IH.
    induction e using exp_ind'; intros k IH rho rho' Henv. 
    (* Each case follows from the corresponding compat lemma *)
    - eapply preord_exp_const_compat; eauto; intros.
      * eapply Forall2_same. intros x HIn. apply Henv. now constructor.
      * eapply IHe; try eassumption. eapply preord_env_P_extend.
        eapply preord_env_P_antimon. eassumption.
        now (normalize_occurs_free; eauto with Ensembles_DB). 
        rewrite preord_val_eq. constructor; eauto using Forall2_Forall2_asym_included.
    - eapply preord_exp_case_nil_compat.
    - eapply preord_exp_case_cons_compat; eauto.
      now apply Forall2_refl.
      apply IHe; try eassumption. intros x P. apply Henv. now constructor; eauto.
      apply IHe0; try eassumption. intros x P. apply Henv. now apply Free_Ecase3; eauto.
    - eapply preord_exp_proj_compat; eauto.
      intros v1 v2 Hval. eapply IHe; try eassumption. eapply preord_env_P_extend; eauto.
      eapply preord_env_P_antimon. eassumption.
      now (normalize_occurs_free; eauto with Ensembles_DB).
    - eapply preord_exp_letapp_compat; eauto.
      eapply Henv. constructor. now left.
      eapply Forall2_same. intros. apply Henv. constructor. now right.
      intros m v1 v2 Hlt Hval. 
      eapply IHe; try eassumption. 
      intros. eapply IH; try eassumption. omega.
      eapply preord_env_P_extend; eauto.
      eapply preord_env_P_antimon.
      eapply preord_env_P_monotonic; eassumption.
      now (normalize_occurs_free; eauto with Ensembles_DB).
    - eapply preord_exp_fun_compat; eauto. 
      eapply IHe; try eassumption. eapply preord_env_P_antimon.
      eapply preord_env_P_def_funs_pre; eauto.
      now eapply occurs_free_Efun_Included.
    - eapply preord_exp_app_compat. eassumption.
      intros x HP. apply Henv; eauto.
      apply Forall2_same. intros. apply Henv. now constructor.
    - eapply preord_exp_prim_compat; eauto; intros.
      eapply Forall2_same. intros. apply Henv. now constructor.
      eapply IHe; try eassumption. eapply preord_env_P_extend; eauto.
      eapply preord_env_P_antimon. eassumption.
      now (normalize_occurs_free; eauto with Ensembles_DB).
    - eapply preord_exp_halt_compat; try eassumption.
      intros x HP. apply Henv; eauto.
   Qed.
  (* Note: I think that the above proof could go through also by mutual
     induction on expressions and function definitions and then nested induction
     at the step-index only for the function case *)

  End Refl.

  Section Rel.

    (* PostCondition parameter for the reflexivity proof *)
    Context (P1 : relation nat) (* Local *)
            (PG : nat -> relation (exp * env * nat)) (* Global *)           
            (HPost : post_compat P1 P1)
            (HPostApp : post_app_compat PG P1)
            (HPostLetApp : post_letapp_compat PG P1 P1)
            (HPostRefl : post_refl P1)

            (HGPost : forall m e1 e2 rho rho' c1 c2, P1 c1 c2 -> PG m (e1, rho, c1) (e2, rho', c2))
            
            (HPostG : forall j e1 rho1 rho2, post_compat
                                          (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2))
                                          (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2)))
            (HPostAppG : forall j e1 rho1 rho2, post_app_compat
                                             PG
                                             (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2)))
            (HPostLetAppG : forall j e1 rho1 rho2, post_letapp_compat
                                                PG
                                                (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2))
                                                (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2)))

            (HPostReflG : forall j e1 rho1 rho2, post_refl (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2)))

            (* Asserts that the global post is independent from the term and environment. Its a simplification
             * that should work for all L^ transformations *) 
            (HPostInv : forall j e1 rho1 e2 rho2 j' e1' rho1' e2' rho2' c1 c2,  PG j (e1, rho1, c1) (e2, rho2, c2) ->
                                                                           PG j' (e1', rho1', c1) (e2', rho2', c2)).
  
  Lemma preord_env_P_def_funs k B rho rho' B' S1 :
    preord_env_P (fun x => (~ name_in_fundefs B' x /\ S1 x) \/
                        occurs_free_fundefs B' x) k PG rho rho' ->
    preord_env_P (fun x => (~ name_in_fundefs B' x /\ S1 x) \/
                           occurs_free_fundefs B' x \/ name_in_fundefs B x)
                 k PG (def_funs B' B rho rho) (def_funs B' B rho' rho').
  Proof.
    intros Hpre.
    revert B rho rho' B' Hpre.
    induction k as [ k IH' ] using lt_wf_rec1. intros B rho rho' B' Hpre.
    induction B.
    - simpl. apply preord_env_P_extend.
      + intros x H. inv H. eapply IHB; eauto.
        inv H0; eauto. inv H; eauto. inv H0; try contradiction; eauto.
      + rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
        edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
        exists xs1. exists e1. exists rho2'. split; eauto.
        split. eauto. intros Hleq Hpre'.
        eapply preord_exp_refl; eauto.
        
        eapply preord_env_P_set_lists_l; [| | eauto | eauto | eauto].
        apply IH'; eauto. 
        eapply (preord_env_P_monotonic PG _ k); eauto. omega.
        intros x Hin Hfr. 
        apply find_def_correct in Hf.
        edestruct (occurs_free_in_fun _ _ _ _ _ Hf x Hfr);
          eauto; try contradiction.
        inv H; eauto.
    - simpl. intros x HP. inv HP. apply Hpre; eauto. inv H.
      apply Hpre; eauto. inv H0.
  Qed.

  Corollary preord_env_P_def_funs_cor k B rho rho' S1 :
    preord_env_P (Union var (Setminus var S1 (name_in_fundefs B))
                        (occurs_free_fundefs B)) k PG rho rho' ->
    preord_env_P S1 k PG (def_funs B B rho rho) (def_funs B B rho' rho').
  Proof.
    intros Hpre. eapply preord_env_P_antimon.
    - eapply preord_env_P_def_funs; eauto.
      eapply preord_env_P_antimon; eauto.
      intros x HS. inv HS. inv H. left. constructor; eauto.
      right; eauto.
    - intros x HS.
      destruct (@Dec _ _ (Decidable_name_in_fundefs B) x); eauto.
  Qed.
  
  Lemma preord_exp_refl_weak (k : nat) e rho rho' :
      preord_env k PG rho rho' ->
      preord_exp k (fun c1 c2 : nat => PG k (e, rho, c1) (e, rho', c2)) PG (e, rho) (e, rho').
  Proof.
    intros Henv. eapply preord_exp_refl; try eauto.
    eapply preord_env_P_antimon; eauto.
    intros x H; simpl; eauto.
  Qed.
  
  Lemma preord_val_refl (k : nat) :
    Reflexive (preord_val k PG).
  Proof.
    induction k using lt_wf_rec1.
    destruct k as [| k]; unfold Reflexive; intros x; rewrite preord_val_eq;
    induction x using val_ind'; simpl; eauto;
    try (now (try split; eauto); econstructor; eauto; rewrite preord_val_eq; eauto).
    - split; eauto. constructor; eauto. rewrite preord_val_eq; eauto.
      destruct IHx0. eauto.
    - intros.
      edestruct (set_lists_length (def_funs f0 f0 t t) (def_funs f0 f0 t t))
        as [rho2' Hset']; eauto.
      do 3 eexists; split; eauto. split; eauto. intros Hc.
      exfalso. omega.
    - split; eauto. constructor; eauto. rewrite preord_val_eq; eauto.
        destruct IHx0. eauto.
    - intros.
      edestruct (set_lists_length (def_funs f0 f0 t t) (def_funs f0 f0 t t))
        as [rho2' Hset']; eauto.
      do 3 eexists; eauto. split; eauto.
      split; eauto.
      intros Hleq Hall v1 c Hleq' Hstep. 
      eapply preord_exp_refl_weak; eauto.
      eapply preord_env_set_lists_l; eauto.
      eapply preord_env_refl; eauto.
  Qed.

  Lemma preord_env_P_refl S k rho :
    preord_env_P S k PG rho rho.
  Proof.
    intros x Px v Hget.
    eexists; split; eauto. eapply preord_val_refl; eauto.
  Qed.

  Lemma preord_env_def_funs k f rho1 rho2 :
    preord_env k PG rho1 rho2 ->
    preord_env k PG (def_funs f f rho1 rho1) (def_funs f f rho2 rho2).
  Proof.
    intros Henv. eapply preord_env_P_def_funs_cor.
    eapply preord_env_P_antimon; eauto. intros x H; simpl; eauto.
  Qed.

    
  Lemma preord_exp_case_compat k rho1 rho2 x c e1 e2 D1' D1 :
    preord_env_P (occurs_free (Ecase x (D1' ++ ((c, e1) :: D1)))) k PG rho1 rho2 ->
    preord_exp k P1 PG (e1, rho1) (e2, rho2) ->
    preord_exp k P1 PG (Ecase x (D1' ++ ((c, e1) :: D1)), rho1)
               (Ecase x (D1' ++ ((c, e2) :: D1)), rho2).
  Proof.
    (* TODO : this lemma could be used to refactor hoisting correctness proof *)
    induction D1' as [| [c' e'] P1' IHP1']; simpl;
      intros Henv Hexp v1 c1 Hleq1 Hstep1.
    - inv Hstep1. simpl in H4. edestruct Henv as [v2' [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v2'; try (now simpl in Hpre; contradiction). inv Hpre.
      destruct (M.elt_eq c1 c) eqn:Heq; subst.
      + inv H4. edestruct Hexp as [v2 [c2 [Hstep2 [Hpost2 Hpre2]]]]; [ | eassumption | ].
        omega. 
        repeat eexists.
        econstructor; [ now eauto | | | eassumption ].
        eapply caseConsistent_same_ctor_tags; [| eassumption ].
        constructor. reflexivity. now apply Forall2_refl.
        now constructor. eapply HPost. eassumption.
        eapply preord_val_monotonic. eassumption. omega.

        contradiction.
      + inv H4. contradiction.
        edestruct (preord_exp_refl P1 PG) with (e := e) as [v2 [c2 [Hstep2 [Hpost2 Hpre2]]]];
          [ | | | | | | | eassumption | ]; try eassumption.
        eapply preord_env_P_antimon. eassumption. normalize_occurs_free.
        intros x' H'. right. right. eapply occurs_free_Ecase_Included; [| eassumption ].
        eapply find_tag_nth_In_patterns. eassumption.
        omega.
        repeat eexists. econstructor; [ eassumption | | | ].
        eapply caseConsistent_same_ctor_tags; [| eassumption ].
        constructor. reflexivity. now apply Forall2_refl.
        econstructor; eassumption. eassumption.  eapply HPost. eassumption.
        eapply preord_val_monotonic. eassumption. omega.
    - inv Hstep1. simpl in H4. edestruct Henv as [v2' [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v2'; try (now simpl in Hpre; contradiction). inv Hpre.
      destruct (M.elt_eq c' c1) eqn:Heq; subst.
      + inv H4; [| contradiction ].
        edestruct (preord_exp_refl P1 PG) with (e := e) as [v2 [c2 [Hstep2 [Hpost Hpre2]]]];
          [ | | | | | | | eassumption | ]; try eassumption.
        * eapply preord_env_P_antimon; [ eassumption | ].
          intros x' H'. eapply occurs_free_Ecase_Included; eauto. now left.
        * omega. 
        * repeat eexists.
          econstructor; [ now eauto | | | eassumption ].
          inv H2. econstructor; [ now eauto | now eauto | now eauto |].
          eapply caseConsistent_same_ctor_tags; [| eassumption ].
          apply Forall2_app. now apply Forall2_refl.
          constructor. reflexivity. now apply Forall2_refl.
          constructor.
          eapply HPost. eassumption.
          eapply preord_val_monotonic. eassumption. omega.
      + inv H4; try contradiction.
        edestruct IHP1' with (c1 := c0 + n1) as [v2 [c2 [Hstep2 [ Hpost2 Hpre2 ]]]]; [ | | | | ]; eauto.
        * eapply preord_env_P_antimon; [ eassumption | ].
          intros x' H'. eapply Free_Ecase3; eauto.
        * omega.
        * econstructor; eauto.
          inv H2. eassumption.
        * inv Hstep2. rewrite Hget in H4; inv H4.
          repeat eexists. 
          econstructor. eassumption.
          eapply caseConsistent_same_ctor_tags; [| now eapply H2 ].
          constructor. reflexivity. 
          apply Forall2_app. now apply Forall2_refl.
          constructor. reflexivity. now apply Forall2_refl.
          now constructor; eauto.
          eassumption. 
          rewrite !plus_assoc. eapply HPost. eassumption. 
          eapply preord_val_monotonic. eassumption. omega.
  Qed.

  (** * Compatibility with context application *)

  Lemma preord_env_P_def_funs_compat_pre k B rho1 rho2 B' e1 e2 S1 :
    (forall m c (rho1 rho2 : env),
       m <  k ->
       preord_env_P (occurs_free (c |[ e1 ]|)) m PG rho1 rho2 ->
       preord_exp m P1 PG (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2)) ->
    preord_env_P (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                        (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>))))
                 k PG rho1 rho2 ->
    preord_env_P (Union _ (Setminus _ S1 (name_in_fundefs (B' <[ e1 ]>)))
                        (Union _ (occurs_free_fundefs (B' <[ e1 ]>))
                               (name_in_fundefs (B <[ e1 ]>))))
                 k PG (def_funs (B' <[ e1 ]>) (B <[ e1 ]>) rho1 rho1)
                 (def_funs (B' <[ e2 ]>) (B <[ e2 ]>) rho2 rho2).
  Proof.
    revert B rho1 rho2 B' e1 e2 S1.
    induction k as [ k IH' ] using lt_wf_rec1.
    intros B rho1 rho2 B' e1 e2 S1 Hpre Henv.
    assert (Hval : forall f, preord_val k PG (Vfun rho1 (B' <[ e1 ]>) f)
                                   (Vfun rho2 (B' <[ e2 ]>) f)).
    { intros f. rewrite preord_val_eq.
      intros vs1 vs2 j t1 xs1 e' rho1' Hlen Hf Hs.
      edestruct find_def_def_funs_ctx as [H1 | [c [H1 H2]]]; eauto.
      + edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall.
        eapply preord_exp_refl; try now eauto. 
        eapply preord_env_P_set_lists_l; [| | now eauto | now eauto | now eauto ].
        eapply IH'; eauto. 
        intros. eapply Hpre; eauto. omega. 
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x H Hfv. 
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Union_commut. eauto.
      + subst. edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
        do 4 eexists; eauto. split; eauto.
        intros Hleq Hall.
        eapply preord_exp_post_monotonic; [| eapply Hpre ]. 
        intros ? ? ?. now eapply HGPost.
        omega.
        eapply preord_env_P_set_lists_l; [| | eauto | eauto | eauto ].
        eapply IH'; eauto.
        intros. eapply Hpre; eauto. omega. 
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        intros x H Hfv. 
        eapply find_def_correct in Hf; eauto.
        eapply occurs_free_in_fun in Hfv; eauto.
        inv Hfv. exfalso. eauto. right. eapply Union_commut. eauto. }
    induction B.
    - simpl. apply preord_env_P_extend.
      + induction f.
        { simpl. apply preord_env_P_extend.
          - eapply preord_env_P_antimon; [ eassumption |].
            rewrite !Setminus_Union_distr. eapply Union_Included.
            now eauto with Ensembles_DB.
            eapply Union_Included.
            now eauto with Ensembles_DB.
            eapply Union_Included.
            now eauto with Ensembles_DB.
            rewrite Setminus_Union. rewrite (Union_commut [set v] [set v0]). 
            rewrite <- Setminus_Union.
            rewrite Setminus_Same_set_Empty_set.
            now eauto with Ensembles_DB.
          - eapply Hval. }
        { simpl. eapply preord_env_P_antimon ; [ eassumption |].
          eauto with Ensembles_DB. }
      + eapply Hval.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon; [now eauto |].
        eauto 10 with Ensembles_DB.
      + apply Hval.
  Qed.
  
  Lemma preord_exp_compat k rho1 rho2 c e1 e2 :
    (* Annoying, but we need that for the cost of fundefs *)
    (* PS.cardinal (exp_fv (c |[ e1 ]|)) = PS.cardinal (exp_fv (c |[ e2 ]|)) -> *)
    (forall k rho1 rho2, preord_env_P (occurs_free e1) k PG rho1 rho2 ->
                    preord_exp k P1 PG (e1, rho1) (e2, rho2)) ->
    preord_env_P (occurs_free (c |[ e1 ]|)) k PG rho1 rho2 ->
    preord_exp k P1 PG (c |[ e1 ]|, rho1) (c |[ e2 ]|, rho2).
  Proof.
    (* unfold exp_fv. *)
    revert c rho1 rho2 e1 e2. induction k as [ k IH' ] using lt_wf_rec1. 
    intros c. revert k IH'. 
    induction c; intros k IH' rho1 rho2 e1 e2 Hyp Hpre; eauto.
    - simpl. eapply preord_exp_const_compat; eauto.
      + eapply Forall2_same. intros x Hin. eapply Hpre. constructor; eauto.
      + intros vs1 vs2 Hall. eapply IHc; eauto.
        eapply preord_env_P_extend.
        * eapply preord_env_P_antimon; eauto.
          simpl. intros x H. inv H. constructor 2; eauto.
          intros H. subst; eauto.
        * rewrite preord_val_eq. simpl; split; eauto using Forall2_Forall2_asym_included.
    - simpl. eapply preord_exp_proj_compat; eauto.
      + eapply Hpre. constructor; eauto.
      + intros vs1 vs2 Hall. eapply IHc; eauto.
        eapply preord_env_P_extend; [| assumption ].
        eapply preord_env_P_antimon; eauto.
        simpl. intros x H. inv H. constructor; eauto.
        intros H. subst; eauto.
    - simpl. eapply preord_exp_prim_compat; eauto.
      + eapply Forall2_same. intros x Hin. eapply Hpre. constructor; eauto.
      + intros vs1 vs2 Hall. eapply IHc; eauto.
        eapply preord_env_P_extend; [| assumption ].
        eapply preord_env_P_antimon; eauto.
        simpl. intros x H. inv H. eapply Free_Eprim2; eauto.
        intros H. subst; eauto.
    - simpl. eapply preord_exp_letapp_compat; eauto.
      + eapply Hpre. constructor. now left.
      + eapply Forall2_same. intros x Hin. eapply Hpre. constructor; eauto.
        now right.
      + intros m vs1 vs2 Hlt Hall.
        eapply IHc; eauto. intros. eapply IH'. omega. eassumption. 
        eassumption. 
        eapply preord_env_P_extend; [| assumption ].
        eapply preord_env_P_antimon.
        eapply preord_env_P_monotonic; [| eassumption ]. omega.
        simpl. normalize_occurs_free. now eauto with Ensembles_DB. 
    - simpl. eapply preord_exp_case_compat; eauto.
      eapply IHc; auto. eapply preord_env_P_antimon; eauto.
      simpl. intros x H.
      eapply occurs_free_Ecase_Included; eauto.
      eapply in_or_app. right. left; eauto.
    - simpl. eapply preord_exp_fun_compat; eauto.
      eapply IHc; auto.
      eapply preord_env_P_def_funs_cor.
      eapply preord_env_P_antimon; [ eassumption |].
      intros x' H'. inv H'.
      + inv H. simpl. constructor; eauto.
      + simpl. eapply Free_Efun2; eauto.
    - simpl app_ctx_f.
      eapply preord_exp_fun_compat.
      admit. (* Needs some assumption about the num of FV in *)
      eapply preord_exp_refl; eauto.
      
      eapply preord_env_P_antimon.
      eapply preord_env_P_def_funs_compat_pre.
      * intros. eapply IH'; eauto.
      * eapply preord_env_P_antimon. eassumption.
        simpl. rewrite occurs_free_Efun. reflexivity.
      * rewrite <- Union_Included_Union_Setminus. now sets. tci. sets.
  Abort. 

  End Rel.

  Definition comp (P1 P2 : Post) : Post := fun c1 c2 => exists c3, P1 c1 c3 /\ P2 c3 c2.
  Definition compG (P1 P2 : PostG) : PostG := fun i c1 c2 => exists c3, P1 i c1 c3 /\ P2 i c3 c2.

  Section Trans.

    Context (P1 P2 : relation nat) (* Local *)
            (PG  : nat -> relation (exp * env * nat)) (* Global *)

            (HPostApp1 : post_app_compat PG P1)
            (HPostApp2 : post_app_compat PG P2)

            (HIncl : forall i e1 rho1 e2 rho2, inclusion _ (comp P1 P2) (fun c1 c2 => PG i (e1, rho1, c1) (e2, rho2, c2)))

            (HPostG : forall j e1 rho1 rho2, post_compat
                                          (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2))
                                          (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2)))
            (HPostAppG : forall j e1 rho1 rho2, post_app_compat
                                             PG
                                             (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2)))
            (HPostLetAppG : forall j e1 rho1 rho2, post_letapp_compat
                                                PG
                                                (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2))
                                                (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2)))
            
            (HPostReflG : forall j e1 rho1 rho2, post_refl (fun c1 c2 : nat => PG j (e1, rho1, c1) (e1, rho2, c2)))
            (HGPost :
               forall (j : nat) (e1 : exp) (rho1 : env) (e2 : exp) (rho2 : env) (j' : nat) 
                 (e1' : exp) (rho1' : env) (e2' : exp) (rho2' : env) (c1 c2 : nat),
                 PG j (e1, rho1, c1) (e2, rho2, c2) -> PG j' (e1', rho1', c1) (e2', rho2', c2)).

    
  (** * Transitivity Properties *)
  
  (** Expression relation is transitive *)
  Lemma preord_exp_trans_pre (k : nat) :
    (* The induction hypothesis for transitivity of
       the value relation. *)
    (forall k' v1 v2 v3,
       k' <= k ->
       preord_val k' PG v1 v2 ->
       (forall m, preord_val m PG v2 v3) ->
       preord_val k' PG v1 v3) ->
    forall rho1 rho2 rho3 e1 e2 e3,
      preord_exp k P1 PG (e1, rho1) (e2, rho2) ->
      (forall m, preord_exp m P2 PG (e2, rho2) (e3, rho3)) ->
      preord_exp k (comp P1 P2) PG (e1, rho1) (e3, rho3).
  Proof.
    intros Htrans rho1 rho2 rho3 e1 e2 e3 H1 H2 v1 c1 Hleq1 Hstep1.
    edestruct H1 as [v2 [c2 [Hstep2 [Hpost2 Hpre2]]]]; eauto. 
    edestruct (H2 c2) as [v3 [c3 [Hstep3 [Hpost3 Hpre3]]]]; [| eauto |]. omega.
    exists v3, c3. split; eauto.
    split. now eexists; split; eauto.     
    eapply Htrans. omega. eauto. intros m.
    edestruct (H2 (m + c2)) as [v3' [c3' [Hstep3' [Hpost3' Hpre3']]]]; [| eauto |]. omega.
    eapply bstep_cost_deterministic in Hstep3; eauto. inv Hstep3.
    eapply preord_val_monotonic; eauto. omega.
  Qed.

  Lemma preord_val_trans (k : nat) v1 v2 v3 :
    preord_val k PG v1 v2 ->
    (forall m, preord_val m PG v2 v3) ->
    preord_val k PG v1 v3.
  Proof.
    revert v1 v2 v3.
    induction k using lt_wf_rec1.
    intros x; induction x using val_ind'; simpl; eauto;
    intros v1 v2;
    try (now  intros H1 H2; specialize (H2 k); rewrite !preord_val_eq in *;
           destruct v1; destruct v2; 
         try (now simpl in *; contradiction); inv H1; inv H2; simpl; eauto).
    - intros H1 H2. assert (H2' := H2 k); rewrite !preord_val_eq in *.
      destruct v1; destruct v2; try (now simpl in *; contradiction).
      destruct H1 as [H1 H1']. destruct H2' as [H3 H3']. subst.
      destruct l0; try inv H1'; try inv H3'. split; eauto. 
      econstructor; eauto.
      + eapply IHx. eassumption.
        intros m. specialize (H2 m). rewrite !preord_val_eq in H2.
        inv H2. now inv H1.
      + assert
          (Hsuf :
             preord_val k PG (Vconstr c0 l) (Vconstr c0 l')).
        { eapply IHx0 with (v2 := Vconstr c0 l0); [| intros m];
          rewrite !preord_val_eq in *. simpl. split; eauto.
          specialize (H2 m). rewrite !preord_val_eq in H2.
          split; eauto. inv H2. now inv H1. }
        rewrite !preord_val_eq in Hsuf. now inv Hsuf.
    - intros H1 H2. assert (H2' := H2 k); rewrite !preord_val_eq in *.
      destruct v1; destruct v2; try (now simpl in *; contradiction).
      intros vs1 vs3 j t1' xs1 e1 rho1' Hlen Hf Hs. 
      edestruct (H1 vs1 vs3) as [xs2 [e2 [rho2 [Hf2 [Hs2 Hpre2]]]]]; eauto.
      edestruct (H2' vs3 vs3) with (j := 0) as [xs3 [e3 [rho3 [Hf3 [Hs3 Hpre3]]]]]; eauto.
      do 3 eexists; split; eauto. split; eauto. intros Hlt Hall. 
      eapply preord_exp_post_monotonic; [| eapply preord_exp_trans_pre ].
      now eauto.
      intros. eapply H; eauto. omega.
      eapply preord_exp_post_monotonic; [| eapply Hpre2; eauto ].
      intros c1 c2 HG.
      rewrite (plus_n_O c1), (plus_n_O c2).      
      eapply HPostApp1. now eauto.
      intros m. specialize (H2 (m + 1)). rewrite !preord_val_eq in H2.
      edestruct (H2 vs3 vs3) with (j := m)
        as [xs3' [e3' [rho3' [Hf3' [Hs3' Hpre3']]]]]; eauto.
      rewrite Hf3 in Hf3'. inv Hf3'. rewrite <- Hs3 in Hs3'. inv Hs3'.
      eapply preord_exp_post_monotonic; [| eapply Hpre3'; eauto ].
      intros c1 c2 HG.
      rewrite (plus_n_O c1), (plus_n_O c2).      
      eapply HPostApp2. now eauto.
      omega. eapply Forall2_refl. eapply preord_val_refl; eauto.
  Qed.

  Lemma preord_env_P_trans (k : nat) P rho1 rho2 rho3 :
    preord_env_P P k PG rho1 rho2 ->
    (forall m,  preord_env_P P m PG rho2 rho3) ->
    preord_env_P P k PG rho1 rho3.
  Proof.
    intros H1 H2 x Px v Hget. assert (H2' := (H2 k)).
    edestruct H1 as [v' [Hget' Hpre']]; eauto.
    edestruct H2' as [v'' [Hget'' Hpre'']]; eauto.
    eexists; split; eauto. eapply preord_val_trans; eauto.
    intros m.
    edestruct (H2 m) as [v''' [Hget''' Hpre''']]; eauto.
    rewrite Hget'' in Hget'''. now inv Hget'''.
  Qed.
  
  Corollary preord_exp_trans (k : nat) :
    forall rho1 rho2 rho3 e1 e2 e3,
      preord_exp k P1 PG (e1, rho1) (e2, rho2) ->
      (forall m, preord_exp m P2 PG (e2, rho2) (e3, rho3)) ->
      preord_exp k (comp P1 P2) PG (e1, rho1) (e3, rho3).
  Proof.
    intros. eapply preord_exp_trans_pre; eauto.
    intros. eapply preord_val_trans; eauto.
  Qed.

  Context (HIncl1 : forall i e1 rho1 e2 rho2, inclusion _ P1 (fun c1 c2 => PG i (e1, rho1, c1) (e2, rho2, c2))).

  Lemma preord_env_P_def_funs_pre' k (S1 S2 : var -> Prop) B rho1 rho2 :
    preord_env_P S1 k PG rho1 rho2 ->
    (forall x, S2 x -> S1 x) -> 
    (forall m (rho rho' : env) (e : exp),
       m <  k ->
       preord_env_P S1 m PG rho rho' ->
       preord_exp m P1 PG (e, rho) (e, rho')) ->
    preord_env_P S2 k PG (def_funs B B rho1 rho1) (def_funs B B rho2 rho2).
  Proof.
    generalize B at 1 3. revert S1 S2 B rho1 rho2.
    induction k as [ k IH' ] using lt_wf_rec1. intros S1 S2 B.
    induction B; intros rho rho2 B' Henv Hyp1 Hyp2 x HP.
    - simpl. apply preord_var_env_extend; eauto.
      + eapply IHB; eauto.
      + rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
        edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
        exists xs1. exists e1. exists rho2'. split; eauto.
        split. eauto. intros Hleq Hpre.
        eapply preord_exp_post_monotonic; [| eapply Hyp2 ]; try omega.
        now eauto.
        eapply preord_env_P_set_lists_l; eauto.
        eapply IH'; try omega; eauto. 
        eapply preord_env_P_monotonic; [| eauto]. omega.
        intros. eapply Hyp2; eauto. omega.
    - simpl. eauto.
  Qed.

  (** Commutativity property *)  
  Lemma preord_exp_preord_env_com rho1 rho2 rho1' rho2' e1 e2 :
    (forall k, preord_exp k P1 PG (e1, rho1) (e2, rho2)) ->
    (forall k, preord_env_P (occurs_free e1) k PG rho1' rho1) ->
    (forall k, preord_env_P (occurs_free e2) k PG rho2 rho2') ->
    (forall k, preord_exp k P1 PG (e1, rho1') (e2, rho2')).
  Proof.
    intros Hexp1 Henv1 Henv2 k. 
  Abort.
  (* Should be provable but we need to find the right preconditions for the post *)
  
  (*   eapply preord_exp_trans. *)
  (*   - now eapply preord_exp_refl. *)
  (*   - intros m. eapply preord_exp_trans; [ now eauto | ]. *)
  (*     intros m'. now eapply preord_exp_refl. *)
  (* Qed. *)

  Lemma preord_env_permut k x y v1 v2 rho1 rho2 P :
    x <> y ->
    preord_env_P P k PG (M.set x v1 (M.set y v2 rho1)) (M.set x v1 (M.set y v2 rho2)) ->
    preord_env_P P k PG (M.set x v1 (M.set y v2 rho1)) (M.set y v2 (M.set x v1 rho2)).
  Proof.
    intros Hneq Hpre x' HP v1' Hget.
    rewrite M.gsspec in Hget.
    destruct (peq x' x). inv Hget. 
    - edestruct (Hpre x) as [v1'' [Hget'' Hpre'']]; eauto. rewrite M.gss; eauto.
      rewrite M.gss in Hget''; inv Hget''.
      eexists. rewrite M.gso; eauto. rewrite M.gss; eauto.
    - edestruct (Hpre x') as [v1'' [Hget'' Hpre'']]; eauto.
      rewrite M.gso; eauto. rewrite M.gsspec in Hget.
      destruct (peq x' y). inv Hget.
      + eexists. rewrite M.gss; eauto. split; eauto.
        eapply preord_val_refl; try eauto. 
      + do 2 (rewrite M.gso in Hget''; eauto).
        eexists. split; eauto.
        do 2 (rewrite M.gso; eauto).
  Qed.

  (** Left weakening *)
  Lemma preord_env_P_set_not_in_P_l x v P k rho1 rho2 :
    preord_env_P P k PG rho1 rho2 ->
    Disjoint var P (Singleton var x) ->
    preord_env_P P k PG (M.set x v rho1) rho2.
  Proof.
    intros Hpre HP x' HP' v' Hget.
    rewrite M.gsspec in Hget. destruct (peq x' x).
    - inv Hget. exfalso. inv HP. eapply H; eauto.
    - edestruct Hpre; eauto.
  Qed.

  (** Right weakening *)
  Lemma preord_env_P_set_not_in_P_r x v P k rho1 rho2 :
    preord_env_P P k PG rho1 rho2 ->
    Disjoint var P (Singleton var x) ->
    preord_env_P P k PG rho1 (M.set x v rho2).
  Proof.
    intros Hpre HP x' HP' v' Hget.
    rewrite M.gsspec. destruct (peq x' x); subst.
    - exfalso; eauto. inv HP. eapply H; eauto.
    - edestruct Hpre; eauto.
  Qed.

  (** Left weakening for function definitions *)
  Lemma preord_env_P_def_funs_not_in_P_l B B' P k rho rho1 rho2 :
    preord_env_P P k PG rho1 rho2 ->
    Disjoint var P (name_in_fundefs B) ->
    preord_env_P P k PG (def_funs B' B rho rho1) rho2.
  Proof.
    intros Hpre HP x' HP' v' Hget.
    eapply def_funs_spec in Hget.
    destruct Hget as [[Hname Heq] | [Hname Heq ]]; subst.
    - exfalso. eapply HP; eauto.
    - edestruct Hpre; eauto.
  Qed.

  (** Right weakening for function definitions *)
  Lemma preord_env_P_def_funs_not_in_P_r B B' P k rho rho1 rho2 :
    preord_env_P P k PG rho1 rho2 ->
    Disjoint var P (name_in_fundefs B) ->
    preord_env_P P k PG rho1 (def_funs B' B rho rho2).
  Proof.
    intros Hpre HP x' HP' v' Hget.
    edestruct (@Dec _ _ (Decidable_name_in_fundefs B) x').
    - exfalso. eapply HP; eauto.
    - edestruct Hpre as [v'' [Hget' Hpre']]; eauto.
      eexists. rewrite def_funs_neq; eauto.
  Qed.

  (** Left weakening for set_lists *)
  Lemma preord_env_P_set_lists_not_in_P_r xs vs P k rho1 rho2 rho2' :
    preord_env_P P k PG rho1 rho2 ->
    Some rho2' = set_lists xs vs rho2 -> 
    Disjoint var P (FromList xs) ->
    preord_env_P P k PG rho1 rho2'.
  Proof.
    revert vs rho2'. induction xs; intros vs rho2' Hpre Hset HD.
    - destruct vs; try discriminate. inv Hset; eauto.
    - destruct vs; try discriminate. simpl in Hset.
      destruct (set_lists xs vs rho2) eqn:Heq ; try discriminate. inv Hset.
      rewrite FromList_cons in HD.
      apply preord_env_P_set_not_in_P_r; [| now eauto with Ensembles_DB ].
      eapply IHxs; eauto with Ensembles_DB. 
  Qed.

  (** Right weakening for set_lists *)
  Lemma preord_env_P_set_lists_not_in_P_l xs vs P k rho1 rho2 rho1' :
    preord_env_P P k PG rho1 rho2 ->
    Some rho1' = set_lists xs vs rho1 -> 
    Disjoint var P (FromList xs) ->
    preord_env_P P k PG rho1' rho2.
  Proof.
    revert vs rho1'. induction xs; intros vs rho1' Hpre Hset HD.
    - destruct vs; try discriminate. inv Hset; eauto.
    - destruct vs; try discriminate. simpl in Hset.
      destruct (set_lists xs vs rho1) eqn:Heq ; try discriminate. inv Hset.
      rewrite FromList_cons in HD.
      apply preord_env_P_set_not_in_P_l; [| now eauto with Ensembles_DB ].
      eapply IHxs; eauto with Ensembles_DB.
  Qed.

  Lemma preord_env_P_singleton_extend (rho1 rho2 : env) (k : nat) (x : var)
        (v1 v2 : val) :
    preord_val k PG v1 v2 ->
    preord_env_P (Singleton var x) k PG (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros Hpre. eapply preord_env_P_extend; eauto.
    eapply preord_env_P_antimon. apply preord_env_Empty_set.
    eauto with Ensembles_DB. 
  Qed.

  (** * Technical lemmas about mutually recursive function definitions *)

  Lemma preord_env_set_def_funs_permut k x S1 B v1 v2 rho1 rho2 :
    ~ bound_var_fundefs B x ->
    closed_fundefs B ->
    preord_val k PG v1 v2 ->
    preord_env_P S1 k PG rho1 rho2 ->
    preord_env_P (Union var S1 (Union var (Singleton var x) (name_in_fundefs B))) k PG
                 (def_funs B B (M.set x v1 rho1) (M.set x v1 rho1)) 
                 (M.set x v2 (def_funs B B rho2 rho2)).
  Proof.
    intros Hb Hclo Hval Hpre. rewrite (@Union_Setminus _ _ _ _).
    apply preord_env_P_union.
    - apply preord_env_P_def_funs_not_in_P_l; [| now eauto with Ensembles_DB ]. 
      apply preord_env_P_set_not_in_P_l; [| now eauto with Ensembles_DB ]. 
      apply preord_env_P_set_not_in_P_r; [| now eauto with Ensembles_DB ]. 
      apply preord_env_P_def_funs_not_in_P_r; [| now eauto with Ensembles_DB ].
      eapply preord_env_P_antimon; now eauto with Ensembles_DB.
    - apply preord_env_P_union.
      + apply preord_env_P_def_funs_not_in_P_l.
        eapply preord_env_P_singleton_extend; eauto.
        apply Disjoint_Singleton_l. intros Hc; apply Hb.
        now apply name_in_fundefs_bound_var_fundefs.
      + apply preord_env_P_set_not_in_P_r.
        eapply preord_env_P_def_funs_cor; eauto.
        eapply preord_env_P_antimon. apply preord_env_Empty_set.
        eauto with Ensembles_DB.
        unfold closed_fundefs in Hclo. rewrite <- Hclo; eauto with Ensembles_DB.
        apply Disjoint_Singleton_r. intros Hc; apply Hb.
        now apply name_in_fundefs_bound_var_fundefs.
  Qed.
  
  Lemma preord_env_def_funs_permut (k : nat) S1 (B1 B2 : fundefs) (rho1 rho2 : env) :
    closed_fundefs B1 -> closed_fundefs B2 ->
    Disjoint var (name_in_fundefs B1) (name_in_fundefs B2) ->
    preord_env_P S1 k PG rho1 rho2 ->
    preord_env_P (Union var S1 (Union var (name_in_fundefs B1) (name_in_fundefs B2)))
                 k PG (def_funs B1 B1 (def_funs B2 B2 rho1 rho1) (def_funs B2 B2 rho1 rho1))
                 (def_funs B2 B2 (def_funs B1 B1 rho2 rho2) (def_funs B1 B1 rho2 rho2)).
  Proof.
    intros Hclo1 Hclo2 HD Hpre. rewrite (@Union_Setminus _ _ _ _).
    apply preord_env_P_union.
    - eapply preord_env_P_def_funs_not_in_P_r; [| now eauto with Ensembles_DB ]. 
      eapply preord_env_P_def_funs_not_in_P_l; [| now eauto with Ensembles_DB ]. 
      eapply preord_env_P_def_funs_not_in_P_r; [| now eauto with Ensembles_DB ].
      eapply preord_env_P_def_funs_not_in_P_l; [| now eauto with Ensembles_DB ]. 
      eapply preord_env_P_antimon; now eauto with Ensembles_DB.
    - apply preord_env_P_union.
      + apply preord_env_P_def_funs_not_in_P_r; eauto.
        eapply preord_env_P_def_funs_cor; eauto.
        eapply preord_env_P_antimon. apply preord_env_Empty_set.
        unfold closed_fundefs in Hclo1. rewrite <- Hclo1; eauto with Ensembles_DB.
      + apply preord_env_P_def_funs_not_in_P_l; eauto using Disjoint_sym.
        eapply preord_env_P_def_funs_cor; eauto.
        eapply preord_env_P_antimon. apply preord_env_Empty_set.
        unfold closed_fundefs in Hclo2. rewrite <- Hclo2; eauto with Ensembles_DB.
  Qed.
  
  Lemma preord_env_P_def_funs_strengthen_l (k : nat) rho rho' B1 B1' B2 :
    Disjoint var (occurs_free_fundefs B1') (name_in_fundefs B2) ->
    Disjoint var (name_in_fundefs B1') (name_in_fundefs B2) ->
    closed_fundefs B1' ->
    preord_env_P (name_in_fundefs B1) k PG
                 (def_funs B1' B1 rho rho')
                 (def_funs (fundefs_append B2 B1') B1 rho rho').
  Proof.
    revert rho rho' B1 B1' B2.
    induction k as [ k IH' ] using lt_wf_rec1. intros rho rho' B1 B1' B2 HD1 HD2 Hclo.
    induction B1.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon. eapply IHB1; eauto.
        eauto with Ensembles_DB typeclass_instances.
      + rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
        edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
        exists xs1. exists e1. exists rho2'. split; eauto.
        specialize (find_def_name_in_fundefs _ _ _ Hf); intros Hname.
        destruct (@Dec _ _  (Decidable_name_in_fundefs B2) v) as [Hin | Hnin ].
        exfalso. inv HD2. eapply H; eauto.
        eapply name_not_in_fundefs_find_def_None in Hnin.
        erewrite find_def_fundefs_append_r; eauto.
        split. eauto. intros Hleq Hpre'.
        eapply preord_exp_refl; eauto. 
        eapply preord_env_P_set_lists_l; [| | now eauto | now eauto | now eauto].
        rewrite def_funs_append.
        apply preord_env_P_def_funs_not_in_P_r; eauto. 
        intros x Hin Hfr.
        apply find_def_correct in Hf.  
        edestruct (occurs_free_in_fun _ _ _ _ _ Hf x Hfr); try contradiction.
        inv H; eauto. unfold closed_fundefs in Hclo. rewrite Hclo in H0. inv H0.
    - simpl. intros x HP. inv HP.
  Qed.

  (* 
  Lemma preord_val_def_funs_append_pre (k : nat) f tau xs e (B1 B2 : fundefs)
        (rho1 rho2  : env) :
    closed_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    closed_fundefs B2 ->
    unique_bindings_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    Disjoint var (name_in_fundefs (Fcons f tau xs e B1)) (name_in_fundefs B2) ->
    (forall j S1 rho1 rho2 rho1' rho2',
       j < k ->
       preord_env_P S1 j PG rho1 rho2 ->
       preord_env_P (Union var S1 (name_in_fundefs B1))
                    j PG
                    (def_funs (Fcons f tau xs (Efun B2 e) B1) B1 rho1' rho1)
                    (def_funs (fundefs_append (Fcons f tau xs e B1) B2) B1 rho2' rho2)) ->
    preord_val k PG (Vfun rho1 (Fcons f tau xs (Efun B2 e) B1) f)
               (Vfun rho2 (fundefs_append (Fcons f tau xs e B1) B2) f).
  Proof.
    revert f tau xs e B1 B2 rho1 rho2. induction k using lt_wf_rec1.
    intros f tau xs e B1 B2 rho1 rho2 Hcl1 Hcl2 Hun HD Hyp. rewrite preord_val_eq.
    intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs. inv Hf. destruct (M.elt_eq f f); try congruence. subst; inv H1.
    clear e0. 
    
    edestruct (@set_lists_length val) as [rho2' Hs']; eauto.
    do 3 eexists. split. simpl.
    
    destruct (M.elt_eq f f); try congruence. eauto. split; eauto.
    
    intros Hleq Hpre'. simpl in Hs, Hs'. rewrite def_funs_append in Hs'.
    
    intros v1 c1 Hleq1 Hstep1. inv Hstep1.
    edestruct preord_exp_refl
      with (k := j + c) (rho := def_funs B2 B2 rho1' rho1') as [v2 [c2 [Hst2 [Hp2 Hv2]]]]; (try now eapply H5); eauto.
    - intros. eapply HGPost. now eapply H0.
    - admit.
    - omega.
    - do 2 eexists. split; eauto. split; eauto. simpl in Hp2. admit. eapply Hp2. 
    - apply preord_env_P_antimon with
          (P2 := Union var (FromList xs1)
                       (Union var (name_in_fundefs B2)
                              (Union var (Singleton var f) (name_in_fundefs B1)))).
      { - repeat apply preord_env_P_union. 
          + apply preord_env_P_def_funs_not_in_P_l.
            * eapply preord_env_P_set_lists_l with (P1 := Empty_set var) (xs := xs1);
                [ | | | now eauto | clear Hs'; now eauto ].
              eapply preord_env_Empty_set. intros x Hc1 Hc2. exfalso. eapply Hc1; eauto.
              eapply Forall2_refl. now eapply preord_val_refl. 
            * inv Hun. eapply Disjoint_Included_r.
              eapply name_in_fundefs_bound_var_Efun. eauto using Disjoint_sym.
          + apply preord_env_P_def_funs_not_in_P_l. eapply preord_env_P_refl; eauto.
            eassumption. 
          * eapply preord_env_P_set_lists_l with (P1 := Empty_set var) (xs := xs1);
              [ | | | now eauto | clear Hs'; now eauto ].
            eapply preord_env_Empty_set. intros x Hc1 Hc2. exfalso. eapply Hc1; eauto.
            eapply Forall2_refl. now eapply preord_val_refl. 
          * inv Hun. eapply Disjoint_Included_r.
            eapply name_in_fundefs_bound_var_Efun. eauto using Disjoint_sym.
       
        + eapply preord_env_P_set_lists_not_in_P_r.
          * eapply preord_env_P_set_not_in_P_r; eauto with Ensembles_DB.
            eapply preord_env_P_def_funs_not_in_P_r; eauto with Ensembles_DB.
            eapply preord_env_P_trans;
              [| intros m; eapply preord_env_P_def_funs_strengthen_l
                             with (B2 := Fcons f t1 xs1 e B1) ]; eauto with Ensembles_DB. 
            eapply preord_env_P_def_funs_cor; eauto.
            eapply preord_env_P_antimon. eapply preord_env_Empty_set.
          unfold closed_fundefs in Hcl2. rewrite Hcl2. eauto with Ensembles_DB.
          unfold closed_fundefs in Hcl2. rewrite Hcl2. eauto with Ensembles_DB.
        * inv Hun. eapply Disjoint_Included_l ; [| apply H8 ].
          eapply name_in_fundefs_bound_var_Efun.
      + inv Hun. eapply preord_env_P_set_lists_not_in_P_r; eauto with Ensembles_DB.
        eapply preord_env_P_def_funs_not_in_P_l; eauto with Ensembles_DB.
        eapply preord_env_P_set_lists_not_in_P_l; eauto with Ensembles_DB.
        eapply preord_env_P_extend. rewrite Setminus_Same_set_Empty_set.
        eapply preord_env_Empty_set. 
        eapply H; eauto. now constructor; eauto. intros. eapply Hyp; eauto. omega.
      + inv Hun. eapply preord_env_P_set_lists_not_in_P_r; eauto.
        * eapply preord_env_P_set_not_in_P_r; eauto.
          eapply preord_env_P_def_funs_not_in_P_l; eauto with Ensembles_DB.
          eapply preord_env_P_set_lists_not_in_P_l; eauto with Ensembles_DB.
          eapply preord_env_P_set_not_in_P_l; eauto with Ensembles_DB.
          eapply preord_env_P_antimon. eapply Hyp. omega.
          eapply preord_env_Empty_set. eauto with Ensembles_DB.
          eapply Disjoint_Singleton_r. intros Hc. apply H7.
          apply name_in_fundefs_bound_var_fundefs; eauto.
          eapply Disjoint_Included_l; [| apply H9 ].
          apply name_in_fundefs_bound_var_fundefs; eauto.
          eapply Disjoint_Singleton_r. intros Hc. apply H7.
          apply name_in_fundefs_bound_var_fundefs; eauto.
        * eapply Disjoint_Included_l; [| apply H9 ]. intros x Hx. 
          eapply name_in_fundefs_bound_var_fundefs; eauto.
    - eapply Included_trans. eapply occurs_free_Efun_Included with (B := B2).
      unfold closed_fundefs in Hcl1.
      intros x Hfr. inv Hfr; eauto.
      assert (Hin : fun_in_fundefs (Fcons f t1 xs1 (Efun B2 e) B1)
                                   (f, t1, xs1, (Efun B2 e)))
        by (constructor; eauto).
      edestruct (occurs_free_in_fun _ _ _ _ _ Hin x H0); eauto.  inv H1; eauto.
      unfold closed_fundefs in Hcl1. rewrite Hcl1 in H2. inv H2.
    - 
    - edestruct H0 as [c2 [Hs'' [Hp Hr]]].
     

      Grab Existential Variables. eauto. eauto. eauto. eauto.
  Qed.

  Lemma preord_env_P_def_funs_append (k : nat) S1 f tau xs e (B1 B1' B2 : fundefs)
        (rho1 rho2 rho1' rho2' : env) :
    closed_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    closed_fundefs B2 ->
    unique_bindings_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    Disjoint var (name_in_fundefs (Fcons f tau xs e B1)) (name_in_fundefs B2) ->
    preord_env_P S1 k PG rho1 rho2 ->
    preord_env_P (Union var S1 (name_in_fundefs B1'))
                 k PG (def_funs (Fcons f tau xs (Efun B2 e) B1) B1' rho1' rho1)
                 (def_funs (fundefs_append (Fcons f tau xs e B1) B2) B1' rho2' rho2).
  Proof.
    revert S1 f tau xs e B1 B1' B2 rho1 rho2 rho1' rho2'. induction k using lt_wf_rec1.
    intros S1 f tau xs e B1 B1' B2 rho1 rho2 rho1' rho2' Hcl1 Hcl2 Hun HD Hpre1. simpl.
    induction B1'.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon. now eauto. now eauto 7 with Ensembles_DB.
      + destruct (M.elt_eq v f); subst.
        * eapply preord_val_def_funs_append_pre; eauto.
        * rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs.
          edestruct (@set_lists_length val) as [rho2'' Hs']; [eauto | | ]. eauto.
          exists xs1, e1, rho2''. repeat split; eauto.
          simpl in *. destruct (M.elt_eq v f); try congruence.
          specialize (find_def_name_in_fundefs _ _ _ Hf); intros Hname.
          erewrite <- find_def_fundefs_append_l in Hf; eauto.
          intros Hleq Hpre'. eapply preord_exp_refl; eauto.
          eapply preord_env_P_set_lists_l with
          (P1 := Union var (name_in_fundefs B1) (Singleton var f)); [| | eauto | eauto | eauto].
          simpl. eapply preord_env_P_extend. eapply preord_env_P_antimon.
          rewrite def_funs_append. eapply H; eauto. eapply preord_env_Empty_set.
          now eauto with Ensembles_DB.
          eapply preord_val_def_funs_append_pre; eauto. intros; eauto.
          eapply H; eauto. omega.
          destruct (M.elt_eq v f); try congruence. 
          apply find_def_correct in Hf.
          intros x Hin Hfr. specialize (occurs_free_in_fun _ _ _ _ _ Hf x Hfr).
          intros H1. inv H1; try contradiction.
          inv H0; eauto. simpl in H1. inv H1; eauto. right; eauto. left; eauto.
          destruct (var_dec f x); subst. right; eauto.  
          exfalso. eapply not_In_Empty_set. eapply Hcl1; eauto.
    - simpl. now rewrite Union_Empty_set_neut_r.
  Qed.
  
  
  Lemma preord_env_P_def_funs_hoist (k : nat) S1 f tau xs e (B1 B2 : fundefs)
        (rho1 rho2 : env) :
    closed_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    closed_fundefs B2 ->
    unique_bindings_fundefs (Fcons f tau xs (Efun B2 e) B1) ->
    Disjoint var S1 (name_in_fundefs B2) ->
    Disjoint var (name_in_fundefs (Fcons f tau xs e B1)) (name_in_fundefs B2) ->
    preord_env_P S1 k PG rho1 rho2 ->
    preord_env_P (Union var S1 (Union var (name_in_fundefs B1) (Singleton var f)))
                 k PG (def_funs (Fcons f tau xs (Efun B2 e) B1)
                                (Fcons f tau xs (Efun B2 e) B1)
                                rho1 rho1)
                 (def_funs (fundefs_append (Fcons f tau xs e B1) B2)
                           (fundefs_append (Fcons f tau xs e B1) B2)
                           rho2 rho2).
  Proof.
    intros Hcl1 Hcl2 Hun HD1 HD2 Hpre. simpl.
    eapply preord_env_P_extend.
    - eapply preord_env_P_antimon. 
      rewrite def_funs_append. eapply preord_env_P_def_funs_append with (S1 := S1); eauto.
      eapply preord_env_P_def_funs_not_in_P_r; eauto.
      eauto with Ensembles_DB.
    - eapply preord_val_def_funs_append_pre; eauto.
      intros. eapply preord_env_P_def_funs_append; eauto.
  Qed.
   *)

  (* TODO : figure out fundefs above... *)
  
  Lemma proerd_env_P_def_funs_weakening k S1 B B1 B2 f tau xs e rho rho':
    ~ In var S1 f ->
    preord_env_P S1 k PG (def_funs B (fundefs_append B1 B2) rho rho')
                 (def_funs B (fundefs_append B1 (Fcons f tau xs e B2)) rho rho').
  Proof.
    revert S1 rho'. induction B1; intros S1 rho' Hin; simpl.
    - destruct (var_dec f v); subst.
      + apply preord_env_P_set_not_in_P_l; eauto using Disjoint_Singleton_r.
        apply preord_env_P_set_not_in_P_r; eauto using Disjoint_Singleton_r.
      + apply preord_env_P_extend. 
        * eapply IHB1. intros Hc. inv Hc. eauto.
        * eapply preord_val_refl; eauto.
    - apply preord_env_P_set_not_in_P_r; eauto using Disjoint_Singleton_r.
      apply preord_env_P_refl; eauto.
  Qed.

  (* TODO : make this a corollary of a following proof *)
  Lemma preord_env_P_split_fds k S1 B1 B1' B2 B2' B11 B12 B11' B12' rho1 rho1' :
    split_fds B11 B12 B1 ->
    split_fds B11' B12' B1' ->
    split_fds B11 B12 B2 ->
    split_fds B11' B12' B2' ->
    unique_bindings_fundefs B1' ->
    unique_bindings_fundefs B1 ->  
    preord_env_P S1 k PG (def_funs B1' B1 rho1 rho1') (def_funs B2' B2 rho1 rho1').
  Proof.
    intros Hspl.
    revert B1 B11 B12 Hspl S1 B1' B2 B2' B11' B12' rho1 rho1'. induction k using lt_wf_rec1.
    induction B1; intros B11 B12 Hspl1 S1 B1' B2 B2' B11' B12' rho1 rho1'
                         Hspl1' Hspl2 Hspl2' Hun1 Hun2.
    - edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]]; [| |]; eauto.
      specialize (split_fds_unique_bindings_fundefs_r _ _ _ H1 H2 H3 Hspl2); intros H4.
      inv Hspl1.
      + edestruct split_fds_cons_l_append_fundefs as [B3 [B4 [Heq Hspl3]]]; eauto.
        eapply preord_env_P_antimon;
          [| apply (@Included_Union_Setminus _ _ (name_in_fundefs B2) _)].
        eapply preord_env_P_union.
        * eapply preord_env_P_def_funs_not_in_P_r; eauto with Ensembles_DB.
          eapply preord_env_P_def_funs_not_in_P_l. eapply preord_env_P_refl; eauto.
          rewrite split_fds_name_in_fundefs; eauto. simpl.
          rewrite split_fds_name_in_fundefs with (B3 := B1); eauto.
          eauto with Ensembles_DB.
        * rewrite split_fds_name_in_fundefs; eauto. simpl (Union _ _ _).
          rewrite <- Union_assoc.
          eapply preord_env_P_union.
          rewrite Heq. rewrite def_funs_append; eauto.
          eapply preord_env_P_def_funs_not_in_P_r.
          simpl. apply preord_env_P_extend.
          rewrite Setminus_Same_set_Empty_set. apply preord_env_Empty_set.
          { rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs.
            edestruct (@set_lists_length val) as [rho2'' Hs']; [eauto | | ]. eauto.
            exists xs1, e1, rho2''. repeat split; eauto.
            erewrite <- find_def_split_fds; eauto.
            intros Hleq Hpre'. eapply preord_exp_refl; eauto.
            eapply preord_env_P_set_lists_l; [| | | eauto | eauto ]; eauto. }
          symmetry in Heq. eapply fundefs_append_split_fds in Heq.
          edestruct split_fds_unique_bindings_fundefs_l as [H5 [H6 H8]]. apply H4.  eauto.
          rewrite bound_var_fundefs_Fcons in H8.
          eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
          now eauto with Ensembles_DB.
          simpl. eapply preord_env_P_set_not_in_P_l.
          rewrite Heq. eapply preord_env_P_trans;
            [| intros m; apply proerd_env_P_def_funs_weakening ].
          eapply IHB1; eauto. inv Hun2; eauto.
          edestruct split_fds_unique_bindings_fundefs_l as [H5 [H6 H8]]; [apply H4| |]; eauto.
          intros Hc. inv H5. inv Hc; eauto. apply H14.
          apply name_in_fundefs_bound_var_fundefs; eauto.
          eapply H8. constructor; eauto. now apply name_in_fundefs_bound_var_fundefs; eauto.
          inv H1. apply Disjoint_Singleton_r. intros Hc. inv Hc.
          eapply H11. now apply name_in_fundefs_bound_var_fundefs; eauto.
          eapply H3. constructor; eauto.
          now apply name_in_fundefs_bound_var_fundefs; eauto.
      + edestruct split_fds_cons_r_append_fundefs as [B3 [B4 [Heq Hspl3]]]; eauto.
        eapply preord_env_P_antimon;
          [| apply (@Included_Union_Setminus _ _ (name_in_fundefs B2) _)].
        eapply preord_env_P_union.
        * eapply preord_env_P_def_funs_not_in_P_r;
          eauto with Ensembles_DB.
          eapply preord_env_P_def_funs_not_in_P_l. eapply preord_env_P_refl; eauto.
          rewrite split_fds_name_in_fundefs; eauto. simpl.
          rewrite split_fds_name_in_fundefs with (B3 := B1); eauto.
          eauto with Ensembles_DB.
        * rewrite split_fds_name_in_fundefs; eauto. simpl (Union _ _ _).
          rewrite Union_assoc, (Union_commut _ (Singleton var v)), <- Union_assoc.
          eapply preord_env_P_union.
          rewrite Heq. rewrite def_funs_append; eauto.
          eapply preord_env_P_def_funs_not_in_P_r.
          simpl. apply preord_env_P_extend.
          rewrite Setminus_Same_set_Empty_set. apply preord_env_Empty_set.
          { rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs.
            edestruct (@set_lists_length val) as [rho2'' Hs']; [eauto | | ]. eauto.
            exists xs1, e1, rho2''. repeat split; eauto.
            erewrite <- find_def_split_fds; eauto.
            intros Hleq Hpre'. eapply preord_exp_refl; eauto.
            eapply preord_env_P_set_lists_l; [| | | eauto | eauto ]; eauto. }
          symmetry in Heq. eapply fundefs_append_split_fds in Heq.
          edestruct split_fds_unique_bindings_fundefs_l as [H5 [H6 H8]].
          apply H4. eauto. rewrite bound_var_fundefs_Fcons in H8.
          eapply Disjoint_Included_r.
          eapply name_in_fundefs_bound_var_fundefs. eauto with Ensembles_DB.
          simpl. eapply preord_env_P_set_not_in_P_l.
          rewrite Heq. eapply preord_env_P_trans;
            [| intros m; apply proerd_env_P_def_funs_weakening ].
          eapply IHB1; eauto. inv Hun2; eauto.
          edestruct split_fds_unique_bindings_fundefs_l as [H5 [H6 H8]]; [apply H4| |]; eauto.
          intros Hc. inv H6. inv Hc; eauto. eapply H8. constructor; eauto.
          now apply name_in_fundefs_bound_var_fundefs; eauto.
          eapply H14. now apply name_in_fundefs_bound_var_fundefs; eauto.
          inv H2. apply Disjoint_Singleton_r. intros Hc. inv Hc.
          eapply H3. constructor. now apply name_in_fundefs_bound_var_fundefs; eauto.
          rewrite bound_var_fundefs_Fcons. left; eauto.
          eapply H11. now apply name_in_fundefs_bound_var_fundefs; eauto.
    - inv Hspl1. simpl. inv Hspl2. eapply preord_env_P_refl; eauto.
  Qed.

  Lemma preord_env_P_Included_fun_in_fundefs k B1 B1' B2 B2' rho1 rho1' :
    Included _ (fun_in_fundefs B1) (fun_in_fundefs B2) ->
    Included _ (fun_in_fundefs B1') (fun_in_fundefs B2') ->
    closed_fundefs B1' ->
    unique_bindings_fundefs B1'->
    unique_bindings_fundefs B1 ->
    unique_bindings_fundefs B2'->
    unique_bindings_fundefs B2 ->
    preord_env_P (name_in_fundefs B1) k PG (def_funs B1' B1 rho1 rho1')
                 (def_funs B2' B2 rho1 rho1').
  Proof.
    revert B1 B1' B2 B2' rho1 rho1'. induction k using lt_wf_rec1.
    induction B1; intros B1' B2 B2' rho1 rho1' HS1 HS2 Hcl Hun1' Hun1 Hun2' Hun2.
    - edestruct fun_in_fundefs_unique_bindings_split
      with (B := B2) as [B [B' [Heq [Hn [HS Hun']]]]]; eauto.
      eapply HS1. left. eauto.
      edestruct fundefs_append_unique_bindings_l as [H1 [H2 H3]]; eauto.
      rewrite Heq.
      eapply preord_env_P_antimon;
        [| apply (@Included_Union_Setminus _ _ (Singleton var v) _)].
      eapply preord_env_P_union.
      + simpl. eapply preord_env_P_set_not_in_P_l; eauto with Ensembles_DB.
        eapply preord_env_P_trans;
          [| intros m; apply proerd_env_P_def_funs_weakening; intros Hc; inv Hc; eauto ].
        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        eapply preord_env_P_antimon; [ eapply IHB1; eauto |].
        rewrite (fundefs_append_fun_in_fundefs B B' (fundefs_append B B')); eauto.
        rewrite HS. simpl in HS1.
        rewrite <- (Setminus_Disjoint (fun_in_fundefs B1) (Singleton _ (v, f, l, e))).
        eapply Included_Setminus_compat; eauto using Included_refl.
        eapply Included_trans; [| eassumption ]. eauto with Ensembles_DB.
        eapply Disjoint_Singleton_r. inv Hun1; eauto. intros Hc. apply H9.
        apply name_in_fundefs_bound_var_fundefs.
        now eapply fun_in_fundefs_name_in_fundefs; eauto.
        now inv Hun1; eauto. eauto with Ensembles_DB.
      + rewrite def_funs_append;
        eapply preord_env_P_def_funs_not_in_P_r.
        * simpl. eapply preord_env_P_extend.
          rewrite Setminus_Same_set_Empty_set. apply preord_env_Empty_set.
          rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs. 
          edestruct (@set_lists_length val) as [rho2'' Hs']; [eauto | | ]. eauto.
          exists xs1, e1, rho2''. repeat split; eauto.
          erewrite <- find_def_Included_fun_in_fundefs; eauto.
          eapply fun_in_fundefs_name_in_fundefs. now eapply find_def_correct; eauto.
          intros Hleq Hpre'. eapply preord_exp_refl; eauto. 
          eapply preord_env_P_set_lists_l; [| | | eauto | eauto ]; eauto.
          intros c Hnin Hf'. apply find_def_correct in Hf.
          eapply occurs_free_in_fun in Hf'; eauto. inv Hf'.
          exfalso; eauto. inv H0; eauto.
          exfalso. eapply not_In_Empty_set. eapply Hcl; eauto.
        * apply Disjoint_Singleton_l. eauto.
    - simpl. eapply preord_env_Empty_set.
  Qed.

  Lemma preord_env_P_def_funs_merge k S1 B B' B'' rho rho' :
    unique_bindings_fundefs B ->
    split_fds B' B'' B ->
    closed_fundefs B' ->
    closed_fundefs B'' ->
    preord_env_P S1 k PG rho rho' ->
    preord_env_P (Union var S1 (name_in_fundefs B)) k PG
                 (def_funs B' B' (def_funs B'' B'' rho rho)
                           (def_funs B'' B'' rho rho))
                 (def_funs B B rho' rho').
  Proof.
    intros Hun HS Hcl Hcl' Hpre.
    assert (Hcl'' := split_fds_closed_fundefs B' B'' B HS Hcl Hcl').
    rewrite (@Union_Setminus _ _ _ _ ).
    eapply preord_env_P_union.
    - eapply preord_env_P_def_funs_not_in_P_l; eauto with Ensembles_DB.
      eapply preord_env_P_def_funs_not_in_P_l; eauto with Ensembles_DB.
      eapply preord_env_P_def_funs_not_in_P_r; eauto with Ensembles_DB.
      eapply preord_env_P_antimon; eauto with Ensembles_DB.
      rewrite split_fds_name_in_fundefs; eauto with Ensembles_DB.
      rewrite (split_fds_name_in_fundefs B' B'' B); eauto with Ensembles_DB.
    - edestruct split_fds_unique_bindings_fundefs_l as [H1 [H2 H3]]; eauto.
      rewrite split_fds_name_in_fundefs; eauto. eapply preord_env_P_union.
      + eapply preord_env_P_trans.
        eapply preord_env_P_Included_fun_in_fundefs with (B2 := B) (B2' := B);
          eauto using Included_refl;
          try (now rewrite (split_fds_fun_in_fundefs B' B'' B); eauto;
               apply Included_Union_l).
        intros m. eapply preord_env_P_def_funs_cor; eauto.
        rewrite (split_fds_name_in_fundefs B' B'' B); eauto.
        unfold closed_fundefs in *. rewrite Hcl'', Union_Empty_set_neut_r.
        rewrite Setminus_Included_Empty_set. eapply preord_env_Empty_set.
        eauto with Ensembles_DB.
      + eapply preord_env_P_def_funs_not_in_P_l.
        eapply preord_env_P_trans.
        eapply preord_env_P_Included_fun_in_fundefs with (B2 := B) (B2' := B);
          eauto using Included_refl;
          try (now rewrite (split_fds_fun_in_fundefs B' B'' B); eauto;
               apply Included_Union_r).
        intros m. eapply preord_env_P_def_funs_cor; eauto.
        rewrite (split_fds_name_in_fundefs B' B'' B); eauto.
        unfold closed_fundefs in *. rewrite Hcl'', Union_Empty_set_neut_r.
        rewrite Setminus_Included_Empty_set. eapply preord_env_Empty_set.
        now eauto with Ensembles_DB.
        eapply Disjoint_Included_r. eapply name_in_fundefs_bound_var_fundefs.
        eapply Disjoint_Included_l. eapply name_in_fundefs_bound_var_fundefs.
        now apply Disjoint_sym.
  Qed.


  Lemma preord_env_P_Same_set_fun_in_fundefs k S1 B1 B1' B2 B2' rho1 rho1' :
    Same_set _ (fun_in_fundefs B1) (fun_in_fundefs B2) ->
    Same_set _ (fun_in_fundefs B1') (fun_in_fundefs B2') ->
    unique_bindings_fundefs B1'->
    unique_bindings_fundefs B1 ->
    unique_bindings_fundefs B2'->
    unique_bindings_fundefs B2 ->
    preord_env_P S1 k PG (def_funs B1' B1 rho1 rho1') (def_funs B2' B2 rho1 rho1').
  Proof. 
    revert B1 S1 B1' B2 B2' rho1 rho1'. induction k using lt_wf_rec1.
    induction B1; intros S1 B1' B2 B2' rho1 rho1' HS1 HS2 Hun1' Hun1 Hun2' Hun2.
    - edestruct fun_in_fundefs_unique_bindings_split
      with (B := B2) as [B [B' [Heq [Hn [HS Hun']]]]]; eauto.
      eapply HS1. left. eauto.
      edestruct fundefs_append_unique_bindings_l as [H1 [H2 H3]]; eauto.
      rewrite Heq. 
      eapply preord_env_P_antimon;
        [| apply (@Included_Union_Setminus _ _ (Singleton var v) _)].
      eapply preord_env_P_union.
      + simpl. eapply preord_env_P_set_not_in_P_l;
          eauto using Disjoint_Setminus_l, Included_refl.
        eapply preord_env_P_trans;
          [| intros m; apply proerd_env_P_def_funs_weakening; intros Hc; inv Hc; eauto ].
        eapply IHB1; eauto ; try (now inv Hun1; eauto).
        rewrite (fundefs_append_fun_in_fundefs B B' (fundefs_append B B')); eauto.
        rewrite HS, <- HS1. eauto with Ensembles_DB. simpl.
        rewrite Setminus_Union_distr, Setminus_Same_set_Empty_set, Union_Empty_set_neut_l.
        inv Hun1. rewrite Setminus_Disjoint; eauto with Ensembles_DB.
        eapply Disjoint_Singleton_r.
        intros Hc. apply H9. apply name_in_fundefs_bound_var_fundefs.
        eapply fun_in_fundefs_name_in_fundefs; eauto.
      + rewrite def_funs_append;
        eapply preord_env_P_def_funs_not_in_P_r.
        * simpl. eapply preord_env_P_extend.
          rewrite Setminus_Same_set_Empty_set. apply preord_env_Empty_set.
          rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1'' Hlen Hf Hs. 
          edestruct (@set_lists_length val) as [rho2'' Hs']; [eauto | | ]. eauto.
          exists xs1, e1, rho2''. repeat split; eauto.
          erewrite <- find_def_Same_set_fun_in_fundefs; eauto.
          intros Hleq Hpre'. eapply preord_exp_refl; eauto.
          eapply preord_env_P_set_lists_l; [| | | eauto | eauto ]; eauto.
        * eauto with Ensembles_DB.
    - simpl. destruct B2; eauto using preord_env_P_refl.
      destruct HS1 as [_ H1]. exfalso. eapply not_In_Empty_set. eapply H1.
      simpl. eauto.
  Qed.

  End Trans.

End Log_rel.
