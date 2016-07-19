Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles.
Require Import cps cps_util identifiers env eval ctx Ensembles_util List_util.
Import ListNotations.


(** step-indexed relation on cps terms. Relates
 * cps-terms with closure-converted terms  *)
(* Expression relation : 
 * ---------------------
 *  (e1, ρ1) ~_k (e2, ρ2) iff 
 *    forall c1 <= k, 
 *      ρ1 |- e1 ->^c1 v1 -> 
 *      exists v2, p2 |- e2 -> v2 /\ v1 ~_(k-c1) v2 
 * Value relation :
 * ----------------
 * Integers: (n1 ~_k n2) iff n1 = n2
 * Constructors: C[v_1, .., v_n] ~_k C[v'_1, .., v'_m] iff
                     n <= m /\ v_1 ~_k v'_1 /\ ... /\ v_n ~_k v'_n'
 * Closures: (\f1 x1. e1, ρ1) ~_k {(\f2 Γ x2. e2, ρ2); ρ} iff 
 *              \forall v1 v2 i < k, v1 ~_j v2 => 
 *                (e1, ρ1[x1 -> v1, f1 -> (\f1 x1. e1, ρ1)]) ~_j 
 *                (e2, [x2 -> v2, f2 -> (\f2 x2. e2, ρ2), Γ -> ρ])
 *)
Fixpoint cc_approx_val (k : nat) (v1 v2 : val) {struct k} : Prop :=
  let cc_approx_exp (k : nat) (p1 p2 : exp * env) : Prop :=
      let '(e1, rho1) := p1 in
      let '(e2, rho2) := p2 in
      forall v1 c1,
        c1 <= k -> bstep_e rho1 e1 v1 c1 ->
        exists v2 c2, bstep_e rho2 e2 v2 c2 /\ 
                 cc_approx_val (k - c1) v1 v2
  in
  let fix cc_approx_val_aux (v1 v2 : val) {struct v1} : Prop :=
      let fix Forall2_aux vs1 vs2 :=
          match vs1, vs2 with
            | [], _ => True
            | v1 :: vs1, v2 :: vs2 =>
              cc_approx_val_aux v1 v2 /\ Forall2_aux vs1 vs2
            | _, _ => False
          end
      in
      match v1, v2 with
        | Vfun rho1 defs1 f1,
          Vconstr tau t ((Vfun rho2 defs2 f2) ::  (Vconstr tau' t' fvs) :: l)  =>
          forall (vs1 vs2 : list val) (j : nat) (t1 : type) 
            (xs1 : list var) (e1 : exp) (rho1' : env),
            length vs1 = length vs2 ->
            find_def f1 defs1 = Some (t1, xs1, e1) ->
            Some rho1' = setlist xs1 vs1 (def_funs defs1 defs1 rho1 rho1) ->
            exists (t2 : type) (Γ : var) (xs2 : list var) (e2 : exp) (rho2' : env),
              find_def f2 defs2 = Some (t2, Γ :: xs2, e2) /\
              Some rho2' = setlist (Γ :: xs2) ((Vconstr tau' t' fvs) :: vs2)
                                   (def_funs defs2 defs2 rho2 rho2) /\
              match k with
                | 0 => True
                | S k =>
                  let R := cc_approx_val (k - (k-j)) in
                  j < S k ->
                  Forall2 R vs1 vs2 ->
                  cc_approx_exp (k - (k - j)) (e1, rho1') (e2, rho2')
              end
        | Vconstr tau1 t1 vs1, Vconstr tau2 t2 vs2 =>
          t1 = t2 /\ Forall2_aux vs1 vs2
        | Vint n1, Vint n2 => n1 = n2
        | Vother t1, Vother t2 => True
        (* XXX : Question.  *)
        | Vobvs t1, Vobvs t2 => True
        | Vobservable t1 vs1, Vobservable t2 vs2 =>
          Forall2_aux vs1 vs2
        | _, _ => False
      end
  in cc_approx_val_aux v1 v2.

Definition cc_approx_exp (k : nat) (p1 p2 : exp * env) : Prop :=
  let '(e1, rho1) := p1 in
  let '(e2, rho2) := p2 in
  forall v1 c1,
    c1 <= k -> bstep_e rho1 e1 v1 c1 ->
    exists v2 c2, bstep_e rho2 e2 v2 c2 /\
             cc_approx_val (k - c1) v1 v2.

(** more compact definition of the value relation *)
Definition cc_approx_val' (k : nat) (v1 v2 : val) : Prop :=
  match v1, v2 with
    | Vfun rho1 defs1 f1,
      Vconstr tau t ((Vfun rho2 defs2 f2) ::  (Vconstr tau' t' fvs) :: l) =>
      forall (vs1 vs2 : list val) (j : nat) (t1 : type) 
        (xs1 : list var) (e1 : exp) (rho1' : env),
        length vs1 = length vs2 ->
        find_def f1 defs1 = Some (t1, xs1, e1) ->
        Some rho1' = setlist xs1 vs1 (def_funs defs1 defs1 rho1 rho1) ->
        exists (t2 : type) (Γ : var) (xs2 : list var) (e2 : exp) (rho2' : env),
          find_def f2 defs2 = Some (t2, Γ :: xs2, e2) /\
          Some rho2' = setlist (Γ :: xs2) ((Vconstr tau' t' fvs) :: vs2)
                               (def_funs defs2 defs2 rho2 rho2) /\
          (j < k -> Forall2 (cc_approx_val j) vs1 vs2 ->
           cc_approx_exp j (e1, rho1') (e2, rho2'))
    | Vconstr tau1 t1 vs1, Vconstr tau2 t2 vs2 =>
      t1 = t2 /\ Forall2_asym (cc_approx_val k) vs1 vs2
    | Vint n1, Vint n2 => n1 = n2
    | Vother t1, Vother t2 => True
    | Vobvs t1, Vobvs t2 => True
    | Vobservable t1 vs1, Vobservable t2 vs2 =>
      Forall2_asym (cc_approx_val k) vs1 vs2
    | _, _ => False
  end.

(** correspondence of the two definitions *)
Lemma cc_approx_val_eq (k : nat) (v1 v2 : val) :
  cc_approx_val k v1 v2 <-> cc_approx_val' k v1 v2.
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
  - split; intros Hpre; simpl; destruct l; try contradiction;
    destruct v0; try contradiction; destruct l; try contradiction;
    destruct l; try contradiction; destruct v1; try contradiction;
    intros; edestruct (Hpre vs1 vs2 0) as [t2' [Γ [xs2 [e2 [rho' [H1' [H2' H3']]]]]]];
    eauto; do 5 eexists; repeat split; eauto; intros Hc; exfalso; omega.
  - revert l0; induction l as [| x xs IHxs];
    intros l2; destruct l2 as [| y ys ];
    split; intros H; try (now simpl in H; inv H); try now (simpl; eauto).
    + destruct H as [H1 H2]; eauto.
      constructor; eauto. eapply IHxs. eauto.
    + inv H. split; eauto. eapply IHxs; eauto. 
  - split.
    * revert l0; induction l as [| x xs IHxs];
      intros l2; destruct l2 as [| y ys ];
      try (now intros [H1 H2]; split; eauto; inv H2).
      intros H; split; destruct H as [H1 [H2 H3]]; eauto. constructor. eauto.
      eapply IHxs. simpl. eauto.
    * revert l0; induction l as [| x xs IHxs];
      intros l2; destruct l2 as [| y ys ];
      try (now intros [H1 H2]; split; eauto; inv H2).
      intros H; split; inv H; eauto. inv H1.
      split; [now eauto | now apply IHxs].
  - split; intros Hpre; simpl; destruct l; try contradiction;
    destruct v0; try contradiction; destruct l; try contradiction;
    destruct l; try contradiction; destruct v1; try contradiction;
    intros;
    edestruct (Hpre vs1 vs2 j) as [t2' [Γ [xs2 [e2 [rho' [H1' [H2' H3']]]]]]];
    eauto; do 5 eexists; repeat split; eauto; intros Hleq Hf v1 c1 Hleq' Hstep;
    (assert (Heq : k - (k - j) = j) by omega);
    rewrite Heq in *;  eapply H3'; eauto.
  - simpl; revert l0; induction l as [| x xs IHxs];
    intros l2; destruct l2 as [| y ys ];
    split; intros H; try (now simpl in H; inv H).
    destruct H as [H1 H2]; eauto.
    constructor; eauto. now eapply IHxs.
    inv H. split; [now eauto | now apply IHxs].
Qed.

Opaque cc_approx_val.

(** Environment relation for a single point (i.e. variable) : 
 * ρ1 ~_k^x ρ2 iff ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
Definition cc_approx_var_env (k : nat) (rho1 rho2 : env) (x y : var) : Prop :=
  forall v1, 
    M.get x rho1 = Some v1 -> 
    exists v2, M.get y rho2 = Some v2 /\ cc_approx_val k v1 v2.

(** Environment relation for a set of points (i.e. predicate over variables) : 
 * ρ1 ~_k^S ρ2 iff 
 *   forall x, S x -> ρ1(x) = Some v -> ρ2(x) = Some v' /\ v ~_k v' *)
Definition cc_approx_env_P (P : Ensemble var) k rho1 rho2 :=
  forall (x : var), P x -> cc_approx_var_env k rho1 rho2 x x.

(** Environment relation for the whole domain of definition :
 * ρ1 ~_k ρ2 iff forall x, ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
Definition cc_approx_env (k : nat) (rho1 rho2 : env) : Prop :=
  cc_approx_env_P (fun _ => True) k rho1 rho2.

(** Lemmas about extending the environment *)
Lemma cc_approx_var_env_extend_eq :
  forall (rho1 rho2 : env) (k : nat) (x : var) (v1 v2 : val),
    cc_approx_val k v1 v2 ->
    cc_approx_var_env k (M.set x v1 rho1) (M.set x v2 rho2) x x.
Proof.
  intros rho1 rho2 k x v1 v2 Hval x' Hget.
  rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss. split; eauto.
Qed.

Lemma cc_approx_var_env_extend_neq :
  forall (rho1 rho2 : env) (k : nat) (x y : var) (v1 v2 : val),
    cc_approx_var_env k rho1 rho2 y y ->
    y <> x ->
    cc_approx_var_env k (M.set x v1 rho1) (M.set x v2 rho2) y y.
Proof.
  intros rho1 rho2 k x  y v1 v2 Hval Hneq x' Hget.
  rewrite M.gso in *; eauto.
Qed.

Lemma cc_approx_var_env_extend :
  forall (rho1 rho2 : env) (k : nat) (x y : var) (v1 v2 : val),
    cc_approx_var_env k rho1 rho2 y y ->
    cc_approx_val k v1 v2 ->
    cc_approx_var_env k (M.set x v1 rho1) (M.set x v2 rho2) y y.
Proof.
  intros rho1 rho2 k x y v1 v2 Henv Hval.
  destruct (Coqlib.peq y x); subst.
  - apply cc_approx_var_env_extend_eq; eauto.
  - apply cc_approx_var_env_extend_neq; eauto.
Qed.

(** The environment relation is antimonotonic in the set
 * of free variables *) 
Lemma cc_approx_env_P_antimon (P1 P2 : var -> Prop) k rho1 rho2 :
  cc_approx_env_P P2 k rho1 rho2 ->
  (Included var P1 P2) ->
  cc_approx_env_P P1 k rho1 rho2.
Proof.
  intros Hpre Hin x HP2. eapply Hpre; eapply Hin; eauto.
Qed.

Global Instance cc_approx_env_proper :
  Proper (Same_set var ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> iff)
         cc_approx_env_P.
Proof.
  intros s1 s2 [H1 H2]; split; intros Hpre;
  eapply cc_approx_env_P_antimon; subst; eauto.
Qed.

(** Lemmas about the sets that index the environment relation *)
Lemma cc_approx_env_Empty_set k (rho1 rho2 : env) :
  cc_approx_env_P (Empty_set var) k rho1 rho2.
Proof.
  intros x H. inv H.
Qed.

Lemma cc_approx_env_P_union (P1 P2 : var -> Prop) k rho1 rho2 :
  cc_approx_env_P P1 k rho1 rho2 ->
  cc_approx_env_P P2 k rho1 rho2 ->
  cc_approx_env_P (Union var P1 P2) k rho1 rho2.
Proof.
  intros Hpre1 Hpre2 x HP2. inv HP2; eauto.
Qed.

Lemma cc_approx_env_P_inter_l (P1 P2 : var -> Prop) k rho1 rho2 :
  cc_approx_env_P P1 k rho1 rho2 ->
  cc_approx_env_P (Intersection var P1 P2) k rho1 rho2.
Proof.
  intros Hpre x HP2. inv HP2; eauto.
Qed.

Lemma cc_approx_env_P_inter_r (P1 P2 : var -> Prop) k rho1 rho2 :
  cc_approx_env_P P2 k rho1 rho2 ->
  cc_approx_env_P (Intersection var P1 P2) k rho1 rho2.
Proof.
  intros Hpre x HP2.
  inv HP2; eauto.
Qed.

(** Extend the related environments with a single point *)
Lemma cc_approx_env_P_extend :
  forall P (rho1 rho2 : env) (k : nat) (x : var) (v1 v2 : val),
    cc_approx_env_P (Setminus var P (Singleton var x)) k rho1 rho2 ->
    cc_approx_val k v1 v2 ->
    cc_approx_env_P P k (M.set x v1 rho1) (M.set x v2 rho2).
Proof.
  intros P rho1 rho2 k x v1 v2 Henv Hval x' HP v1' Hget.
  rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x); subst.
  - inv Hget. eexists. rewrite M.gss. split; eauto.
  - apply Henv in Hget; eauto. destruct Hget as [v2' [Heq Hpre]].
    eexists; split; eauto. rewrite M.gso; eauto. constructor; eauto.
    intros Hin. inv Hin. congruence.
Qed.

(** Extend the related environments with a list *)
Lemma cc_approx_env_P_setlist_l:
  forall (P1 P2 : var -> Prop) (rho1 rho2 rho1' rho2' : env)
    (k : nat) (xs : list var) (vs1 vs2 : list val),
    cc_approx_env_P P1 k rho1 rho2 ->
    (forall x, ~ List.In x xs -> P2 x -> P1 x) ->
    Forall2 (cc_approx_val k) vs1 vs2 ->
    setlist xs vs1 rho1 = Some rho1' ->
    setlist xs vs2 rho2 = Some rho2' ->
    cc_approx_env_P P2 k rho1' rho2'.
Proof.
  intros P1 P2 rho1' rho2' rho1 rho2 k xs vs1 vs2 Hpre Hyp Hall Hset1 Hset2
         x HP v Hget.
  destruct (in_dec var_dec x xs).
  - edestruct setlist_Forall2_get as [v1 [v2 [Hget1 [Hget2 HP']]]]; eauto.
    rewrite Hget in Hget1. inv Hget1. repeat eexists; eauto.
  - erewrite <- setlist_not_In in Hget; eauto.
    edestruct Hpre as [v2 [Hget' Hpre']]; eauto.
    repeat eexists; eauto. erewrite <- setlist_not_In; eauto.
Qed.


Lemma cc_approx_var_env_getlist (rho1 rho2 : env) (k : nat)
      (xs ys : list var) (vs1 : list val) :
  Forall2 (cc_approx_var_env k rho1 rho2) xs ys ->
  getlist xs rho1 = Some vs1 ->
  exists vs2,
    getlist ys rho2 = Some vs2 /\ Forall2 (cc_approx_val k) vs1 vs2.
Proof.
  revert ys vs1. induction xs as [| x xs IHxs]; intros ys vs2 Hall Hget.
  - destruct ys; inv Hall. inv Hget. eexists. split; simpl; eauto.
  - simpl in Hget.
    destruct (M.get x rho1) eqn:Heq1; try discriminate.
    destruct (getlist xs rho1) eqn:Heq2; try discriminate. inv Hget.
    destruct ys as [| y ys]; inv Hall. 
    destruct (IHxs ys l H4 eq_refl) as [vs2 [Hget HAll]].
    destruct (H2 _ Heq1) as [v2 [Heq Hpre]].
    eexists. split; simpl; eauto. rewrite Hget, Heq. eauto.
Qed.

Lemma cc_approx_env_P_getlist_l (P : var -> Prop) (rho1 rho2 : env) (k : nat)
      (xs : list var) (vs1 : list val) :
  cc_approx_env_P P k rho1 rho2 ->
  Included _ (FromList xs) P ->
  getlist xs rho1 = Some vs1 ->
  exists vs2,
    getlist xs rho2 = Some vs2 /\ Forall2 (cc_approx_val k) vs1 vs2.
Proof.
  intros Henv. revert vs1.
  induction xs as [| x xs IHxs]; intros vs1 Hp Hget.
  - inv Hget. eexists. split; simpl; eauto.
  - simpl in Hget. destruct (M.get x rho1) eqn:Heq1; try discriminate.
    destruct (getlist xs rho1) eqn:Heq2; try discriminate. inv Hget.
    edestruct (IHxs l) as  [vs2 [Hget HAll]]; eauto.
    + intros x' Hin. eapply Hp. constructor 2; eauto.
    + eapply Henv in Heq1. destruct Heq1 as [v2 [H1 H2]].
      eexists. split; simpl; eauto. rewrite H1. rewrite Hget.
      constructor. apply Hp. now constructor.
Qed.

Corollary cc_approx_env_getlist_l (rho1 rho2 : env) (k : nat)
          (xs : list var) (vs1 : list val) :
  cc_approx_env k rho1 rho2 ->
  getlist xs rho1 = Some vs1 ->
  exists vs2,
    getlist xs rho2 = Some vs2 /\ Forall2 (cc_approx_val k) vs1 vs2.
Proof.
  intros. eapply cc_approx_env_P_getlist_l; eauto.
  intros x H'; simpl; eauto.
Qed.

Corollary cc_approx_env_extend (rho1 rho2 : env) (k : nat)
          (x : var) (v1 v2 : val) :
  cc_approx_env k rho1 rho2 ->
  cc_approx_val k v1 v2 ->
  cc_approx_env k (M.set x v1 rho1) (M.set x v2 rho2).
Proof.
  intros H1 Hval. apply cc_approx_env_P_extend; eauto.
  eapply cc_approx_env_P_antimon; eauto. intros x' H; simpl; eauto.
Qed.

Corollary cc_approx_env_setlist_l (rho1 rho2 rho1' rho2' : env) (k : nat)
          (xs : list var) (vs1 vs2 : list val) :
  cc_approx_env k rho1 rho2 ->
  Forall2 (cc_approx_val k) vs1 vs2 ->
  setlist xs vs1 rho1 = Some rho1' ->
  setlist xs vs2 rho2 = Some rho2' ->
  cc_approx_env k rho1' rho2'.
Proof.
  intros. eapply cc_approx_env_P_setlist_l; eauto.
Qed.

Lemma cc_approx_env_P_set_not_in_P_r P k rho rho' x v :
  cc_approx_env_P P k rho rho' ->
  ~ In _ P x ->
  cc_approx_env_P P k rho (M.set x v rho').
Proof. 
  intros Hcc Hnin y Py v' Hget.
  edestruct Hcc as [v'' [Hget' Happrox]]; eauto.
  exists v''. rewrite M.gsspec.
  destruct (Coqlib.peq y x); subst.
  - contradiction.
  - eauto.
Qed.

Lemma cc_approx_env_P_def_funs_not_In_P_l k rho1 rho2 S B B' :
  Disjoint _ S (name_in_fundefs B') ->
  cc_approx_env_P S k rho1 rho2 ->
  cc_approx_env_P S k (def_funs B B' rho1 rho1) rho2.
Proof.
  intros Hd Hcc x HS v Hget. eapply Hcc; eauto. 
  erewrite <- def_funs_neq. eassumption.  
  intros Hc. eapply Hd; constructor; eauto.
Qed.

Lemma cc_approx_env_P_def_funs_not_In_P_r k rho1 rho2 S B B' :
  Disjoint _ S (name_in_fundefs B') ->
  cc_approx_env_P S k rho1 rho2 ->
  cc_approx_env_P S k rho1 (def_funs B B' rho2 rho2).
Proof.
  intros Hd Hcc x HS v Hget.
  edestruct Hcc as [v' [Hget' Hcc']]; eauto.
  eexists; split; eauto.
  rewrite def_funs_neq. eassumption.
  intros Hc. eapply Hd; constructor; eauto.
Qed.

(** * Index Monotonicity Properties *)

(** The value relation is monotonic in the step index *)
Lemma cc_approx_val_monotonic (k : nat) :
  (forall v1 v2 j,
     cc_approx_val k v1 v2 -> j <= k -> cc_approx_val j v1 v2).
Proof.
  intros v1 v2 h Hpre Hleq. try rewrite cc_approx_val_eq in *.
  revert v2 Hpre; induction v1 using val_ind'; intros v2 Hpre;
  destruct v2; try (simpl; contradiction); eauto.
  - destruct l; try now inv Hpre.
  - inv Hpre. inv H0.
    split; auto. constructor; rewrite cc_approx_val_eq in *.
    now eapply IHv1; eauto.
    destruct (IHv0 ((Vconstr tau t1 l'))) as [Heq Hpre']; eauto.
    now split; eauto.
  - destruct l; try contradiction. destruct v0; try contradiction. 
    destruct l; try contradiction. destruct v1; try contradiction. 
    intros vs1 vs2 j t1' xs e1 rho1' Hlen Hf Heq.
    edestruct Hpre as [t2' [Γ [xs2 [e2 [rho2' [H1 [H2 H3]]]]]]]; eauto.
    do 5 eexists; split; eauto. split; eauto. intros Hleq' Hall. 
    eapply H3; eauto. omega.
  - constructor.
  - inv Hpre. constructor; rewrite cc_approx_val_eq in *. now eapply IHv1; eauto.
    now eapply (IHv0 (Vobservable tau l')) in H3.
Qed.

(** The expression relation is monotonic in the step index *)
Lemma cc_approx_exp_monotonic (k : nat) :
  (forall rho1 e1 rho2 e2 j,
     cc_approx_exp k (rho1, e1) (rho2, e2) ->
     j <= k -> cc_approx_exp j (rho1, e1) (rho2, e2)).
Proof.
  intros rho1 e1 rho2 e2 j Hpre Hleq v1 c1 Hlt Hstep.
  edestruct (Hpre v1 c1) as [v2 [c2 [H1 H2]]]; eauto. omega.
  do 2 eexists; split; eauto.
  eapply cc_approx_val_monotonic. eapply H2. omega.
Qed.

(** The environment relations are monotonic in the step index *)
Lemma cc_approx_env_P_monotonic :
  forall P (k j : nat) (rho1 rho2 : env),
    j <= k -> cc_approx_env_P P k rho1 rho2 -> cc_approx_env_P P j rho1 rho2.
Proof.
  intros P k j rho1 rho2 Hleq Hpre x HP v Hget.
  edestruct Hpre as [v2 [Heq Hpre2]]; eauto.
  eexists; split; eauto. eapply cc_approx_val_monotonic; eauto.
Qed.

Lemma cc_approx_env_monotonic k j rho1 rho2 :
  j <= k -> cc_approx_env k rho1 rho2 -> cc_approx_env j rho1 rho2.
Proof.
  intros Hleq H. eapply cc_approx_env_P_monotonic; eauto.
Qed.


(** * Compatibility lemmas *)

Lemma cc_approx_exp_const_compat k rho1 rho2 x tau t ys1 ys2 e1 e2 :
  Forall2 (cc_approx_var_env k rho1 rho2) ys1 ys2 ->
  (forall vs1 vs2 : list val,
     Forall2 (cc_approx_val k) vs1 vs2 ->
     cc_approx_exp k (e1, M.set x (Vconstr tau t vs1) rho1)
                   (e2, M.set x (Vconstr tau t vs2) rho2)) ->
  cc_approx_exp k (Econstr x tau t ys1 e1, rho1) (Econstr x tau t ys2 e2, rho2).
Proof.
  intros Hall Hpre v1 c1 Hleq1 Hstep1. inv Hstep1.
  edestruct (cc_approx_var_env_getlist rho1 rho2) as [vs2' [Hget' Hpre']];
    [| eauto |]; eauto.
  edestruct Hpre as [v2 [c2 [Hstep Hval]]]; eauto.
  repeat eexists; eauto. econstructor; eauto.
Qed.

Lemma cc_approx_exp_proj_compat k rho1 rho2 x tau n y1 y2 e1 e2 :
  cc_approx_var_env k rho1 rho2 y1 y2 ->
  (forall v1 v2,
     cc_approx_val k v1 v2 -> 
     cc_approx_exp k (e1, M.set x v1 rho1)
                   (e2, M.set x v2 rho2)) ->
  cc_approx_exp k (Eproj x tau n y1 e1, rho1) (Eproj x tau n y2 e2, rho2).
Proof.
  intros Henv Hexp v1 c1 Hleq1 Hstep1. inv Hstep1.
  edestruct Henv as [v' [Hget Hpre]]; eauto.
  destruct v'; rewrite cc_approx_val_eq in Hpre; simpl in Hpre; try contradiction.
  inv Hpre.
  edestruct (Forall2_asym_nthN (cc_approx_val k) vs l) as [v2 [Hnth Hval]]; eauto.
  edestruct Hexp as [v2' [c2 [Hstep Hval']]]; eauto.
  repeat eexists; eauto. econstructor; eauto.
Qed.

Lemma cc_approx_exp_case_nil_compat k rho1 rho2 x1 x2 :
  cc_approx_exp k (Ecase x1 [], rho1) (Ecase x2 [], rho2).
Proof.
  intros v1 c1 Hleq1 Hstep1. inv Hstep1. inv H3.
Qed.

Lemma cc_approx_exp_case_cons_compat k rho1 rho2 x1 x2 c e1 e2 P1 P2:
  cc_approx_var_env k rho1 rho2 x1 x2 ->
  cc_approx_exp k (e1, rho1) (e2, rho2) ->
  cc_approx_exp k (Ecase x1 P1, rho1)
                (Ecase x2 P2, rho2) ->
  cc_approx_exp k (Ecase x1 ((c, e1) :: P1), rho1)
                (Ecase x2 ((c, e2) :: P2), rho2).
Proof.
  intros Henv Hexp_hd Hexp_tl v1 c1 Hleq1 Hstep1. inv Hstep1. inv H3.
  destruct (M.elt_eq c t) eqn:Heq; subst.
  - inv H0. edestruct Hexp_hd as [v2 [c2 [Hstep2 Hpre2]]]; eauto.
    edestruct Henv as [v2' [Hget Hpre]]; eauto.
    rewrite cc_approx_val_eq in Hpre.
    destruct v2'; try (now simpl in Hpre; contradiction). inv Hpre. 
    repeat eexists; eauto. econstructor; eauto. simpl; rewrite Heq; eauto.
  - edestruct Hexp_tl as [v2 [c2 [Hstep2 Hpre2]]]; eauto.
    econstructor; eauto. inv Hstep2.
    edestruct Henv as [v2' [Hget Hpre]]; eauto.
    rewrite cc_approx_val_eq in Hpre.
    destruct v2'; try (now simpl in Hpre; contradiction). inv Hpre.
    rewrite Hget in H3; inv H3.
    repeat eexists; eauto. econstructor; eauto. simpl; rewrite Heq; eauto.
Qed.

Axiom Prim_axiom :
  forall f f' v1,
    M.get f pr = Some f' ->
    forall k vs1 vs2,
      Forall2 (cc_approx_val k) vs1 vs2 ->
      f' vs1 = Some v1 ->
      exists v2,
        f' vs2 = Some v2 /\                      
        cc_approx_val k v1 v2.

Lemma cc_approx_exp_prim_compat k rho1 rho2 x1 x2 tau f ys1 ys2 e1 e2 :
  Forall2 (cc_approx_var_env k rho1 rho2) ys1 ys2 ->
  (forall v1 v2,
     cc_approx_val k v1 v2 -> 
     cc_approx_exp k (e1, M.set x1 v1 rho1)
                   (e2, M.set x2 v2 rho2)) ->
  cc_approx_exp k (Eprim x1 tau f ys1 e1, rho1) (Eprim x2 tau f ys2 e2, rho2).
Proof.
  intros Henv Hexp v1 c1 Hleq1 Hstep1. inv Hstep1.
  edestruct cc_approx_var_env_getlist as [vs2 [Hget' Hpre']]; eauto.
  edestruct Prim_axiom as [v2 [Heq Hprev2]]; eauto.
  edestruct Hexp as [v2' [c2 [Hstepv2' Hprev2']]]; eauto.
  repeat eexists; eauto. econstructor; eauto.
Qed.


(** Lift a value predicate to a subset of an environment *)
Definition lift_P_env (S : Ensemble var) (P : Ensemble val) (rho : env) :=
  forall x v, S x -> M.get x rho = Some v -> P v.

(* TODO: move to identifiers.v *)
Inductive closed_fundefs_in_val : val -> Prop :=
| Vconstr_closed :
    forall tau t vs,
      Forall closed_fundefs_in_val vs ->
      closed_fundefs_in_val (Vconstr tau t vs)
| Vfun_closed :
    forall rho B f,
      closed_fundefs B ->
      closed_fundefs_in_fundefs B ->
      (* fun_in_fundefs B (f, tau, xs, e) -> *)
      (* Included _ (occurs_free e) (Union _ (FromList xs) (name_in_fundefs B)) -> *)
      closed_fundefs_in_val (Vfun rho B f)
| Vint_closed :
    forall z, closed_fundefs_in_val (Vint z)
| Vother_closed :
    forall tau, closed_fundefs_in_val (Vother tau)
| Vobs :
    forall tau, closed_fundefs_in_val (Vobvs tau)
| Vobservable_closed :
    forall tau vs,
      Forall closed_fundefs_in_val vs ->
      closed_fundefs_in_val (Vobservable tau vs).

Definition closed_fundefs_in_env (S : Ensemble var) rho : Prop :=
  lift_P_env S closed_fundefs_in_val rho.

Lemma lift_P_env_antimon S S' P rho :
  Included _ S S' ->
  lift_P_env S' P rho ->
  lift_P_env S P rho.
Proof.
  intros H Henv x v HS Hget.
  eapply Henv; eauto. eapply H; eauto.
Qed.

Instance lift_P_env_proper : Proper (Same_set var ==> eq ==> eq ==> iff) lift_P_env.
Proof.
  intros S1 S2 Heq P1 P2 Heq' rho1 rho2 Heq''; subst.
  split; intros H x v Hs Hget; (eapply H; [ | now eauto ]);
  now eapply Heq.
Qed.

Lemma lift_P_env_Union_l S1 S2 P rho :
  lift_P_env (Union _ S1 S2) P rho ->
  lift_P_env S1 P rho.
Proof.
  intros H. eapply lift_P_env_antimon; [| now eauto ].
  now apply Included_Union_l.
Qed.

Lemma lift_P_env_Union_r S1 S2 P rho :
  lift_P_env (Union _ S1 S2) P rho ->
  lift_P_env S2 P rho.
Proof.
  intros H. eapply lift_P_env_antimon; [| now eauto ].
  now apply Included_Union_r.
Qed.

Lemma lift_P_env_Emtpy_set P rho :
  lift_P_env (Empty_set _) P rho.
Proof.
  intros x v H. inv H.
Qed.


Lemma lift_P_env_extend S P rho x v :
  lift_P_env (Setminus _ S (Singleton _ x)) P rho ->
  P v ->
  lift_P_env S P (M.set x v rho). 
Proof.
  intros H Hp x' v' HS Hget.
  rewrite M.gsspec in Hget.
  destruct (Coqlib.peq x' x); subst.
  - now inv Hget.
  - eapply H; [| eassumption ].
    constructor; eauto. intros Hc. inv Hc. congruence.
Qed.

Lemma lift_P_env_setlist S P rho rho' xs vs :
  lift_P_env (Setminus _ S (FromList xs)) P rho ->
  Forall P vs ->
  setlist xs vs rho = Some rho' ->
  lift_P_env S P rho'. 
Proof.
  revert S xs rho rho'. induction vs; intros S xs rho rho' Henv Hall Hset.
  - destruct xs; inv Hset.
    rewrite FromList_nil, Setminus_Empty_set_Same_set in Henv.
    eapply Henv; now eauto.
  - destruct xs; try discriminate. inv Hall.
    simpl in Hset. destruct (setlist xs vs rho) eqn:Heq ; try discriminate.
    inv Hset. eapply lift_P_env_extend; eauto.
    eapply IHvs; eauto.
    now rewrite FromList_cons, <- Setminus_Union in Henv.
Qed.

Lemma lift_P_env_def_funs S P B B' rho  :
  lift_P_env (Setminus _ S (name_in_fundefs B)) P rho ->
  (forall f, P (Vfun rho B' f)) ->
  lift_P_env S P (def_funs B' B rho rho). 
Proof.
  revert S rho. induction B; intros S rho Henv Hfun.
  - simpl. eapply lift_P_env_extend; [| now eauto ].
    eapply IHB; [| eassumption ].
    eapply lift_P_env_antimon; [| eassumption ].
    rewrite Setminus_Union. now eapply Included_refl.
  - now rewrite Setminus_Empty_set_Same_set in Henv. 
Qed.

Lemma lift_P_env_get S P rho x v :
  lift_P_env S P rho ->
  Included _ (Singleton _ x) S ->
  M.get x rho = Some v ->
  P v.
Proof.
  intros Henv HS Hget. eapply Henv; eauto. 
  now eapply HS; eauto. 
Qed.

Lemma lift_P_env_getlist S P rho xs vs :
  lift_P_env S P rho ->
  Included _ (FromList xs) S ->
  getlist xs rho = Some vs ->
  Forall P vs.
Proof.
  revert S xs rho. induction vs; intros S xs rho Henv Hincl Hget.
  - eauto.
  - destruct xs; try discriminate. simpl in Hget.
    destruct (M.get v rho) eqn:Heq; try discriminate.
    destruct (getlist xs rho) eqn:Heq'; try discriminate.
    inv Hget. rewrite FromList_cons in Hincl.
    constructor.
    + eapply lift_P_env_get; eauto.
      eapply Included_trans; [| now eauto ].
      eapply Included_Union_l.
    + eapply IHvs; eauto.
      eapply Included_trans; [| now eauto ].
      eapply Included_Union_r.
Qed.

Lemma Forall_nthN {A} (R : A -> Prop) l n v :
  Forall R l ->
  nthN l n = Some v ->
  R v.
Proof.
  revert n. induction l; intros n Hall Hnth; [ discriminate |].
  inv Hall. simpl in Hnth.
  destruct n. 
  - inv Hnth; eauto.
  - eapply IHl; eauto.  
Qed. 

(* TODO: move to identifiers.v *)
Lemma fun_in_fundefs_funs_in_fundef B B' f t xs e :
  fun_in_fundefs B (f, t, xs, e) ->
  funs_in_exp B' e ->
  funs_in_fundef B' B.
Proof.
  induction B; intros Hin Hfuns.
  - inv Hin.
    + inv H. now eauto.
    + constructor 2. eapply IHB; eauto.
  - inv Hin.
Qed.

Axiom prims_closed_fundefs :
  forall (f : prim) (f' : list val -> option val) vs v,
    M.get f pr = Some f' ->
    Forall closed_fundefs_in_val vs ->
    f' vs = Some v ->
    closed_fundefs_in_val v.

Lemma bstep_e_preserves_closed_fundefs rho e v c :
  bstep_e rho e v c ->
  closed_fundefs_in_env (occurs_free e) rho ->
  closed_fundefs_in_exp e ->
  closed_fundefs_in_val v.
Proof.
  intros Hstep Hcl1 Hcl2. induction Hstep.
  - constructor.
    eapply lift_P_env_getlist; eauto.
    rewrite occurs_free_Eapp. apply Included_Union_l.
  - eapply IHHstep.
    + subst. eapply lift_P_env_extend. 
      * eapply lift_P_env_antimon; [| now eauto ].
        rewrite occurs_free_Econstr.
        eapply Included_Union_r.
      * constructor. eapply lift_P_env_getlist; eauto.
        rewrite occurs_free_Econstr. eapply Included_Union_l.
    + intros B Hin. eauto.
  - eapply IHHstep.
    + subst. eapply lift_P_env_extend. 
      * eapply lift_P_env_antimon; [| now eauto ].
        rewrite occurs_free_Eproj.
        eapply Included_Union_r.
      * eapply Forall_nthN; [| eassumption ].
        eapply lift_P_env_get in H; [| eassumption |].
        now inv H. 
        rewrite occurs_free_Eproj. eapply Included_Union_l.
    + intros B Hin. eauto.
  - eapply IHHstep.
    + eapply lift_P_env_antimon; [| now eauto ].
      eapply occurs_free_Ecase_Included.
      eapply findtag_In_patterns. eassumption.
    + intros B Hin. eapply Hcl2.
      econstructor; eauto. apply findtag_In_patterns. eassumption.
  - eapply IHHstep.
    + eapply Hcl1 in H; [| now eauto ]. inv H.
      apply find_def_correct in H1.  
      eapply lift_P_env_antimon. eapply occurs_free_in_fun.
      eassumption.
      unfold closed_fundefs in H5. rewrite H5, Union_Empty_set_l.
      eapply lift_P_env_setlist; [| | now eauto ].
      * rewrite Setminus_Union_distr, Setminus_Empty_set, Union_Empty_set_r.
        eapply  lift_P_env_def_funs.
        rewrite Setminus_Included_Empty_set. now apply lift_P_env_Emtpy_set.
        eapply Setminus_Included. now apply Included_refl.
        intros f''. now constructor. 
      * eapply lift_P_env_getlist; [ eassumption | | eassumption ].
        rewrite occurs_free_Eapp. eapply Included_Union_l.
    + intros B Hin.
      eapply Hcl1 in H; [| now eauto ].
      eapply find_def_correct in H1.
      inv H. eapply H7. eapply fun_in_fundefs_funs_in_fundef; eassumption. 
  - eapply IHHstep.
    + eapply lift_P_env_def_funs.
      * eapply lift_P_env_antimon; [| eassumption ].
        rewrite occurs_free_Efun. eapply Included_Union_r.
      * intros f. constructor. now eapply Hcl2.
        intros B H. eapply Hcl2. now eauto.
    + intros B Hin. eauto.
  - eapply IHHstep.
    + subst. eapply lift_P_env_extend. 
      * eapply lift_P_env_antimon; [| now eauto ].
        rewrite occurs_free_Eprim. eapply Included_Union_r.
      * eapply prims_closed_fundefs; [ eassumption | | eassumption ].
        eapply lift_P_env_getlist; [ eassumption | | eassumption ].
        rewrite occurs_free_Eprim. eapply Included_Union_l.
    + intros B Hin. eauto.
Qed.
 
Lemma cc_approx_exp_respects_preord_exp_r_pre (k : nat)
      (rho1 rho2 rho3 : env) (e1 e2 e3 : exp) :
  (forall j v1 v2 v3,
     j <= k ->
     cc_approx_val j v1 v2 ->
     (forall k, preord_val k v2 v3) ->
     cc_approx_val j v1 v3) ->
  cc_approx_exp k (e1, rho1) (e2, rho2) ->
  (forall k', preord_exp k' (e2, rho2) (e3, rho3)) ->
  cc_approx_exp k (e1, rho1) (e3, rho3).
Proof.
  intros IH Hexp1 Hexp2 v1 c Hleq1 Hstep1. 
  edestruct Hexp1 as [v2 [c2 [Hstep2 Hpre2]]]; eauto. 
  edestruct (Hexp2 c2) as [v3 [c3 [Hstep3 Hpre3]]]; [| eauto | ]. omega.
  exists v3, c3. split; eauto.
  eapply IH; [ omega | now eauto | ].
  intros m.
  edestruct (Hexp2 (m + c2)) as [v3' [c3' [Hstep3' Hpre3']]]; [| eauto |]. omega.
  eapply bstep_e_deterministic in Hstep3; eauto. inv Hstep3.
  eapply preord_val_monotonic; eauto. omega.
Qed.

Lemma occurs_free_closed_fundefs f tau xs e B :
  fun_in_fundefs B (f, tau, xs, e) ->
  closed_fundefs B ->
  Included _ (occurs_free e) (Union _ (FromList xs) (name_in_fundefs B)).
Proof.
  intros H Hcl.
  eapply Included_trans. now eapply occurs_free_in_fun; eauto.
  unfold closed_fundefs in Hcl. rewrite Hcl, Union_Empty_set_l.
  eapply Included_refl.
Qed.

Lemma cc_approx_val_respects_preord_val_r (k : nat) (v1 v2 v3 : val) :
  cc_approx_val k v1 v2 ->
  (forall k, preord_val k v2 v3) ->
  cc_approx_val k v1 v3.
Proof.
  revert v1 v2 v3. induction k using lt_wf_rec.
  induction v1 using val_ind'; intros v2 v3 Happrox Hpre;
  assert (Hpre' := Hpre k);
  rewrite cc_approx_val_eq, preord_val_eq in *.
  - destruct v2; try contradiction.
    destruct v3; try contradiction.
    inv Hpre'; inv Happrox. split; eauto.
  - destruct v2; try contradiction.
    destruct v3; try contradiction.
    destruct l0; [now inv Happrox; inv H1 |].
    destruct l1; [now inv Hpre'; inv H1 |].
    inv Hpre'; inv Happrox. inv H1; inv H2; split; eauto.
    constructor; eauto.
    + eapply IHv1; [ now eauto |].
      intros k'. specialize (Hpre k').
      rewrite preord_val_eq in Hpre. inv Hpre. now inv H1.
    + assert (Hsuf : cc_approx_val' k (Vconstr tau t3 l)  (Vconstr tau t3 l1)).
      { rewrite <- cc_approx_val_eq.
        eapply IHv0 with (v2 := Vconstr tau t3 l0).
        - rewrite cc_approx_val_eq. now split; eauto.
        - intros k'. specialize (Hpre k'). rewrite preord_val_eq in Hpre.
          inv Hpre. inv H1. rewrite preord_val_eq. now split; eauto. }
      now inv Hsuf.
  - destruct v2, v3; try contradiction. 
    destruct l; try contradiction.
    destruct v0, l; try contradiction.
    destruct v1; try contradiction. 
    inversion Hpre' as [Hleq Hall]. clear Hpre'. inv Hall.
    rewrite preord_val_eq in H2. inv H4.
    rewrite preord_val_eq in H3.
    destruct y, y0; try contradiction.
    intros vs1 vs2 j t1' xs1 e1 rho1 Heq1 Hfind1 Hset1.
    edestruct (Happrox vs1 vs2) as [t2' [Γ [xs2 [e2 [rho2' [Hfind2 [Hset2 Heval2]]]]]]]; eauto.
    edestruct (H2 (Vconstr t5 t6 l1 :: vs2) (Vconstr t7 t8 l0 :: vs2)) with (j := 0) as
        [t3' [xs3' [e3 [rho3 [Hfind3 [Hset3 _]]]]]]; eauto.
    edestruct xs3' as [| Γ' xs3]; try discriminate. 
    do 5 eexists. repeat split; eauto.
    intros Hlt Hall. 
    eapply cc_approx_exp_respects_preord_exp_r_pre
    with (e2 := e2) (rho2 := rho2').
    + intros. eapply H; [ omega | eassumption | eassumption ].
    + eapply Heval2. omega. assumption.
    + intros k'. specialize (Hpre (k'+1)). rewrite preord_val_eq in Hpre.
      inversion Hpre as [_ Hall']. clear Hpre. inv Hall'.
      rewrite preord_val_eq in H5.
      edestruct (H5 (Vconstr t5 t6 l1 :: vs2) (Vconstr t7 t8 l0 :: vs2)) as
          [t3'' [xs3'' [e3' [rho4 [Hfind3' [Hset3' Heval3']]]]]]; eauto. 
      rewrite Hfind3' in Hfind3. inv Hfind3.
      rewrite <- Hset3 in Hset3'. inv Hset3'.
      eapply Heval3'. omega. inv H8. constructor.
      eapply preord_val_monotonic. eassumption. omega.
      eapply Forall2_refl. eapply preord_val_refl.
  - destruct v2; try contradiction.
    destruct v3; try contradiction. inv Happrox.
    inv Hpre'. reflexivity.
  - destruct v2; try contradiction.
    destruct v3; try contradiction. inv Happrox.
    inv Hpre'. reflexivity.
  - destruct v2; try contradiction.
    destruct v3; try contradiction. inv Happrox.
    inv Hpre'. reflexivity.
  - destruct v2; try contradiction.
    destruct v3; try contradiction.
    constructor.
  - destruct v2; try contradiction.
    destruct v3; try contradiction.
    destruct l0; [now inv Happrox; inv H1 |].
    destruct l1; [now inv Hpre'; inv H1 |].
    inv Hpre'; inv Happrox.
    constructor.
    + eapply IHv1; [ now eauto |].
      intros k'. specialize (Hpre k').
      rewrite preord_val_eq in Hpre. now inv Hpre.
    + assert (Hsuf : cc_approx_val' k (Vobservable tau l)  (Vobservable tau l1)).
      { rewrite <- cc_approx_val_eq.
        eapply IHv0 with (v2 := Vobservable tau l0); eauto.
        - rewrite cc_approx_val_eq. now eauto.
        - intros k'. specialize (Hpre k'). rewrite preord_val_eq in Hpre.
          inv Hpre. now rewrite preord_val_eq. }
      now eauto.
Qed.