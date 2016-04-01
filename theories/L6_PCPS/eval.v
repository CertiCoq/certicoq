Require Import cps cps_util identifiers env.
Require Import BinNat Relations MSets MSetRBT List Omega.
Import ListNotations.

Section EVAL.
  
  Parameter pr : prims.
  
  (** Big step evaluation relation with step counting *)
  (* This is almost a copy of the big step relation in cps.v.
   * There are two differences:
   * a. This definition counts the number of β-reductions which is 
   *    needed to define the relations (see below). 
   * b. This definition can return arbitrary values as opposed to 
   *    only observable values which is the case with the old definition 
   * Eventually, we should move everything related to evaluation in this file. *)
  Inductive bstep_e : env -> exp -> val -> nat -> Prop :=
  | BStep_app_obs :
      forall (rho : env) (t : type) (ys : list var)
             (vs : list val) (f : var),
        M.get f rho = Some (Vobvs t) ->
        getlist ys rho = Some vs ->
        bstep_e rho (Eapp f ys) (Vobservable t vs) 0
  | BStep_constr :
      forall (x : var) (t : type) (n : tag) (ys :list var) (e : exp)
             (rho rho' : env) (vs : list val) (v : val) (c : nat),
        getlist ys rho = Some vs ->
        M.set x (Vconstr t n vs) rho = rho' ->
        bstep_e rho' e v c ->
        bstep_e rho (Econstr x t n ys e) v c
  | BStep_proj :
      forall (t' : type) (n' : tag) (vs : list val) (v : val)
             (rho : env) (x : var) (t : type) (n : N) (y : var)
             (e : exp) (ov : val) (c : nat),
        M.get y rho = Some (Vconstr t' n' vs) ->
        nthN vs n = Some v ->
        bstep_e (M.set x v rho) e ov c ->
        bstep_e rho (Eproj x t n y e) ov c 
  | BStep_case :
      forall (y : var) (v : val) (k : var) (t : tag) (cl : list (tag * var))
             (vl : list val) (tau : type) (rho : env) (c : nat),
        M.get y rho = Some (Vconstr tau t vl) ->
        findtag cl t = Some k ->
        bstep_e rho (Eapp k (y :: nil)) v c ->
        bstep_e rho (Ecase y cl) v c
  | BStep_app_fun :
      forall (rho' : env) (fl : fundefs) (f' : var) (vs : list val) 
             (xs : list var) (e : exp) (rho'' rho : env) (f : var)
             (t : type) (ys : list var) (v : val) (c : nat),
        M.get f rho = Some (Vfun rho' fl f') ->
        getlist ys rho = Some vs ->
        find_def f' fl = Some (t,xs,e) ->
        setlist xs vs (def_funs fl fl rho' rho') = Some rho'' ->
        bstep_e rho'' e v c ->
        bstep_e rho (Eapp f ys) v (c+1)
  | BStep_fun :
      forall (rho : env) (fl : fundefs) (e : exp) (v : val) (c : nat),
        bstep_e (def_funs fl fl rho rho) e v c ->
        bstep_e rho (Efun fl e) v c
  | BStep_prim :
      forall (vs : list val) (rho' rho : env) (x : var) (t : type) (f : prim) 
             (f' : list val -> option val) (ys : list var) (e : exp)
             (v v' : val) (c : nat),
        getlist ys rho = Some vs ->
        M.get f pr = Some f' ->
        f' vs = Some v ->
        M.set x v rho = rho' ->
        bstep_e rho' e v' c ->
        bstep_e rho (Eprim x t f ys e) v' c.

  Ltac subst_exp :=
    match goal with
      | [H1 : ?e = ?e1, H2 : ?e = ?e2 |- _ ] =>
        rewrite H1 in H2; inv H2
    end.
  
  Lemma bstep_e_deterministic e rho v1 v2 c1 c2 :
    bstep_e rho e v1 c1 ->
    bstep_e rho e v2 c2 ->
    v1 = v2 /\ c1 = c2.
  Proof.
    intros Heval1 Heval2.
    revert c2 Heval2; induction Heval1; intros c2 Heval2;
    inv Heval2; repeat subst_exp; eauto.
    split; f_equal; eapply IHHeval1; eauto. 
  Qed.

  (** Induction principle for values. TODO: Move this to cps.v *)
  Lemma val_ind :
    forall P : val -> Prop,
      (forall (tau : type) (t : tag), P (Vconstr tau t nil)) ->
      (forall (tau : type) (t : tag) (v : val) (l : list val),
         P v -> P (Vconstr tau t l) -> P (Vconstr tau t (v :: l))) ->
      (forall (t : M.t val) (f0 : fundefs) (v : var), P (Vfun t f0 v)) ->
      (forall z : Z, P (Vint z)) ->
      (forall t : type, P (Vother t)) ->
      (forall t : type, P (Vobvs t)) ->
      (forall (tau : type), P (Vobservable tau nil)) ->
      (forall (tau : type) (v : val) (l : list val),
         P v -> P (Vobservable tau l) -> P (Vobservable tau (v :: l))) ->
      forall v : val, P v.
  Proof.
    intros P H1 H2 H3 H4 H5 H6 H7 H8.
    fix 1.
    destruct v; try (now clear val_ind; eauto).
    - induction l as [ | x xs IHxs].
      eapply H1. eapply H2. apply val_ind. eauto.
    - induction l as [ | x xs IHxs].
      eapply H7. eapply H8. apply val_ind. eauto.
  Qed.
 

  (** step-indexed preorder on cps terms *)
  (* Expression relation : 
   * ---------------------
   *  (e1, ρ1) ~_k (e2, ρ2) iff 
   *    forall c1 <= k, 
   *      e1, ρ1 ->^c1 v1 -> 
   *      e2, ρ2 ->^c2 v2 /\ c2 <= c1 /\ v1 ~_(k-c1) v2 
   * Note that restrict the number of applications in the evaluation
   * of the second argument so that the relation is transitive.
   * Value relation :
   * ----------------
   * Integers: (n1 ~_k n2) iff n1 = n2
   * Constructors: [v_1, .., v_n] ~_k [v_1', .., v_n'] iff 
   *                 v_1 ~_k v_1' /\ ... /\ v_n ~_k v_n'
   * Closures: (\f1 x1. e1, ρ1) ~_k (\f2 x2. e2, ρ2) iff 
   *              \forall v1 v2 i < k, v1 ~_j v2 => 
   *                (e1, ρ1[x1 -> v1, f1 -> (\f1 x1. e1, ρ1)]) ~_j 
   *                (e2, ρ2[x2 -> v2, f2 -> (\f2 x2. e2, ρ2)])
   *)
  Fixpoint preord_val (k : nat) (v1 v2 : val) {struct k} : Prop :=
    let preord_exp (k : nat) (p1 p2 : exp * env) : Prop :=
        let '(e1, rho1) := p1 in
        let '(e2, rho2) := p2 in
        forall v1 c1,
           c1 <= k -> bstep_e rho1 e1 v1 c1 ->
           exists v2 c2, bstep_e rho2 e2 v2 c2 /\ c2 <= c1 /\
                         preord_val (k - c1) v1 v2
    in
    let fix Forall2 R vs1 vs2 :=
        match vs1, vs2 with
          | [], [] => True
          | v1 :: vs1, v2 :: vs2 =>
            R v1 v2 /\ Forall2 R vs1 vs2
          | _, _ => False
        end
    in
    let fix preord_val_aux1 (v1 v2 : val) {struct v1} : Prop :=
        let fix Forall2_aux vs1 vs2 :=
               match vs1, vs2 with
                 | [], [] => True
                 | v1 :: vs1, v2 :: vs2 =>
                   preord_val_aux1 v1 v2 /\ Forall2_aux vs1 vs2
                 | _, _ => False
               end
           in
           match v1, v2 with
             | Vfun rho1 defs1 f1, Vfun rho2 defs2 f2 =>
               forall (vs1 vs2 : list val) (j : nat) (t1 : type) 
                      (xs1 : list var) (e1 : exp) (rho1' : env),
                 length vs1 = length vs2 ->
                 find_def f1 defs1 = Some (t1, xs1, e1) ->
                 Some rho1' = setlist xs1 vs1 (def_funs defs1 defs1 rho1 rho1) ->
                 exists (t2 : type) (xs2 : list var) (e2 : exp) (rho2' : env),
                   find_def f2 defs2 = Some (t2, xs2, e2) /\
                   Some rho2' = setlist xs2 vs2 (def_funs defs2 defs2 rho2 rho2) /\
                   match k with
                     | 0 => True
                     | S k =>
                       let R := preord_val (k - (k-j)) in
                       j < S k ->
                       Forall2 R vs1 vs2 ->
                       preord_exp (k - (k-j)) (e1, rho1') (e2, rho2')
                   end
           | Vconstr tau1 t1 vs1, Vconstr tau2 t2 vs2 =>
             t1 = t2 /\ Forall2_aux vs1 vs2
           | Vint n1, Vint n2 => n1 = n2
           | Vother t1, Vother t2 => True
           | Vobvs t1, Vobvs t2 => True
           | Vobservable t1 vs1, Vobservable t2 vs2 =>
             Forall2_aux vs1 vs2
           | _, _ => False
           end
    in preord_val_aux1 v1 v2.
           
  Definition preord_exp (k : nat) (p1 p2 : exp * env) : Prop :=
    let '(e1, rho1) := p1 in
    let '(e2, rho2) := p2 in
    forall v1 c1,
      c1 <= k -> bstep_e rho1 e1 v1 c1 ->
      exists v2 c2, bstep_e rho2 e2 v2 c2 /\ c2 <= c1 /\
                    preord_val (k - c1) v1 v2.
  
  Definition preord_val' (k : nat) (v1 v2 : val) : Prop :=
    match v1, v2 with
      | Vfun rho1 defs1 f1, Vfun rho2 defs2 f2 =>
        forall (vs1 vs2 : list val) j (t1 : type) (xs1 : list var)
               (e1 : exp) (rho1' : env),
          length vs1 = length vs2 -> 
          find_def f1 defs1 = Some (t1, xs1, e1) ->
          Some rho1' = setlist xs1 vs1 (def_funs defs1 defs1 rho1 rho1) ->
          exists (t2 : type) (xs2 : list var) (e2 : exp) (rho2' : env),
            find_def f2 defs2 = Some (t2, xs2, e2) /\
            Some rho2' = setlist xs2 vs2 (def_funs defs2 defs2 rho2 rho2) /\
            (j < k -> Forall2 (preord_val j) vs1 vs2 ->
             preord_exp j (e1, rho1') (e2, rho2'))
      | Vconstr tau1 t1 vs1, Vconstr tau2 t2 vs2 =>
        t1 = t2 /\ Forall2 (preord_val k) vs1 vs2
      | Vint n1, Vint n2 => n1 = n2
      | Vother t1, Vother t2 => True
      | Vobvs t1, Vobvs t2 => True
      | Vobservable t1 vs1, Vobservable t2 vs2 =>
        Forall2 (preord_val k) vs1 vs2
      | _, _ => False
    end.

  Lemma preord_val_eq (k : nat) (v1 v2 : val) :
    preord_val k v1 v2 <-> preord_val' k v1 v2.
  Proof.
    (* TODO : refactor this proof *)
    destruct k as [ | k ]; destruct v1; destruct v2;
    eauto; try (split; intros H; (now simpl in H; inv H)).
    - split.
      * revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        try (now intros [H1 H2]; split; eauto; inv H2).
        intros H; split; destruct H as [H1 [H2 H3]]; eauto. constructor. eauto.
        eapply IHxs. simpl. eauto.
      * revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        try (now intros [H1 H2]; split; eauto; inv H2).
        intros H; split; inv H; eauto. inv H1. split; eauto.
        eapply IHxs. simpl. eauto.
    - split; intros Hpre; simpl; intros; 
      edestruct (Hpre vs1 vs2 0) as [t2 [xs2 [e2 [rho' [H1' [H2' H3']]]]]];
      eauto; do 4 eexists; split; eauto; split; eauto; intros Hc; exfalso; omega.
    - revert l0; induction l as [| x xs IHxs];
      intros l2; destruct l2 as [| y ys ];
      split; intros H; try (now simpl in H; inv H). constructor. 
      destruct H as [H1 H2]; eauto.
      constructor; eauto. eapply IHxs. eauto.
      inv H. split; eauto. eapply IHxs; eauto. 
    - split.
      * revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        try (now intros [H1 H2]; split; eauto; inv H2).
        intros H; split; destruct H as [H1 [H2 H3]]; eauto. constructor. eauto.
        eapply IHxs. simpl. eauto.
      * revert l0; induction l as [| x xs IHxs];
        intros l2; destruct l2 as [| y ys ];
        try (now intros [H1 H2]; split; eauto; inv H2).
        intros H; split; inv H; eauto. inv H1. split; eauto.
        eapply IHxs. simpl. eauto.
    - split; intros Hpre; simpl; intros. 
      + edestruct Hpre as [t2 [xs2 [e2 [rho' [H1' [H2' H3']]]]]]; eauto.
        do 4 eexists. split; eauto. split; eauto. intros Hleq Hf v1 c1 Hleq' Hstep. 
        assert (Heq : k - (k - j) = j) by omega. rewrite Heq in H3'.
        simpl in H3'. eapply H3'; eauto. clear H0 H1 H1' H2' H3' H Hleq'.
        induction Hf; eauto.
      + edestruct Hpre as [t2 [xs2 [e2 [rho' [H1' [H2' H3']]]]]]; eauto.
        do 4 eexists. split; eauto. split; eauto.
        intros Hleq Hf v1 Hstep.
        assert (Heq : k - (k - j) = j) by omega. rewrite Heq in *.
        eapply H3'; eauto. clear H0 H1 H2' H3' H.
        revert vs2 Hf; induction vs1 as [| v1' vs1 IHvs1];
        intros [| v2 vs2 ]; intros Hall; try now inv Hall; eauto.
        constructor. destruct Hall. constructor; eauto.
    - simpl. 
      revert l0; induction l as [| x xs IHxs];
      intros l2; destruct l2 as [| y ys ];
      split; intros H; try (now simpl in H; inv H).
      destruct H as [H1 H2]; eauto.
      constructor; eauto. eapply IHxs. eauto.
      inv H. split; eauto. eapply IHxs; eauto.
  Qed.

  Opaque preord_val.
  
  (** Environment relation *)
  (* ρ1 ~_k ρ2 iff ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' 
   *)
  Definition preord_env (k : nat) (rho1 rho2 : env) : Prop :=
    forall (x : var) (v1 : val),
      M.get x rho1 = Some v1 ->
      exists v2 : val, M.get x rho2 = Some v2 /\ preord_val k v1 v2.

  Open Scope ctx_scope.

  (** Context relation. *)
  Definition preord_ctx (k : nat) (rho1 rho2 : env)
             (p1 p2 : exp_ctx * env) :=
    let '(c1, rho1') := p1 in
    let '(c2, rho2') := p2 in
    forall e1 e2, preord_exp k (e1, rho1) (e2, rho2) ->
                  preord_exp k (c1 |[ e1 ]|, rho1')
                             (c2 |[ e2 ]|, rho2').

  Definition preord_var_env (k : nat) (rho1 rho2 : env) (x y : var) : Prop :=
    forall v1, 
      M.get x rho1 = Some v1 -> 
      exists v2, M.get y rho2 = Some v2 /\ preord_val k v1 v2.

  Lemma Forall2_length {A} (R : A -> A -> Prop) (l1 l2 : list A) :
    Forall2 R l1 l2 -> length l1 = length l2.
  Proof.
    revert l2. induction l1 as [| x xs IHxs ]; intros l2 H.
    - inv H; eauto.
    - inv H. simpl. f_equal. eauto.
  Qed.

  Lemma Forall2_monotonic {A} (R R' : A -> A -> Prop) (l1 l2 : list A) :
    (forall x1 x2, R x1 x2 -> R' x1 x2) ->
    Forall2 R l1 l2 ->
    Forall2 R' l1 l2.
  Proof.
    intros H. revert l2.
    induction l1 as [| x xs IHxs ]; intros l2 Hall.
    - inv Hall; eauto. 
    - destruct l2; inv Hall. constructor; eauto.
  Qed.

  Lemma Forall2_refl {A} (R : A -> A -> Prop) (l : list A) :
    Reflexive R ->
    Forall2 R l l.
  Proof.
    intros H. induction l as [| x l IHl]; eauto.
  Qed.
  
  Lemma Forall2_trans {A} (R : A -> A -> Prop) (l1 l2 l3 : list A) :
    Transitive R ->
    Forall2 R l1 l2 ->
    Forall2 R l2 l3 ->
    Forall2 R l1 l3.
  Proof.
    intros Htrans.
    revert l2 l3. induction l1 as [| x l IHl ]; intros l2 l3 H1 H2.
    - inv H1. inv H2. constructor.
    - inv H1. inv H2. constructor; eauto.
  Qed.      

  Lemma Forall2_trivial {A} (R : A -> A -> Prop) (l1 l2 : list A) :
    (forall x y, R x y) ->
    (length l1 = length l2) -> 
    Forall2 R l1 l2.
  Proof.
    intros H.
    revert l2; induction l1 as [| x l IHl]; intros l2 Hlen;
    destruct l2; try discriminate; eauto.
  Qed.


  Lemma Forall2_nthN {A} (R : A -> A -> Prop) (l1 l2 : list A)
        (n : N) (v1 : A):
      Forall2 R l1 l2 ->
      nthN l1 n = Some v1 ->
      exists v2,
        nthN l2 n = Some v2 /\
        R v1 v2.
  Proof.
    revert l2 n.
    induction l1 as [| x xs IHxs ]; intros l2 n H Hnth.
    - inv H. discriminate.
    - inv H. destruct n as [| n].
      + simpl in Hnth. inv Hnth.
        eexists. split; simpl; eauto.
      + edestruct IHxs as [v2 [Hnth2 Hr]]; eauto.
  Qed.

  Lemma nthN_length {A} (l1 l2 : list A) (n : N) (v1 : A) :
    length l1 = length l2 ->
    nthN l1 n = Some v1 ->
    exists v2,
      nthN l2 n = Some v2.
  Proof.
    revert l2 n.
    induction l1 as [| x xs IHxs ]; intros l2 n H Hnth.
    - inv H. discriminate.
    - inv H. destruct n as [| n]; destruct l2; try discriminate.
      + simpl in Hnth. inv Hnth.
        eexists. split; simpl; eauto.
      + inv H1. edestruct IHxs as [v2 Hnth2]; eauto.
  Qed.
  
  Lemma preord_env_getlist_l (rho1 rho2 : env) (k : nat)
        (xs : list var) (vs1 : list val) :
    preord_env k rho1 rho2 ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist xs rho2 = Some vs2 /\ Forall2 (preord_val k) vs1 vs2.
  Proof.
    intros Henv. revert vs1.
    induction xs as [| x xs IHxs]; intros vs1 Hget.
    - inv Hget. eexists. split; simpl; eauto.
    - simpl in Hget. destruct (M.get x rho1) eqn:Heq1; try discriminate.
      destruct (getlist xs rho1) eqn:Heq2; try discriminate. inv Hget.
      destruct (IHxs l eq_refl) as  [vs2 [Hget HAll]].
      eapply Henv in Heq1. destruct Heq1 as [v2 [H1 H2]].
      eexists. split; simpl; eauto. rewrite H1. rewrite Hget. eauto.
  Qed.

  Lemma preord_env_extend (rho1 rho2 : env) (k : nat)
        (x : var) (v1 v2 : val) :
    preord_env k rho1 rho2 ->
    preord_val k v1 v2 ->
    preord_env k (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros H1 Hval. intros y v1' Hget1.
    rewrite M.gsspec in Hget1. destruct (Coqlib.peq y x); subst.
    inv Hget1. eexists; split; eauto. now rewrite M.gss.
    edestruct H1; eauto. eexists. now rewrite M.gso.
  Qed.

  Lemma preord_env_refl k :
    Reflexive (preord_val k) ->
    Reflexive (preord_env k).
  Proof.
    intros H r. intros; eexists; eauto.
  Qed.

  Lemma setlist_length (rho rho' rho1 : env)
        (xs : list var) (vs1 vs2 : list val) :
    length vs1 = length vs2 -> 
    setlist xs vs1 rho = Some rho1 ->
    exists rho2, setlist xs vs2 rho' = Some rho2.
  Proof.
    revert vs1 vs2 rho1.
    induction xs as [| x xs IHxs ]; intros vs1 vs2 rho1 Hlen Hset.
    - inv Hset. destruct vs1; try discriminate. inv H0.
      destruct vs2; try discriminate. eexists; simpl; eauto. 
    - destruct vs1; try discriminate. destruct vs2; try discriminate.
      inv Hlen. simpl in Hset. 
      destruct (setlist xs vs1 rho) eqn:Heq2; try discriminate.
      edestruct (IHxs _ _ _ H0 Heq2) as  [vs2' Hset2].
      eexists. simpl; rewrite Hset2; eauto.
  Qed.

  Lemma preord_env_setlist_l (rho1 rho2 rho1' rho2' : env) (k : nat)
        (xs : list var) (vs1 vs2 : list val) :
    preord_env k rho1 rho2 ->
    Forall2 (preord_val k) vs1 vs2 ->
    setlist xs vs1 rho1 = Some rho1' ->
    setlist xs vs2 rho2 = Some rho2' ->
    preord_env k rho1' rho2'.
  Proof.
    revert vs1 vs2 rho1 rho2 rho1' rho2'.
    induction xs as [| x xs IHxs ];
      intros vs1 vs2 rho1 rho2 rho1' rho2' Hr Hall Hset1 Hset2.
    - inv Hall; try discriminate. simpl in *.
      inv Hset1; inv Hset2. eauto.
    - destruct vs1; try discriminate.
      inv Hall; try discriminate. simpl in Hset1, Hset2.
      destruct (setlist xs vs1 rho1) eqn:Heq2; try discriminate.
      destruct (setlist xs l' rho2) eqn:Heq3; try discriminate. 
      inv Hset1; inv Hset2. eapply preord_env_extend; eauto.
  Qed.
  
  Lemma preord_val_monotonic (k : nat) :
    (forall v1 v2 j,
       preord_val k v1 v2 -> j <= k -> preord_val j v1 v2).
  Proof.
    induction k using lt_wf_rec1; destruct k as [| k ];
    try (now intros; replace j with 0 in * by omega; eauto).
    intros v1 v2 h Hpre Hleq. try rewrite preord_val_eq in *.
    revert v2 Hpre; induction v1 using val_ind; intros v2 Hpre;
    destruct v2; try (simpl; contradiction); eauto.
    - destruct l; try now inv Hpre.
    - inv Hpre. inv H1.
      split; auto. constructor; eauto; rewrite preord_val_eq in *.
      eapply IHv1; eauto.
      destruct (IHv0 ((Vconstr tau t1 l'))) as [Heq Hpre']; eauto.
      simpl. split; eauto.
    - intros vs1 vs2 j t1 xs e1 rho1' Hlen Hf Heq.
      edestruct Hpre as [t2 [xs2 [e2 [rho2' [H1 [H2 H3]]]]]]; eauto.
      do 4 eexists; split; eauto. split; eauto. intros Hleq' Hall. 
      eapply H3; eauto. omega. 
    - destruct l; try now inv Hpre. constructor.
    - inv Hpre. constructor; rewrite preord_val_eq in *. eapply IHv1; eauto.
        eapply (IHv0 (Vobservable tau l')) in H4. eauto.
  Qed.

  Lemma preord_exp_monotonic (k : nat) :
    (forall rho1 e1 rho2 e2 j,
       preord_exp k (rho1, e1) (rho2, e2) ->
       j <= k -> preord_exp j (rho1, e1) (rho2, e2)).
  Proof.
    intros rho1 e1 rho2 e2 j Hpre Hleq v1 c1 Hlt Hstep.
    edestruct (Hpre v1 c1) as [v2 [c2 [H1 [H3 H2]]]]; eauto. omega.
    do 2 eexists; split; eauto. split; eauto.
     eapply preord_val_monotonic. eapply H2. omega.
  Qed.

  Lemma preord_env_monotonic k j rho1 rho2 :
    j <= k -> preord_env k rho1 rho2 -> preord_env j rho1 rho2.
  Proof.
    intros Hleq H; intros x v Hget;
    eapply H in Hget; destruct Hget as [v2 [Hget1 Hval]];
    eexists; split; eauto; eapply preord_val_monotonic; eauto.
  Qed.

  Lemma preord_var_env_getlist (rho1 rho2 : env) (k : nat)
        (xs ys : list var) (vs1 : list val) :
    Forall2 (preord_var_env k rho1 rho2) xs ys ->
    getlist xs rho1 = Some vs1 ->
    exists vs2,
      getlist ys rho2 = Some vs2 /\ Forall2 (preord_val k) vs1 vs2.
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

  Parameter Prim_axiom :
    forall f f' v1,
      M.get f pr = Some f' ->
      forall k vs1 vs2,
        Forall2 (preord_val k) vs1 vs2 ->
        f' vs1 = Some v1 ->
        exists v2,
          f' vs2 = Some v2 /\                      
          preord_val k v1 v2.
  
  Lemma preord_exp_refl_pre (k : nat) :
    Reflexive (preord_val k) ->
    forall rho rho' e,
      preord_env k rho rho' ->
      preord_exp k (e, rho) (e, rho').
  Proof.
    induction k as [ k IH ] using lt_wf_rec1.
    intros Hrefl rho rho' e Henv v c Hleq Hstep.
    revert rho' Henv. induction Hstep; intros rho2 Henv.
    - edestruct preord_env_getlist_l as [vs2 [Hget' Hpre']]; eauto.
      edestruct Henv as [v2 [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v2; try (now simpl in Hpre; contradiction).
      repeat eexists. constructor; eauto. eauto.
      rewrite preord_val_eq. rewrite <- minus_n_O. eauto.
    - edestruct preord_env_getlist_l as [vs2 [Hget' Hpre']]; eauto.
      inv H0. edestruct IHHstep as [v2 [c2 [Hstep2 [Hleq2 Hpre2]]]]; eauto.
      eapply preord_env_extend with (v2 :=  Vconstr t n vs2); eauto.
      rewrite preord_val_eq; simpl; eauto.
      repeat eexists; eauto.
      econstructor. eauto. reflexivity. eauto.
    - edestruct Henv as [v2' [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v2'; try (now simpl in Hpre; contradiction).
      destruct Hpre as [? Hpre]; subst.
      edestruct (Forall2_nthN _ _ _ _ _ Hpre H0) as [v' [Hnth Hpre']].
      edestruct IHHstep as [v2 [c2 [Hstep2 [Hleq2 Hpre2]]]]; eauto.
      eapply preord_env_extend; eauto. 
      repeat eexists; eauto.
      econstructor; eauto.
    - inv Hstep.
      + simpl in H7. destruct (M.get y rho) eqn:Hget; try discriminate.
        inv H7. inv H.
        edestruct (Henv k0) as [v2 [Hget2 Hpre]]; eauto.
        edestruct (Henv y) as [v2' [Hget2' Hpre']]; eauto.
        rewrite preord_val_eq in Hpre, Hpre'.
        destruct v2; try (now simpl in Hpre; contradiction).
        destruct v2'; try (now simpl in Hpre'; contradiction).
        destruct Hpre' as [? Hpre']; subst.
        repeat eexists. econstructor; eauto. constructor; eauto.
        simpl. rewrite Hget2'. eauto. eauto.
        rewrite preord_val_eq. rewrite <- minus_n_O; simpl; eauto.
        constructor. rewrite preord_val_eq. simpl; eauto. constructor.
      + edestruct Henv as [f2 [Hget2 Hpref]]; eauto.
        rewrite preord_val_eq in Hpref.
        destruct f2; try (now simpl in Hpref; contradiction).
        edestruct preord_env_getlist_l as [vs2 [Hget' Hpre']]; eauto.
        edestruct (Hpref vs vs2 (k-1)) as [t2 [xs2 [e2 [rho2' [Hf [Hset H']]]]]]; eauto.
        eapply Forall2_length; eauto.
        edestruct H' with (c1 := c0) as [v2 [c2 [Hstep' [Hc2 Hpre'']]]];
        eauto; try omega.
        eapply Forall2_monotonic. intros.
        eapply (preord_val_monotonic k). eauto. omega. eauto.
        simpl in Hget'. destruct (M.get y rho2) eqn:Hgety; try discriminate.
        inv Hget'. simpl in H4.
        destruct (M.get y rho) eqn:Hgety'; try discriminate. inv H4. inv H.
        inv Hpre'. rewrite preord_val_eq in H4.
        destruct v1; try (now simpl in H4; contradiction).
        destruct H4 as [? Hpre]; subst.
        repeat eexists. econstructor; eauto. econstructor 5; eauto.
        simpl. rewrite Hgety; eauto. omega.
        replace (k - (c0 + 1)) with (k - 1 - c0) by omega. eauto.
    - edestruct Henv as [v2' [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v2'; try (now simpl in Hpre; contradiction).
      edestruct preord_env_getlist_l as [vs2 [Hget' Hpre']]; eauto.
      edestruct (Hpre vs vs2 (k-1)) as [t2 [xs2 [e2 [rho2' [Hf [Hset H']]]]]]; eauto.
      eapply Forall2_length; eauto.
      edestruct H' with (c1 := c) as [v2 [c2 [Hstep' [Hc2 Hpre'']]]];
        eauto; try omega.
      eapply Forall2_monotonic. intros.
      eapply (preord_val_monotonic k). eauto. omega. eauto.
      repeat eexists. econstructor 5; eauto. omega.
      replace (k - (c + 1)) with (k - 1 - c) by omega. eauto.
    - edestruct IHHstep with (rho' := def_funs fl fl rho2 rho2)
        as [v2 [c2 [Hstep' [Hleq' Hpre']]]]; eauto.
      + clear IHHstep Hstep e v c Hleq. generalize fl at 1 3.
        revert fl rho rho2 Henv Hrefl.
        induction k as [ k IH' ] using lt_wf_rec1. intros fl rho rho2 Henv Hrefl.
        induction fl; intros defs; simpl; eauto. 
        eapply preord_env_extend. eapply IHfl.
        rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
        edestruct setlist_length as [rho2' Hs']; eauto.
        exists t1. exists xs1. exists e1. exists rho2'. split; eauto.
        split. eauto. intros Hleq Hpre. eapply IH; eauto.
        intros v'. eapply (preord_val_monotonic k). eapply Hrefl. omega.
        eapply preord_env_setlist_l; eauto.
        eapply IH'; try omega; eauto.
        intros. eapply IH; eauto. omega.
        eapply preord_env_monotonic; [| eauto]. omega.
        intros v'. eapply (preord_val_monotonic k). eapply Hrefl. omega.
      + repeat eexists; eauto. constructor; eauto.
    - edestruct preord_env_getlist_l as [vs2 [Hget' Hpre']]; eauto.
      edestruct Prim_axiom as [v2 [Heq Hprev2]]; eauto.
      edestruct (IHHstep Hleq (M.set x v2 rho2))
        as [v2' [c2 [Hstepv2' [ Hleq2 Hprev2']]]]; eauto.
      rewrite <- H2. eapply preord_env_extend; eauto. 
      repeat eexists; eauto. econstructor; eauto.
  Qed.
    
  Lemma preord_val_refl (k : nat) :
    Reflexive (preord_val k).
  Proof.
    induction k using lt_wf_rec1.
    destruct k as [| k]; unfold Reflexive; intros x; rewrite preord_val_eq;
    induction x using val_ind; simpl; eauto;
    try (now (try split; eauto); econstructor; eauto; rewrite preord_val_eq; eauto).
    - split; eauto. constructor; eauto. rewrite preord_val_eq; eauto.
      destruct IHx0. eauto.
    - intros.
      edestruct (setlist_length (def_funs f0 f0 t t) (def_funs f0 f0 t t))
        as [rho2' Hset']; eauto.
      do 4 eexists; split; eauto. split; eauto. intros Hc.
      exfalso. omega.
    - split; eauto. constructor; eauto. rewrite preord_val_eq; eauto.
        destruct IHx0. eauto.
    - intros.
      edestruct (setlist_length (def_funs f0 f0 t t) (def_funs f0 f0 t t))
        as [rho2' Hset']; eauto.
      do 4 eexists; eauto. split; eauto. split; eauto.
      intros Hleq Hall v1 c Hleq' Hstep. 
      eapply preord_exp_refl_pre; eauto.
      eapply preord_env_setlist_l; eauto.
      eapply preord_env_refl; eauto.
  Qed.

  Corollary preord_exp_refl (k : nat) (rho rho' : env) (e : exp) :
      preord_env k rho rho' ->
      preord_exp k (e, rho) (e, rho').
  Proof.
    intros. eapply preord_exp_refl_pre; eauto.
    eapply preord_val_refl.
  Qed.
    
  Lemma preord_exp_trans_pre (k : nat) :
    (forall m, m <= k -> Transitive (preord_val m)) ->
    forall rho1 rho2 rho3 e1 e2 e3,
      preord_exp k (e1, rho1) (e2, rho2) ->
      preord_exp k (e2, rho2) (e3, rho3) ->
      preord_exp k (e1, rho1) (e3, rho3).
  Proof.
    intros Htrans rho1 rho2 rho3 e1 e2 e3 H1 H2 v1 c1 Hleq1 Hstep1.
    edestruct H1 as [v2 [c2 [Hstep2 [Hleq2 Hpre2]]]]; eauto.
    edestruct H2 as [v3 [c3 [Hstep3 [Hleq3 Hpre3]]]]; [| eauto |]. omega.
    repeat eexists; eauto. omega.
    eapply Htrans; eauto. omega.
    eapply preord_val_monotonic; eauto. omega.
  Qed.

  Lemma preord_val_trans (k : nat) :
    Transitive (preord_val k).
  Proof.
    induction k using lt_wf_rec1.
    intros x; induction x using val_ind; simpl; eauto;
    intros v1 v2; rewrite !preord_val_eq;
    try (now intros H1 H2; destruct v1; destruct v2;
         try (now simpl in *; contradiction); inv H1; inv H2; simpl; eauto).
    - intros H1 H2. destruct v1; destruct v2; try (now simpl in *; contradiction).
      destruct H1 as [H1 H1']. destruct H2 as [H2 H2']. subst.
      destruct l; destruct l0; try inv H1'; try inv H2'.
      split; eauto.
    - intros H1 H2. destruct v1; destruct v2; try (now simpl in *; contradiction).
      destruct H1 as [H1 H1']. destruct H2 as [H2 H2']. subst.
      destruct l0; try inv H1'; try inv H2'. split; eauto. constructor; eauto.
      specialize (IHx0 (Vconstr tau t3 l0) (Vconstr tau t3 l')).
      rewrite !preord_val_eq in IHx0. eapply IHx0; split; eauto.
    - intros H1 H2. destruct v1; destruct v2; try (now simpl in *; contradiction).
      intros vs1 vs3 j t1' xs1 e1 rho1' Hlen Hf Hs.
      edestruct (H1 vs1 vs1) as [t2' [xs2 [e2 [rho2 [Hf2 [Hs2 Hpre2]]]]]]; eauto.
      edestruct H2 as [t3' [xs3 [e3 [rho3 [Hf3 [Hs3 Hpre3]]]]]]; eauto.
      do 4 eexists; split; eauto. split; eauto. intros Hlt Hall.
      eapply preord_exp_trans_pre. intros. eapply H. omega.
      eapply Hpre2. omega. eapply Forall2_refl. apply preord_val_refl.
      eapply Hpre3; eauto.
    - intros H1 H2. destruct v1; destruct v2; try (now simpl in *; contradiction).
      destruct l0; try inv H1; try inv H2. simpl. constructor; eauto.
      specialize (IHx0 (Vobservable tau l0) (Vobservable tau l')).
      rewrite !preord_val_eq in IHx0. eapply IHx0; eauto.
  Qed.

  Inductive Forall2_fundefs
            (R : var -> type -> list var -> exp ->
                 var -> type -> list var -> exp -> Prop)
  : fundefs -> fundefs -> Prop :=
  | Forall2_Fcons :
      forall f t xs e defs f' t' xs' e' defs',
        R f t xs e f' t' xs' e' ->
        Forall2_fundefs R defs defs' ->
        Forall2_fundefs R (Fcons f t xs e defs) (Fcons f' t' xs' e' defs')
  | Forall2_Fnil : Forall2_fundefs R Fnil Fnil.
  

  Lemma find_def_spec f f' xs t e defs t' ys e' :
    find_def f ( Fcons f' t xs e defs) = Some (t', ys, e') ->
    (f = f' /\ t = t' /\ xs = ys /\ e = e') \/
    (find_def f defs = Some (t', ys, e') /\ f <> f'). 
  Proof.
    intros Hdef. simpl in Hdef. destruct (M.elt_eq f f'); subst; eauto.
    inv Hdef. eauto.
  Qed.

  Lemma find_def_eq f f' xs t e defs t' ys e' :
    find_def f (Fcons f' t xs e defs) = Some (t', ys, e') ->
    f = f' ->
    (t = t' /\ xs = ys /\ e = e'). 
  Proof.
    intros Hdef Heq. simpl in Hdef. destruct (M.elt_eq f f'); subst; eauto.
    inv Hdef. eauto. congruence.
  Qed.

  Lemma find_def_neq f f' xs t e defs t' ys e' :
    find_def f (Fcons f' t xs e defs) = Some (t', ys, e') ->
    f <> f' ->
    find_def f defs = Some (t', ys, e'). 
  Proof.
    intros Hdef Heq. simpl in Hdef. destruct (M.elt_eq f f'); subst; eauto.
    congruence.
  Qed.
      
End EVAL.

