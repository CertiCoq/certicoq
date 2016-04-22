Require Import cps cps_util identifiers env ctx.
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
      forall (y : var) (v : val) (e : exp) (t : tag) (cl : list (tag * exp))
             (vl : list val) (tau : type) (rho : env) (c : nat),
        M.get y rho = Some (Vconstr tau t vl) ->
        findtag cl t = Some e ->
        bstep_e rho e v c ->
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

  Open Scope env_scope.

  Lemma env_subset_getlist_2 rho1 rho2 ys:
    env_subset rho1 rho2 ->
    (forall x, In x ys -> M.get x rho2 = M.get x rho1) ->
    getlist ys rho2 = getlist ys rho1.
  Proof.
    intros Hsub. induction ys as [| y ys IHys]; eauto; intros Hget.
    simpl. rewrite Hget, IHys; try now constructor.
    intros x HIn. apply Hget. now constructor 2.
  Qed.

  Lemma getlist_In (rho : env) ys x vs :
    getlist ys rho = Some vs ->
    In x ys ->
    exists v, M.get x rho = Some v.
  Proof.
    revert x vs. induction ys; intros x vs Hget H. inv H.
    inv H; simpl in Hget.
    - destruct (M.get x rho) eqn:Heq; try discriminate; eauto.
    - destruct (M.get a rho) eqn:Heq; try discriminate; eauto.
      destruct (getlist ys rho) eqn:Heq'; try discriminate; eauto.
  Qed.

  Lemma findtag_In {A} (P : list (tag * A)) c e :
    findtag P c = Some e -> List.In (c, e) P.
  Proof.
    revert e. induction P as [| [c' e'] P IHp]; intros x H; try now inv H.
    simpl in H. inv H.
    destruct (M.elt_eq c' c); inv H1; try now constructor.
    constructor 2. apply IHp; eauto.
  Qed.

  Definition bstep_e_strengthen rho1 rho2 e v c:
    bstep_e rho1 e v c ->
    env_subset rho2 rho1 ->
    rho2 ⊢ e ->
    bstep_e rho2 e v c.
  Proof.
    intros Hstep. revert rho2.
    induction Hstep; intros rho2 Hext Hws; inv Hws.
    - erewrite Hext in H; eauto; inv H.
      constructor; eauto.
  Abort All. (* need more lemmas *)
      
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
  
  (** Environment relations *)
  Definition preord_var_env (k : nat) (rho1 rho2 : env) (x y : var) : Prop :=
    forall v1, 
      M.get x rho1 = Some v1 -> 
      exists v2, M.get y rho2 = Some v2 /\ preord_val k v1 v2.

  Definition preord_env_P (P : var -> Prop) k rho1 rho2 :=
    forall (x : var), P x -> preord_var_env k rho1 rho2 x x.
  
  (** ρ1 ~_k ρ2 iff ρ1(x) = v => ρ2(x) = v' /\ v ~_k v' *)
  Definition preord_env (k : nat) (rho1 rho2 : env) : Prop :=
    preord_env_P (fun _ => True) k rho1 rho2.

  Open Scope ctx_scope.

  (** Context relation. *)
  Definition preord_ctx (k : nat) (rho1 rho2 : env)
             (p1 p2 : exp_ctx * env) :=
    let '(c1, rho1') := p1 in
    let '(c2, rho2') := p2 in
    forall e1 e2, preord_exp k (e1, rho1) (e2, rho2) ->
                  preord_exp k (c1 |[ e1 ]|, rho1')
                             (c2 |[ e2 ]|, rho2').

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

  Lemma Forall2_same {A} (R : A -> A -> Prop) l:
    (forall x, List.In x l -> R x x) ->
    Forall2 R l l.
  Proof.
    induction l; intros H; constructor.
    - apply H. constructor; eauto.
    - apply IHl. intros. apply H. constructor 2; eauto.
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

  Lemma preord_var_env_extend :
    forall (rho1 rho2 : env) (k : nat) (x y : var) (v1 v2 : val),
      preord_var_env k rho1 rho2 y y ->
      preord_val k v1 v2 ->
      preord_var_env k (M.set x v1 rho1) (M.set x v2 rho2) y y.
  Proof.
    intros rho1 rho2 k x y v1 v2 Henv Hval x' Hget.
    rewrite M.gsspec in Hget. destruct (Coqlib.peq y x); subst.
    - inv Hget. eexists. rewrite M.gss. split; eauto.
    - apply Henv in Hget. destruct Hget as [v2' [Heq Hpre]].
      eexists; split; eauto. rewrite M.gso; eauto.
  Qed.

  Lemma preord_var_env_extend_eq :
    forall (rho1 rho2 : env) (k : nat) (x : var) (v1 v2 : val),
      preord_val k v1 v2 ->
      preord_var_env k (M.set x v1 rho1) (M.set x v2 rho2) x x.
  Proof.
    intros rho1 rho2 k x v1 v2 Hval x' Hget.
    rewrite M.gss in Hget. inv Hget. eexists. rewrite M.gss. split; eauto.
  Qed.

  Lemma preord_env_P_antimon (P1 P2 : var -> Prop) k rho1 rho2 :
    preord_env_P P2 k rho1 rho2 ->
    (forall x, P1 x -> P2 x) ->
    preord_env_P P1 k rho1 rho2.
  Proof.
    intros Hpre Hin x HP2. eapply Hpre; eauto.
  Qed.
  
  Lemma preord_env_P_extend :
    forall P (rho1 rho2 : env) (k : nat) (x : var) (v1 v2 : val),
      preord_env_P (fun y => P y /\ y <> x) k rho1 rho2 ->
      preord_val k v1 v2 ->
      preord_env_P P k (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros P rho1 rho2 k x v1 v2 Henv Hval x' HP v1' Hget.
    rewrite M.gsspec in Hget. destruct (Coqlib.peq x' x); subst.
    - inv Hget. eexists. rewrite M.gss. split; eauto.
    - apply Henv in Hget; eauto. destruct Hget as [v2' [Heq Hpre]].
      eexists; split; eauto. rewrite M.gso; eauto.
  Qed.

  Lemma setlist_Forall2_get (P : val -> val -> Prop)
        xs vs1 vs2 rho1 rho2 rho1' rho2' x : 
    Forall2 P vs1 vs2 ->
    setlist xs vs1 rho1 = Some rho1' ->
    setlist xs vs2 rho2 = Some rho2' ->
    In x xs ->
    exists v1 v2,
      M.get x rho1' = Some v1 /\
      M.get x rho2' = Some v2 /\ P v1 v2.
  Proof.
    revert rho1' rho2' vs1 vs2.
    induction xs; simpl; intros rho1' rho2' vs1 vs2 Hall Hset1 Hset2 Hin.
    - inv Hin.
    - destruct (Coqlib.peq a x); subst.
      + destruct vs1; destruct vs2; try discriminate.
        destruct (setlist xs vs1 rho1) eqn:Heq1;
          destruct (setlist xs vs2 rho2) eqn:Heq2; try discriminate.
        inv Hset1; inv Hset2. inv Hall.
        repeat eexists; try rewrite M.gss; eauto.
    + destruct vs1; destruct vs2; try discriminate.
      destruct (setlist xs vs1 rho1) eqn:Heq1;
        destruct (setlist xs vs2 rho2) eqn:Heq2; try discriminate.
      inv Hset1; inv Hset2. inv Hall. inv Hin; try congruence.
      edestruct IHxs as [v1 [v2 [Hget1 [Hget2 HP]]]]; eauto.
      repeat eexists; eauto; rewrite M.gso; eauto.
  Qed.

  Lemma setlist_not_In (xs : list var) (vs : list val) (rho rho' : env) (x : var) : 
    setlist xs vs rho = Some rho' ->
    ~ In x xs ->
    M.get x rho = M.get x rho'.
  Proof.
    revert vs rho'.
    induction xs; simpl; intros vs rho' Hset Hin.
    - destruct vs; congruence.
    - destruct vs; try discriminate.
      destruct (setlist xs vs rho) eqn:Heq1; try discriminate. inv Hset.
      rewrite M.gso; eauto.
  Qed.

  Lemma preord_env_P_setlist_l:
    forall (P1 P2 : var -> Prop) (rho1 rho2 rho1' rho2' : env)
           (k : nat) (xs : list var) (vs1 vs2 : list val),
      preord_env_P P1 k rho1 rho2 ->
      (forall x, ~ In x xs -> P2 x -> P1 x) ->
      Forall2 (preord_val k) vs1 vs2 ->
      setlist xs vs1 rho1 = Some rho1' ->
      setlist xs vs2 rho2 = Some rho2' ->
      preord_env_P P2 k rho1' rho2'.
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
      eexists. split; simpl; eauto. rewrite H1. rewrite Hget.
      constructor. eauto.
  Qed.

  Lemma preord_env_extend (rho1 rho2 : env) (k : nat)
        (x : var) (v1 v2 : val) :
    preord_env k rho1 rho2 ->
    preord_val k v1 v2 ->
    preord_env k (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros H1 Hval. apply preord_env_P_extend; eauto.
    eapply preord_env_P_antimon; eauto. intros; simpl; eauto.
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
    revert v2 Hpre; induction v1 using val_ind'; intros v2 Hpre;
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

  Lemma preord_env_P_monotonic :
    forall P (k j : nat) (rho1 rho2 : env),
      j <= k -> preord_env_P P k rho1 rho2 -> preord_env_P P j rho1 rho2.
  Proof.
    intros P k j rho1 rho2 Hleq Hpre x HP v Hget.
    edestruct Hpre as [v2 [Heq Hpre2]]; eauto.
    eexists; split; eauto. eapply preord_val_monotonic; eauto.
  Qed.


  Lemma preord_env_monotonic k j rho1 rho2 :
    j <= k -> preord_env k rho1 rho2 -> preord_env j rho1 rho2.
  Proof.
    intros Hleq H. eapply preord_env_P_monotonic; eauto.
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

  Lemma preord_exp_const_compat k rho1 rho2 x tau t ys1 ys2 e1 e2 :
    Forall2 (preord_var_env k rho1 rho2) ys1 ys2 ->
    (forall vs1 vs2 : list val,
       Forall2 (preord_val k) vs1 vs2 ->
       preord_exp k (e1, M.set x (Vconstr tau t vs1) rho1)
                  (e2, M.set x (Vconstr tau t vs2) rho2)) ->
    preord_exp k (Econstr x tau t ys1 e1, rho1) (Econstr x tau t ys2 e2, rho2).
  Proof.
    intros Hall Hpre v1 c1 Hleq1 Hstep1. inv Hstep1.
    edestruct (preord_var_env_getlist rho1 rho2) as [vs2' [Hget' Hpre']]; [| eauto |]; eauto.
    edestruct Hpre as [v2 [c2 [Hstep [Hleq Hval]]]]; eauto.
    repeat eexists; eauto. econstructor; eauto.
  Qed.

  Lemma preord_exp_proj_compat k rho1 rho2 x tau n y1 y2 e1 e2 :
    preord_var_env k rho1 rho2 y1 y2 ->
    (forall v1 v2,
       preord_val k v1 v2 -> 
       preord_exp k (e1, M.set x v1 rho1)
                  (e2, M.set x v2 rho2)) ->
    preord_exp k (Eproj x tau n y1 e1, rho1) (Eproj x tau n y2 e2, rho2).
  Proof.
    intros Henv Hexp v1 c1 Hleq1 Hstep1. inv Hstep1.
    edestruct Henv as [v' [Hget Hpre]]; eauto.
    destruct v'; rewrite preord_val_eq in Hpre; simpl in Hpre; try contradiction.
    inv Hpre.
    edestruct (Forall2_nthN (preord_val k) vs l) as [v2 [Hnth Hval]]; eauto.
    edestruct Hexp as [v2' [c2 [Hstep [Hleq Hval']]]]; eauto.
    repeat eexists; eauto. econstructor; eauto.
  Qed.

  Lemma preord_exp_app_compat k rho1 rho2 x1 x2 ys1 ys2 :
    preord_var_env k rho1 rho2 x1 x2 ->
    Forall2 (preord_var_env k rho1 rho2) ys1 ys2 ->
    preord_exp k (Eapp x1 ys1, rho1) (Eapp x2 ys2, rho2).
  Proof.
    intros Hvar Hall v1 c1 Hleq1 Hstep1. inv Hstep1.
    - edestruct preord_var_env_getlist as [vs2 [Hget' Hpre']]; eauto.
      edestruct Hvar as [v2 [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v2; try (now simpl in Hpre; contradiction).
      repeat eexists. constructor; eauto. eauto.
      rewrite preord_val_eq. rewrite <- minus_n_O. eauto.
    - edestruct Hvar as [v2' [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v2'; try (now simpl in Hpre; contradiction).
      edestruct preord_var_env_getlist as [vs2 [Hget' Hpre']]; eauto.
      edestruct (Hpre vs vs2 (k-1)) as [t2 [xs2 [e2 [rho2' [Hf [Hset H']]]]]]; eauto.
      eapply Forall2_length; eauto.
      edestruct H' with (c1 := c) as [v2 [c2 [Hstep' [Hc2 Hpre'']]]];
        eauto; try omega.
      eapply Forall2_monotonic. intros.
      eapply (preord_val_monotonic k). eauto. omega. eauto.
      repeat eexists. econstructor 5; eauto. omega.
      replace (k - (c + 1)) with (k - 1 - c) by omega. eauto.
  Qed.

  Lemma preord_exp_case_nil_compat k rho1 rho2 x1 x2 :
    preord_exp k (Ecase x1 [], rho1) (Ecase x2 [], rho2).
  Proof.
    intros v1 c1 Hleq1 Hstep1. inv Hstep1. inv H3.
  Qed.

  Lemma preord_exp_case_cons_compat k rho1 rho2 x1 x2 c e1 e2 P1 P2:
    preord_var_env k rho1 rho2 x1 x2 ->
    preord_exp k (e1, rho1) (e2, rho2) ->
    preord_exp k (Ecase x1 P1, rho1)
               (Ecase x2 P2, rho2) ->
    preord_exp k (Ecase x1 ((c, e1) :: P1), rho1)
               (Ecase x2 ((c, e2) :: P2), rho2).
  Proof.
    intros Henv Hexp_hd Hexp_tl v1 c1 Hleq1 Hstep1. inv Hstep1. inv H3.
    destruct (M.elt_eq c t) eqn:Heq; subst.
    - inv H0. edestruct Hexp_hd as [v2 [c2 [Hleq2 [Hstep2 Hpre2]]]]; eauto.
      edestruct Henv as [v2' [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v2'; try (now simpl in Hpre; contradiction). inv Hpre. 
      repeat eexists; eauto. econstructor; eauto. simpl; rewrite Heq; eauto.
    - edestruct Hexp_tl as [v2 [c2 [Hstep2 [Hleq2 Hpre2]]]]; eauto.
      econstructor; eauto. inv Hstep2.
      edestruct Henv as [v2' [Hget Hpre]]; eauto.
      rewrite preord_val_eq in Hpre.
      destruct v2'; try (now simpl in Hpre; contradiction). inv Hpre.
      rewrite Hget in H3; inv H3.
      repeat eexists; eauto. econstructor; eauto. simpl; rewrite Heq; eauto.
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

  Lemma preord_exp_prim_compat k rho1 rho2 x1 x2 tau f ys1 ys2 e1 e2 :
    Forall2 (preord_var_env k rho1 rho2) ys1 ys2 ->
    (forall v1 v2,
       preord_val k v1 v2 -> 
       preord_exp k (e1, M.set x1 v1 rho1)
                  (e2, M.set x2 v2 rho2)) ->
    preord_exp k (Eprim x1 tau f ys1 e1, rho1) (Eprim x2 tau f ys2 e2, rho2).
  Proof.
    intros Henv Hexp v1 c1 Hleq1 Hstep1. inv Hstep1.
    edestruct preord_var_env_getlist as [vs2 [Hget' Hpre']]; eauto.
    edestruct Prim_axiom as [v2 [Heq Hprev2]]; eauto.
    edestruct Hexp as [v2' [c2 [Hstepv2' [ Hleq2 Hprev2']]]]; eauto.
    repeat eexists; eauto. econstructor; eauto.
  Qed.

  Lemma preord_exp_fun_compat k rho1 rho2 B e1 e2 :
    preord_exp k (e1, def_funs B B rho1 rho1)
               (e2, def_funs B B rho2 rho2) ->
    preord_exp k (Efun B e1, rho1) (Efun B e2, rho2).
  Proof.
    intros Hexp v1 c1 Hleq1 Hstep1. inv Hstep1.
    edestruct Hexp as [v2' [c2 [Hstepv2' [ Hleq2 Hprev2']]]]; eauto.
    repeat eexists; eauto. econstructor; eauto.
  Qed.

  Lemma preord_env_P_def_funs k B rho rho' e B' :
    (forall m (rho rho' : env) (e : exp),
       m <  k ->
       preord_env_P (fun x => occurs_free x e) m rho rho' ->
       preord_exp m (e, rho) (e, rho')) ->
    preord_env_P (fun x => occurs_free_fundefs x B' \/
                           (~ name_in_fundefs x B' /\ occurs_free x e))
                 k rho rho' ->
    preord_env_P (fun x => occurs_free x (Efun B' e) \/ name_in_fundefs x B)
                 k (def_funs B' B rho rho) (def_funs B' B rho' rho').
  Proof.
    revert B rho rho' e B'.
    induction k as [ k IH' ] using lt_wf_rec1. intros B rho rho' e B'.
    induction B; intros Hyp Hpre.
    - simpl. apply preord_env_P_extend.
      + intros x H. inv H. eapply IHB; eauto.
        inv H0; eauto. inv H; try congruence. eauto.
      + rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
        edestruct setlist_length as [rho2' Hs']; eauto.
        exists t1. exists xs1. exists e1. exists rho2'. split; eauto.
        split. eauto. intros Hleq Hpre'. 
        eapply Hyp. omega.
        eapply preord_env_P_setlist_l; [| | | eauto | eauto]; eauto. 
        apply IH'; eauto. intros. apply Hyp. omega. eauto.
        eapply (preord_env_P_monotonic _ k); eauto. omega.
        intros x Hin Hfr. simpl.
        apply find_def_correct in Hf.
        edestruct occurs_free_in_fun as [H1 | [H1 | H1]]; eauto; try contradiction.
        left. apply Free_Efun2; eauto.
    - simpl. intros x HP. inv HP. inv H. apply Hpre; eauto.
      apply Hpre; eauto. inv H.
  Qed.

  Lemma preord_exp_refl k e rho rho' :
    preord_env_P (fun x => occurs_free x e) k rho rho' ->
    preord_exp k (e, rho) (e, rho').
  Proof.
    (* intros Hvalrefl. *)
    revert e rho rho'.
    induction k as [ k IH ] using lt_wf_rec1.
    induction e using exp_ind'; intros rho rho' Henv.
    - eapply preord_exp_const_compat; eauto; intros.
      eapply Forall2_same. intros x HIn. apply Henv. now constructor.
      eapply IHe. eapply preord_env_P_extend.
      eapply preord_env_P_antimon; eauto. intros x [H1 H2]. constructor 2; eauto.
      rewrite preord_val_eq. constructor; eauto.
    - eapply preord_exp_case_nil_compat.
    - eapply preord_exp_case_cons_compat; eauto.
      apply Henv. constructor.
      apply IHe. intros x P. apply Henv. constructor; eauto.
      apply IHe0. intros x P. apply Henv. apply Free_Ecase3; eauto.
    - eapply preord_exp_proj_compat; eauto.
      apply Henv. now constructor.
      intros v1 v2 Hval. eapply IHe. eapply preord_env_P_extend; eauto.
      eapply preord_env_P_antimon; eauto.
      intros x [H1 H2]; eauto. constructor; eauto.
    - eapply preord_exp_fun_compat; eauto.
      eapply IHe. eapply preord_env_P_antimon. 
      eapply preord_env_P_def_funs; eauto.
      eapply preord_env_P_antimon. eauto.
      intros x H. destruct H as [H | [H1 H2]]; try now (constructor; eauto).
      intros x H. destruct (name_in_fundefs_dec x f2); eauto.
      left. constructor; eauto.
    - eapply preord_exp_app_compat.
      intros x HP. apply Henv; eauto. now constructor.
      apply Forall2_same. intros. apply Henv. now constructor.
    - eapply preord_exp_prim_compat; eauto; intros.
      eapply Forall2_same. intros. apply Henv. now constructor.
      eapply IHe. eapply preord_env_P_extend; eauto.
      eapply preord_env_P_antimon; eauto. intros x [H1 H2].
      apply Free_Eprim2; eauto. 
  Qed.

  Lemma preord_exp_refl_weak (k : nat) rho rho' e :
      preord_env k rho rho' ->
      preord_exp k (e, rho) (e, rho').
  Proof.
    intros Henv. eapply preord_exp_refl.
    eapply preord_env_P_antimon; eauto.
    intros; simpl; eauto.
  Qed.
  
  Lemma preord_val_refl (k : nat) :
    Reflexive (preord_val k).
  Proof.
    induction k using lt_wf_rec1.
    destruct k as [| k]; unfold Reflexive; intros x; rewrite preord_val_eq;
    induction x using val_ind'; simpl; eauto;
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
      eapply preord_exp_refl_weak; eauto.
      eapply preord_env_setlist_l; eauto.
      eapply preord_env_refl; eauto.
  Qed.

  Lemma preord_env_def_funs k f rho1 rho2 :
    preord_env k rho1 rho2 ->
    preord_env k (def_funs f f rho1 rho1) (def_funs f f rho2 rho2).
  Proof.
    intros Henv. 
    generalize f at 1 3. revert f rho1 rho2 Henv.
    induction k as [ k IH' ] using lt_wf_rec1. intros f rho rho2 Henv.
    induction f; eauto; intros defs. simpl; eauto. 
    eapply preord_env_extend. simpl. eapply IHf.
    rewrite preord_val_eq. intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
    edestruct setlist_length as [rho2' Hs']; eauto.
    exists t1. exists xs1. exists e1. exists rho2'. split; eauto.
    split. eauto. intros Hleq Hpre. eapply preord_exp_refl_weak.
    eapply preord_env_setlist_l with (vs1 := vs1) (vs2 := vs2); eauto.
    eapply IH'; try omega; eauto.
    eapply preord_env_monotonic; [| eauto]. omega.
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
    intros x; induction x using val_ind'; simpl; eauto;
    intros v1 v2; rewrite !preord_val_eq;
    try (now intros H1 H2; destruct v1; destruct v2;
         try (now simpl in *; contradiction); inv H1; inv H2; simpl; eauto).
    - intros H1 H2. destruct v1; destruct v2; try (now simpl in *; contradiction).
      destruct H1 as [H1 H1']. destruct H2 as [H2 H2']. subst.
      destruct l; destruct l0; try inv H1'; try inv H2'. split; eauto.
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

  Corollary preord_exp_trans (k : nat) :
    forall rho1 rho2 rho3 e1 e2 e3,
      preord_exp k (e1, rho1) (e2, rho2) ->
      preord_exp k (e2, rho2) (e3, rho3) ->
      preord_exp k (e1, rho1) (e3, rho3).
  Proof.
    intros. eapply preord_exp_trans_pre; eauto.
    intros. eapply preord_val_trans.
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

  Lemma preord_env_P_def_funs_pre k (P1 P2 : var -> Prop) B rho1 rho2 :
    preord_env_P P1 k rho1 rho2 ->
    (forall x, P2 x -> P1 x) -> 
    (forall m (rho rho' : env) (e : exp),
       m <  k ->
       preord_env_P P1 m rho rho' ->
       preord_exp m (e, rho) (e, rho')) ->
    preord_env_P P2 k (def_funs B B rho1 rho1) (def_funs B B rho2 rho2).
  Proof.
    generalize B at 1 3. revert P1 P2 B rho1 rho2.
    induction k as [ k IH' ] using lt_wf_rec1. intros P1 P2 B.
    induction B; intros rho rho2 B' Henv Hyp1 Hyp2 x HP.
    - simpl. apply preord_var_env_extend; eauto.
      + eapply IHB; eauto.
      + rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf Hs.
        edestruct setlist_length as [rho2' Hs']; eauto.
        exists t1. exists xs1. exists e1. exists rho2'. split; eauto.
        split. eauto. intros Hleq Hpre. 
        eapply Hyp2; try omega.
        eapply preord_env_P_setlist_l; eauto.
        eapply IH'; try omega; eauto. 
        eapply preord_env_P_monotonic; [| eauto]. omega.
        intros. eapply Hyp2; eauto. omega.
    - simpl. eauto.
  Qed.

End EVAL.
