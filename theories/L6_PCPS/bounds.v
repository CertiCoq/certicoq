Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles Coq.micromega.Lia.

Require Import L6.cps L6.eval L6.Ensembles_util L6.List_util L6.tactics L6.set_util
        L6.logical_relations L6.logical_relations_cc L6.algebra.
Require Import micromega.Lia.

Import ListNotations.

Open Scope alg_scope. 
Section Temp.

    Context {steps: Type} {Hr : @resource_exp steps}.

    Definition remove_steps_letapp cenv (P1 P2 P3 : PostT) :=
    forall (x f z : positive) (t : fun_tag) (ys : list map_util.M.elt) (e1 : exp)
           (rho1 : map_util.M.t val)
           (xs : list var) (e_b1 : exp) (v1 : val) (e2 e2' e_b2: exp) (rho2 rho2' rhoc2  rhoc1 : M.t val) 
           (fl : fundefs) (h : var) (vs : list val) (rhoc1' : map_util.M.t val) (c1 c1' c2 c2' : steps),
      rho1 ! f = Some (Vfun rhoc1 fl h) ->
      get_list ys rho1 = Some vs ->
      find_def h fl = Some (t, xs, e_b1) ->
      set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->
      bstep_fuel cenv rhoc1' e_b1 (Res v1) c1 ->

      P1 (e_b1, rhoc1', c1) (e_b2, rhoc2, c2) (* when inlined body makes a tail call *) \/
      P1 (e_b1, rhoc1', c1) (e_b2, rhoc2, c2 <+> one (Ehalt z)) (* when inlined body returns *) ->
      P2 (e1, M.set x v1 rho1, c1') (e2', rho2', c2') ->
      P3 (Eletapp x f t ys e1, rho1, c1 <+> c1' <+> one (Eletapp x f t ys e1))
         (e2, rho2, c2 <+> c2').


  Definition remove_steps_letapp_OOT cenv (P1 P2 : PostT) :=
    forall (x f z: positive) (t : fun_tag) (ys : list map_util.M.elt) (e1 : exp) (rho1 : map_util.M.t val)
           (xs : list var) (e_b1 : exp) (r : res) (e2 e_b2 : exp) (rho2 rhoc1 : M.t val) (rhoc2 : env) 
           (fl : fundefs) (h : var) (vs : list val) (rhoc1' : map_util.M.t val) (c1 c2 : steps),
      rho1 ! f = Some (Vfun rhoc1 fl h) ->
      get_list ys rho1 = Some vs ->
      find_def h fl = Some (t, xs, e_b1) ->
      set_lists xs vs (def_funs fl fl rhoc1 rhoc1) = Some rhoc1' ->
      bstep_fuel cenv rhoc1' e_b1 r c1 ->
      
      P1 (e_b1, rhoc1', c1) (e_b2, rhoc2, c2) \/
      P1 (e_b1, rhoc1', c1) (e_b2, rhoc2, c2 <+> one (Ehalt z)) ->
      P2 (Eletapp x f t ys e1, rho1, c1 <+> one (Eletapp x f t ys e1)) (e2, rho2, c2). 


End Temp.

Section Bounds.
  
  
  Program Instance resource_tup : @resource fin (nat * nat) :=
    { zero := (0, 0)%type;
      one_i fin :=
        match fin with
        | Four => (1, 1)
        | Six => (1, 1)
        | _ => (1, 0)
        end;
      plus x y  :=
        let '(x1, x2) := x in
        let '(y1, y2) := y in
        (x1 + y1, x2 + y2);
      
      lt_i fin x y :=
        let '(x1, x2) := x in
        let '(y1, y2) := y in
        match fin with
        | Four => x1 < y1 
        | Six => x1 < y1
        | _ => x1 < y1
        end;

      to_nat x := fst x;
      
    }.
  Solve Obligations with (try (split; congruence)).
  Solve Obligations with (simpl; f_equal; try lia).
  Next Obligation. simpl; f_equal; try lia. Qed.
  Next Obligation. simpl; f_equal; try lia. Qed.
  Next Obligation. simpl; f_equal; try lia. Qed.
  Next Obligation.  
    intro; intros.
    destruct x as [? ?]. destruct y as [? ?]. destruct z as [? ?].
    destruct i; try (simpl in *; lia).
  Qed.
  Next Obligation. intro; intros. destruct x as [? ?]. intro. destruct i; simpl in *; lia. Qed.
  Next Obligation. destruct i; simpl; try eapply Compare_dec.lt_dec. Qed.
  Next Obligation. intros H. destruct i; simpl; lia. Qed.
  Next Obligation. destruct i; simpl; lia. Qed.
  Next Obligation. destruct i; simpl in *; lia. Qed.
  Next Obligation. 
    (* simpl in *. *)
    (* edestruct (Compare_dec.le_dec n0 n3); edestruct (Compare_dec.le_dec n1 n4); *)
    (*   edestruct (Compare_dec.le_dec n n2). *)
    (* - right. eexists (n3 - n0, n4 - n1, n2 - n). simpl. f_equal; [ f_equal | ]; lia. *)
    (* - left. exists Four. lia. *)
    (* - left. exists Six. lia. *)
    (* - left. exists Six. lia. *)
    (* - left. exists One. lia. *)
    (* - left. exists One. lia. *)
    (* - left. exists One. lia. *)
    (* - left. exists One. lia. *)
  Admitted. 
  Next Obligation.
    destruct i; simpl;
    
      try (edestruct (Compare_dec.lt_dec n0 1); [ now eauto  | right; eexists (n0 -1, n1, n); simpl; f_equal; [ f_equal | ]; lia]);
      try (edestruct (Compare_dec.lt_dec n1 1); [ now eauto  | right; eexists (n0, n1 -1, n); simpl; f_equal; [ f_equal | ]; lia]).
    
  Admitted.
  Next Obligation.
    destruct i; simpl; try f_equal; lia.
  Qed. 
  Next Obligation.
    intros Heq. destruct i; simpl in *; try lia.
    (* inv H; inv Heq; try lia. *)
  Qed.
  Next Obligation.
    destruct i; simpl; reflexivity.
  Qed.

  Program Instance resource_tup_e : @resource_exp (nat * nat).

  (* (possible) bound for inlining *)
  Definition inline_bound (L G : nat) : relation (exp * env * (nat * nat)) := 
    fun '(e1, rho1, (c1, c2)) '(e2, rho2, (c1', c2')) =>
      c1 <= c1' + 2 * G * c2' + 2 * L /\
      c2 <= c2' + 2 * G * c2' + 2 * L.

  Context (cenv : ctor_env).


  Close Scope alg_scope.
  
  Instance inline_bound_compat L G (Hi : L <= G) :
    Post_properties cenv (inline_bound L G) (inline_bound L G) (inline_bound G G). 
  Proof.
    constructor; try (intro; intros; intro; intros; unfold inline_bound in *; lia);
    try now (intro; intros; intro; intros; unfold inline_bound in *;
         destruct c1 as [? ?]; destruct c2 as [? ?]; destructAll; simpl;
         split; lia). 
    - intro; intros; intro; intros; unfold inline_bound in *.
      destruct c1 as [? ?]. destruct c2 as [? ?].
      destruct c1' as [? ?]. destruct c2' as [? ?].
      destructAll. simpl. split; lia.
    - intro; intros; intro; intros; unfold inline_bound in *. 
      destruct c as [? ?]. simpl in *. split; lia.      
    - intro; intros; intro; intros; unfold inline_bound in *. 
      destruct c as [? ?]. simpl in *. split; lia.      
    - intro; intros; unfold inline_bound in *.
      destruct x as [[? ?] [? ?]]; destruct y as [[? ?] [? ?]].
      destructAll. split; lia.
  Qed. 

  
  Lemma cost_exp_size_exp e :
    1 = cost e.
  Proof.
    destruct e; simpl; lia.
  Qed.
  

  (* Lemma inline_bound_Hpost_zero i G f ft ys rho1 e2 rho2 (Hleq : 1 <= i): *)
  (*   post_zero (Eapp f ft ys) rho1 e2 rho2 (inline_bound i G). *)
  (* Proof. *)
  (*   intro; intros; unfold inline_bound in *.  *)
  (*   destruct c as [? ?]. *)
  (*   simpl. unfold lt_e in H. simpl in H. split; try lia. *)
  (* Qed. *)

  
  Lemma inline_bound_post_Eapp_l i G v t l rho1 x rho2 :
    post_Eapp_l (inline_bound i G) (inline_bound (S i) G) v t l rho1 x rho2.
  Proof.
    intro; intros. unfold inline_bound in *.
    destruct c1 as [? ?].
    destruct c2 as [? ?]. simpl. split; lia.
  Qed.
  
  Lemma inline_bound_remove_steps_letapp i j G : 
    remove_steps_letapp cenv (inline_bound i G) (inline_bound j G) (inline_bound (S (i + j)) G).
  Proof.
    intro; intros. unfold inline_bound in *.
    destruct c1 as [? ?].
    destruct c2 as [? ?].
    destruct c1' as [? ?].
    destruct c2' as [? ?].
    simpl. inv H4. lia. simpl in *.
    rewrite !NPeano.Nat.mul_add_distr_l, !Nat.mul_0_r in *. simpl in *.
    lia. 
  Qed.    

  Lemma inline_bound_remove_steps_letapp_OOT i j G : 
    remove_steps_letapp_OOT cenv (inline_bound j G) (inline_bound (S (i + j)) G).
  Proof.
    intro; intros. unfold inline_bound in *.
    destruct c1 as [? ?].
    destruct c2 as [? ?].
    simpl. inv H4. lia. simpl in *.
    rewrite !NPeano.Nat.mul_add_distr_l, !Nat.mul_0_r in *. simpl in *. lia.
  Qed.
      

    
    post_constr_compat'; post_proj_compat' .

      11:{ intro; intros. unfold inline_bound in *.
         destruct x as [[? ? ] ?]. destruct y as [[? ? ] ?]. eapply le_trans. eassumption.
         eapply plus_le_compat_r. eapply mult_le_compat_l. eapply plus_le_compat_l.
         eapply mult_le_compat_r. eassumption. }
    
    - (* constr *) intro; intros. intro; intros.
      unfold inline_bound in *.
      eapply le_trans. eapply plus_le_compat_r. eassumption.
      assert (Hleq : cost_exp_env G e1 (map_util.M.set x (Vconstr t vs) rho1) <= cost_exp_env G (Econstr x t ys e1) rho1).
      { unfold cost_exp_env. eapply Max.max_lub.
        -- eapply le_trans; [| eapply Max.le_max_l ]. simpl. lia.
        -- eapply le_trans. eapply max_env_set.
           eapply Max.max_lub; [| lia ]. eapply le_trans.
           simpl. eapply max_env_getlist. eassumption.
           rewrite max_env_max_value_eq. lia. }      
        
      rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat.
      * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)).
        eapply plus_le_compat. lia. 
        eapply mult_le_compat_l. eapply plus_le_compat_l. eapply mult_le_compat_l. eassumption.
      * eassumption.
    - (* proj *) intro; intros. intro; intros.
      unfold inline_bound in *. 
      eapply le_trans. eapply plus_le_compat_r. eassumption.
      assert (Hleq : cost_exp_env G e1 (map_util.M.set x v1 rho1) <= cost_exp_env G (Eproj x t N y e1) rho1).
      { unfold cost_exp_env. eapply Max.max_lub.
        -- eapply le_trans; [| eapply Max.le_max_l ]. simpl. lia.
        -- eapply le_trans. eapply max_env_set.
           eapply Max.max_lub; [| lia ]. eapply le_trans; [| eapply Max.le_max_r ].
           eapply le_trans; [| eapply max_env_get; eauto ]. simpl.
           rewrite size_value_eq. eapply fold_left_max_in. eapply nthN_In. eassumption. }            
      rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat.
      * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)).
        eapply plus_le_compat. lia. 
        eapply mult_le_compat_l. eapply plus_le_compat_l. eapply mult_le_compat_l. eassumption.
      * eassumption.
    - (* fun *) intro; intros. intro; intros.
      unfold inline_bound in *.
      eapply le_trans. eapply plus_le_compat_r. eassumption.
      assert (Hleq : cost_exp_env G e1 (def_funs B1 B1 rho1 rho1) <= cost_exp_env G (Efun B1 e1) rho1). 
      { unfold cost_exp_env. eapply Max.max_lub.
        -- eapply le_trans; [| eapply Max.le_max_l ]. simpl. lia.
        -- eapply le_trans. eapply max_env_def_funs. simpl. lia. }
      rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat.
      * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)).
        eapply plus_le_compat. lia. 
        eapply mult_le_compat_l. eapply plus_le_compat_l. eassumption.
      * eassumption.
    - (* case hd *) intro; intros. intro; intros.
      unfold inline_bound in *.
      eapply le_trans. eapply plus_le_compat_r. eassumption.
      assert (Hleq : cost_exp_env e1 rho1 <= cost_exp_env (Ecase x ((t, e1) :: B1)) rho1).
      { unfold cost_exp_env. eapply Nat.max_le_compat_r.
        simpl. lia. }
      rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat.
      * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)).
        eapply plus_le_compat. lia. 
        eapply mult_le_compat_l. eapply plus_le_compat_l.
        simpl. eassumption.
      * eassumption.
    - (* case tl *) intro; intros. intro; intros.
      unfold inline_bound in *.
      eapply le_trans. eassumption.
      assert (Hleq : cost_exp_env (Ecase x B1) rho1 <= cost_exp_env (Ecase x ((t, e1) :: B1)) rho1).
      { unfold cost_exp_env. eapply Nat.max_le_compat_r. simpl. lia. }
      eapply plus_le_compat.
      * eapply mult_le_compat_l. eapply plus_le_compat_l. eassumption.
      * eassumption.
    - (* app *) intro; intros. intro; intros.  
      unfold inline_bound in *.
      eapply le_trans. eapply plus_le_compat_r. eassumption.
      assert (Hleq : cost_exp_env e1 rhoc1' <= cost_exp_env (Eapp x t xs) rho1).
      { unfold cost_exp_env at 2. eapply le_trans; [| eapply Max.le_max_r ].
        unfold cost_exp_env. eapply Nat.max_lub.

  Fixpoint size_exp (e : exp) : nat :=
    match e with
    | Econstr x _ ys e => 1 + length ys + size_exp e
    | Ecase x l =>
      1  + (fix size_l l :=
              match l with
              | [] => 0
              | (t, e) :: l => max (size_exp e) (size_l l)
              end) l
    | Eproj x _ _ y e => 1 + size_exp e
    | Eletapp x f _ ys e => 1 + length ys + size_exp e
    | Efun B e => max (size_fundefs B) (1 + size_exp e)
    | Eapp x _ ys => 1 + length ys
    | Eprim x _ ys e => length ys + size_exp e
    | Ehalt x => 1
    end
  with size_fundefs (B : fundefs) : nat := 
    match B with
    | Fcons _ _ xs e B => max (size_exp e) (size_fundefs B)
    | Fnil => 0
    end.

    
  Fixpoint size_value' (G : nat) (v : val) {struct v} :=
    match v with
    | Vconstr _ vs => fold_left (fun m v => max m (size_value' G v)) vs 0
    | Vfun rho B _ =>
      let senv :=
          (fix max_env m :=
             match m with
             | M.Leaf => 0
             | M.Node l (Some v) r => max (size_value' G v) (max (max_env l) (max_env r))
             | M.Node l None r => (max (max_env l) (max_env r))
             end) rho in
      G * max (size_fundefs B) senv
    | Vint x => 0
    end.

  Fixpoint max_env {A} (f : A -> nat) (m : M.t A) :=
    match m with
    | M.Leaf => 0
    | M.Node l (Some v) r => max (f v) (max (max_env f l) (max_env f r))
    | M.Node l None r => (max (max_env f l) (max_env f r))
    end.

  Definition size_value (G : nat) (v : val) :=
    match v with
    | Vconstr _ vs => fold_left (fun m v => max m (size_value' G v)) vs 0
    | Vfun rho B _ =>
      G * max (size_fundefs B) (max_env (size_value' G) rho)
    | Vint x => 0
    end.

  Lemma size_value_eq G v :
    size_value G v = size_value' G v.
  Proof.
    destruct v.
    - reflexivity.
    - simpl. do 2 f_equal. induction t.
      + reflexivity.
      + simpl. destruct o; eauto.
    - reflexivity.
  Qed.
  
  Lemma max_env_f_eq {A} (f f' : A -> nat) rho :
    (forall a, f a = f' a) ->
    max_env f rho = max_env f' rho.
  Proof.
    induction rho; eauto; intros.
    simpl. rewrite IHrho1, IHrho2; eauto. destruct o; eauto.
  Qed.

  Lemma max_env_max_value_eq G rho :
    max_env (size_value' G) rho = max_env (size_value G) rho.
  Proof.
    erewrite max_env_f_eq. reflexivity.
    intros. rewrite size_value_eq. reflexivity. 
  Qed.
  
  Definition cost_exp_env G e rho := max (size_exp e) (max_env (size_value G) rho). 


  Lemma fold_left_max_acc {A} l acc (f : A -> nat) :
    fold_left (fun m v => max m (f v)) l acc = 
    max (fold_left (fun m v => max m (f v)) l 0) acc. 
  Proof.
    revert acc; induction l; intros; simpl; eauto.
    rewrite IHl. rewrite (IHl (f a)). lia.
  Qed.


  Lemma fold_left_max_in {A} l (x : A) acc f :
    List.In x l ->
    f x <= fold_left (fun m v => max m (f v)) l acc. 
  Proof.
    revert acc; induction l; intros acc Hin. now inv Hin.
    simpl. inv Hin.
    - simpl. rewrite fold_left_max_acc. lia.
    - eapply le_trans. eapply IHl. eassumption. reflexivity.
  Qed.


  Lemma max_env_set {A} (f : A -> nat) rho x v :
    max_env f (M.set x v rho) <= max (f v) (max_env f rho).
  Proof.
    revert rho. induction x; intros.
    - destruct rho; simpl; eauto.
      + rewrite IHx. simpl. reflexivity.
      + destruct o; specialize (IHx rho2); lia.
    - destruct rho; simpl; eauto.
      + specialize (IHx M.Leaf). simpl in *. lia.
      +  destruct o; specialize (IHx rho1); lia.
    - simpl. destruct rho. simpl. lia.
      simpl. destruct o; simpl; lia.
  Qed.      

  Lemma max_env_setlist {A} (f : A -> nat) rho rho' xs vs :
    set_lists xs vs rho = Some rho' -> 
    max_env f rho' <= max (fold_left (fun m v => max m (f v)) vs 0) (max_env f rho).
  Proof.
    revert rho rho' vs. induction xs; intros.
    - destruct vs; inv H. lia.
    - simpl in H. destruct vs. inv H.
      destruct (set_lists xs vs rho) eqn:Heqs; inv H.
      simpl. rewrite fold_left_max_acc. eapply le_trans.
      eapply max_env_set. eapply Max.max_lub. lia.
      eapply le_trans. eapply IHxs; eauto. lia. 
  Qed.

  Require Import identifiers.


  Lemma size_fundefs_fun_in_fundefs B xs t e :
    fun_in_fundefs B (xs, t, e) ->
    size_exp e <= size_fundefs B.
  Proof.
    induction B; intros Hbin; inv Hbin.
    - inv H. simpl. lia.
    - eapply le_trans. eapply IHB. eassumption. simpl. lia.
  Qed.
    
  Lemma max_env_def_funs G rho B B0 :
    max_env (size_value G) (def_funs B0 B rho rho) <=
    max (G * max (size_fundefs B0) (max_env (size_value G) rho)) (max_env (size_value G) rho).
  Proof.
    induction B; simpl; [| lia ].
    
    eapply le_trans. eapply max_env_set. eapply Nat.max_lub.
    + simpl. rewrite max_env_max_value_eq. lia.
    + lia.
  Qed.

  
  Lemma max_env_get {A} (f : A -> nat) rho x v :
    M.get x rho = Some v ->
    f v <= max_env f rho. 
  Proof.
    revert rho. induction x; simpl; intros.
    - destruct rho. congruence. eapply IHx in H.
      eapply le_trans. eassumption. destruct o; simpl; lia.
    - destruct rho. congruence. eapply IHx in H.
      eapply le_trans. eassumption. destruct o; simpl; lia.
    - destruct rho. congruence. destruct o; simpl in H; inv H.
      simpl; lia.
  Qed.

    
  Lemma max_env_getlist {A} (f : A -> nat) rho xs vs :
    get_list xs rho = Some vs ->
    fold_left (fun m v => max m (f v)) vs 0 <= max_env f rho. 
  Proof.
    revert vs rho. induction xs; intros.
    + inv H. simpl. lia.
    + simpl in H. destruct (rho ! a) eqn:Hgeta; try congruence.
      destruct (get_list xs rho) eqn:Hgetl; try congruence.
      inv H. simpl. rewrite fold_left_max_acc. eapply Max.max_lub.
      * eapply IHxs. eassumption.
      * eapply max_env_get. eassumption.
  Qed.


  
  (* (possible) bound for inlining *)
  Definition inline_bound (i G : nat) : relation (exp * env *  nat) := 
    fun '(e1, rho1, c1) '(e2, rho2, c2) =>
      c1 <= c2 * (1 + i * cost_exp_env G e1 rho1) + cost_exp_env G e1 rho1.

  Context (cenv : ctor_env).
  
  Instance inline_bound_compat i G (Hi : i <= G) :
    Post_properties cenv (inline_bound i G) (inline_bound i G) (inline_bound G G). 
  Proof.
    constructor.
    11:{ intro; intros. unfold inline_bound in *.
         destruct x as [[? ? ] ?]. destruct y as [[? ? ] ?]. eapply le_trans. eassumption.
         eapply plus_le_compat_r. eapply mult_le_compat_l. eapply plus_le_compat_l.
         eapply mult_le_compat_r. eassumption. }
    
    - (* constr *) intro; intros. intro; intros.
      unfold inline_bound in *.
      eapply le_trans. eapply plus_le_compat_r. eassumption.
      assert (Hleq : cost_exp_env G e1 (map_util.M.set x (Vconstr t vs) rho1) <= cost_exp_env G (Econstr x t ys e1) rho1).
      { unfold cost_exp_env. eapply Max.max_lub.
        -- eapply le_trans; [| eapply Max.le_max_l ]. simpl. lia.
        -- eapply le_trans. eapply max_env_set.
           eapply Max.max_lub; [| lia ]. eapply le_trans.
           simpl. eapply max_env_getlist. eassumption.
           rewrite max_env_max_value_eq. lia. }      
        
      rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat.
      * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)).
        eapply plus_le_compat. lia. 
        eapply mult_le_compat_l. eapply plus_le_compat_l. eapply mult_le_compat_l. eassumption.
      * eassumption.
    - (* proj *) intro; intros. intro; intros.
      unfold inline_bound in *. 
      eapply le_trans. eapply plus_le_compat_r. eassumption.
      assert (Hleq : cost_exp_env G e1 (map_util.M.set x v1 rho1) <= cost_exp_env G (Eproj x t N y e1) rho1).
      { unfold cost_exp_env. eapply Max.max_lub.
        -- eapply le_trans; [| eapply Max.le_max_l ]. simpl. lia.
        -- eapply le_trans. eapply max_env_set.
           eapply Max.max_lub; [| lia ]. eapply le_trans; [| eapply Max.le_max_r ].
           eapply le_trans; [| eapply max_env_get; eauto ]. simpl.
           rewrite size_value_eq. eapply fold_left_max_in. eapply nthN_In. eassumption. }            
      rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat.
      * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)).
        eapply plus_le_compat. lia. 
        eapply mult_le_compat_l. eapply plus_le_compat_l. eapply mult_le_compat_l. eassumption.
      * eassumption.
    - (* fun *) intro; intros. intro; intros.
      unfold inline_bound in *.
      eapply le_trans. eapply plus_le_compat_r. eassumption.
      assert (Hleq : cost_exp_env G e1 (def_funs B1 B1 rho1 rho1) <= cost_exp_env G (Efun B1 e1) rho1). 
      { unfold cost_exp_env. eapply Max.max_lub.
        -- eapply le_trans; [| eapply Max.le_max_l ]. simpl. lia.
        -- eapply le_trans. eapply max_env_def_funs. simpl. lia. }
      rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat.
      * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)).
        eapply plus_le_compat. lia. 
        eapply mult_le_compat_l. eapply plus_le_compat_l. eassumption.
      * eassumption.
    - (* case hd *) intro; intros. intro; intros.
      unfold inline_bound in *.
      eapply le_trans. eapply plus_le_compat_r. eassumption.
      assert (Hleq : cost_exp_env e1 rho1 <= cost_exp_env (Ecase x ((t, e1) :: B1)) rho1).
      { unfold cost_exp_env. eapply Nat.max_le_compat_r.
        simpl. lia. }
      rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat.
      * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)).
        eapply plus_le_compat. lia. 
        eapply mult_le_compat_l. eapply plus_le_compat_l.
        simpl. eassumption.
      * eassumption.
    - (* case tl *) intro; intros. intro; intros.
      unfold inline_bound in *.
      eapply le_trans. eassumption.
      assert (Hleq : cost_exp_env (Ecase x B1) rho1 <= cost_exp_env (Ecase x ((t, e1) :: B1)) rho1).
      { unfold cost_exp_env. eapply Nat.max_le_compat_r. simpl. lia. }
      eapply plus_le_compat.
      * eapply mult_le_compat_l. eapply plus_le_compat_l. eassumption.
      * eassumption.
    - (* app *) intro; intros. intro; intros.  
      unfold inline_bound in *.
      eapply le_trans. eapply plus_le_compat_r. eassumption.
      assert (Hleq : cost_exp_env e1 rhoc1' <= cost_exp_env (Eapp x t xs) rho1).
      { unfold cost_exp_env at 2. eapply le_trans; [| eapply Max.le_max_r ].
        unfold cost_exp_env. eapply Nat.max_lub.
        - eapply le_trans; [| eapply max_env_get; eauto ]. simpl.
          eapply le_trans. 
          eapply size_fundefs_fun_in_fundefs. eapply find_def_correct. eassumption.
          lia.
        - eapply le_trans. eapply max_env_setlist. eassumption. eapply Nat.max_lub.
          + eapply le_trans. eapply max_env_getlist. eassumption. lia.
          + eapply le_trans; [| eapply max_env_get; eauto ]. simpl.
            eapply le_trans. eapply max_env_def_funs. rewrite max_env_max_value_eq. lia. }
      rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat.
      * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)).
        eapply plus_le_compat. lia. 
        eapply mult_le_compat_l. eapply plus_le_compat_l. eassumption.
      * eassumption.
    - (* letapp *) intro; intros. intro; intros.
      unfold inline_bound in *. admit. 
      (* eapply le_trans. eapply plus_le_compat_r. eassumption. *)
      (* assert (Hleq : cost_exp_env e1 rhoc1' <= cost_exp_env (Eapp x t xs) rho1). *)
      (* { unfold cost_exp_env at 2. eapply le_trans; [| eapply Max.le_max_r ]. *)
      (*   unfold cost_exp_env. eapply Nat.max_lub. *)
      (*   - eapply le_trans; [| eapply max_env_get; eauto ]. simpl. *)
      (*     eapply le_trans.  *)
      (*     eapply size_fundefs_fun_in_fundefs. eapply find_def_correct. eassumption. *)
      (*     lia. *)
      (*   - eapply le_trans. eapply max_env_setlist. eassumption. eapply Nat.max_lub. *)
      (*     + eapply le_trans. eapply max_env_getlist. eassumption. lia. *)
      (*     + eapply le_trans; [| eapply max_env_get; eauto ]. simpl. *)
      (*       eapply le_trans. eapply max_env_def_funs. rewrite max_env_max_value_eq. lia. } *)
      (* rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat. *)
      (* * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)). *)
      (*   eapply plus_le_compat. lia.  *)
      (*   eapply mult_le_compat_l. eapply plus_le_compat_l. eassumption. *)
      (* * eassumption. *)      
      (* admit. *)
    - (* letapp OOT *) intro; intros. intro; intros.
      unfold inline_bound in *.
      assert (Hleq : cost_exp_env e_b1 rhoc1' <= cost_exp_env (Eletapp x f t xs e1) rho1).
      { unfold cost_exp_env at 2. eapply le_trans; [| eapply Max.le_max_r ].
        unfold cost_exp_env. eapply Nat.max_lub.
        - eapply le_trans; [| eapply max_env_get; eauto ]. simpl.
          eapply le_trans. 
          eapply size_fundefs_fun_in_fundefs. eapply find_def_correct. eassumption.
          lia.
        - eapply le_trans. eapply max_env_setlist. eassumption. eapply Nat.max_lub.
          + eapply le_trans. eapply max_env_getlist. eassumption. lia.
          + eapply le_trans; [| eapply max_env_get; eauto ]. simpl.
            eapply le_trans. eapply max_env_def_funs. rewrite max_env_max_value_eq. lia. }      

      eapply le_trans. eapply plus_le_compat_r. eassumption.
      rewrite (plus_comm _ a), plus_assoc. eapply plus_le_compat.
      * rewrite (NPeano.Nat.mul_add_distr_r _ a). rewrite (plus_comm (_ * _) (_ * _)).
        eapply plus_le_compat. lia. 
        eapply mult_le_compat_l. eapply plus_le_compat_l. eassumption.
      * eassumption.
    - (* OOT *) intro; intros. intro; intros. unfold inline_bound. lia.
    - (* base *) intro; intros. intro; intros. unfold inline_bound. lia.
  Admitted.

  Lemma size_exp_ge_1 e :
    1 <= size_exp e.
  Proof.
    induction e using exp_ind'; simpl; try lia.
  Qed.
  
  Lemma cost_exp_size_exp e :
    cost e <= size_exp e.
  Proof.
    induction e using exp_ind'; simpl; try lia.
    assert (Hge := size_exp_ge_1 e). lia. 
  Qed.
  
  Lemma inline_bound_Hpost_zero e1 rho1 e2 rho2 :
    post_zero e1 rho1 e2 rho2 inline_bound.
  Proof.
    intro; intros. unfold inline_bound. simpl.
    eapply le_trans; [| eapply le_trans; [ eapply cost_exp_size_exp with (e := e1) |] ].
    lia. unfold cost_exp_env. lia.
  Qed.

  Lemma inline_bound_post_Eapp_l v t l rho1 x rho2 :
    post_Eapp_l inline_bound inline_bound v t l rho1 x rho2.
  Proof.
    intro; intros. unfold inline_bound in *.

    Require Import inline_letapp.
           (HEletapp : remove_steps_letapp cenv P1 P1 P1)
           (Eletapp' : remove_steps_letapp' cenv P1 P1 P1)
           (Eletapp_OOT : remove_steps_letapp_OOT cenv P1 P1)
           (Eletapp_OOT' : remove_steps_letapp_OOT' cenv P1 P1).

      
      
  Context (K : nat -> env -> exp -> nat) (* in essence, the number of inlined applications *)
          (M : nat -> env -> exp -> nat). (* The total overhead of all L6 transformations, generally different for each program *)
          
  (* TODO: maybe remove step-index k if not needed in bounds *)

  Definition upper_boundG (k : nat) : relation (exp * env *  nat) := 
    fun '(e1, rho1, c1) '(e2, rho2, c2) => c2 <= (M k rho1 e1) * (c1 + 1).

  Definition lower_boundG (k : nat) : relation (exp * env * nat) := 
    fun '(e1, rho1, c1) '(e2, rho2, c2) => c1 <= (K k rho1 e1) * (c2 + 1).

  (* + 1 is needed in the lower bound ecause sourvce might time out 
   * in say M steps but that may be 0 steps in target *)

  (* + 1 is not technically needed in the upper bound but it makes 
    things easier *)

  Definition boundG (k : nat) : relation (exp * env *  nat) :=
    relation_conjunction (lower_boundG k) (upper_boundG k).
 
  Definition upper_boundL (local : nat) (k : nat) (rho : env) (e : exp) : relation nat := 
    fun c1 c2 => c2 + local <= M k rho e * (c1 + 1).

  Definition lower_boundL (local : nat) (k : nat) (rho : env) (e : exp) : relation nat := 
    fun c1 c2 => c1 <= K k rho e * (c2 + 1 + local).

  Definition boundL (local : nat) (k : nat) (rho : env) (e : exp) : relation nat :=
    relation_conjunction (lower_boundL local k rho e) (upper_boundL local k rho e).
  
  (* bound properties *)
  
  Lemma boundL_0_implies_boundG k e1 e2 rho1 rho2 c1 c2 : 
    boundL 0 k rho1 e1 c1 c2 -> boundG k (e1, rho1, c1) (e2, rho2, c2).
  Proof.
    unfold boundL, boundG, lower_boundL, lower_boundG, upper_boundL, upper_boundG. 
    intros [H1 H2]. split; eauto.
    eapply le_trans. eassumption. 
    eapply Nat_as_OT.mul_le_mono_l. omega. 
    rewrite Nat_as_DT.add_0_r in H2. 
    eapply le_trans. eassumption. 
    eapply Nat_as_OT.mul_le_mono_l. omega.       
  Qed.
(*
  (* Divergence preservation *)
  Lemma cc_approx_exp_divergence pr cenv ct l e1 rho1 e2 rho2 :  
    (forall k, cc_approx_exp pr cenv ct k (boundL l) boundG (e1, rho1) (e2, rho2)) ->
    diverge pr cenv rho1 e1 -> 
    diverge pr cenv rho2 e2.
  Proof.
    intros Hexp H1 c2. assert (Hd := H1). specialize (H1 (K*(c2 + 1 + l))).
    edestruct Hexp as [v2 [c2' [Hs2 [Hp Hval]]]]. reflexivity. eassumption.
    destruct v2; try contradiction.
    assert (Hleq : c2 <= c2').
    { destruct Hp as [Hp1 Hp2]. unfold lower_boundL in Hp1.  
      eapply Nat_as_DT.mul_le_mono_pos_l in Hp1; eauto. omega. }
    eapply bstep_fuel_OOT_monotonic; eassumption. 
  Qed.
*)

End Bounds.

  
