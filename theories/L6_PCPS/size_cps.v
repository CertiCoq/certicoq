(* Size of CPS term, values, environments, etc. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2017
 *)

From Coq Require Import ZArith List.
From ExtLib Require Import Structures.Monads Data.Monads.StateMonad.
From Common Require Import AstCommon.
From L6 Require Import List_util cps.

Require Import Libraries.Maps.

Import MonadNotation ListNotations.

Open Scope monad_scope.


(** * Size of CPS terms, values and environments, needed to express the upper bound on the execution cost of certain transformations *)

(** The size of CPS expressions. Right now we only count the number of
  * variables in a program (free or not), the number of functions and
  * the number of function definition blocks *)
Fixpoint sizeOf_exp (e : exp) : nat :=
  match e with
    | Econstr x _ ys e => length ys + sizeOf_exp e
    | Ecase x l =>
      1  + (fix sizeOf_l l :=
              match l with
                | [] => 0
                | (t, e) :: l => sizeOf_exp e + sizeOf_l l
              end) l
    | Eproj x _ _ y e => 1 + sizeOf_exp e
    | Efun B e => 1 + sizeOf_fundefs B + sizeOf_exp e
    | Eapp x _ ys => 1 + length ys
    | Eprim x _ ys e => length ys + sizeOf_exp e
    | Ehalt x => 1
  end
with sizeOf_fundefs (B : fundefs) : nat := 
       match B with
         | Fcons _ _ xs e B =>
           1 + sizeOf_exp e + sizeOf_fundefs B
         | Fnil => 0
       end.


(* Compute the maximum of a tree given a measure function *)
Definition max_ptree_with_measure {A} (f : A -> nat) (i : nat) (rho : M.t A) :=
  M.fold (fun c _ v => max c (f v)) rho i.

Lemma Mfold_monotonic {A} f1 f2 (rho : M.t A) n1 n2 :
  (forall x1 x1' x2 x3, x1 <= x1' -> f1 x1 x2 x3 <= f2 x1' x2 x3) ->
  n1 <= n2 ->
  M.fold f1 rho n1 <= M.fold f2 rho n2.
Proof.
  rewrite !M.fold_spec.
  intros. eapply fold_left_monotonic; eauto.
Qed.

Lemma max_ptree_with_measure_spec1 {A} (f : A -> nat) i rho x v :
  rho ! x = Some v ->
  f v <= max_ptree_with_measure f i rho. 
Proof.
  intros Hget. unfold max_ptree_with_measure.
  rewrite M.fold_spec.
  assert (List.In (x, v) (M.elements rho))
    by (eapply PTree.elements_correct; eauto).
  revert H. generalize (M.elements rho).
  intros l Hin. induction l. now inv Hin.
  inv Hin.
  - simpl. eapply le_trans. now apply Max.le_max_r.
    eapply fold_left_extensive.
    intros [y u] n; simpl. now apply Max.le_max_l.
  - simpl. eapply le_trans. now eapply IHl; eauto. 
    eapply fold_left_monotonic.
    intros. now eapply NPeano.Nat.max_le_compat_r; eauto.
    now apply Max.le_max_l.
Qed.


(** Stratified size for values *)
Fixpoint sizeOf_val' (i : nat) (v : val) : nat :=
  match i with
    | 0 => 0
    | S i' =>
      (fix aux v : nat :=
       let sizeOf_env rho := max_ptree_with_measure (sizeOf_val' i') 0 rho in
       match v with
         | Vconstr _ vs => max_list_nat_with_measure aux 0 vs
         | Vfun rho B f =>
           max (sizeOf_fundefs B) (sizeOf_env rho)
         (* Ignore Vint, it's not used *)
         | Vint x => 0
       end) v
  end.

(** Size of environments.
  * The size of an environment is the size of the maximum value stored in it *)
Definition sizeOf_env i rho := max_ptree_with_measure (sizeOf_val' i) 0 rho.

(** Equivalent definition *)
Definition sizeOf_val (i : nat) (v : val) : nat :=
  match i with
    | 0 => 0
    | S i' =>
      match v with
        | Vconstr _ vs =>
          max_list_nat_with_measure (sizeOf_val' i) 0 vs
        | Vfun rho B f =>
          max (sizeOf_fundefs B) (sizeOf_env i' rho)           
        | Vint x => 0
      end
  end.

Lemma sizeOf_val_eq i v :
  sizeOf_val' i v = sizeOf_val i v.
Proof.
  revert v; induction i; eauto.
  induction v using val_ind'; eauto.
Qed.

Opaque sizeOf_val'.

Lemma sizeOf_val_Vconstr_unfold i t v l:
  sizeOf_val i (Vconstr t (v :: l)) =
  max (sizeOf_val i v) (sizeOf_val i (Vconstr t l)).
Proof.
  destruct i; simpl (sizeOf_val _ (Vconstr t _)); eauto.
  rewrite <- (Max.max_0_l (sizeOf_val' (S i) v)).
  unfold max_list_nat_with_measure.
  rewrite (fold_left_comm (fun (c : nat) (v0 : val) => Init.Nat.max c (sizeOf_val' (S i) v0))); eauto.
  rewrite Max.max_comm, sizeOf_val_eq. reflexivity.
  intros. now rewrite <- !Max.max_assoc, (Max.max_comm (sizeOf_val' (S i) y)).
Qed.

Lemma sizeOf_val_monotic i i' v :
  i <= i' ->
  sizeOf_val i v <= sizeOf_val i' v.
Proof.
  revert i' v. induction i as [i IHi] using lt_wf_rec1; intros i' v.
  destruct i; try (simpl; omega). intros Hlt.
  induction v using val_ind'.
  - destruct i'; simpl; omega.
  - destruct i'; try now (simpl; omega).
    rewrite !sizeOf_val_Vconstr_unfold.
    eapply NPeano.Nat.max_le_compat; eauto. 
  - destruct i'; try now (simpl; omega).
    eapply NPeano.Nat.max_le_compat; eauto.
    unfold sizeOf_env. eapply Mfold_monotonic; eauto.
    intros. eapply NPeano.Nat.max_le_compat; eauto.
    rewrite !sizeOf_val_eq; eapply IHi; omega.
  - destruct i'; simpl; omega.
Qed.

Lemma sizeOf_env_monotic i i' v :
  i <= i' ->
  sizeOf_env i v <= sizeOf_env i' v.
Proof.
  intros Hi. unfold sizeOf_env.
  eapply Mfold_monotonic; eauto.
  intros. eapply NPeano.Nat.max_le_compat; eauto.
  rewrite !sizeOf_val_eq. now eapply sizeOf_val_monotic.
Qed.

(** Number of function definitions *)
Fixpoint numOf_fundefs (B : fundefs) : nat := 
  match B with
    | Fcons _ _ xs e B =>
      1 + numOf_fundefs B
    | Fnil => 0
  end.

(** Number of function definitions in an expression *)
Fixpoint numOf_fundefs_in_exp (e : exp) : nat :=
  match e with
    | Econstr x _ ys e => numOf_fundefs_in_exp e
    | Ecase x l =>
      1  + (fix num l :=
              match l with
                | [] => 0
                | (t, e) :: l => numOf_fundefs_in_exp e + num l
              end) l
    | Eproj x _ _ y e => 1 + numOf_fundefs_in_exp e
    | Efun B e => numOf_fundefs_in_fundefs B + numOf_fundefs_in_exp e
    | Eapp x _ ys => 0
    | Eprim x _ ys e => numOf_fundefs_in_exp e
    | Ehalt x => 0
  end
with numOf_fundefs_in_fundefs (B : fundefs) : nat :=
  match B with
    | Fcons _ _ xs e B =>
      1 + numOf_fundefs_in_exp e + numOf_fundefs_in_fundefs B
    | Fnil => 0
  end.

Lemma numOf_fundefs_le_sizeOf_fundefs B :
  numOf_fundefs B <= sizeOf_fundefs B.
Proof.
  induction B; eauto; simpl; omega.
Qed.

Lemma sizeOf_env_set k rho x v :
  sizeOf_env k (M.set x v rho) = max (sizeOf_val k v) (sizeOf_env k rho).
Proof.
(* Obvious but seems painful, admitting for now *)
Admitted.

Lemma max_list_nat_acc_spec {A} (xs : list A) f acc :
  max_list_nat_with_measure f acc xs =
  max acc (max_list_nat_with_measure f 0 xs).
Proof.
  rewrite <- (Max.max_0_r acc) at 1. generalize 0.
  revert acc. induction xs; intros acc n; simpl; eauto.
  rewrite <- Max.max_assoc. eauto.
Qed.

Lemma sizeOf_env_setlist k rho rho' xs vs :
  setlist xs vs rho = Some rho' ->
  sizeOf_env k rho' = max (max_list_nat_with_measure (sizeOf_val k) 0 vs) (sizeOf_env k rho).
Proof.
  revert vs rho rho'. induction xs; intros vs rho rho' Hset.
  - destruct vs; try discriminate. inv Hset.
    reflexivity.
  - destruct vs; try discriminate.
    simpl in Hset. destruct (setlist xs vs rho) eqn:Hset'; try discriminate.
    inv Hset. rewrite sizeOf_env_set; simpl.
    rewrite max_list_nat_acc_spec.
    rewrite <- Max.max_assoc. eapply NPeano.Nat.max_compat. reflexivity.
    eauto.
Qed.

Lemma sizeOf_env_get k rho x v :
  rho ! x = Some v ->
  sizeOf_val k v <= sizeOf_env k rho.
Proof.
  intros Hget. 
  unfold sizeOf_env. rewrite <- sizeOf_val_eq.
  eapply max_ptree_with_measure_spec1.
  eassumption.
Qed.

Lemma sizeOf_env_getlist k rho xs vs :
  getlist xs rho = Some vs ->
  max_list_nat_with_measure (sizeOf_val k) 0 vs  <= sizeOf_env k rho.
Proof.
  revert vs. induction xs; intros vs Hgetl. 
  - destruct vs; try discriminate; simpl; omega.
  - simpl in Hgetl.
    destruct (rho ! a) eqn:Hgeta; try discriminate.
    destruct (getlist xs rho) eqn:Hgetl'; try discriminate.
    destruct vs; try discriminate. inv Hgetl. simpl.
    eapply le_trans.
    + rewrite <- (Max.max_0_l (sizeOf_val k v0)).
      unfold max_list_nat_with_measure.
      rewrite (fold_left_comm (fun (c : nat) (v : val) => Init.Nat.max c (sizeOf_val k v))).
      eapply NPeano.Nat.max_le_compat. eapply IHxs. reflexivity.
      eapply sizeOf_env_get. eassumption.
      intros x v1 v2. rewrite <- !Max.max_assoc, (Max.max_comm (sizeOf_val k v1)).
      reflexivity.
    + eapply NPeano.Nat.max_lub; omega.
Qed.

Lemma sizeOf_env_set_constr k rho xs c vs y:
  getlist xs rho = Some vs ->
  sizeOf_env k (M.set y (Vconstr c vs) rho) = sizeOf_env k rho.
Proof.
  intros Hget. rewrite sizeOf_env_set.
  assert (Hlow : sizeOf_env k rho <= max (sizeOf_val k (Vconstr c vs)) (sizeOf_env k rho))
    by apply Max.le_max_r.
  assert (Hhigh :  max (sizeOf_val k (Vconstr c vs)) (sizeOf_env k rho) <= sizeOf_env k rho).
  { eapply NPeano.Nat.max_lub; try omega.
    destruct k; simpl. omega.
    unfold max_list_nat_with_measure. eapply le_trans.
    eapply fold_left_monotonic; [| now eauto ].
    intros. rewrite sizeOf_val_eq. eapply NPeano.Nat.max_le_compat.
    now eauto. now eauto.
    eapply (sizeOf_env_getlist (S k)). eassumption. }
  omega.
Qed.

Lemma sizeOf_env_set_proj k rho x c vs y v :
  M.get x rho = Some (Vconstr c vs) ->
  List.In v vs ->
  sizeOf_env k (M.set y v rho) = sizeOf_env k rho.
Proof.
  intros Hget Hin. rewrite sizeOf_env_set.
  assert (Hlow : sizeOf_env k rho <= max (sizeOf_val k v) (sizeOf_env k rho))
    by apply Max.le_max_r.
  assert (Hhigh :  max (sizeOf_val k v) (sizeOf_env k rho) <= sizeOf_env k rho).
  { eapply NPeano.Nat.max_lub; try omega.
    eapply le_trans; [ | now eapply sizeOf_env_get; eauto ].
    destruct k; eauto. simpl (sizeOf_val (S k) (Vconstr c vs)).
    rewrite <- sizeOf_val_eq.
    eapply max_list_nat_spec2. eassumption. }
  omega.
Qed.

Lemma sizeOf_env_def_funs k rho B B' :
  sizeOf_env k (def_funs B B' rho rho) <=
  max (sizeOf_env k rho) (sizeOf_fundefs B).
Proof.
  induction B'; simpl.
  - rewrite sizeOf_env_set. destruct k; simpl; eauto.
    eapply Nat.max_lub; eauto.
    rewrite Max.max_comm. eapply NPeano.Nat.max_le_compat; eauto.
    eapply sizeOf_env_monotic. omega.
  - eapply Max.le_max_l.
Qed.

Lemma sizeOf_env_get_set k rho1 rho2 x y v :
  rho1 ! x = Some v ->
  sizeOf_env k (M.set y v rho2) <= max (sizeOf_env k rho1) (sizeOf_env k rho2).
Proof.
  intros H. rewrite sizeOf_env_set.
  eapply NPeano.Nat.max_le_compat; eauto.
  eapply sizeOf_env_get; eauto.
Qed.

(* Lemma fun_in_fundefs_sizeOf_exp B f tau xs e : *)
(*   fun_in_fundefs B (f, tau, xs, e) -> *)
(*   sizeOf_exp e <= sizeOf_fundefs B. *)
(* Proof. *)
(*   intros Hin. induction B; inv Hin. *)
(*   - inv H. simpl; omega. *)
(*   - eapply le_trans. eapply IHB; eauto. *)
(*     simpl. omega.   *)
(* Qed. *)


Lemma sizeOf_env_getlist_setlist k rho1 rho2 rho2' xs ys vs :
  getlist xs rho1 = Some vs ->
  setlist ys vs rho2 = Some rho2' ->
  sizeOf_env k rho2' <= max (sizeOf_env k rho1) (sizeOf_env k rho2).
Proof.
  intros Hget Hset. erewrite sizeOf_env_setlist; eauto.
  eapply NPeano.Nat.max_le_compat; eauto.
  eapply sizeOf_env_getlist; eauto.
Qed.

Lemma max_list_nat_monotonic (A : Type) (f1 f2 : A -> nat) (l : list A) (n1 n2 : nat) :
  (forall (x1 : A), f1 x1 <= f2 x1) ->
  n1 <= n2 ->
  max_list_nat_with_measure f1 n1 l <= max_list_nat_with_measure f2 n2 l.
Proof.
  unfold max_list_nat_with_measure.
  intros. eapply fold_left_monotonic; eauto.
  intros. eapply NPeano.Nat.max_le_compat; eauto.
Qed.

Lemma sizeOf_env_set_app k rho rho' rho'' f xs B f' ys e vs :
  k > 0 ->
  rho ! f = Some (Vfun rho' B f') ->
  getlist xs rho = Some vs ->
  sizeOf_exp e <= sizeOf_fundefs B ->
  setlist ys vs (def_funs B B rho' rho') = Some rho'' ->
  max (sizeOf_exp e) (sizeOf_env (k - 1) rho'') <= sizeOf_env k rho.
Proof.
  intros Hgt Hget Hget' Hf Hset.
  erewrite sizeOf_env_setlist; eauto.
  rewrite (Max.max_comm (max_list_nat_with_measure _ _ _) _), Max.max_assoc.
  eapply Nat.max_lub.
  - eapply le_trans; [| now eapply sizeOf_env_get; eauto ].
    destruct k; try omega. simpl. rewrite <- minus_n_O.
    eapply le_trans.
    + eapply NPeano.Nat.max_le_compat.
      * eassumption.
      * eapply sizeOf_env_def_funs.
    + rewrite (Max.max_comm (sizeOf_env k rho')),
      Max.max_assoc, Max.max_idempotent; eauto.
  - eapply le_trans. eapply (max_list_nat_monotonic _ _ (sizeOf_val k)); eauto.
    intros. eapply sizeOf_val_monotic. omega.
    eapply sizeOf_env_getlist; eauto.
Qed.