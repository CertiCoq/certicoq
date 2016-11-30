(* Set library utilities. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

Require Import Coq.PArith.PArith Coq.MSets.MSetRBT Coq.Classes.Morphisms.

Module PS := MSetRBT.Make POrderedType.Positive_as_OT.

Import PS.

Ltac inv H := inversion H; clear H; subst.

(** Some set lemmas that might be useful *)
Lemma Subset_add s s' e :
  Subset s s' ->
  Subset (add e s) (add e s').
Proof.
  intros H e' HIn. eapply add_spec in HIn.
  inv HIn; eapply add_spec; eauto. 
Qed.

Lemma Subset_union_l s s' s'' :
  Subset s s' ->
  Subset (union s'' s) (union s'' s').
Proof.
  intros H e' HIn. eapply union_spec in HIn.
  inv HIn; eapply union_spec; eauto. 
Qed.

Lemma Subset_union_r s s' s'' :
  Subset s s' ->
  Subset (union s s'') (union s' s'').
Proof.
  intros H e' HIn. eapply union_spec in HIn.
  inv HIn; eapply union_spec; eauto. 
Qed.

Lemma Subset_refl s :
  Subset s s.
Proof.
  intros H e; eauto. 
Qed.

Lemma Subset_union_mon_l s s' s'' :
  Subset s s' ->
  Subset s (union s' s'').
Proof.
  intros H e' HIn.
  eapply union_spec; eauto. 
Qed.

Lemma Subset_union_mon_r s s' s'' :
  Subset s s' ->
  Subset s (union s'' s').
Proof.
  intros H e' HIn.
  eapply union_spec; eauto. 
Qed.

Definition union_list (s : PS.t) (l : list elt) : PS.t :=
  List.fold_left (fun set e => add e set) l s.

Lemma union_list_spec (s : PS.t) (l : list elt) : 
  forall (x : elt), In x (union_list s l) <->
                    In x s \/ List.In x l.
Proof.
  revert s; induction l as [| x xs IHxs ]; simpl;
  intros s e; split; intros H; eauto.
  - inv H; eauto. contradiction.
  - eapply IHxs in H. inversion H as [H1 | H2]; eauto.
    eapply add_spec in H1; inv H1; eauto.
  - inversion H as [H1 | [ H2 | H3 ]]; subst;
    eapply IHxs; solve [ left; eapply add_spec; eauto
                       | right; eauto ].
Qed.

Definition diff_list (s : PS.t) (l : list elt) : PS.t :=
  List.fold_left (fun set e => remove e set) l s.

Lemma diff_list_spec (s : PS.t) (l : list elt) : 
  forall (x : elt), In x (diff_list s l) <->
                    In x s /\ ~ List.In x l.
Proof.
  revert s; induction l as [| x xs IHxs ]; simpl;
  intros s e; split; intros H; eauto.
  - inv H; eauto.
  - eapply IHxs in H. inversion H as [H1 H2]; eauto.
    eapply remove_spec in H1; inv H1; split; eauto.
    intros [Hc | Hc]; congruence.
  - eapply IHxs. inversion H as [H1 H2]. split.
    * eapply remove_spec. split; eauto.
    * intros Hc. eauto.
Qed.


Lemma Subset_union_list s s' l :
  Subset s s' ->
  Subset (union_list s l) (union_list s' l).
Proof.
  intros H e' HIn. eapply union_list_spec in HIn.
  inv HIn; eapply union_list_spec; eauto. 
Qed.

Lemma eq_lists (l1 l2 : list elt) :
  Sorted.Sorted (fun x y : positive => (x ?= y)%positive = Lt) l1 ->
  Sorted.Sorted (fun x y : positive => (x ?= y)%positive = Lt) l2 ->
  SetoidList.NoDupA Logic.eq l1 ->
  SetoidList.NoDupA Logic.eq l2 ->
  (forall x, SetoidList.InA Logic.eq x l1 <-> SetoidList.InA Logic.eq x l2) ->
  l1 = l2.
Proof.
  revert l2. induction l1; intros l2  Hs1 Hs2 Hd1 Hd2 Helem.
  - destruct l2; eauto.
    exfalso. specialize (Helem e).
    assert (Hc : SetoidList.InA Logic.eq e nil)
      by (eapply Helem; constructor; eauto).
    inv Hc.
  - destruct l2; eauto.
    + exfalso. specialize (Helem a).
      assert (Hc : SetoidList.InA Logic.eq a nil)
        by (eapply Helem; constructor; eauto).
      inv Hc.
    + inv Hs1. inv Hs2. inv Hd1. inv Hd2.
      assert (Helem' :
                forall x, SetoidList.InA Logic.eq x l1 <->
                          SetoidList.InA Logic.eq x l2).
      { intros x. split; intros H. 
        - assert (HIn : SetoidList.InA Logic.eq x (e :: l2))
            by (eapply Helem; constructor 2; eauto).
          inv HIn; eauto.
          assert (HIn' : SetoidList.InA Logic.eq a (e :: l2))
            by (eapply Helem; constructor; eauto).
          assert (Hlt : (a ?= e)%positive = Lt).
          { eapply SetoidList.SortA_InfA_InA
            with (ltA := fun x y : positive => (x ?= y)%positive = Lt).
            apply eq_equivalence. eapply E.lt_strorder.
            apply E.lt_compat.
            apply H1. eauto. eauto. }
          inv HIn'. exfalso. eapply E.lt_strorder; eauto.
          assert (Hlt' : (e ?= a)%positive = Lt).
          { eapply SetoidList.SortA_InfA_InA
            with (ltA := fun x y : positive => (x ?= y)%positive = Lt).
            apply eq_equivalence. eapply E.lt_strorder.
            apply E.lt_compat.
            apply H3. eauto. eauto. }
          rewrite (@PositiveOrder.le_antisym e a); eauto; congruence.
        - assert (HIn : SetoidList.InA Logic.eq x (a :: l1))
            by (eapply Helem; constructor 2; eauto).
          inv HIn; eauto.
          assert (HIn' : SetoidList.InA Logic.eq e (a :: l1))
            by (eapply Helem; constructor; eauto).
          assert (Hlt : (e ?= a)%positive = Lt).
          { eapply SetoidList.SortA_InfA_InA
            with (ltA := fun x y : positive => (x ?= y)%positive = Lt).
            apply eq_equivalence. eapply E.lt_strorder.
            apply E.lt_compat.
            apply H3. eauto. eauto. }
          inv HIn'. exfalso. eapply E.lt_strorder; eauto.
          assert (Hlt' : (a ?= e)%positive = Lt).
          { eapply SetoidList.SortA_InfA_InA
            with (ltA := fun x y : positive => (x ?= y)%positive = Lt).
            apply eq_equivalence. eapply E.lt_strorder.
            apply E.lt_compat.
            apply H1. eauto. eauto. }
          rewrite (@PositiveOrder.le_antisym a e); eauto; congruence. }
      f_equal; eauto.  
      assert (HIn' : SetoidList.InA Logic.eq e (a :: l1)) by
          (eapply Helem; constructor; eauto).
      assert (HIn : SetoidList.InA Logic.eq a (e :: l2)) by
          (eapply Helem; constructor; eauto).
      inv HIn'; try now apply Heq. inv HIn; eauto.
      assert (Hlt : (a ?= e)%positive = Lt).
      { eapply SetoidList.SortA_InfA_InA
        with (ltA := fun x y : positive => (x ?= y)%positive = Lt).
        apply eq_equivalence. eapply E.lt_strorder.
        apply E.lt_compat.
        apply H1. eauto. eauto. }
      inv HIn; eauto.
      assert (Hlt' : (e ?= a)%positive = Lt).
      { eapply SetoidList.SortA_InfA_InA
        with (ltA := fun x y : positive => (x ?= y)%positive = Lt).
        apply eq_equivalence. eapply E.lt_strorder.
        apply E.lt_compat.
        apply H3. eauto. eauto. }
      rewrite (@PositiveOrder.le_antisym a e); eauto; congruence.
Qed.

Lemma elements_eq s1 s2 :
  eq s1 s2 ->
  elements s1 = elements s2.
Proof.
  intros H. apply eq_lists.
  apply elements_spec2. apply elements_spec2.
  apply elements_spec2w. apply elements_spec2w.
  intros x'; split; intros H';
  eapply elements_spec1; eapply elements_spec1 in H';
  eapply H; eauto.
Qed.

Ltac apply_set_specs_ctx :=
  match goal with
    | [ H : In _ (add _ _) |- _ ] =>
      apply add_spec in H; inv H
    | [ H : In _ (remove _ _) |- _ ] =>
      apply remove_spec in H; inv H
    | [ H : In _  (singleton _ ) |- _ ] =>
      apply singleton_spec in H; subst
    | [ H : In _ (union _ _) |- _ ] =>
      apply union_spec in H; inv H
    | [ H : In _ (diff _ _) |- _ ] =>
      apply diff_spec in H; inv H
    | [ H : In _ (diff_list _ _) |- _ ] =>
      apply diff_list_spec in H; inv H
    | [ H : In _ (union_list _ _) |- _ ] =>
      apply union_list_spec in H; inv H
  end.

Ltac apply_set_specs :=
  match goal with
    | [ |- In _ (add _ _) ] =>
      apply add_spec
    | [ |- In _ (remove _ _) ] =>
      apply remove_spec; split
    | [ |- In _  (singleton _ ) ] =>
      apply singleton_spec
    | [ |- In _ (union _ _) ] =>
      apply union_spec
    | [ |- In _ (diff _ _) ] =>
      apply diff_spec; split
    | [ |- In _ (diff_list _ _) ] =>
      apply diff_list_spec; split
    | [ |- In _ (union_list _ _) ] =>
      apply union_list_spec
  end.

Lemma Subset_Equal s s' :
  Subset s s' ->
  Subset s' s ->
  Equal s s'.
Proof.
  intros H1 H2 x. split; eauto.
Qed.

Lemma Equal_Subset_l s s' :
  Equal s s' ->
  Subset s s'.
Proof.
  intros H1 x Hin. apply H1; eauto.
Qed.

Lemma Equal_Subset_r s s' :
  Equal s s' ->
  Subset s' s.
Proof.
  intros H1 x Hin. apply H1; eauto.
Qed.

Lemma union_assoc s1 s2 s3 :
  Equal (union (union s1 s2) s3) (union s1 (union s2 s3)).
Proof.
  split; intros HIn; repeat apply_set_specs_ctx; apply_set_specs; eauto;
  solve [ right; apply_set_specs; eauto | left; apply_set_specs; eauto ].
Qed.

Lemma union_sym s1 s2 :
  Equal (union s1 s2) (union s2 s1).
Proof.
  split; intros HIn; repeat apply_set_specs_ctx; apply_set_specs; eauto;
  solve [ right; apply_set_specs; eauto | left; apply_set_specs; eauto ].
Qed.

Instance In_proper x :  Proper (Equal ==> iff) (In x).
Proof.
  constructor; intros Hin; eapply H; eauto.
Qed.

Instance union_proper_r x :  Proper (Equal ==> Equal) (union x).
Proof.
  constructor; intros Hin; apply_set_specs_ctx; apply_set_specs; eauto;
  right; apply H; eauto.
Qed.
