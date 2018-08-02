(* Set library utilities. Part of the CertiCoq project.
 * Author: Zoe Paraskevopoulou, 2016
 *)

From Coq Require Import PArith.PArith MSets.MSetRBT Classes.Morphisms Sets.Ensembles
         Relations.Relations Lists.List Lists.SetoidList Permutation Omega.
From L6 Require Import tactics Ensembles_util List_util functions.

Module PS := MSetRBT.Make POrderedType.Positive_as_OT.

Import PS.

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
  Equal s1 s2 ->
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


(* Equality morphisms *)

Instance Proper_In x :  Proper (Equal ==> iff) (In x).
Proof.
  constructor; intros Hin; eapply H; eauto.
Qed.

Instance Proper_union_r x :  Proper (Equal ==> Equal) (union x).
Proof.
  constructor; intros Hin; apply_set_specs_ctx; apply_set_specs; eauto;
  right; apply H; eauto.
Qed.

Instance Proper_union_l :  Proper (Equal ==> Logic.eq ==> Equal) union.
Proof.
  constructor; intros; apply_set_specs_ctx; apply_set_specs; eauto;
  left; apply H; eauto.
Qed.

Instance Proper_elements :  Proper (Equal ==> Logic.eq) elements.
Proof.
  intros x y Heq; eauto. eapply elements_eq. eassumption.
Qed.

Instance Proper_carinal :  Proper (Equal ==> Logic.eq) cardinal.
Proof.
  intros x y Heq; eauto. rewrite !cardinal_spec, Heq. reflexivity.
Qed.

Instance union_proper_l :  Proper (PS.Equal ==> eq ==> PS.Equal) PS.union.
Proof.
  intros x y Heq1 x' y' Heq2; subst.
  intros z; split; intros Hin; eapply PS.union_spec in Hin;
  inv Hin; eapply PS.union_spec; now firstorder.
Qed.

Instance diff_proper_l :  Proper (PS.Equal ==> eq ==> PS.Equal) PS.diff.
Proof.
  intros x y Heq1 x' y' Heq2; subst.
  intros z; split; intros Hin; eapply PS.diff_spec in Hin;
  inv Hin; eapply PS.diff_spec; now firstorder.
Qed.

Instance diff_proper_r :  Proper (eq ==> PS.Equal ==> PS.Equal) PS.diff.
Proof.
  intros x y Heq1 x' y' Heq2; subst.
  intros z; split; intros Hin; eapply PS.diff_spec in Hin;
  inv Hin; eapply PS.diff_spec; now firstorder.
Qed.


Lemma PS_nonempty_add (S : PS.t) :
  PS.cardinal S > 0 ->
  exists x S', ~ PS.In x S' /\ PS.Equal S (PS.add x S'). 
Proof.
  intros Hsize. destruct (PS.elements S) eqn:Helem. 
  - rewrite PS.cardinal_spec, Helem in Hsize; eauto. simpl in *. omega.
  - eexists e, (PS.remove e S). split.

    intros Hin. eapply PS.remove_spec in Hin.
    inv Hin; eauto.
    
    intros x. split; intros Hin.
    destruct (Coqlib.peq x e); subst.
    + eapply PS.add_spec. now left.
    + eapply PS.add_spec. right.
      eapply PS.remove_spec. split; eauto.
    + eapply PS.add_spec in Hin. inv Hin; subst.
      eapply PS.elements_spec1. rewrite Helem.
      now constructor.
      eapply PS.remove_spec in H. inv H; eauto.
Qed.

Lemma PS_add_elements S x : 
  ~ PS.In x S ->
  Permutation (x :: PS.elements S) (PS.elements (PS.add x S)).
Proof.
  intros Hnin. 
  eapply NoDup_Permutation.
  - constructor. intros Hin. eapply Hnin.
    eapply PS.elements_spec1. eapply In_InA; try eassumption.
    now eauto with typeclass_instances.
    eapply NoDupA_NoDup. eapply PS.elements_spec2w.
  - eapply NoDupA_NoDup. eapply PS.elements_spec2w.
  - intros y. split.
    + intros Hin. inv Hin.

      assert (HinA : InA Logic.eq y (PS.elements (PS.add y S))).
      { eapply PS.elements_spec1. eapply PS.add_spec. now left. }
      edestruct InA_alt as [[z [Heq1 Hin]] _]. eassumption.
      subst. eassumption.

      eapply In_InA in H. 
      assert (HinA : InA Logic.eq y (PS.elements (PS.add x S))).
      { eapply PS.elements_spec1. eapply PS.add_spec. right.
        eapply PS.elements_spec1 in H. eassumption. }

      edestruct InA_alt as [[z [Heq1 Hin]] _]. eassumption. subst.
      subst. eassumption.

      now eauto with typeclass_instances.
    + intros Hin.
      eapply In_InA in Hin.

      eapply PS.elements_spec1 in Hin. 
      eapply PS.add_spec in Hin. inv Hin.
      now constructor.
      constructor 2.

      assert (HinA : InA Logic.eq y (PS.elements S)).
      { eapply PS.elements_spec1. eassumption. }

      edestruct InA_alt as [[z [Heq1 Hin]] _]. eassumption.
      subst. eassumption.

      now eauto with typeclass_instances.
Qed. 

Lemma PS_cardinal_empty S :
  PS.cardinal S = 0 -> PS.Equal S PS.empty. 
Proof.
  intros Heq x. rewrite PS.cardinal_spec in Heq.
  split; intros Hin.
  - eapply PS.elements_spec1 in Hin.
    destruct (PS.elements S) as [| x1 l1 ]. now inv Hin.
    now inv Heq.
  - inv Hin.
Qed.

Lemma PS_cardinal_add (S : PS.t) x :
  ~ PS.In x S ->
  1 + PS.cardinal S = PS.cardinal (PS.add x S).
Proof. 
  intros Hnin. rewrite !PS.cardinal_spec.
  erewrite (@Permutation_length _ (PS.elements (PS.add x S)));
    [| symmetry; now apply PS_add_elements ]. 
  reflexivity.
Qed.

Lemma PS_ind (P : PS.t -> Prop) {_ : Proper (PS.Equal ==> iff) P} :
  P PS.empty ->
  (forall x S, ~ PS.In x S -> P S -> P (PS.add x S)) ->
  (forall S, P S).
Proof.
  intros Hemp IH S.
  assert (Hs: PS.cardinal S = PS.cardinal S) by reflexivity.
  revert Hs.
  generalize (PS.cardinal S) at 1. intros n.
  revert S. induction n; intros S Heq.
  - eapply H. eapply PS_cardinal_empty. now eauto. eassumption.
  - edestruct PS_nonempty_add as (e & S' & HninS & HeqS).
    rewrite <- Heq. omega. 
    eapply H. eassumption. eapply IH. 
    eassumption. eapply IHn.
    rewrite HeqS in Heq. simpl in Heq. 
    rewrite <- PS_cardinal_add in Heq. omega.
    eassumption.
Qed.


(** * Coercion from set *)

Definition FromSet (s : PS.t) : Ensemble positive :=
  FromList (elements s).

Lemma FromSet_sound (S : Ensemble positive) (s : PS.t) x :
  S <--> FromSet s ->
  x \in S -> In x s.
Proof. 
  intros Heq Hin. eapply Heq in Hin.
  unfold FromSet, FromList, Ensembles.In in Hin.
  eapply In_InA in Hin. eapply PS.elements_spec1 in Hin.
  eassumption.
  now eapply PS.E.eq_equiv.
Qed.

Lemma FromSet_complete (S : Ensemble positive) (s : PS.t) x :
  S <--> FromSet s ->
  In x s -> x \in S.
Proof. 
  intros Heq Hin.
  eapply Heq. unfold FromSet, FromList, Ensembles.In.
  eapply PS.elements_spec1 in Hin. eapply InA_alt in Hin.
  edestruct Hin as [y [Heq' Hin']]. subst. eassumption.
Qed.

Lemma FromSet_union s1 s2 :
  FromSet (PS.union s1 s2) <--> FromSet s1 :|: FromSet s2.
Proof.
  unfold FromSet, FromList. split; intros x Hin; unfold Ensembles.In in *; simpl in *.
  - eapply In_InA with (eqA := Logic.eq) in Hin; eauto with typeclass_instances. 
    eapply PS.elements_spec1 in Hin. eapply PS.union_spec in Hin.
    inv Hin; [ left | right ]; unfold In; simpl.
    + assert (HinA: InA Logic.eq x (PS.elements s1)).
      { eapply PS.elements_spec1. eassumption. }
      eapply InA_alt in HinA. destruct HinA as [y [Heq Hin]]. subst; eauto.
    + assert (HinA: InA Logic.eq x (PS.elements s2)).
      { eapply PS.elements_spec1. eassumption. }
      eapply InA_alt in HinA. destruct HinA as [y [Heq Hin]]. subst; eauto.
  - assert (HinA: InA Logic.eq x (PS.elements (PS.union s1 s2))).
    { eapply PS.elements_spec1. eapply PS.union_spec.
      inv Hin; unfold Ensembles.In in *; simpl in *.
      + eapply In_InA with (eqA := Logic.eq) in H; eauto with typeclass_instances. 
        eapply PS.elements_spec1 in H. now left.
      + eapply In_InA with (eqA := Logic.eq) in H; eauto with typeclass_instances. 
        eapply PS.elements_spec1 in H. now right. }
    eapply InA_alt in HinA. destruct HinA as [y [Heq Hin']]. subst; eauto.
Qed.

Lemma FromSet_diff s1 s2 :
  FromSet (PS.diff s1 s2) <--> FromSet s1 \\ FromSet s2.
Proof.
  unfold FromSet, FromList. split; intros x Hin; unfold Ensembles.In in *; simpl in *.
  - eapply In_InA with (eqA := Logic.eq) in Hin; eauto with typeclass_instances. 
    eapply PS.elements_spec1 in Hin. eapply PS.diff_spec in Hin.
    inv Hin. constructor.
    + assert (HinA: InA Logic.eq x (PS.elements s1)).
      { eapply PS.elements_spec1. eassumption. }
      eapply InA_alt in HinA. destruct HinA as [y [Heq Hin]]. subst; eauto.
    + intros Hin. simpl in Hin. unfold Ensembles.In in Hin.
      eapply In_InA with (eqA := Logic.eq) in Hin; eauto with typeclass_instances.
      eapply PS.elements_spec1 in Hin; eauto.
  - assert (HinA: InA Logic.eq x (PS.elements (PS.diff s1 s2))).
    { eapply PS.elements_spec1. eapply PS.diff_spec.
      inv Hin; unfold Ensembles.In in *; simpl in *. split.
      + eapply In_InA with (eqA := Logic.eq) in H; eauto with typeclass_instances. 
        eapply PS.elements_spec1 in H. eassumption.
      + intros Hin. eapply PS.elements_spec1 in Hin.
        eapply InA_alt in Hin. destruct Hin as [y [Heq Hin]].
        subst; eauto. }
    eapply InA_alt in HinA. destruct HinA as [y [Heq Hin']]. subst; eauto.
Qed.

Lemma FromSet_add x s :
  FromSet (PS.add x s) <-->  x |: FromSet s.
Proof.
  unfold FromSet, FromList. split; intros z Hin; unfold Ensembles.In in *; simpl in *.
  - eapply In_InA with (eqA := Logic.eq) in Hin; eauto with typeclass_instances. 
    eapply PS.elements_spec1 in Hin. eapply PS.add_spec in Hin.
    inv Hin; [ left | right ]; unfold In; simpl.
    + reflexivity.
    + assert (HinA: InA Logic.eq z (PS.elements s)).
      { eapply PS.elements_spec1. eassumption. }
      eapply InA_alt in HinA. destruct HinA as [y [Heq Hin]]. subst; eauto.
  - assert (HinA: InA Logic.eq z (PS.elements (PS.add x s))).
    { eapply PS.elements_spec1. eapply PS.add_spec.
      inv Hin; unfold Ensembles.In in *; simpl in *.
      + left. inv H. reflexivity.
      + eapply In_InA with (eqA := Logic.eq) in H; eauto with typeclass_instances.
        eapply PS.elements_spec1 in H. now right. }
    eapply InA_alt in HinA. destruct HinA as [y [Heq Hin']]. subst; eauto.
Qed.

Lemma FromSet_union_list s l:
  FromSet (union_list s l) <--> FromSet s :|: FromList l.
Proof.
  revert s; induction l; intros s; simpl.
  - rewrite FromList_nil, Union_Empty_set_neut_r.
    reflexivity.
  - rewrite IHl, FromSet_add, FromList_cons, Union_assoc, (Union_commut (FromSet s) [set a]). 
    reflexivity.
Qed.

Lemma FromSet_empty :
  FromSet PS.empty <--> Empty_set _.
Proof.
  split; intros x Hin; now inv Hin.
Qed.

Lemma FromSet_singleton x :
  FromSet (PS.singleton x) <--> [set x].
Proof.
  split; intros z Hin; unfold FromSet, FromList, Ensembles.In in *.
  - eapply In_InA in Hin. eapply PS.elements_spec1 in Hin.
    eapply PS.singleton_spec in Hin. subst. reflexivity.
    now eauto with typeclass_instances.
  - inv Hin. eapply InA_In.  eapply PS.elements_spec1.
    eapply PS.singleton_spec. reflexivity.
Qed.

Lemma FromSet_cardinal_empty s :
  PS.cardinal s = 0 -> FromSet s <--> Empty_set _.
Proof.
  rewrite PS.cardinal_spec. intros Hc.
  split; intros x Hin; try now inv Hin. 
  unfold FromSet, Ensembles.In, FromList in Hin.
  eapply In_InA with (eqA := Logic.eq) in Hin;
    eauto with typeclass_instances.
  destruct (PS.elements s); try congruence.
  now inv Hin. now inv Hc.
Qed.

Instance Decidable_FromSet (s : PS.t) : Decidable (FromSet s).
Proof.
  unfold FromSet.
  eapply Ensembles_util.Decidable_FromList. 
Qed.


Instance Proper_From_set : Proper (PS.Equal ==> Same_set _) FromSet.
Proof.
  constructor.
  - intros z Hin. eapply FromSet_sound in Hin; [| reflexivity ].
    eapply FromSet_complete. reflexivity. eapply H. eassumption.
  - intros z Hin. eapply FromSet_sound in Hin; [| reflexivity ].
    eapply FromSet_complete. reflexivity. eapply H. eassumption.
Qed.

Lemma Same_set_From_set (s1 s2 : PS.t) :
  FromSet s1 <--> FromSet s2 -> PS.Equal s1 s2.
Proof.
  intros Heq z. split.
  - intros Hin. eapply FromSet_complete in Hin; [| reflexivity ].
    eapply FromSet_sound. reflexivity. eapply Heq. eassumption.
  - intros Hin. eapply FromSet_complete in Hin; [| reflexivity ].
    eapply FromSet_sound. reflexivity. eapply Heq. eassumption.
Qed.

(** Coercion from Ensemble to PS.t *)

Class ToMSet (S : Ensemble positive) :=
  {
    mset : PS.t;
    mset_eq : S <--> FromSet mset
  }.

Instance ToMSet_EmptySet : ToMSet (Empty_set _).
Proof.
  econstructor. 
  symmetry. eapply FromSet_empty.
Qed.

Instance ToMSet_Singleton x : ToMSet [set x].
Proof.
  econstructor. 
  symmetry. eapply FromSet_singleton.
Qed.

Instance ToMSet_Same_set (S1 S2 : Ensemble positive) :
  S1 <--> S2 ->
  ToMSet S1 ->
  ToMSet S2.
Proof.
  intros Heq [mset mset_eq]. rewrite Heq in mset_eq.
  econstructor. eassumption.
Qed.

Instance ToMSet_image'_Singleton {A} (f : A -> option positive) (x : A) :
  ToMSet (image' f [set x]).
Proof.
  destruct (f x) eqn:Heq.
  econstructor. rewrite image'_Singleton_Some; eauto.
  symmetry. eapply FromSet_singleton.
  econstructor. rewrite image'_Singleton_None; eauto.
  symmetry. eapply FromSet_empty.
Qed.

Instance ToMSet_Union S1 {H1 : ToMSet S1} S2 {H2 : ToMSet S2} : ToMSet (S1 :|: S2).
Proof.
  destruct H1 as [m1 Heq1]. destruct H2 as [m2 Heq2].  
  econstructor. symmetry. rewrite FromSet_union.
  rewrite Heq1, Heq2. reflexivity. 
Qed.  

Instance ToMSet_Setminus S1 {H1 : ToMSet S1} S2 {H2 : ToMSet S2} : ToMSet (S1 \\ S2).
Proof.
  destruct H1 as [m1 Heq1]. destruct H2 as [m2 Heq2].  
  econstructor. symmetry. rewrite FromSet_diff.
  rewrite Heq1, Heq2. reflexivity. 
Qed.

Instance ToMSet_Intersection (S1 : Ensemble positive) `{ToMSet S1}
         (S2 : Ensemble positive) `{ToMSet S2} : ToMSet (S1 :&: S2).
Proof.
  destruct H as [m1 Hm1]; destruct H0 as [m2 Hm2].
  eexists (PS.inter m1 m2).
  split.
  - intros x H. destruct H as [y Hs1 Hs2].  
    eapply FromSet_complete. reflexivity.
    eapply PS.inter_spec. split.
    eapply FromSet_sound. eapply Hm1; eauto. eassumption. 
    eapply FromSet_sound. eapply Hm2; eauto. eassumption. 
  - intros x H.
    eapply FromSet_sound in H; [| reflexivity ].
    eapply PS.inter_spec in H. inv H. constructor.
    eapply FromSet_complete. eapply Hm1; eauto. eassumption. 
    eapply FromSet_complete. eapply Hm2; eauto. eassumption. 
Qed.


Instance Decidable_ToMSet S {HM : ToMSet S} : Decidable S.
Proof.
  constructor. intros x.
  destruct HM as [m Heq].
  destruct (PS.mem x m) eqn:Hin.
  - eapply PS.mem_spec in Hin.
    left. eapply Heq. unfold FromSet, FromList, In.
    eapply InA_In. eapply PS.elements_spec1. eassumption.
  - right. intros Hc.
    eapply Heq in Hc.
    unfold FromSet, FromList, Ensembles.In in Hc.
    eapply In_InA with (eqA := Logic.eq)in Hc;
      eauto with typeclass_instances.
    eapply PS.elements_spec1 in Hc.
    eapply PS.mem_spec in Hc. congruence.
Qed.

Lemma ToMSet_add x S :
  ToMSet (x |: S) ->
  ~ x \in S ->
  ToMSet S.
Proof.
  intros [m Hm] Hnin.
  eapply Build_ToMSet with (mset := PS.remove x m).
  split; intros y Hin.
  - unfold FromSet, FromList, In in *. simpl.
    eapply InA_In. eapply PS.elements_spec1.
    eapply PS.remove_spec. split.
    + unfold FromSet, FromList, In. simpl.
      eapply PS.elements_spec1. eapply In_InA.
      now eauto with typeclass_instances.
      eapply Hm. now right.
    + intros Hc; subst; eauto.
  - unfold FromSet, FromList, Ensembles.In in *. simpl in *.
    eapply In_InA with (eqA := Logic.eq) in Hin; eauto with typeclass_instances.
    eapply PS.elements_spec1 in Hin. eapply PS.remove_spec in Hin.
    inv Hin.
    eapply PS.elements_spec1 in H. eapply InA_In in H.
    eapply Hm in H. inv H; eauto.
    inv H1. exfalso; eauto. 
Qed.

Lemma Ensemble_ind (P : Ensemble positive -> Prop) {_ : Proper (Same_set _ ==> iff) P} :
  P (Empty_set _) ->
  (forall x S {_ : ToMSet S}, ~ x \in S -> P S -> P (x |: S)) ->
  (forall S {_ : ToMSet S}, P S).
Proof.
  intros Hbase IH S HS.
  eapply H. eapply HS.
  eapply PS_ind with (S := mset).
  - intros x y Heq. eapply H.
    unfold FromSet. rewrite Heq. reflexivity.
  - rewrite FromSet_empty. eassumption.
  - intros z S1 Hnin HP.
    rewrite FromSet_add. eapply IH; try eassumption.
    econstructor. reflexivity.
    intros Hc. eapply Hnin. unfold FromSet, FromList, Ensembles.In in Hc.
    simpl in Hc. eapply In_InA in Hc. eapply PS.elements_spec1 in Hc.
    eassumption. eauto with typeclass_instances.
Qed.

    
Definition PS_map f s :=
  PS.fold (fun x s => PS.add (f x) s) s PS.empty.

Definition PS_map_opt f s :=
  PS.fold (fun x s => match f x with
                     | Some y => PS.add y s
                     | None => s
                   end) s PS.empty.

Lemma FromSet_elements m :
  FromSet m <--> FromList (PS.elements m).
Proof.
  split.
  - intros x H.
    eapply FromSet_sound in H; try eassumption; [| reflexivity ].
    unfold In, FromList.
    eapply InA_In. eapply PS.elements_spec1. eassumption.
  - intros x H.
    unfold Ensembles.In, FromList in H.
    eapply In_InA in H. eapply PS.elements_spec1 in H.
    eapply FromSet_complete. reflexivity. eassumption.
    tci.
Qed.

Lemma PS_fold_left_map s l b : 
  image b (FromList l) :|: FromSet s <-->
        FromSet
        (fold_left (fun (a : PS.t) (e : PS.elt) => PS.add (b e) a) l s).
Proof with (now eauto with Ensembles_DB).
  revert s; induction l; intros s; eauto.
  - rewrite FromList_nil, image_Empty_set...
  - rewrite FromList_cons. simpl.
    rewrite image_Union, (Union_commut (image _ _ )), <- Union_assoc.
    rewrite image_Singleton. rewrite <- FromSet_add.
    now apply IHl.
Qed.

Lemma PS_fold_left_map_opt s l (b : positive -> option positive) : 
  image' b (FromList l) :|: FromSet s <-->
         FromSet
         (fold_left (fun s x  => match b x with
                                | Some y => PS.add y s
                                | None => s
                              end)  l s).
Proof with (now eauto with Ensembles_DB).
  revert s; induction l; intros s; eauto.
  - rewrite FromList_nil, image'_Empty_set...
  - rewrite FromList_cons. simpl.
    rewrite image'_Union, (Union_commut (image' _ _ )), <- Union_assoc.
    destruct (b a) eqn:Hbs.
    + rewrite image'_Singleton_Some; eauto.
      rewrite <- FromSet_add.
      now apply IHl.
    + rewrite image'_Singleton_None; eauto.
      rewrite Union_Empty_set_neut_l.
      eapply IHl. 
Qed.

  
Instance ImageToMSet b S `{_: ToMSet S} : ToMSet (image b S).
Proof.
  destruct H as [m Hm].
  exists (PS_map b m).  rewrite Hm. unfold PS_map.
  rewrite FromSet_elements.
  rewrite PS.fold_spec. 
  rewrite FromSet_elements in Hm.
  generalize (PS.elements m) Hm. clear Hm.
  intros l Heq.
  rewrite <- PS_fold_left_map. rewrite FromSet_empty.
  now eauto with Ensembles_DB.
Qed.

Instance Image'ToMSet b S `{_: ToMSet S} : ToMSet (image' b S).
Proof.
  destruct H as [m Hm].
  exists (PS_map_opt b m).  rewrite Hm. unfold PS_map_opt.
  rewrite FromSet_elements.
  rewrite PS.fold_spec. 
  rewrite FromSet_elements in Hm.
  generalize (PS.elements m) Hm. clear Hm.
  intros l Heq.
  rewrite <- PS_fold_left_map_opt. rewrite FromSet_empty.
  now eauto with Ensembles_DB.
Qed.


Lemma PS_elements_subset S1 {HS1 : ToMSet S1} S2 {HS2 : ToMSet S2} :
  S1 \subset S2 ->
  (PS.cardinal (@mset S1 _)) <= (PS.cardinal (@mset S2 _)).
Proof.
  rewrite !PS.cardinal_spec. intros Hin.
  eapply Same_set_FromList_length.
  eapply NoDupA_NoDup. eapply PS.elements_spec2w.
  rewrite <- !FromSet_elements. unfold mset. 
  destruct HS1 as [m1 HS1].
  destruct HS2 as [m2 HS2].
  rewrite <- HS1, <- HS2. eassumption.
Qed. 

Definition disjoint (s1 s2 : PS.t) : Prop :=
  PS.Equal (PS.inter s1 s2) PS.empty.

Lemma disjoint_spec (s1 s2 : PS.t) x :
  disjoint s1 s2 ->
  PS.In x s1->
  ~ PS.In x s2.
Proof.
  intros Hd Hin1 Hin2.
  assert (Hin3 : PS.In x (PS.inter s1 s2)).
  { eapply PS.inter_spec; eauto. }
  unfold disjoint in Hd. rewrite Hd in Hin3.
  inv Hin3.
Qed.

Lemma disjoint_spec' (s1 s2 : PS.t) x :
  disjoint s1 s2 ->
  PS.In x s2 ->
  ~ PS.In x s1.
Proof.
  intros Hd Hin1 Hin2.
  assert (Hin3 : PS.In x (PS.inter s1 s2)).
  { eapply PS.inter_spec; eauto. }
  unfold disjoint in Hd. rewrite Hd in Hin3.
  inv Hin3.
Qed.

Lemma FromSet_intersection (s1 s2 : PS.t) : 
  FromSet (PS.inter s1 s2) <--> FromSet s1 :&: FromSet s2. 
Proof.
  split; intros x Hin.
  eapply FromSet_sound in Hin; [| reflexivity ].
  eapply PS.inter_spec in Hin. destruct Hin as [Hin1 Hin2].
  constructor; (eapply FromSet_complete; [ reflexivity | eassumption ]). 
  inv Hin.
  eapply FromSet_complete. reflexivity.
  eapply PS.inter_spec.
  split; (eapply FromSet_sound; [ reflexivity | eassumption ]).
Qed. 

Lemma FromSet_disjoint (s1 s2 : PS.t) : 
  disjoint s1 s2 <-> Disjoint _ (FromSet s1) (FromSet s2). 
Proof.
  split; intros Hd.
  - constructor. intros x Hin.
    eapply FromSet_intersection in Hin.
    unfold disjoint in Hd. rewrite Hd in Hin.
    eapply FromSet_empty in Hin. inv Hin.
  - inv Hd. unfold disjoint. intros y.
    specialize (H y). split; intros Hin; [| now inv Hin ].
    exfalso. eapply H.
    eapply FromSet_intersection.
    eapply FromSet_complete; [| eassumption ].
    reflexivity.
Qed.

Lemma PS_union_elements s1 s2 :
  disjoint s1 s2 -> 
  Permutation (PS.elements s1 ++ PS.elements s2) (PS.elements (PS.union s1 s2)).
Proof.
  intros Hnin. 
  eapply NoDup_Permutation.
  - eapply NoDup_app.
    eapply NoDupA_NoDup. now eapply PS.elements_spec2w.
    eapply NoDupA_NoDup. now eapply PS.elements_spec2w.
    eapply FromSet_disjoint. eassumption.      
  - eapply NoDupA_NoDup. eapply PS.elements_spec2w.
  - intros y. split.
    + intros Hin.
      eapply InA_In.
      eapply PS.elements_spec1. eapply PS.union_spec. 
      eapply Coqlib.in_app in Hin. 
      inv Hin.
      * left. eapply PS.elements_spec1.
        eapply In_InA. eauto with typeclass_instances.
        eassumption.
      * right. eapply PS.elements_spec1.
        eapply In_InA. eauto with typeclass_instances.
        eassumption.
    + intros HIn.
      eapply In_InA in HIn. 
      eapply PS.elements_spec1 in HIn. 
      eapply PS.union_spec in HIn.
      eapply Coqlib.in_app.
      inv HIn.
      * left. eapply InA_In. eapply PS.elements_spec1.
        eassumption. 
      * right. eapply InA_In. eapply PS.elements_spec1.
        eassumption.
      * eauto with typeclass_instances.
Qed. 

Lemma PS_cardinal_union s1 s2 :
  disjoint s1 s2 -> 
  PS.cardinal s1 + PS.cardinal s2 = PS.cardinal (PS.union s1 s2).
Proof.
  intros Hd.
  rewrite !PS.cardinal_spec.
  erewrite (@Permutation_length _ (PS.elements (PS.union s1 s2))).
  rewrite <- app_length. reflexivity.
  symmetry. eapply PS_union_elements. eassumption.
Qed.
