Require Import List Relations RelationClasses.
Import ListNotations.

Ltac inv H := inversion H; clear H; subst.

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