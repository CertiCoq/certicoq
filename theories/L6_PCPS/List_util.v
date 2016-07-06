Require Import Coq.Lists.List Coq.Relations.Relations Coq.Classes.RelationClasses
        Coq.omega.Omega Coq.Numbers.BinNums Coq.Structures.OrdersEx.

Import ListNotations.

Ltac inv H := inversion H; clear H; subst.

Function nthN {A: Type} (al: list A) (n: N) : option A :=
  match al, n with
    | a::al', 0%N => Some a
    | a::al', _ => nthN al' (n-1)%N
    | _, _ => None
  end.

(** Asymmetric version of Forall2 *) 
Inductive Forall2_asym {A} (R : relation A) : list A -> list A -> Prop :=
| Forall2_asym_nil : forall l, Forall2_asym R [] l
| Forall2_asym_cons :
    forall x y l l', R x y -> Forall2_asym R l l' -> Forall2_asym R (x :: l) (y :: l').

Hint Constructors Forall2_asym.

Lemma Forall2_length {A} (R : A -> A -> Prop) (l1 l2 : list A) :
  Forall2 R l1 l2 -> length l1 = length l2. 
Proof.
  revert l2. induction l1 as [| x xs IHxs ]; intros l2 H.
  - inv H; eauto.
  - inv H. simpl. f_equal. eauto.
Qed.

Lemma Forall2_asym_length {A} (R : A -> A -> Prop) (l1 l2 : list A) :
  Forall2_asym R l1 l2 -> length l1 <= length l2. 
Proof.
  revert l2. induction l1 as [| x xs IHxs ]; intros l2 H.
  - inv H; simpl. omega.
  - inv H. simpl. eapply IHxs in H4. omega.
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

Lemma Forall2_asym_monotonic {A} (R R' : A -> A -> Prop) (l1 l2 : list A) :
  (forall x1 x2, R x1 x2 -> R' x1 x2) ->
  Forall2_asym R l1 l2 ->
  Forall2_asym R' l1 l2.
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

Lemma Forall2_asym_refl {A} (R : A -> A -> Prop) (l : list A) :
  Reflexive R ->
  Forall2_asym R l l.
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

Lemma Forall2_asym_trans {A} (R : A -> A -> Prop) (l1 l2 l3 : list A) :
  Transitive R ->
  Forall2_asym R l1 l2 ->
  Forall2_asym R l2 l3 ->
  Forall2_asym R l1 l3.
Proof.
  intros Htrans.
  revert l2 l3. induction l1 as [| x l IHl ]; intros l2 l3 H1 H2.
  - inv H1. inv H2; eauto.
  - inv H1. inv H2; eauto.
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

Lemma Forall2_asym_trivial {A} (R : A -> A -> Prop) (l1 l2 : list A) :
  (forall x y, R x y) ->
  (length l1 <= length l2) -> 
  Forall2_asym R l1 l2.
Proof.
  intros H.
  revert l2; induction l1 as [| x l IHl]; intros l2 Hlen; eauto.
  destruct l2; simpl in *; try omega. constructor; eauto.
  eapply IHl; omega.
Qed.

Lemma Forall2_same {A} (R : A -> A -> Prop) l:
  (forall x, List.In x l -> R x x) ->
  Forall2 R l l.
Proof.
  induction l; intros H; constructor.
  - apply H. constructor; eauto.
  - apply IHl. intros. apply H. constructor 2; eauto.
Qed.

Lemma Forall2_asym_same {A} (R : A -> A -> Prop) l:
  (forall x, List.In x l -> R x x) ->
  Forall2_asym R l l.
Proof.
  induction l; intros H; constructor.
  - apply H. constructor; eauto.
  - apply IHl. intros. apply H. constructor 2; eauto.
Qed.

Lemma In_nthN (A : Type) (l : list A) (v : A) :
  List.In v l -> exists n, nthN l n = Some v .
Proof.
  intros Hin. induction l.
  - inv Hin.
  - inv Hin.
    + exists 0%N. eauto.
    + destruct IHl as [n Hnth].
      eassumption. 
      exists (n+1)%N. simpl. destruct (n + 1)%N eqn:Heq; eauto. 
      zify. omega. 
      rewrite <- Heq. rewrite N_as_OT.add_sub.
      eassumption.
Qed.