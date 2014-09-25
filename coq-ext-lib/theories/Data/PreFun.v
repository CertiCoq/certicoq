Require Import Morphisms.
Require Import Coq.Relations.Relations.
Require Import ExtLib.Structures.Proper.
Require Import ExtLib.Core.Type.

Set Implicit Arguments.
Set Strict Implicit.

Definition Fun A B := A -> B.

Section type.
  Variables (T U : Type) (tT : type T) (tU : type U).

  Global Instance type_Fun  : type (T -> U) :=
  { equal := fun f g => respectful equal equal f g
  ; proper := fun x => respectful equal equal x x
  }.

  Variables (tOk : typeOk tT) (uOk : typeOk tU).

  Global Instance typeOk_Fun : typeOk type_Fun.
  Proof.
    constructor.
    { unfold equiv. simpl. unfold respectful.
      destruct tOk. destruct uOk; intros.
      split; intros.
      { destruct (only_proper _ _ H0).
        etransitivity. eapply H. eassumption.
        symmetry. eapply H. symmetry. auto. }
      { destruct (only_proper _ _ H0).
        symmetry. etransitivity; [ | eapply H ].
        symmetry. eapply H. eassumption. symmetry. eauto. } }
    { red. intros. apply H. }
    { compute. intuition. symmetry. eapply H. symmetry. auto. }
    { simpl; intro; intros. intuition. red in H; red in H0; simpl in *.
      red; intros.
      etransitivity. eapply H. eassumption.
      eapply H0.
      eapply only_proper in H1; intuition.
      (* eapply preflexive with (wf := proper); auto.
      apply tOk. *) }
  Qed.

  Global Instance proper_app : forall (f : T -> U) (a : T),
    proper f -> proper a -> proper (f a).
  Proof.
    simpl; intros. red in H.
    eapply proper_left; eauto.
    eapply H. eapply preflexive. eapply equiv_prefl; auto. auto.
  Qed.

  Theorem proper_fun : forall (f : T -> U),
    (forall x y, equal x y -> equal (f x) (f y)) ->
    proper f.
  Proof.
    intros. do 3 red. eauto.
  Qed.

  Theorem equal_fun : forall (f g : T -> U),
    (forall x y, equal x y -> equal (f x) (g y)) ->
    equal f g.
  Proof. intros. do 3 red. apply H. Qed.

  Theorem equal_app : forall (f g : T -> U) (x y : T),
    equal f g -> equal x y ->
    equal (f x) (g y).
  Proof.
    clear. intros. do 3 red in H. auto.
  Qed.

End type.

Definition compose {A B C : Type} (g : B -> C) (f : A -> B) : A -> C :=
  fun x => g (f x).
