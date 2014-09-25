Require Arith.
Require Import ExtLib.Core.RelDec.
Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.Monoid.
Require Import ExtLib.Tactics.Consider.

Set Implicit Arguments.
Set Strict Implicit.


Global Instance RelDec_eq : RelDec (@eq nat) :=
{ rel_dec := EqNat.beq_nat }.

Global Instance type_nat : type nat :=
{ equal := @eq nat
; proper := fun _ => True
}.

Global Instance typeOk_nat : typeOk type_nat.
Proof.
  constructor.
  { compute; auto. }
  { compute; auto. }
  { compute; auto. }
  { compute. intros. etransitivity; eauto. }
Qed.

Global Instance nat_proper (n : nat) : proper n.
Proof. exact I. Qed.

Global Instance RelDec_lt : RelDec lt :=
{ rel_dec := NPeano.ltb }.

Global Instance RelDec_le : RelDec le :=
{ rel_dec := NPeano.leb }.

Global Instance RelDec_gt : RelDec gt :=
{ rel_dec := fun x y => NPeano.ltb y x }.

Global Instance RelDec_ge : RelDec ge :=
{ rel_dec := fun x y => NPeano.leb y x }.

Global Instance RelDecCorrect_eq : RelDec_Correct RelDec_eq.
Proof.
  constructor; simpl. apply EqNat.beq_nat_true_iff.
Qed.

Global Instance RelDecCorrect_lt : RelDec_Correct RelDec_lt.
Proof.
  constructor; simpl. eapply NPeano.ltb_lt.
Qed.

Global Instance RelDecCorrect_le : RelDec_Correct RelDec_le.
Proof.
  constructor; simpl. eapply NPeano.leb_le.
Qed.

Global Instance RelDecCorrect_gt : RelDec_Correct RelDec_gt.
Proof.
  constructor; simpl. unfold rel_dec; simpl.
  intros. eapply NPeano.ltb_lt.
Qed.

Global Instance RelDecCorrect_ge : RelDec_Correct RelDec_ge.
Proof.
  constructor; simpl. unfold rel_dec; simpl.
  intros. eapply NPeano.leb_le.
Qed.

Inductive R_nat_S : nat -> nat -> Prop :=
| R_S : forall n, R_nat_S n (S n).

Theorem wf_R_S : well_founded R_nat_S.
Proof.
  red; induction a; constructor; intros.
    inversion H.
    inversion H; subst; auto.
Defined.

Inductive R_nat_lt : nat -> nat -> Prop :=
| R_lt : forall n m, n < m -> R_nat_lt n m.

Theorem wf_R_lt : well_founded R_nat_lt.
Proof.
  red; induction a; constructor; intros.
  { inversion H. exfalso. subst. inversion H0. }
  { inversion H; clear H; subst. inversion H0; clear H0; subst; auto.
    inversion IHa. eapply H. constructor. eapply H1. }
Defined.

Definition Monoid_nat_plus : Monoid nat :=
{| monoid_plus := plus
 ; monoid_unit := 0
 |}.

Definition Monoid_nat_mult : Monoid nat :=
{| monoid_plus := mult
 ; monoid_unit := 1
 |}.
