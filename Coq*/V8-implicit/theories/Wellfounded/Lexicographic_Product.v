(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: Lexicographic_Product.v 9598 2007-02-06 19:45:52Z herbelin $ i*)

(** Authors: Bruno Barras, Cristina Cornes *)

Require Import Eqdep.
Require Import Relation_Operators.
Require Import Transitive_Closure.

(**  From : Constructing Recursion Operators in Type Theory            
     L. Paulson  JSC (1986) 2, 325-355 *)

Section WfLexicographic_Product.
  Variable A : Type.
  Variable B : A -> Type.
  Variable leA : A -> A -> Prop.
  Variable leB : forall x:A, B x -> B x -> Prop.

  Notation LexProd := (lexprod A B leA leB).
  
  Lemma acc_A_B_lexprod :
    forall x:A,
      Acc leA x ->
      (forall x0:A, clos_trans A leA x0 x -> well_founded (leB x0)) ->
      forall y:B x, Acc (leB x) y -> Acc LexProd (existS B x y).
  Proof.
    induction 1 as [x _ IHAcc] using Acc_ind'; intros H2 y.
    induction 1 as [x0 H IHAcc0] using Acc_ind'; intros.
    apply Acc_intro.
    destruct y as [x2 y1]; intro H6.
    simple inversion H6; intro.
    cut (leA x2 x); intros.
    apply IHAcc; auto with sets.
    intros.
    apply H2.
    apply t_trans with x2; auto with sets.
    
    red in H2.
    apply H2.
    auto with sets.
    
    injection H1.
    destruct 2.
    injection H3.
    destruct 2; auto with sets.
    
    rewrite <- H1.
    injection H3; intros _ Hx1.
    subst x1.
    apply IHAcc0.
    elim inj_pair2 with A B x y' x0; assumption.
  Qed.

  Theorem wf_lexprod :
    well_founded leA ->
    (forall x:A, well_founded (leB x)) -> well_founded LexProd.
  Proof.
    intros wfA wfB; unfold well_founded in |- *.
    destruct a.
    apply acc_A_B_lexprod; auto with sets; intros.
    red in wfB.
    auto with sets.
  Qed.


End WfLexicographic_Product.


Section Wf_Symmetric_Product.
  Variable A : Type.
  Variable B : Type.
  Variable leA : A -> A -> Prop.
  Variable leB : B -> B -> Prop.

  Notation Symprod := (symprod A B leA leB).

  Lemma Acc_symprod :
    forall x:A, Acc leA x -> forall y:B, Acc leB y -> Acc Symprod (x, y).
  Proof.
    induction 1 as [x _ IHAcc]; intros y H2.
    induction H2 as [x1 H3 IHAcc1] using Acc_ind'.
    apply Acc_intro; intros y H5.
    inversion_clear H5; auto with sets.
    apply IHAcc; auto.
    apply Acc_intro; trivial.
  Qed.


  Lemma wf_symprod :
    well_founded leA -> well_founded leB -> well_founded Symprod.
  Proof.
    red in |- *.
    destruct a.
    apply Acc_symprod; auto with sets.
  Qed.

End Wf_Symmetric_Product.


Section Swap.
  
  Variable A : Type.
  Variable R : A -> A -> Prop.

  Notation SwapProd := (swapprod A R).


  Lemma swap_Acc : forall x y:A, Acc SwapProd (x, y) -> Acc SwapProd (y, x).
  Proof.
    intros.
    inversion_clear H.
    apply Acc_intro.
    destruct y0; intros.
    inversion_clear H; inversion_clear H1; apply H0.
    apply sp_swap.
    apply right_sym; auto with sets.
    
    apply sp_swap.
    apply left_sym; auto with sets.
    
    apply sp_noswap.
    apply right_sym; auto with sets.
    
    apply sp_noswap.
    apply left_sym; auto with sets.
  Qed.


  Lemma Acc_swapprod :
    forall x y:A, Acc R x -> Acc R y -> Acc SwapProd (x, y).
  Proof.
    induction 1 as [x0 _ IHAcc0]; intros H2.
    cut (forall y0:A, R y0 x0 -> Acc SwapProd (y0, y)).
    clear IHAcc0.
    induction H2 as [x1 _ IHAcc1] using Acc_ind'; intros H4.
    cut (forall y:A, R y x1 -> Acc SwapProd (x0, y)).
    clear IHAcc1.
    intro.
    apply Acc_intro.
    destruct y; intro H5.
    inversion_clear H5.
    inversion_clear H0; auto with sets.
    
    apply swap_Acc.
    inversion_clear H0; auto with sets.
    
    intros.
    apply IHAcc1; auto with sets; intros.
    apply Acc_inv with (y0, x1); auto with sets.
    apply sp_noswap.
    apply right_sym; auto with sets.
    
    auto with sets.
  Qed.

  
  Lemma wf_swapprod : well_founded R -> well_founded SwapProd.
  Proof.
    red in |- *.
    destruct a; intros.
    apply Acc_swapprod; auto with sets.
  Qed.

End Swap.
