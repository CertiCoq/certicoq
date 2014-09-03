(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: Relation_Operators.v 9609 2007-02-07 14:42:26Z herbelin $ i*)

(****************************************************************************)
(*                      Bruno Barras, Cristina Cornes                       *)
(*                                                                          *)
(*  Some of these definitons were taken from :                              *)
(*     Constructing Recursion Operators in Type Theory                      *)
(*     L. Paulson  JSC (1986) 2, 325-355                                    *)
(****************************************************************************)

Require Import Relation_Definitions.
Require Import List.

(** Some operators to build relations *)

Section Transitive_Closure.
  Variable A : Type.
  Variable R : relation A.
  
  Inductive clos_trans (x: A) : A -> Prop :=
    | t_step : forall y:A, R x y -> clos_trans x y
    | t_trans :
        forall y z:A, clos_trans x y -> clos_trans y z -> clos_trans x z.

  Definition clos_trans_ind'
    [P:A->A->Prop]
    (f:forall x y, R x y -> P x y)
    (f0:forall x y z,
        clos_trans x y -> P x y -> clos_trans y z -> P y z -> P x z) :=
    fix F (x a:A) (c:clos_trans x a) : P x a :=
    match c in (clos_trans _ a0) return P x a0 with
    | t_step y r => f x y r
    | t_trans y z c0 c1 => f0 x y z c0 (F x y c0) c1 (F y z c1)
    end.

End Transitive_Closure.


Section Reflexive_Transitive_Closure.
  Variable A : Type.
  Variable R : relation A.

  Inductive clos_refl_trans (x:A) : A -> Prop:=
    | rt_step : forall y:A, R x y -> clos_refl_trans x y
    | rt_refl : clos_refl_trans x x
    | rt_trans :
        forall y z:A,
          clos_refl_trans x y -> clos_refl_trans y z -> clos_refl_trans x z.

  Definition clos_refl_trans_ind'
    [P:A->A->Prop]
    (f:forall x y, R x y -> P x y)
    (f0:forall x, P x x)
    (f1:forall x y z,
        clos_refl_trans x y -> P x y ->
        clos_refl_trans y z -> P y z -> P x z) :=
    fix F (x a:A) (c:clos_refl_trans x a) : P x a :=
    match c in (clos_refl_trans _ a0) return P x a0 with
    | rt_step y r => f x y r
    | rt_refl => f0 x
    | rt_trans y z c0 c1 => f1 x y z c0 (F x y c0) c1 (F y z c1)
    end.

End Reflexive_Transitive_Closure.


Section Reflexive_Symetric_Transitive_Closure.
  Variable A : Type.
  Variable R : relation A.
  
  Inductive clos_refl_sym_trans : relation A :=
    | rst_step : forall x y:A, R x y -> clos_refl_sym_trans x y
    | rst_refl : forall x:A, clos_refl_sym_trans x x
    | rst_sym :
      forall x y:A, clos_refl_sym_trans x y -> clos_refl_sym_trans y x
    | rst_trans :
      forall x y z:A,
        clos_refl_sym_trans x y ->
        clos_refl_sym_trans y z -> clos_refl_sym_trans x z.

End Reflexive_Symetric_Transitive_Closure.


Section Transposee.
  Variable A : Type.
  Variable R : relation A.

  Definition transp (x y:A) := R y x.
End Transposee.


Section Union.
  Variable A : Type.
  Variables R1 R2 : relation A.

  Definition union (x y:A) := R1 x y \/ R2 x y.
End Union.


Section Disjoint_Union.
Variables A B : Type.
Variable leA : A -> A -> Prop.
Variable leB : B -> B -> Prop.

Inductive le_AsB : A + B -> A + B -> Prop :=
  | le_aa : forall x y:A, leA x y -> le_AsB (inl B x) (inl B y)
  | le_ab : forall (x:A) (y:B), le_AsB (inl B x) (inr A y)
  | le_bb : forall x y:B, leB x y -> le_AsB (inr A x) (inr A y).

End Disjoint_Union. 



Section Lexicographic_Product.
  (* Lexicographic order on dependent pairs *)

  Variable A : Type.
  Variable B : A -> Type.
  Variable leA : A -> A -> Prop.
  Variable leB : forall x:A, B x -> B x -> Prop.

  Inductive lexprod : sigS B -> sigS B -> Prop :=
    | left_lex :
      forall (x x':A) (y:B x) (y':B x'),
        leA x x' -> lexprod (existS B x y) (existS B x' y')
    | right_lex :
      forall (x:A) (y y':B x),
        leB x y y' -> lexprod (existS B x y) (existS B x y').
End Lexicographic_Product.


Section Symmetric_Product.
  Variable A : Type.
  Variable B : Type.
  Variable leA : A -> A -> Prop.
  Variable leB : B -> B -> Prop.

  Inductive symprod : A * B -> A * B -> Prop :=
    | left_sym :
      forall x x':A, leA x x' -> forall y:B, symprod (x, y) (x', y)
    | right_sym :
      forall y y':B, leB y y' -> forall x:A, symprod (x, y) (x, y').

End Symmetric_Product.


Section Swap.
  Variable A : Type.
  Variable R : A -> A -> Prop.

  Inductive swapprod : A * A -> A * A -> Prop :=
    | sp_noswap : forall x x':A * A, symprod A A R R x x' -> swapprod x x'
    | sp_swap :
      forall (x y:A) (p:A * A),
        symprod A A R R (x, y) p -> swapprod (y, x) p.
End Swap.


Section Lexicographic_Exponentiation.
  
  Variable A : Set.
  Variable leA : A -> A -> Prop.
  Let Nil := nil (A:=A).
  Let List := list A.
  
  Inductive Ltl : List -> List -> Prop :=
    | Lt_nil : forall (a:A) (x:List), Ltl Nil (a :: x)
    | Lt_hd : forall a b:A, leA a b -> forall x y:list A, Ltl (a :: x) (b :: y)
    | Lt_tl : forall (a:A) (x y:List), Ltl x y -> Ltl (a :: x) (a :: y).


  Inductive Desc : List -> Prop :=
    | d_nil : Desc Nil
    | d_one : forall x:A, Desc (x :: Nil)
    | d_conc :
      forall (x y:A) (l:List),
        leA x y -> Desc (l ++ y :: Nil) -> Desc ((l ++ y :: Nil) ++ x :: Nil).

  Definition Pow : Set := sig Desc.
  
  Definition lex_exp (a b:Pow) : Prop := Ltl (proj1_sig a) (proj1_sig b).

End Lexicographic_Exponentiation.

Hint Unfold transp union: sets v62.
Hint Resolve t_step rt_step rt_refl rst_step rst_refl: sets v62.
Hint Immediate rst_sym: sets v62.
