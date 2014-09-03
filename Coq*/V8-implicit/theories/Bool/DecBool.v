(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: DecBool.v 9245 2006-10-17 12:53:34Z notin $ i*)

Require Import ImplicitAxioms.

Set Implicit Arguments.

Definition ifdec (A B:Prop) (C:Type) (H:{A} + {B}) (x y:C) : C :=
  if H then x else y.


Theorem ifdec_left :
  forall (A B:Prop) (C:Set) (H:{A} + {B}),
    ~ B -> forall x y:C, ifdec H x y = x.
Proof.
  intros; case H; auto.
  intro; absurd B; apply impl_PI; trivial.
Qed.

Theorem ifdec_right :
  forall (A B:Prop) (C:Set) (H:{A} + {B}),
    ~ A -> forall x y:C, ifdec H x y = y.
Proof.
  intros; case H; auto.
  intro; absurd A; apply impl_PI; trivial.
Qed.

Unset Implicit Arguments.
