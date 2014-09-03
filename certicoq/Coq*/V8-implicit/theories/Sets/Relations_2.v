(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(****************************************************************************)
(*                                                                          *)
(*                         Naive Set Theory in Coq                          *)
(*                                                                          *)
(*                     INRIA                        INRIA                   *)
(*              Rocquencourt                        Sophia-Antipolis        *)
(*                                                                          *)
(*                                 Coq V6.1                                 *)
(*									    *)
(*			         Gilles Kahn 				    *)
(*				 Gerard Huet				    *)
(*									    *)
(*									    *)
(*                                                                          *)
(* Acknowledgments: This work was started in July 1993 by F. Prost. Thanks  *)
(* to the Newton Institute for providing an exceptional work environment    *)
(* in Summer 1995. Several developments by E. Ledinot were an inspiration.  *)
(****************************************************************************)

(*i $Id: Relations_2.v 8642 2006-03-17 10:09:02Z notin $ i*)

Require Export Relations_1.

Section Relations_2.
Variable U : Type.
Variable R : Relation U.

Inductive Rstar (x:U) : U -> Prop :=
  | Rstar_0 : Rstar x x
  | Rstar_n : forall y z:U, R x y -> Rstar y z -> Rstar x z.

Definition Rstar_ind'
    [P:U->U->Prop]
    (f:forall x, P x x)
    (f0:forall x y z, R x y -> Rstar y z -> P y z -> P x z) :=
    fix F (x a:U) (c:Rstar x a) : P x a :=
    match c in (Rstar _ a0) return P x a0 with
    | Rstar_0 => f x
    | Rstar_n y z r c0 => f0 x y z r c0 (F y z c0)
    end.

Inductive Rstar1 (x:U) : U -> Prop :=
  | Rstar1_0 : Rstar1 x x
  | Rstar1_1 : forall y:U, R x y -> Rstar1 x y
  | Rstar1_n : forall y z:U, Rstar1 x y -> Rstar1 y z -> Rstar1 x z.

Definition Rstar1_ind'
    [P:U->U->Prop]
    (f:forall x, P x x)
    (f0:forall x y, R x y -> P x y)
    (f1:forall x y z,
        Rstar1 x y -> P x y -> Rstar1 y z -> P y z -> P x z) :=
    fix F (x a:U) (c:Rstar1 x a) : P x a :=
    match c in (Rstar1 _ a0) return P x a0 with
    | Rstar1_0 => f x
    | Rstar1_1 y r => f0 x y r
    | Rstar1_n y z c0 c1 => f1 x y z c0 (F x y c0) c1 (F y z c1)
    end.

Inductive Rplus (x:U) : U -> Prop :=
  | Rplus_0 : forall y:U, R x y -> Rplus x y
  | Rplus_n : forall y z:U, R x y -> Rplus y z -> Rplus x z.

Definition Rplus_ind'
    [P:U->U->Prop]
    (f:forall x y, R x y -> P x y)
    (f0:forall x y z, R x y -> Rplus y z -> P y z -> P x z) :=
    fix F (x a:U) (c:Rplus x a) : P x a :=
    match c in (Rplus _ a0) return P x a0 with
    | Rplus_0 y r => f x y r
    | Rplus_n y z r c0 => f0 x y z r c0 (F y z c0)
    end.

Definition Strongly_confluent : Prop :=
  forall x a b:U, R x a -> R x b -> ex (fun z:U => R a z /\ R b z).

End Relations_2.

Hint Resolve Rstar_0: sets v62.
Hint Resolve Rstar1_0: sets v62.
Hint Resolve Rstar1_1: sets v62.
Hint Resolve Rplus_0: sets v62.
