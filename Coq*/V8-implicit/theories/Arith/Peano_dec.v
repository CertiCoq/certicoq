(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: Peano_dec.v 9698 2007-03-12 17:11:32Z letouzey $ i*)

Require Import Decidable.

Open Local Scope nat_scope.

Implicit Types m n x y : nat.

Theorem O_or_S : forall n, {m : nat | S m = n} + {0 = n}.
Proof.
  induction n.
  auto.
  left; exists n; auto.
Defined.

Theorem eq_nat_dec : forall n m, {n = m} + {n <> m}.
Proof.
  induction n; destruct m; auto.
  elim (IHn m); auto.
Defined.

Hint Resolve O_or_S eq_nat_dec: arith.

Require Import ImplicitAxioms.

Theorem dec_eq_nat : forall n m, decidable (n = m).
Proof (fun n m => sumbool_or (eq_nat_dec n m)).
