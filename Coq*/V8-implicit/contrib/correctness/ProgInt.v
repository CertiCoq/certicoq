(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: ProgInt.v 5920 2004-07-16 20:01:26Z herbelin $ *)

Require Export ZArith.
Require Export ZArith_dec.

Theorem Znotzero : forall x:Z, {x <> 0%Z} + {x = 0%Z}.
Proof.
intro x. elim (Z_eq_dec x 0); auto.
Qed.