(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: cctac.mli 9151 2006-09-19 13:32:22Z corbinea $ *)

open Term 
open Proof_type

val cc_tactic : int -> constr list -> tactic

val cc_fail : tactic

val congruence_tac : int -> constr list -> tactic
