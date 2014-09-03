(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: clenvtac.mli 6099 2004-09-12 11:38:09Z barras $ i*)

(*i*)
open Util
open Names
open Term
open Sign
open Evd
open Clenv
open Proof_type
(*i*)

(* Tactics *)
val unify : constr -> tactic
val clenv_refine : clausenv -> tactic
val res_pf : clausenv -> ?allow_K:bool -> tactic
val e_res_pf : clausenv -> tactic
val elim_res_pf_THEN_i : clausenv -> (clausenv -> tactic array) -> tactic
