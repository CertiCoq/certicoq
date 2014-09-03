(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: contradiction.mli 9842 2007-05-20 17:44:23Z herbelin $ i*)

(*i*)
open Names
open Term
open Proof_type
open Rawterm
open Genarg
(*i*)

val absurd                      : constr -> tactic
val contradiction               : constr with_ebindings option -> tactic
