(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)
(* $Id: refl_tauto.mli 7233 2005-07-15 12:34:56Z corbinea $ *)


open Term

type atom_env=
    {mutable next:int;
     mutable env:(Term.constr*int) list}

val make_form : atom_env ->
    Proof_type.goal Tacmach.sigma -> Term.types -> Proof_search.form

val make_hyps :
    atom_env ->
    Proof_type.goal Tacmach.sigma ->
    types list ->
    Sign.named_context ->
    (Names.identifier * impl * Proof_search.form) list

(* raises Not_found if no proof is found *)
val rtauto_tac : Proof_type.tactic
