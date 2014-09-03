(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id:$ *)

open Refiner
open Names
open Term
open Tacmach
open Decl_mode

type stack =
  (identifier * (constr option * constr list * impl list) list) list 

val go_to_proof_mode: unit -> unit
val return_from_tactic_mode: unit -> unit

val register_automation_tac: tactic -> unit

val automation_tac : tactic

val daimon_subtree: pftreestate -> pftreestate

val concl_refiner: Termops.metamap -> constr -> Proof_type.goal sigma -> constr

val do_instr: Decl_expr.raw_proof_instr -> pftreestate -> pftreestate
val proof_instr: Decl_expr.raw_proof_instr -> unit

val tcl_change_info : Decl_mode.pm_info -> tactic

val mark_proof_tree_as_done : Proof_type.proof_tree -> Proof_type.proof_tree

val mark_as_done : pftreestate -> pftreestate

val execute_cases :
    name ->
    Decl_mode.per_info ->
    (constr -> Proof_type.tactic) ->
    stack ->
    Term.constr list -> int -> Decl_mode.split_tree -> Proof_type.tactic

val tree_of_pats : 
  identifier * int -> (Rawterm.cases_pattern*recpath) list list ->
  split_tree

val add_branch : 
  identifier * int -> (Rawterm.cases_pattern*recpath) list list ->
  split_tree -> split_tree

val append_branch :
    identifier * int -> int ->
    (Rawterm.cases_pattern * recpath) list list ->
    (Idset.t * split_tree) option ->
    (Idset.t * split_tree) option

val append_tree :
  identifier * int -> int -> (Rawterm.cases_pattern*recpath) list list ->
  split_tree -> split_tree

val build_dep_clause :   types Decl_expr.statement list ->
    Decl_expr.proof_pattern ->
    Decl_mode.per_info ->
    (types Decl_expr.statement, types Decl_expr.or_thesis)
    Decl_expr.hyp list -> Proof_type.goal Tacmach.sigma -> types

val register_dep_subcase :    
    identifier * int ->
    Environ.env ->
    Decl_mode.per_info ->
    Rawterm.cases_pattern -> Decl_mode.elim_kind -> Decl_mode.elim_kind

val thesis_for :     constr ->
    constr -> Decl_mode.per_info -> Environ.env -> constr

val close_previous_case : pftreestate -> pftreestate

val pop_stacks : stack -> stack

val push_head : constr -> Idset.t -> stack -> stack

val push_arg : constr -> impl -> stack -> stack

val hrec_for: 
    identifier ->
    Decl_mode.per_info -> Proof_type.goal Tacmach.sigma -> 
    identifier -> constr

val consider_match :
   bool ->
    (identifier*bool) list ->
    identifier list ->
    (Term.types Decl_expr.statement, Term.types) Decl_expr.hyp list ->
    Proof_type.tactic

val init_tree:
    Idset.t ->
    inductive ->
    recpath ->
    (int -> recpath array -> (Idset.t * split_tree) option) ->
    split_tree
