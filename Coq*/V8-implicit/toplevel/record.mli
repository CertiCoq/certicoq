(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: record.mli 6743 2005-02-18 22:14:08Z herbelin $ i*)

(*i*)
open Names
open Term
open Sign
open Vernacexpr
open Topconstr
(*i*)

(* [declare_projections ref coers params fields] declare projections of
   record [ref] (if allowed), and put them as coercions accordingly to
   [coers]; it returns the absolute names of projections *)

val declare_projections :
  inductive -> bool list -> rel_context -> bool list * constant option list

val definition_structure :
  lident with_coercion * local_binder list *
  (local_decl_expr with_coercion) list * identifier * sorts -> unit
