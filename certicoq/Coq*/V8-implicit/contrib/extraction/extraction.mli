(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i $Id: extraction.mli 6303 2004-11-16 12:37:40Z sacerdot $ i*)

(*s Extraction from Coq terms to Miniml. *)

open Names
open Term
open Declarations
open Environ
open Libnames
open Miniml

val extract_constant : env -> constant -> constant_body -> ml_decl

val extract_constant_spec : env -> constant -> constant_body -> ml_spec

val extract_fixpoint : 
  env -> constant array -> (constr, types) prec_declaration -> ml_decl 

val extract_inductive : env -> kernel_name -> ml_ind

(*s ML declaration corresponding to a Coq reference. *)

val extract_declaration : env -> global_reference -> ml_decl

(*s Without doing complete extraction, just guess what a constant would be. *) 

type kind = Logical | Term | Type 

val constant_kind : env -> constant_body -> kind

(*s Is a [ml_decl] or a [ml_spec] logical ? *) 

val logical_decl : ml_decl -> bool
val logical_spec : ml_spec -> bool

val impl_aware : bool ref

(* DEBUG: *)
type info = Logic | Info
type scheme = TypeScheme | Default
type flag = info * scheme
val flag_of_type : env -> impl -> types -> flag
val extract_type :
  env -> int list -> int ->
    constr -> constr list -> impl list -> ml_type
val extract_term :
  env -> Mlutil.Mlenv.t -> ml_type ->
    constr -> constr list -> impl list -> ml_ast
