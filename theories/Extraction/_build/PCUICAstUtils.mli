open BasicAst
open Datatypes
open PCUICAst
open Utils

val map_def : ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 def -> 'a2 def

val decompose_app_rec : term -> term list -> term * term list

val decompose_app : term -> term * term list

val arities_context : one_inductive_body list -> context_decl list

val decompose_prod_n_assum : context -> nat -> term -> (context * term) option
