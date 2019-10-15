open BasicAst
open Datatypes
open Utils

(** val ident_eq : ident -> ident -> bool **)

let ident_eq x y =
  match string_compare x y with
  | Eq -> true
  | _ -> false
