open BasicAst
open BinPos
open String1
open String0
open Cps

type nEnv = name M.t

val show_pos : int -> char list

type string_tree =
| Emp
| Str of char list
| App of string_tree * string_tree

val show_tree_c : string_tree -> char list -> char list

val show_tree : string_tree -> char list

val show_var : nEnv -> int -> string_tree
