open BasicAst
open BinPos
open String1
open String0
open Cps

type nEnv = name M.t

(** val show_pos : int -> char list **)

let show_pos x =
  nat2string10 (Pos.to_nat x)

type string_tree =
| Emp
| Str of char list
| App of string_tree * string_tree

(** val show_tree_c : string_tree -> char list -> char list **)

let rec show_tree_c t0 acc =
  match t0 with
  | Emp -> acc
  | Str s -> append s acc
  | App (t1, t2) -> show_tree_c t1 (show_tree_c t2 acc)

(** val show_tree : string_tree -> char list **)

let show_tree t0 =
  show_tree_c t0 []

(** val show_var : nEnv -> int -> string_tree **)

let show_var nenv x =
  match M.get x nenv with
  | Some n ->
    (match n with
     | Coq_nAnon -> App ((Str ('x'::[])), (Str (show_pos x)))
     | Coq_nNamed s ->
       App ((App ((Str s), (Str ('_'::[])))), (Str (show_pos x))))
  | None -> App ((Str ('x'::[])), (Str (show_pos x)))
