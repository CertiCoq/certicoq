open BasicAst
open String0
open Cps
open Map_util

type nEnv = name M.t

(** val n_empty : nEnv **)

let n_empty =
  M.empty

(** val add_entry : nEnv -> var -> var -> char list -> nEnv **)

let add_entry nenv x x_origin suff =
  match M.get x_origin nenv with
  | Some n ->
    (match n with
     | Coq_nAnon ->
       M.set x (Coq_nNamed (append ('a'::('n'::('o'::('n'::[])))) suff)) nenv
     | Coq_nNamed s -> M.set x (Coq_nNamed (append s suff)) nenv)
  | None ->
    M.set x (Coq_nNamed (append ('a'::('n'::('o'::('n'::[])))) suff)) nenv

(** val add_entry_str : nEnv -> var -> char list -> nEnv **)

let add_entry_str nenv x name0 =
  M.set x (Coq_nNamed name0) nenv
