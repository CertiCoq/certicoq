open BasicAst
open Datatypes
open PCUICAst
open Utils

(** val map_def : ('a1 -> 'a2) -> ('a1 -> 'a2) -> 'a1 def -> 'a2 def **)

let map_def tyf bodyf d =
  { dname = d.dname; dtype = (tyf d.dtype); dbody = (bodyf d.dbody); rarg =
    d.rarg }

(** val decompose_app_rec : term -> term list -> term * term list **)

let rec decompose_app_rec t l =
  match t with
  | Coq_tApp (f, a) -> decompose_app_rec f (a :: l)
  | _ -> (t, l)

(** val decompose_app : term -> term * term list **)

let decompose_app t =
  decompose_app_rec t []

(** val arities_context : one_inductive_body list -> context_decl list **)

let arities_context l =
  rev_map (fun ind -> vass (Coq_nNamed ind.ind_name) ind.ind_type) l

(** val decompose_prod_n_assum :
    context -> nat -> term -> (context * term) option **)

let rec decompose_prod_n_assum _UU0393_ n t =
  match n with
  | O -> Some (_UU0393_, t)
  | S n0 ->
    (match t with
     | Coq_tProd (na, a, b) ->
       decompose_prod_n_assum (snoc _UU0393_ (vass na a)) n0 b
     | Coq_tLetIn (na, b, bty, b') ->
       decompose_prod_n_assum (snoc _UU0393_ (vdef na b bty)) n0 b'
     | _ -> None)
