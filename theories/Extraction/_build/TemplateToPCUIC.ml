open Ast0
open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICAstUtils
open UGraph0
open Univ0
open Utils

module T = Ast0

(** val trans : T.term -> term **)

let rec trans = function
| T.Coq_tRel n -> Coq_tRel n
| T.Coq_tVar n -> Coq_tVar n
| T.Coq_tMeta n -> Coq_tMeta n
| T.Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map trans args))
| T.Coq_tSort u -> Coq_tSort u
| T.Coq_tCast (c, _, t1) ->
  Coq_tApp ((Coq_tLambda (Coq_nAnon, (trans t1), (Coq_tRel O))), (trans c))
| T.Coq_tProd (na, a, b) -> Coq_tProd (na, (trans a), (trans b))
| T.Coq_tLambda (na, t1, m) -> Coq_tLambda (na, (trans t1), (trans m))
| T.Coq_tLetIn (na, b, t1, b') ->
  Coq_tLetIn (na, (trans b), (trans t1), (trans b'))
| T.Coq_tApp (u, v) -> mkApps (trans u) (map trans v)
| T.Coq_tConst (c, u) -> Coq_tConst (c, u)
| T.Coq_tInd (c, u) -> Coq_tInd (c, u)
| T.Coq_tConstruct (c, k, u) -> Coq_tConstruct (c, k, u)
| T.Coq_tCase (ind, p, c, brs) ->
  let brs' = map (on_snd trans) brs in
  Coq_tCase (ind, (trans p), (trans c), brs')
| T.Coq_tProj (p, c) -> Coq_tProj (p, (trans c))
| T.Coq_tFix (mfix, idx) ->
  let mfix' = map (map_def trans trans) mfix in Coq_tFix (mfix', idx)
| T.Coq_tCoFix (mfix, idx) ->
  let mfix' = map (map_def trans trans) mfix in Coq_tCoFix (mfix', idx)

(** val trans_decl : T.context_decl -> context_decl **)

let trans_decl d =
  let { T.decl_name = na; T.decl_body = b; T.decl_type = t0 } = d in
  { decl_name = na; decl_body = (option_map trans b); decl_type = (trans t0) }

(** val trans_local : T.context_decl list -> context_decl list **)

let trans_local _UU0393_ =
  map trans_decl _UU0393_

(** val trans_one_ind_body : T.one_inductive_body -> one_inductive_body **)

let trans_one_ind_body d =
  { ind_name = d.T.ind_name; ind_type = (trans d.T.ind_type); ind_kelim =
    d.T.ind_kelim; ind_ctors =
    (map (fun pat ->
      let (y0, z) = pat in let (x, y) = y0 in ((x, (trans y)), z))
      d.T.ind_ctors); ind_projs =
    (map (fun pat -> let (x, y) = pat in (x, (trans y))) d.T.ind_projs) }

(** val trans_constant_body : T.constant_body -> constant_body **)

let trans_constant_body bd =
  { cst_type = (trans bd.T.cst_type); cst_body =
    (option_map trans bd.T.cst_body); cst_universes = bd.T.cst_universes }

(** val trans_minductive_body :
    T.mutual_inductive_body -> mutual_inductive_body **)

let trans_minductive_body md =
  { ind_npars = md.T.ind_npars; ind_params = (trans_local md.T.ind_params);
    ind_bodies = (map trans_one_ind_body md.T.ind_bodies); ind_universes =
    md.T.ind_universes }

(** val trans_global_decl : T.global_decl -> global_decl **)

let trans_global_decl = function
| T.ConstantDecl (kn, bd) -> ConstantDecl (kn, (trans_constant_body bd))
| T.InductiveDecl (kn, bd) -> InductiveDecl (kn, (trans_minductive_body bd))

(** val trans_global_decls : T.global_decl list -> global_decl list **)

let trans_global_decls d =
  map trans_global_decl d

(** val trans_global : T.global_context -> global_decl list * t **)

let trans_global _UU03a3_ =
  ((trans_global_decls (fst _UU03a3_)), (snd _UU03a3_))
