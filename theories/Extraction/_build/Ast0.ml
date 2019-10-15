open BasicAst
open Datatypes
open UGraph0
open Univ0

type term =
| Coq_tRel of nat
| Coq_tVar of ident
| Coq_tMeta of nat
| Coq_tEvar of nat * term list
| Coq_tSort of universe
| Coq_tCast of term * cast_kind * term
| Coq_tProd of name * term * term
| Coq_tLambda of name * term * term
| Coq_tLetIn of name * term * term * term
| Coq_tApp of term * term list
| Coq_tConst of kername * universe_instance
| Coq_tInd of inductive * universe_instance
| Coq_tConstruct of inductive * nat * universe_instance
| Coq_tCase of (inductive * nat) * term * term * (nat * term) list
| Coq_tProj of projection * term
| Coq_tFix of term mfixpoint * nat
| Coq_tCoFix of term mfixpoint * nat

(** val term_rect :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> 'a1) -> (nat -> term list ->
    'a1) -> (universe -> 'a1) -> (term -> 'a1 -> cast_kind -> term -> 'a1 ->
    'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (name -> term ->
    'a1 -> term -> 'a1 -> 'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> term
    -> 'a1 -> 'a1) -> (term -> 'a1 -> term list -> 'a1) -> (kername ->
    universe_instance -> 'a1) -> (inductive -> universe_instance -> 'a1) ->
    (inductive -> nat -> universe_instance -> 'a1) -> ((inductive * nat) ->
    term -> 'a1 -> term -> 'a1 -> (nat * term) list -> 'a1) -> (projection ->
    term -> 'a1 -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term mfixpoint
    -> nat -> 'a1) -> term -> 'a1 **)

let rec term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
| Coq_tRel n -> f n
| Coq_tVar id -> f0 id
| Coq_tMeta meta -> f1 meta
| Coq_tEvar (ev, args) -> f2 ev args
| Coq_tSort s -> f3 s
| Coq_tCast (t1, kind, v) ->
  f4 t1
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 t1)
    kind v
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 v)
| Coq_tProd (na, ty, body) ->
  f5 na ty
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ty)
    body
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 body)
| Coq_tLambda (na, ty, body) ->
  f6 na ty
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ty)
    body
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 body)
| Coq_tLetIn (na, def, def_ty, body) ->
  f7 na def
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 def)
    def_ty
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 def_ty)
    body
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 body)
| Coq_tApp (f16, args) ->
  f8 f16
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16)
    args
| Coq_tConst (c, u) -> f9 c u
| Coq_tInd (ind, u) -> f10 ind u
| Coq_tConstruct (ind, idx, u) -> f11 ind idx u
| Coq_tCase (ind_and_nbparams, type_info, discr, branches) ->
  f12 ind_and_nbparams type_info
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      type_info) discr
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 discr)
    branches
| Coq_tProj (proj, t1) ->
  f13 proj t1
    (term_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 t1)
| Coq_tFix (mfix, idx) -> f14 mfix idx
| Coq_tCoFix (mfix, idx) -> f15 mfix idx

(** val term_rec :
    (nat -> 'a1) -> (ident -> 'a1) -> (nat -> 'a1) -> (nat -> term list ->
    'a1) -> (universe -> 'a1) -> (term -> 'a1 -> cast_kind -> term -> 'a1 ->
    'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> 'a1) -> (name -> term ->
    'a1 -> term -> 'a1 -> 'a1) -> (name -> term -> 'a1 -> term -> 'a1 -> term
    -> 'a1 -> 'a1) -> (term -> 'a1 -> term list -> 'a1) -> (kername ->
    universe_instance -> 'a1) -> (inductive -> universe_instance -> 'a1) ->
    (inductive -> nat -> universe_instance -> 'a1) -> ((inductive * nat) ->
    term -> 'a1 -> term -> 'a1 -> (nat * term) list -> 'a1) -> (projection ->
    term -> 'a1 -> 'a1) -> (term mfixpoint -> nat -> 'a1) -> (term mfixpoint
    -> nat -> 'a1) -> term -> 'a1 **)

let rec term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 = function
| Coq_tRel n -> f n
| Coq_tVar id -> f0 id
| Coq_tMeta meta -> f1 meta
| Coq_tEvar (ev, args) -> f2 ev args
| Coq_tSort s -> f3 s
| Coq_tCast (t1, kind, v) ->
  f4 t1 (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 t1)
    kind v
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 v)
| Coq_tProd (na, ty, body) ->
  f5 na ty
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ty)
    body
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 body)
| Coq_tLambda (na, ty, body) ->
  f6 na ty
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 ty)
    body
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 body)
| Coq_tLetIn (na, def, def_ty, body) ->
  f7 na def
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 def)
    def_ty
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 def_ty)
    body
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 body)
| Coq_tApp (f16, args) ->
  f8 f16
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16)
    args
| Coq_tConst (c, u) -> f9 c u
| Coq_tInd (ind, u) -> f10 ind u
| Coq_tConstruct (ind, idx, u) -> f11 ind idx u
| Coq_tCase (ind_and_nbparams, type_info, discr, branches) ->
  f12 ind_and_nbparams type_info
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      type_info) discr
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 discr)
    branches
| Coq_tProj (proj, t1) ->
  f13 proj t1
    (term_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 t1)
| Coq_tFix (mfix, idx) -> f14 mfix idx
| Coq_tCoFix (mfix, idx) -> f15 mfix idx

(** val mkApps : term -> term list -> term **)

let mkApps t0 us = match us with
| [] -> t0
| _ :: _ ->
  (match t0 with
   | Coq_tApp (f, args) -> Coq_tApp (f, (app args us))
   | _ -> Coq_tApp (t0, us))

(** val mkApp : term -> term -> term **)

let mkApp t0 u =
  match t0 with
  | Coq_tApp (f, args) -> Coq_tApp (f, (app args (u :: [])))
  | _ -> Coq_tApp (t0, (u :: []))

(** val isApp : term -> bool **)

let isApp = function
| Coq_tApp (_, _) -> true
| _ -> false

(** val isLambda : term -> bool **)

let isLambda = function
| Coq_tLambda (_, _, _) -> true
| _ -> false

type parameter_entry = { parameter_entry_type : term;
                         parameter_entry_universes : universe_context }

(** val parameter_entry_type : parameter_entry -> term **)

let parameter_entry_type x = x.parameter_entry_type

(** val parameter_entry_universes : parameter_entry -> universe_context **)

let parameter_entry_universes x = x.parameter_entry_universes

type definition_entry = { definition_entry_type : term;
                          definition_entry_body : term;
                          definition_entry_universes : universe_context;
                          definition_entry_opaque : bool }

(** val definition_entry_type : definition_entry -> term **)

let definition_entry_type x = x.definition_entry_type

(** val definition_entry_body : definition_entry -> term **)

let definition_entry_body x = x.definition_entry_body

(** val definition_entry_universes : definition_entry -> universe_context **)

let definition_entry_universes x = x.definition_entry_universes

(** val definition_entry_opaque : definition_entry -> bool **)

let definition_entry_opaque x = x.definition_entry_opaque

type constant_entry =
| ParameterEntry of parameter_entry
| DefinitionEntry of definition_entry

(** val constant_entry_rect :
    (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry
    -> 'a1 **)

let constant_entry_rect f f0 = function
| ParameterEntry x -> f x
| DefinitionEntry x -> f0 x

(** val constant_entry_rec :
    (parameter_entry -> 'a1) -> (definition_entry -> 'a1) -> constant_entry
    -> 'a1 **)

let constant_entry_rec f f0 = function
| ParameterEntry x -> f x
| DefinitionEntry x -> f0 x

type recursivity_kind =
| Finite
| CoFinite
| BiFinite

(** val recursivity_kind_rect :
    'a1 -> 'a1 -> 'a1 -> recursivity_kind -> 'a1 **)

let recursivity_kind_rect f f0 f1 = function
| Finite -> f
| CoFinite -> f0
| BiFinite -> f1

(** val recursivity_kind_rec :
    'a1 -> 'a1 -> 'a1 -> recursivity_kind -> 'a1 **)

let recursivity_kind_rec f f0 f1 = function
| Finite -> f
| CoFinite -> f0
| BiFinite -> f1

type local_entry =
| LocalDef of term
| LocalAssum of term

(** val local_entry_rect :
    (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1 **)

let local_entry_rect f f0 = function
| LocalDef x -> f x
| LocalAssum x -> f0 x

(** val local_entry_rec :
    (term -> 'a1) -> (term -> 'a1) -> local_entry -> 'a1 **)

let local_entry_rec f f0 = function
| LocalDef x -> f x
| LocalAssum x -> f0 x

type one_inductive_entry = { mind_entry_typename : ident;
                             mind_entry_arity : term;
                             mind_entry_template : bool;
                             mind_entry_consnames : ident list;
                             mind_entry_lc : term list }

(** val mind_entry_typename : one_inductive_entry -> ident **)

let mind_entry_typename x = x.mind_entry_typename

(** val mind_entry_arity : one_inductive_entry -> term **)

let mind_entry_arity x = x.mind_entry_arity

(** val mind_entry_template : one_inductive_entry -> bool **)

let mind_entry_template x = x.mind_entry_template

(** val mind_entry_consnames : one_inductive_entry -> ident list **)

let mind_entry_consnames x = x.mind_entry_consnames

(** val mind_entry_lc : one_inductive_entry -> term list **)

let mind_entry_lc x = x.mind_entry_lc

type mutual_inductive_entry = { mind_entry_record : ident option option;
                                mind_entry_finite : recursivity_kind;
                                mind_entry_params : (ident * local_entry) list;
                                mind_entry_inds : one_inductive_entry list;
                                mind_entry_universes : universe_context;
                                mind_entry_private : bool option }

(** val mind_entry_record : mutual_inductive_entry -> ident option option **)

let mind_entry_record x = x.mind_entry_record

(** val mind_entry_finite : mutual_inductive_entry -> recursivity_kind **)

let mind_entry_finite x = x.mind_entry_finite

(** val mind_entry_params :
    mutual_inductive_entry -> (ident * local_entry) list **)

let mind_entry_params x = x.mind_entry_params

(** val mind_entry_inds :
    mutual_inductive_entry -> one_inductive_entry list **)

let mind_entry_inds x = x.mind_entry_inds

(** val mind_entry_universes : mutual_inductive_entry -> universe_context **)

let mind_entry_universes x = x.mind_entry_universes

(** val mind_entry_private : mutual_inductive_entry -> bool option **)

let mind_entry_private x = x.mind_entry_private

type context_decl = { decl_name : name; decl_body : term option;
                      decl_type : term }

(** val decl_name : context_decl -> name **)

let decl_name x = x.decl_name

(** val decl_body : context_decl -> term option **)

let decl_body x = x.decl_body

(** val decl_type : context_decl -> term **)

let decl_type x = x.decl_type

(** val vass : name -> term -> context_decl **)

let vass x a =
  { decl_name = x; decl_body = None; decl_type = a }

(** val vdef : name -> term -> term -> context_decl **)

let vdef x t0 a =
  { decl_name = x; decl_body = (Some t0); decl_type = a }

type context = context_decl list

(** val snoc : 'a1 list -> 'a1 -> 'a1 list **)

let snoc _UU0393_ d =
  d :: _UU0393_

type one_inductive_body = { ind_name : ident; ind_type : term;
                            ind_kelim : sort_family list;
                            ind_ctors : ((ident * term) * nat) list;
                            ind_projs : (ident * term) list }

(** val ind_name : one_inductive_body -> ident **)

let ind_name x = x.ind_name

(** val ind_type : one_inductive_body -> term **)

let ind_type x = x.ind_type

(** val ind_kelim : one_inductive_body -> sort_family list **)

let ind_kelim x = x.ind_kelim

(** val ind_ctors : one_inductive_body -> ((ident * term) * nat) list **)

let ind_ctors x = x.ind_ctors

(** val ind_projs : one_inductive_body -> (ident * term) list **)

let ind_projs x = x.ind_projs

type mutual_inductive_body = { ind_npars : nat; ind_params : context;
                               ind_bodies : one_inductive_body list;
                               ind_universes : universe_context }

(** val ind_npars : mutual_inductive_body -> nat **)

let ind_npars x = x.ind_npars

(** val ind_params : mutual_inductive_body -> context **)

let ind_params x = x.ind_params

(** val ind_bodies : mutual_inductive_body -> one_inductive_body list **)

let ind_bodies x = x.ind_bodies

(** val ind_universes : mutual_inductive_body -> universe_context **)

let ind_universes x = x.ind_universes

type constant_body = { cst_type : term; cst_body : term option;
                       cst_universes : universe_context }

(** val cst_type : constant_body -> term **)

let cst_type x = x.cst_type

(** val cst_body : constant_body -> term option **)

let cst_body x = x.cst_body

(** val cst_universes : constant_body -> universe_context **)

let cst_universes x = x.cst_universes

type global_decl =
| ConstantDecl of kername * constant_body
| InductiveDecl of kername * mutual_inductive_body

(** val global_decl_rect :
    (kername -> constant_body -> 'a1) -> (kername -> mutual_inductive_body ->
    'a1) -> global_decl -> 'a1 **)

let global_decl_rect f f0 = function
| ConstantDecl (x, x0) -> f x x0
| InductiveDecl (x, x0) -> f0 x x0

(** val global_decl_rec :
    (kername -> constant_body -> 'a1) -> (kername -> mutual_inductive_body ->
    'a1) -> global_decl -> 'a1 **)

let global_decl_rec f f0 = function
| ConstantDecl (x, x0) -> f x x0
| InductiveDecl (x, x0) -> f0 x x0

type global_declarations = global_decl list

type global_context = global_declarations * t

type program = global_declarations * term
