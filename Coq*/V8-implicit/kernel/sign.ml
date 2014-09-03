(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, * CNRS-Ecole Polytechnique-INRIA Futurs-Universite Paris Sud *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(* $Id: sign.ml 9103 2006-09-01 11:02:52Z herbelin $ *)

open Names
open Util
open Term

(*s Signatures of named hypotheses. Used for section variables and
    goal assumptions. *)

type named_context = named_declaration list

let empty_named_context = []

let add_named_decl d sign = d::sign

let rec lookup_named id = function
  | (id',_,_,_ as decl) :: _ when id=id' -> decl
  | _ :: sign -> lookup_named id sign
  | [] -> raise Not_found

let named_context_length = List.length

let vars_of_named_context = List.map (fun (id,_,_,_) -> id)

let instance_from_named_context sign =
  let rec inst_rec rinst rimps = function
    | (id,imp,None,_) :: sign ->
        inst_rec (mkVar id::rinst) (imp::rimps) sign
    | _ :: sign -> inst_rec rinst rimps sign
    | [] -> Array.of_list(List.rev rinst), Array.of_list(List.rev rimps) in
  inst_rec [] [] sign

let imps_from_named_context sign =
  let rec inst_rec imps = function
    | (id,imp,None,_) :: sign -> inst_rec (imp::imps) sign
    | _ :: sign -> inst_rec imps sign
    | [] -> imps in
  inst_rec [] sign
let set_impl_named_context imp ctxt =
  List.map (fun (na,_,b,t) -> (na,imp,b,t)) ctxt

let is_expl_named ctxt i =
  match lookup_named i ctxt with
      (_,Expl,_,_) -> true
    | _ -> false

let fold_named_context f l ~init = List.fold_right f l init
let fold_named_context_reverse f ~init l = List.fold_left f init l

(*s Signatures of ordered section variables *)
type section_context = named_context

(*s Signatures of ordered optionally named variables, intended to be
   accessed by de Bruijn indices (to represent bound variables) *)

type rel_declaration = name * impl * constr option * types
type rel_context = rel_declaration list

let empty_rel_context = []

let add_rel_decl d ctxt = d::ctxt

let rec lookup_rel n sign =
  match n, sign with
  | 1, decl :: _ -> decl
  | n, _ :: sign -> lookup_rel (n-1) sign
  | _, []        -> raise Not_found

let rel_context_length = List.length

let rel_context_nhyps hyps =
  let rec nhyps acc = function
    | [] -> acc
    | (_,_,None,_)::hyps -> nhyps (1+acc) hyps
    | (_,_,Some _,_)::hyps -> nhyps acc hyps in
  nhyps 0 hyps

let fold_rel_context f l ~init:x = List.fold_right f l x
let fold_rel_context_reverse f ~init:x l = List.fold_left f x l

let map_context f l =
  let map_decl (n, imp, body_o, typ as decl) =
    let body_o' = option_smartmap f body_o in
    let typ' = f typ in
      if body_o' == body_o && typ' == typ then decl else
	(n, imp, body_o', typ')
  in
    list_smartmap map_decl l

let map_rel_context = map_context
let map_named_context = map_context

let iter_rel_context f = List.iter (fun (_,_,b,t) -> f t; option_iter f b)
let iter_named_context f = List.iter (fun (_,_,b,t) -> f t; option_iter f b)

(* Push named declarations on top of a rel context *)
(* Bizarre. Should be avoided. *)
let push_named_to_rel_context hyps ctxt =
  let rec push = function
    | (id,imp,b,t) :: l ->
	let s, hyps = push l in
	let d = (Name id, imp,option_map (subst_vars s) b, type_app (subst_vars s) t) in
	id::s, d::hyps
    | [] -> [],[] in
  let s, hyps = push hyps in
  let rec subst = function
    | d :: l ->
	let n, ctxt = subst l in
	(n+1), (map_rel_declaration (substn_vars n s) d)::ctxt
    | [] -> 1, hyps in
  snd (subst ctxt)

let imps_from_rel_context = imps_from_named_context
let set_impl_rel_context = set_impl_named_context
let is_expl_rel ctxt i =
  match lookup_rel i ctxt with
      (_,Expl,_,_) -> true
    | _ -> false

(*********************************)
(*       Term constructors       *)
(*********************************)

let it_mkProd_or_LetIn   =
  List.fold_left (fun c d -> mkProd_or_LetIn d c)
let it_mkLambda_or_LetIn =
  List.fold_left (fun c d -> mkLambda_or_LetIn d c)

(*********************************)
(*       Term destructors        *)
(*********************************)

type arity = rel_context * sorts

(* Decompose an arity (i.e. a product of the form (x1:T1)..(xn:Tn)s
   with s a sort) into the pair ([(xn,Tn);...;(x1,T1)],s) *)

let destArity = 
  let rec prodec_rec l c =
    match kind_of_term c with
    | Prod (x,imp,t,c)    -> prodec_rec ((x,imp,None,t)::l) c
    | LetIn (x,imp,b,t,c) -> prodec_rec ((x,imp,Some b,t)::l) c
    | Cast (c,_,_)      -> prodec_rec l c
    | Sort s          -> l,s
    | _               -> anomaly "destArity: not an arity"
  in 
  prodec_rec []

let mkArity (sign,s) = it_mkProd_or_LetIn (mkSort s) sign

let rec isArity c =
  match kind_of_term c with
  | Prod (_,_,_,c)    -> isArity c
  | LetIn (_,_,b,_,c  ) -> isArity (subst1 b c)
  | Cast (c,_,_)      -> isArity c
  | Sort _          -> true
  | _               -> false

(* Transforms a product term (x1:T1)..(xn:Tn)T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a product *)
let decompose_prod_assum = 
  let rec prodec_rec l c =
    match kind_of_term c with
    | Prod (x,imp,t,c)    ->
        prodec_rec (add_rel_decl (x,imp,None,t) l) c
    | LetIn (x,imp,b,t,c) ->
        prodec_rec (add_rel_decl (x,imp,Some b,t) l) c
    | Cast (c,_,_)      -> prodec_rec l c
    | _               -> l,c
  in 
  prodec_rec empty_rel_context

(* Transforms a lambda term [x1:T1]..[xn:Tn]T into the pair
   ([(xn,Tn);...;(x1,T1)],T), where T is not a lambda *)
let decompose_lam_assum = 
  let rec lamdec_rec l c =
    match kind_of_term c with
    | Lambda (x,imp,t,c)  ->
        lamdec_rec (add_rel_decl (x,imp,None,t) l) c
    | LetIn (x,imp,b,t,c) ->
        lamdec_rec (add_rel_decl (x,imp,Some b,t) l) c
    | Cast (c,_,_)      -> lamdec_rec l c
    | _               -> l,c
  in 
  lamdec_rec empty_rel_context

(* Given a positive integer n, transforms a product term (x1:T1)..(xn:Tn)T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_prod_n_assum n =
  if n < 0 then
    error "decompose_prod_n_assum: integer parameter must be positive";
  let rec prodec_rec l n c = 
    if n=0 then l,c
    else match kind_of_term c with 
    | Prod (x,imp,t,c)    ->
        prodec_rec (add_rel_decl (x,imp,None,t) l) (n-1) c
    | LetIn (x,imp,b,t,c) ->
        prodec_rec (add_rel_decl (x,imp,Some b,t) l) (n-1) c
    | Cast (c,_,_)      -> prodec_rec l n c
    | c -> error "decompose_prod_n_assum: not enough assumptions"
  in 
  prodec_rec empty_rel_context n

(* Given a positive integer n, transforms a lambda term [x1:T1]..[xn:Tn]T 
   into the pair ([(xn,Tn);...;(x1,T1)],T) *)
let decompose_lam_n_assum n =
  if n < 0 then
    error "decompose_lam_n_assum: integer parameter must be positive";
  let rec lamdec_rec l n c = 
    if n=0 then l,c 
    else match kind_of_term c with 
    | Lambda (x,imp,t,c)  ->
        lamdec_rec (add_rel_decl (x,imp,None,t) l) (n-1) c
    | LetIn (x,imp,b,t,c) ->
        lamdec_rec (add_rel_decl (x,imp,Some b,t) l) (n-1) c
    | Cast (c,_,_)      -> lamdec_rec l n c
    | c -> error "decompose_lam_n_assum: not enough abstractions"
  in 
  lamdec_rec empty_rel_context n 
