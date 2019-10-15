open List0
open PCUICAst
open PCUICAstUtils
open UnivSubst
open Univ0
open Utils

(** val subst_instance_constr : universe_instance -> term -> term **)

let rec subst_instance_constr u c = match c with
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (subst_instance_constr u) args))
| Coq_tSort s -> Coq_tSort (subst_instance_univ u s)
| Coq_tProd (na, a, b) ->
  Coq_tProd (na, (subst_instance_constr u a), (subst_instance_constr u b))
| Coq_tLambda (na, t, m) ->
  Coq_tLambda (na, (subst_instance_constr u t), (subst_instance_constr u m))
| Coq_tLetIn (na, b, ty, b') ->
  Coq_tLetIn (na, (subst_instance_constr u b), (subst_instance_constr u ty),
    (subst_instance_constr u b'))
| Coq_tApp (f, v) ->
  Coq_tApp ((subst_instance_constr u f), (subst_instance_constr u v))
| Coq_tConst (c0, u') -> Coq_tConst (c0, (subst_instance_instance u u'))
| Coq_tInd (i, u') -> Coq_tInd (i, (subst_instance_instance u u'))
| Coq_tConstruct (ind, k, u') ->
  Coq_tConstruct (ind, k, (subst_instance_instance u u'))
| Coq_tCase (ind, p, c0, brs) ->
  let brs' = map (on_snd (subst_instance_constr u)) brs in
  Coq_tCase (ind, (subst_instance_constr u p), (subst_instance_constr u c0),
  brs')
| Coq_tProj (p, c0) -> Coq_tProj (p, (subst_instance_constr u c0))
| Coq_tFix (mfix, idx) ->
  let mfix' =
    map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix
  in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let mfix' =
    map (map_def (subst_instance_constr u) (subst_instance_constr u)) mfix
  in
  Coq_tCoFix (mfix', idx)
| _ -> c
