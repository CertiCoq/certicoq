open Datatypes
open List0
open Nat0
open PCUICAst
open PCUICAstUtils
open Utils

(** val lift : nat -> nat -> term -> term **)

let rec lift n k t = match t with
| Coq_tRel i -> if leb k i then Coq_tRel (add n i) else Coq_tRel i
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (lift n k) args))
| Coq_tProd (na, a, b) -> Coq_tProd (na, (lift n k a), (lift n (S k) b))
| Coq_tLambda (na, t0, m) -> Coq_tLambda (na, (lift n k t0), (lift n (S k) m))
| Coq_tLetIn (na, b, t0, b') ->
  Coq_tLetIn (na, (lift n k b), (lift n k t0), (lift n (S k) b'))
| Coq_tApp (u, v) -> Coq_tApp ((lift n k u), (lift n k v))
| Coq_tCase (ind, p, c, brs) ->
  let brs' = map (on_snd (lift n k)) brs in
  Coq_tCase (ind, (lift n k p), (lift n k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (lift n k c))
| Coq_tFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (lift n k) (lift n k')) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (lift n k) (lift n k')) mfix in
  Coq_tCoFix (mfix', idx)
| _ -> t

(** val subst : term list -> nat -> term -> term **)

let rec subst s k u = match u with
| Coq_tRel n ->
  if leb k n
  then (match nth_error s (sub n k) with
        | Some b -> lift k O b
        | None -> Coq_tRel (sub n (length s)))
  else Coq_tRel n
| Coq_tEvar (ev, args) -> Coq_tEvar (ev, (map (subst s k) args))
| Coq_tProd (na, a, b) -> Coq_tProd (na, (subst s k a), (subst s (S k) b))
| Coq_tLambda (na, t, m) -> Coq_tLambda (na, (subst s k t), (subst s (S k) m))
| Coq_tLetIn (na, b, ty, b') ->
  Coq_tLetIn (na, (subst s k b), (subst s k ty), (subst s (S k) b'))
| Coq_tApp (u0, v) -> Coq_tApp ((subst s k u0), (subst s k v))
| Coq_tCase (ind, p, c, brs) ->
  let brs' = map (on_snd (subst s k)) brs in
  Coq_tCase (ind, (subst s k p), (subst s k c), brs')
| Coq_tProj (p, c) -> Coq_tProj (p, (subst s k c))
| Coq_tFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (subst s k) (subst s k')) mfix in
  Coq_tFix (mfix', idx)
| Coq_tCoFix (mfix, idx) ->
  let k' = add (length mfix) k in
  let mfix' = map (map_def (subst s k) (subst s k')) mfix in
  Coq_tCoFix (mfix', idx)
| _ -> u

(** val subst1 : term -> nat -> term -> term **)

let subst1 t k u =
  subst (t :: []) k u
