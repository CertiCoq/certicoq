open BinNat
open Datatypes
open FMapPositive
open List0
open UsefulTypes
open List1
open Terms

type ('name, 'opid) coq_DTerm =
| Coq_vterm of int
| Coq_oterm of 'opid * ('name, 'opid) coq_DBTerm list
and ('name, 'opid) coq_DBTerm =
| Coq_bterm of 'name list * ('name, 'opid) coq_DTerm

(** val get_bvars : ('a1, 'a2) coq_DBTerm -> 'a1 list **)

let get_bvars = function
| Coq_bterm (n, _) -> n

(** val num_bvars : ('a1, 'a2) coq_DBTerm -> nat **)

let num_bvars bt =
  length (get_bvars bt)

(** val lookupNDef : 'a1 -> 'a1 pmap -> int -> 'a1 **)

let lookupNDef def names var =
  opExtract def (pmap_lookup (N.succ_pos var) names)

(** val insertN : 'a1 pmap -> (int * 'a1) -> 'a1 pmap **)

let insertN names = function
| (var, name) -> pmap_insert (N.succ_pos var) name names

(** val insertNs : 'a1 pmap -> (int * 'a1) list -> 'a1 pmap **)

let insertNs names nvars =
  fold_left insertN nvars names

(** val fromDB :
    'a1 -> ((int * 'a1) -> 'a3) -> int -> 'a1 pmap -> ('a1, 'a2) coq_DTerm ->
    ('a3, 'a2) coq_NTerm **)

let rec fromDB defn mkVar max names = function
| Coq_vterm n ->
  Terms.Coq_vterm
    (mkVar ((N.sub (N.sub max n) 1),
      (lookupNDef defn names (N.sub (N.sub max n) 1))))
| Coq_oterm (o, lbt) ->
  Terms.Coq_oterm (o, (map (fromDB_bt defn mkVar max names) lbt))

(** val fromDB_bt :
    'a1 -> ((int * 'a1) -> 'a3) -> int -> 'a1 pmap -> ('a1, 'a2) coq_DBTerm
    -> ('a3, 'a2) coq_BTerm **)

and fromDB_bt defn mkVar max names = function
| Coq_bterm (ln, dt) ->
  let len = length ln in
  let vars = seq N.succ max len in
  let nvars = combine vars ln in
  let names0 = insertNs names nvars in
  let bvars = map mkVar nvars in
  Terms.Coq_bterm (bvars,
  (fromDB defn mkVar (N.add max (N.of_nat len)) names0 dt))
