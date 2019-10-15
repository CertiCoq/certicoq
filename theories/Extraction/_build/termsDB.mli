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

val get_bvars : ('a1, 'a2) coq_DBTerm -> 'a1 list

val num_bvars : ('a1, 'a2) coq_DBTerm -> nat

val lookupNDef : 'a1 -> 'a1 pmap -> int -> 'a1

val insertN : 'a1 pmap -> (int * 'a1) -> 'a1 pmap

val insertNs : 'a1 pmap -> (int * 'a1) list -> 'a1 pmap

val fromDB :
  'a1 -> ((int * 'a1) -> 'a3) -> int -> 'a1 pmap -> ('a1, 'a2) coq_DTerm ->
  ('a3, 'a2) coq_NTerm

val fromDB_bt :
  'a1 -> ((int * 'a1) -> 'a3) -> int -> 'a1 pmap -> ('a1, 'a2) coq_DBTerm ->
  ('a3, 'a2) coq_BTerm
