open List0
open UsefulTypes
open VarInterface

type ('nVar, 'opid) coq_NTerm =
| Coq_vterm of 'nVar
| Coq_oterm of 'opid * ('nVar, 'opid) coq_BTerm list
and ('nVar, 'opid) coq_BTerm =
| Coq_bterm of 'nVar list * ('nVar, 'opid) coq_NTerm

val get_nt : ('a1, 'a2) coq_BTerm -> ('a1, 'a2) coq_NTerm

val get_vars : ('a1, 'a2) coq_BTerm -> 'a1 list

val free_vars : 'a1 coq_Deq -> ('a1, 'a2) coq_NTerm -> 'a1 list

val free_vars_bterm : 'a1 coq_Deq -> ('a1, 'a2) coq_BTerm -> 'a1 list

val getVar : ('a1, 'a2) coq_NTerm -> 'a1 option

val btMapNt :
  (('a3, 'a1) coq_NTerm -> ('a3, 'a2) coq_NTerm) -> ('a3, 'a1) coq_BTerm ->
  ('a3, 'a2) coq_BTerm
