open List0
open UsefulTypes
open VarInterface

type ('nVar, 'opid) coq_NTerm =
| Coq_vterm of 'nVar
| Coq_oterm of 'opid * ('nVar, 'opid) coq_BTerm list
and ('nVar, 'opid) coq_BTerm =
| Coq_bterm of 'nVar list * ('nVar, 'opid) coq_NTerm

(** val get_nt : ('a1, 'a2) coq_BTerm -> ('a1, 'a2) coq_NTerm **)

let get_nt = function
| Coq_bterm (_, nt) -> nt

(** val get_vars : ('a1, 'a2) coq_BTerm -> 'a1 list **)

let get_vars = function
| Coq_bterm (lv, _) -> lv

(** val free_vars : 'a1 coq_Deq -> ('a1, 'a2) coq_NTerm -> 'a1 list **)

let rec free_vars h = function
| Coq_vterm v -> v :: []
| Coq_oterm (_, bts) -> flat_map (free_vars_bterm h) bts

(** val free_vars_bterm : 'a1 coq_Deq -> ('a1, 'a2) coq_BTerm -> 'a1 list **)

and free_vars_bterm h = function
| Coq_bterm (lv, nt) -> remove_nvars h lv (free_vars h nt)

(** val getVar : ('a1, 'a2) coq_NTerm -> 'a1 option **)

let getVar = function
| Coq_vterm v -> Some v
| Coq_oterm (_, _) -> None

(** val btMapNt :
    (('a3, 'a1) coq_NTerm -> ('a3, 'a2) coq_NTerm) -> ('a3, 'a1) coq_BTerm ->
    ('a3, 'a2) coq_BTerm **)

let btMapNt f = function
| Coq_bterm (lv, nt) -> Coq_bterm (lv, (f nt))
