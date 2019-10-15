open BasicAst
open Datatypes
open List0

type dcon = inductive * int

type exp =
| Var_e of int
| Lam_e of name * exp
| App_e of exp * exp
| Con_e of dcon * exps
| Match_e of exp * int * branches_e
| Let_e of name * exp * exp
| Fix_e of efnlst * int
| Prf_e
and exps =
| Coq_enil
| Coq_econs of exp * exps
and efnlst =
| Coq_eflnil
| Coq_eflcons of name * exp * efnlst
and branches_e =
| Coq_brnil_e
| Coq_brcons_e of dcon * (int * name list) * exp * branches_e

val nNameds : char list -> name

val efnlst_as_list : efnlst -> (name * exp) list

val fnames : efnlst -> name list
