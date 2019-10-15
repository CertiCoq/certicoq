open Bool
open Coqlib0
open Datatypes
open List0
open Nat0
open Cps

type live_fun =
| Live of var list list * bool list list

val bool_live : live_fun -> bool list list

val get_vars : fundefs -> var list list

val get_funs : fundefs -> var list

val get_bool_false : var list -> bool list

val get_bool_true : var list -> bool list

val get_bools : fundefs -> bool list list

val get_live_initial : fundefs -> live_fun

val replace_nth : nat -> 'a1 list -> 'a1 -> 'a1 list

val find_fun : var -> var list -> nat -> bool * nat

val add_escaping : var -> live_fun -> var list -> live_fun

val add_escapings' : var list -> live_fun -> var list -> live_fun

val add_var_helper : var -> var list -> bool list -> bool list

val add_var : var -> live_fun -> nat -> live_fun

val add_vars : var list -> live_fun -> nat -> live_fun

val add_fun_args : nat -> var list -> bool list -> live_fun -> live_fun

val add_fun_vars : var -> var list -> var list -> live_fun -> nat -> live_fun

val escaping_fun_exp : exp -> live_fun -> var list -> live_fun

val escaping_fun_fundefs : fundefs -> live_fun -> var list -> live_fun

val live_expr : fundefs -> live_fun -> var list -> nat -> exp -> live_fun

val live : fundefs -> live_fun -> var list -> nat -> live_fun

val check_list_equality : bool list -> bool list -> bool

val check_list_list_equality : bool list list -> bool list list -> bool

val live_equality : live_fun -> live_fun -> bool

val num_vars : fundefs -> nat -> nat

val find_live_helper : fundefs -> live_fun -> var list -> nat -> live_fun

val find_live : exp -> live_fun

val live_args : var list -> bool list -> var list

val eliminate_expr : live_fun -> var list -> exp -> exp

val eliminate_fundefs : fundefs -> live_fun -> var list -> nat -> fundefs

val eliminate : exp -> exp
