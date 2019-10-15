open Datatypes
open UsefulTypes
open List1

type ('t, 'classType) coq_VarClass = 't -> 'classType

(** val varClass : ('a1, 'a2) coq_VarClass -> 'a1 -> 'a2 **)

let varClass varClass0 =
  varClass0

type ('t, 'classType) coq_FreshVars =
  nat -> 'classType option -> 't list -> 't list -> 't list

(** val freshVars :
    ('a1, 'a2) coq_FreshVars -> nat -> 'a2 option -> 'a1 list -> 'a1 list ->
    'a1 list **)

let freshVars freshVars0 =
  freshVars0

(** val remove_nvars : 'a1 coq_Deq -> 'a1 list -> 'a1 list -> 'a1 list **)

let remove_nvars =
  diff

(** val listHead : 'a1 list -> 'a1 **)

let listHead = function
| [] -> assert false (* absurd case *)
| a :: _ -> a

(** val fresh_var :
    'a1 coq_Deq -> ('a1, 'a2) coq_VarClass -> ('a1, 'a2) coq_FreshVars -> 'a1
    list -> 'a1 **)

let fresh_var _ _ h1 lx =
  listHead (freshVars h1 (S O) None lx [])

(** val nvarx :
    'a1 coq_Deq -> ('a1, 'a2) coq_VarClass -> ('a1, 'a2) coq_FreshVars -> 'a1 **)

let nvarx h h0 h1 =
  fresh_var h h0 h1 []

(** val nvary :
    'a1 coq_Deq -> ('a1, 'a2) coq_VarClass -> ('a1, 'a2) coq_FreshVars -> 'a1 **)

let nvary h h0 h1 =
  fresh_var h h0 h1 ((nvarx h h0 h1) :: [])
