open Datatypes
open UsefulTypes
open List1

type ('t, 'classType) coq_VarClass = 't -> 'classType

val varClass : ('a1, 'a2) coq_VarClass -> 'a1 -> 'a2

type ('t, 'classType) coq_FreshVars =
  nat -> 'classType option -> 't list -> 't list -> 't list

val freshVars :
  ('a1, 'a2) coq_FreshVars -> nat -> 'a2 option -> 'a1 list -> 'a1 list ->
  'a1 list

val remove_nvars : 'a1 coq_Deq -> 'a1 list -> 'a1 list -> 'a1 list

val listHead : 'a1 list -> 'a1

val fresh_var :
  'a1 coq_Deq -> ('a1, 'a2) coq_VarClass -> ('a1, 'a2) coq_FreshVars -> 'a1
  list -> 'a1

val nvarx :
  'a1 coq_Deq -> ('a1, 'a2) coq_VarClass -> ('a1, 'a2) coq_FreshVars -> 'a1

val nvary :
  'a1 coq_Deq -> ('a1, 'a2) coq_VarClass -> ('a1, 'a2) coq_FreshVars -> 'a1
