open Datatypes
open List0
open List1
open VarInterface

val varClassNVar : ('a1, 'a3) coq_VarClass -> ('a1 * 'a2, 'a3) coq_VarClass

val freshVarsNVar :
  ('a1, 'a3) coq_FreshVars -> 'a2 -> ('a1 * 'a2, 'a3) coq_FreshVars
