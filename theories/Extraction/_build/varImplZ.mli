open BinPos
open Datatypes
open List0
open UsefulTypes
open List1
open VarInterface

val deqpos : int coq_Deq

val varClassP : (int, bool) coq_VarClass

val freshVarsPosAux : nat -> bool -> int list -> int list -> int list

val freshVarsPos : (int, bool) coq_FreshVars
