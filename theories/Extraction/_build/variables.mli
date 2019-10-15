open AstCommon
open BasicAst
open Datatypes
open UsefulTypes
open VarImplDummyPair
open VarImplZ
open VarInterface0
open VarInterface

type coq_NVar = int * name

val deqnname : name coq_Deq

val varClassNVar : (coq_NVar, bool) coq_VarClass

val freshVarsNVar : (coq_NVar, bool) coq_FreshVars

val coq_NVUpdateName : coq_NVar coq_UpdateName
