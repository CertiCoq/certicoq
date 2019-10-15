open AstCommon
open BasicAst
open Datatypes
open UsefulTypes
open VarImplDummyPair
open VarImplZ
open VarInterface0
open VarInterface

type coq_NVar = int * name

(** val deqnname : name coq_Deq **)

let deqnname =
  deqAsSumbool name_dec

(** val varClassNVar : (coq_NVar, bool) coq_VarClass **)

let varClassNVar =
  varClassNVar varClassP

(** val freshVarsNVar : (coq_NVar, bool) coq_FreshVars **)

let freshVarsNVar =
  freshVarsNVar freshVarsPos Coq_nAnon

(** val coq_NVUpdateName : coq_NVar coq_UpdateName **)

let coq_NVUpdateName = function
| (v, name0) -> ((fst v), name0)
