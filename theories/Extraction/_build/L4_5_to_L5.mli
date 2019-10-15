open BasicAst
open Basics
open Datatypes
open List0
open String1
open String0
open UsefulTypes
open List1
open PolyEval
open Terms
open VarInterface0
open VarInterface

type coq_L4_5Opid =
| NLambda
| NFix of nat * nat
| NDCon of dcon * nat
| NApply
| NLet
| NMatch of (dcon * nat) list

type coq_L5Opid =
| CLambda
| CKLambda
| CLet
| CFix of nat * nat
| CDCon of dcon * nat
| CHalt
| CRet
| CCall
| CMatch of (dcon * nat) list

val coq_Lam_e :
  'a1 -> ('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L4_5Opid) coq_NTerm

val coq_Fix_e' :
  ('a1, coq_L4_5Opid) coq_BTerm list -> nat -> ('a1, coq_L4_5Opid) coq_NTerm

val coq_Lam_c :
  'a1 -> 'a1 -> ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm

val coq_KLam_c :
  'a1 -> ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm

val coq_ContApp_c :
  ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm -> ('a1,
  coq_L5Opid) coq_NTerm

val coq_Halt_c : ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm

val coq_Call_c :
  ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm -> ('a1,
  coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm

val coq_Con_c :
  dcon -> ('a1, coq_L5Opid) coq_NTerm list -> ('a1, coq_L5Opid) coq_NTerm

val is_valueb : ('a1, coq_L4_5Opid) coq_NTerm -> bool

val contVars : ('a1, bool) coq_FreshVars -> nat -> 'a1 list -> 'a1 list

val mkSuggestion :
  'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars -> 'a1
  coq_UpdateName -> char list -> 'a1

val contVar :
  'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars -> 'a1
  coq_UpdateName -> 'a1

val haltCont :
  'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars -> 'a1
  coq_UpdateName -> ('a1, coq_L5Opid) coq_NTerm

val cps_cvt_apply_aux :
  ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm -> ('a1,
  coq_L5Opid) coq_NTerm -> 'a1 -> 'a1 -> ('a1, coq_L5Opid) coq_NTerm

val cps_cvt_apply :
  'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars -> 'a1
  coq_UpdateName -> (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid)
  coq_NTerm) -> ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L4_5Opid) coq_NTerm
  -> ('a1, coq_L5Opid) coq_NTerm

val cps_cvt_lambda :
  'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars -> 'a1
  coq_UpdateName -> (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid)
  coq_NTerm) -> 'a1 -> ('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid)
  coq_NTerm

val cps_cvt_fn_list' :
  (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm) -> ('a1,
  coq_L4_5Opid) coq_BTerm list -> ('a1, coq_L5Opid) coq_BTerm list

val cps_cvt_val' :
  'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars -> 'a1
  coq_UpdateName -> (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid)
  coq_NTerm) -> ('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm

val cps_cvts_chain :
  'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars ->
  (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm) -> 'a1 list
  -> ('a1, coq_L4_5Opid) coq_BTerm list -> ('a1, coq_L5Opid) coq_NTerm ->
  ('a1, coq_L5Opid) coq_NTerm

val cps_cvt_branch :
  (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm) -> ('a1,
  coq_L5Opid) coq_NTerm -> ('a1, coq_L4_5Opid) coq_BTerm -> ('a1, coq_L5Opid)
  coq_BTerm

val cps_cvt_branches :
  (('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm) -> ('a1,
  coq_L5Opid) coq_NTerm -> ('a1, coq_L4_5Opid) coq_BTerm list -> ('a1,
  coq_L5Opid) coq_BTerm list

val val_outer :
  'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars -> 'a1
  coq_UpdateName -> ('a1, coq_L5Opid) coq_NTerm -> ('a1, coq_L5Opid) coq_NTerm

val cps_cvt :
  'a1 coq_Deq -> ('a1, bool) coq_VarClass -> ('a1, bool) coq_FreshVars -> 'a1
  coq_UpdateName -> ('a1, coq_L4_5Opid) coq_NTerm -> ('a1, coq_L5Opid)
  coq_NTerm
