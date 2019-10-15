open Datatypes
open L4_5_to_L5
open L4_to_L4_1_to_L4_2
open List0
open UsefulTypes
open PolyEval
open Terms
open VarImplZ
open VarInterface
open Variables

type coq_L4_5_Term = (coq_NVar, coq_L4_5Opid) coq_NTerm

(** val mapOpidL4_to_L4_5 : coq_L4Opid -> coq_L4_5Opid **)

let mapOpidL4_to_L4_5 = function
| NLambda -> L4_5_to_L5.NLambda
| NFix (nMut, a) -> L4_5_to_L5.NFix (nMut, a)
| NDCon (c, nargs) -> L4_5_to_L5.NDCon (c, nargs)
| NApply -> L4_5_to_L5.NApply
| NLet -> L4_5_to_L5.NLet
| NMatch numargsInBranches -> L4_5_to_L5.NMatch numargsInBranches
| NBox _ -> L4_5_to_L5.NFix (O, O)

(** val coq_L4_2_to_L4_5 : coq_L4_2_Term -> coq_L4_5_Term **)

let rec coq_L4_2_to_L4_5 = function
| Coq_vterm v -> Coq_vterm v
| Coq_oterm (o, lbt) ->
  let lbt0 = map (btMapNt coq_L4_2_to_L4_5) lbt in
  (match o with
   | NBox _ ->
     let f = nvarx (deq_prod deqpos deqnname) varClassNVar freshVarsNVar in
     let arg = nvary (deq_prod deqpos deqnname) varClassNVar freshVarsNVar in
     coq_Fix_e' ((Coq_bterm ((f :: []),
       (coq_Lam_e arg (Coq_vterm f)))) :: []) O
   | _ -> Coq_oterm ((mapOpidL4_to_L4_5 o), lbt0))
