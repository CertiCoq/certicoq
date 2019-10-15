open Datatypes
open List0
open List1
open VarInterface

(** val varClassNVar :
    ('a1, 'a3) coq_VarClass -> ('a1 * 'a2, 'a3) coq_VarClass **)

let varClassNVar varcl p =
  varClass varcl (fst p)

(** val freshVarsNVar :
    ('a1, 'a3) coq_FreshVars -> 'a2 -> ('a1 * 'a2, 'a3) coq_FreshVars **)

let freshVarsNVar freshv def n c avoid suggested =
  let vars = freshVars freshv n c (map fst avoid) (map fst suggested) in
  let names = listPad def (map snd suggested) n in combine vars names
