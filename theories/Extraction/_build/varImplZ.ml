open BinPos
open Datatypes
open List0
open UsefulTypes
open List1
open VarInterface

(** val deqpos : int coq_Deq **)

let deqpos =
  Pos.eqb

(** val varClassP : (int, bool) coq_VarClass **)

let varClassP p =
  (fun f2p1 f2p f1 p ->
  if p<=1 then f1 () else if p mod 2 = 0 then f2p (p/2) else f2p1 (p/2))
    (fun _ -> false)
    (fun _ -> true)
    (fun _ -> false)
    p

(** val freshVarsPosAux : nat -> bool -> int list -> int list -> int list **)

let freshVarsPosAux n c avoid _ =
  let maxn = maxlp avoid 1 in
  let f = fun x -> if c then (fun p->2*p) x else (fun p->1+2*p) x in
  map f (seq Pos.succ maxn n)

(** val freshVarsPos : (int, bool) coq_FreshVars **)

let freshVarsPos n c avoid original =
  let c0 = match c with
           | Some c0 -> c0
           | None -> true in
  freshVarsPosAux n c0 avoid original
