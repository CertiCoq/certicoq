open BasicAst
open BinNat
open Datatypes
open EAst
open List0
open PeanoNat
open String0
open Classes0

(** val name_dec : name -> name -> bool **)

let name_dec s1 s2 =
  match s1 with
  | Coq_nAnon -> (match s2 with
                  | Coq_nAnon -> true
                  | Coq_nNamed _ -> false)
  | Coq_nNamed x ->
    (match s2 with
     | Coq_nAnon -> false
     | Coq_nNamed x0 -> string_dec x x0)

(** val inductive_dec : inductive -> inductive -> bool **)

let inductive_dec s1 s2 =
  let { inductive_mind = mind; inductive_ind = i } = s1 in
  let { inductive_mind = mind'; inductive_ind = i' } = s2 in
  let s = string_dec mind mind' in if s then Nat.eq_dec i i' else false

(** val coq_NEq : int coq_Eq **)

let coq_NEq =
  N.eq_dec

type coq_Cnstr = { coq_CnstrNm : char list; coq_CnstrArity : nat }

type ityp = { itypNm : char list; itypCnstrs : coq_Cnstr list }

type itypPack = ityp list

type 'trm envClass =
| Coq_ecTrm of 'trm
| Coq_ecTyp of nat * itypPack

(** val ecAx : 'a1 envClass **)

let ecAx =
  Coq_ecTyp (O, [])

type 'trm environ = (char list * 'trm envClass) list

(** val cnstr_Cnstr : ((char list * term) * nat) -> coq_Cnstr **)

let cnstr_Cnstr c =
  { coq_CnstrNm = (fst (fst c)); coq_CnstrArity = (snd c) }

(** val ibody_ityp : one_inductive_body -> ityp **)

let ibody_ityp iib =
  let ctors = map cnstr_Cnstr iib.ind_ctors in
  { itypNm = iib.ind_name; itypCnstrs = ctors }

(** val ibodies_itypPack : one_inductive_body list -> itypPack **)

let ibodies_itypPack ibs =
  map ibody_ityp ibs

type 'trm coq_Program = { main : 'trm; env : 'trm environ }

(** val main : 'a1 coq_Program -> 'a1 **)

let main x = x.main

(** val env : 'a1 coq_Program -> 'a1 environ **)

let env x = x.env
