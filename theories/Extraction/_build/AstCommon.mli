open BasicAst
open BinNat
open Datatypes
open EAst
open List0
open PeanoNat
open String0
open Classes0

val name_dec : name -> name -> bool

val inductive_dec : inductive -> inductive -> bool

val coq_NEq : int coq_Eq

type coq_Cnstr = { coq_CnstrNm : char list; coq_CnstrArity : nat }

type ityp = { itypNm : char list; itypCnstrs : coq_Cnstr list }

type itypPack = ityp list

type 'trm envClass =
| Coq_ecTrm of 'trm
| Coq_ecTyp of nat * itypPack

val ecAx : 'a1 envClass

type 'trm environ = (char list * 'trm envClass) list

val cnstr_Cnstr : ((char list * term) * nat) -> coq_Cnstr

val ibody_ityp : one_inductive_body -> ityp

val ibodies_itypPack : one_inductive_body list -> itypPack

type 'trm coq_Program = { main : 'trm; env : 'trm environ }

val main : 'a1 coq_Program -> 'a1

val env : 'a1 coq_Program -> 'a1 environ
