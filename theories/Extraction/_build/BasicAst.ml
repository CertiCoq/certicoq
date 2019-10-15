open Datatypes

type ident = char list

type kername = char list

type name =
| Coq_nAnon
| Coq_nNamed of ident

type inductive = { inductive_mind : kername; inductive_ind : nat }

type projection = (inductive * nat) * nat

type 'term def = { dname : name; dtype : 'term; dbody : 'term; rarg : nat }

(** val dname : 'a1 def -> name **)

let dname x = x.dname

(** val dtype : 'a1 def -> 'a1 **)

let dtype x = x.dtype

(** val dbody : 'a1 def -> 'a1 **)

let dbody x = x.dbody

(** val rarg : 'a1 def -> nat **)

let rarg x = x.rarg

type 'term mfixpoint = 'term def list

type sort_family =
| InProp
| InSet
| InType

type cast_kind =
| VmCast
| NativeCast
| Cast
| RevertCast
