open BasicAst
open Datatypes
open TermAbs

type dcon = inductive * int

type coq_L4Opid =
| NLambda
| NFix of nat * nat
| NDCon of dcon * nat
| NApply
| NLet
| NMatch of (dcon * nat) list
| NBox of char list

type 'opid branch = dcon * 'opid coq_AbsBTerm
