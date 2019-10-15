open Ast0
open AstCommon
open BasicAst
open Datatypes
open EAst
open ETyping
open Extract
open List0
open PCUICChecker
open RandyPrelude
open String0
open TemplateToPCUIC
open ExceptionMonad
open UGraph0
open Utils

type coq_Term =
| TRel of nat
| TProof
| TLambda of name * coq_Term
| TLetIn of name * coq_Term * coq_Term
| TApp of coq_Term * coq_Term
| TConst of char list
| TConstruct of inductive * nat * nat * nat
| TCase of (inductive * nat) * coq_Term * coq_Brs
| TFix of coq_Defs * nat
| TProj of projection * coq_Term
| TWrong of char list
and coq_Brs =
| Coq_bnil
| Coq_bcons of nat * coq_Term * coq_Brs
and coq_Defs =
| Coq_dnil
| Coq_dcons of name * coq_Term * nat * coq_Defs

val defs_Defs : (term -> coq_Term) -> term def list -> coq_Defs

val natterms_Brs : (term -> coq_Term) -> (nat * term) list -> coq_Brs

val print_global_declarations : global_declarations -> char list

val coq_Cstr_npars_nargs :
  global_declarations -> inductive -> nat -> (nat * nat) coq_exception

val term_Term : global_declarations -> term -> coq_Term

val trans_global_decl :
  global_declarations -> global_decl -> char list * coq_Term envClass

val program_Pgm_aux : global_declarations -> coq_Term environ

val program_Program : coq_Fuel -> Ast0.program -> coq_Term coq_Program
