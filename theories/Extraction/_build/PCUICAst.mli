open BasicAst
open Datatypes
open UGraph0
open Univ0

type term =
| Coq_tRel of nat
| Coq_tVar of ident
| Coq_tMeta of nat
| Coq_tEvar of nat * term list
| Coq_tSort of universe
| Coq_tProd of name * term * term
| Coq_tLambda of name * term * term
| Coq_tLetIn of name * term * term * term
| Coq_tApp of term * term
| Coq_tConst of kername * universe_instance
| Coq_tInd of inductive * universe_instance
| Coq_tConstruct of inductive * nat * universe_instance
| Coq_tCase of (inductive * nat) * term * term * (nat * term) list
| Coq_tProj of projection * term
| Coq_tFix of term mfixpoint * nat
| Coq_tCoFix of term mfixpoint * nat

val mkApps : term -> term list -> term

type context_decl = { decl_name : name; decl_body : term option;
                      decl_type : term }

val decl_body : context_decl -> term option

val decl_type : context_decl -> term

val vass : name -> term -> context_decl

val vdef : name -> term -> term -> context_decl

type context = context_decl list

val snoc : 'a1 list -> 'a1 -> 'a1 list

type one_inductive_body = { ind_name : ident; ind_type : term;
                            ind_kelim : sort_family list;
                            ind_ctors : ((ident * term) * nat) list;
                            ind_projs : (ident * term) list }

val ind_name : one_inductive_body -> ident

val ind_type : one_inductive_body -> term

val ind_kelim : one_inductive_body -> sort_family list

val ind_ctors : one_inductive_body -> ((ident * term) * nat) list

val ind_projs : one_inductive_body -> (ident * term) list

type mutual_inductive_body = { ind_npars : nat; ind_params : context;
                               ind_bodies : one_inductive_body list;
                               ind_universes : universe_context }

val ind_npars : mutual_inductive_body -> nat

val ind_bodies : mutual_inductive_body -> one_inductive_body list

type constant_body = { cst_type : term; cst_body : term option;
                       cst_universes : universe_context }

val cst_type : constant_body -> term

val cst_body : constant_body -> term option

type global_decl =
| ConstantDecl of kername * constant_body
| InductiveDecl of kername * mutual_inductive_body

type global_declarations = global_decl list

type global_context = global_declarations * t
