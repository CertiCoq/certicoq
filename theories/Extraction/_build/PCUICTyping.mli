open AstUtils
open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICLiftSubst
open Univ0

val global_decl_ident : global_decl -> kername

val lookup_env : global_declarations -> ident -> global_decl option

val inds :
  kername -> universe_instance -> one_inductive_body list -> term list

val fix_subst : term mfixpoint -> term list

val unfold_fix : term mfixpoint -> nat -> (nat * term) option

val tDummy : term

val iota_red : nat -> nat -> term list -> (nat * term) list -> term
