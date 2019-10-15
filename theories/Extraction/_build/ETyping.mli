open AstUtils
open BasicAst
open EAst

val global_decl_ident : global_decl -> kername

val lookup_env : global_declarations -> ident -> global_decl option
