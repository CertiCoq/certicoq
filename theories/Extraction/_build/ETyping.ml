open AstUtils
open BasicAst
open EAst

(** val global_decl_ident : global_decl -> kername **)

let global_decl_ident = function
| ConstantDecl (id, _) -> id
| InductiveDecl (id, _) -> id

(** val lookup_env : global_declarations -> ident -> global_decl option **)

let rec lookup_env _UU03a3_ id =
  match _UU03a3_ with
  | [] -> None
  | hd :: tl ->
    if ident_eq id (global_decl_ident hd) then Some hd else lookup_env tl id
