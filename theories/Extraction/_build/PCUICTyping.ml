open AstUtils
open BasicAst
open Datatypes
open List0
open PCUICAst
open PCUICLiftSubst
open Univ0

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

(** val inds :
    kername -> universe_instance -> one_inductive_body list -> term list **)

let inds ind u l =
  let rec aux = function
  | O -> []
  | S n0 ->
    (Coq_tInd ({ inductive_mind = ind; inductive_ind = n0 }, u)) :: (aux n0)
  in aux (length l)

(** val fix_subst : term mfixpoint -> term list **)

let fix_subst l =
  let rec aux = function
  | O -> []
  | S n0 -> (Coq_tFix (l, n0)) :: (aux n0)
  in aux (length l)

(** val unfold_fix : term mfixpoint -> nat -> (nat * term) option **)

let unfold_fix mfix idx =
  match nth_error mfix idx with
  | Some d -> Some (d.rarg, (subst (fix_subst mfix) O d.dbody))
  | None -> None

(** val tDummy : term **)

let tDummy =
  Coq_tVar []

(** val iota_red : nat -> nat -> term list -> (nat * term) list -> term **)

let iota_red npar c args brs =
  mkApps (snd (nth c brs (O, tDummy))) (skipn npar args)
