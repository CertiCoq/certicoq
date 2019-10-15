open AST
open Cop
open Coqlib0
open Ctypes
open Floats
open Globalenvs
open Integers
open List0
open Maps
open Memory
open Values

type expr =
| Econst_int of Int.int * coq_type
| Econst_float of float * coq_type
| Econst_single of float32 * coq_type
| Econst_long of Int64.int * coq_type
| Evar of ident * coq_type
| Etempvar of ident * coq_type
| Ederef of expr * coq_type
| Eaddrof of expr * coq_type
| Eunop of unary_operation * expr * coq_type
| Ebinop of binary_operation * expr * expr * coq_type
| Ecast of expr * coq_type
| Efield of expr * ident * coq_type
| Esizeof of coq_type * coq_type
| Ealignof of coq_type * coq_type

(** val typeof : expr -> coq_type **)

let typeof = function
| Econst_int (_, ty) -> ty
| Econst_float (_, ty) -> ty
| Econst_single (_, ty) -> ty
| Econst_long (_, ty) -> ty
| Evar (_, ty) -> ty
| Etempvar (_, ty) -> ty
| Ederef (_, ty) -> ty
| Eaddrof (_, ty) -> ty
| Eunop (_, _, ty) -> ty
| Ebinop (_, _, _, ty) -> ty
| Ecast (_, ty) -> ty
| Efield (_, _, ty) -> ty
| Esizeof (_, ty) -> ty
| Ealignof (_, ty) -> ty

type label = ident

type statement =
| Sskip
| Sassign of expr * expr
| Sset of ident * expr
| Scall of ident option * expr * expr list
| Sbuiltin of ident option * external_function * typelist * expr list
| Ssequence of statement * statement
| Sifthenelse of expr * statement * statement
| Sloop of statement * statement
| Sbreak
| Scontinue
| Sreturn of expr option
| Sswitch of expr * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of int option * statement * labeled_statements

type coq_function = { fn_return : coq_type; fn_callconv : calling_convention;
                      fn_params : (ident * coq_type) list;
                      fn_vars : (ident * coq_type) list;
                      fn_temps : (ident * coq_type) list; fn_body : statement }

(** val fn_return : coq_function -> coq_type **)

let fn_return x = x.fn_return

(** val fn_callconv : coq_function -> calling_convention **)

let fn_callconv x = x.fn_callconv

(** val fn_params : coq_function -> (ident * coq_type) list **)

let fn_params x = x.fn_params

(** val fn_vars : coq_function -> (ident * coq_type) list **)

let fn_vars x = x.fn_vars

(** val fn_temps : coq_function -> (ident * coq_type) list **)

let fn_temps x = x.fn_temps

(** val fn_body : coq_function -> statement **)

let fn_body x = x.fn_body

type fundef = coq_function Ctypes.fundef

(** val type_of_function : coq_function -> coq_type **)

let type_of_function f =
  Tfunction ((type_of_params f.fn_params), f.fn_return, f.fn_callconv)

(** val type_of_fundef : fundef -> coq_type **)

let type_of_fundef = function
| Internal fd -> type_of_function fd
| External (_, args, res, cc) -> Tfunction (args, res, cc)

type program = coq_function Ctypes.program

type genv = { genv_genv : (fundef, coq_type) Genv.t; genv_cenv : composite_env }

(** val genv_genv : genv -> (fundef, coq_type) Genv.t **)

let genv_genv x = x.genv_genv

(** val genv_cenv : genv -> composite_env **)

let genv_cenv x = x.genv_cenv

(** val globalenv : program -> genv **)

let globalenv p =
  { genv_genv = (Genv.globalenv (program_of_program p)); genv_cenv =
    p.prog_comp_env }

type env = (block * coq_type) PTree.t

(** val empty_env : env **)

let empty_env =
  PTree.empty

type temp_env = coq_val PTree.t

(** val create_undef_temps : (ident * coq_type) list -> temp_env **)

let rec create_undef_temps = function
| [] -> PTree.empty
| p :: temps' ->
  let (id, _) = p in PTree.set id Vundef (create_undef_temps temps')

(** val bind_parameter_temps :
    (ident * coq_type) list -> coq_val list -> temp_env -> temp_env option **)

let rec bind_parameter_temps formals args le =
  match formals with
  | [] -> (match args with
           | [] -> Some le
           | _ :: _ -> None)
  | p :: xl ->
    let (id, _) = p in
    (match args with
     | [] -> None
     | v :: vl -> bind_parameter_temps xl vl (PTree.set id v le))

(** val block_of_binding :
    genv -> (ident * (block * coq_type)) -> (block * int) * int **)

let block_of_binding ge = function
| (_, p) -> let (b, ty) = p in ((b, 0), (sizeof ge.genv_cenv ty))

(** val blocks_of_env : genv -> env -> ((block * int) * int) list **)

let blocks_of_env ge e =
  map (block_of_binding ge) (PTree.elements e)

(** val set_opttemp :
    ident option -> coq_val -> temp_env -> coq_val PTree.t **)

let set_opttemp optid v le =
  match optid with
  | Some id -> PTree.set id v le
  | None -> le

(** val select_switch_default : labeled_statements -> labeled_statements **)

let rec select_switch_default sl = match sl with
| LSnil -> sl
| LScons (o, _, sl') ->
  (match o with
   | Some _ -> select_switch_default sl'
   | None -> sl)

(** val select_switch_case :
    int -> labeled_statements -> labeled_statements option **)

let rec select_switch_case n sl = match sl with
| LSnil -> None
| LScons (o, _, sl') ->
  (match o with
   | Some c -> if zeq c n then Some sl else select_switch_case n sl'
   | None -> select_switch_case n sl')

(** val select_switch : int -> labeled_statements -> labeled_statements **)

let select_switch n sl =
  match select_switch_case n sl with
  | Some sl' -> sl'
  | None -> select_switch_default sl

(** val seq_of_labeled_statement : labeled_statements -> statement **)

let rec seq_of_labeled_statement = function
| LSnil -> Sskip
| LScons (_, s, sl') -> Ssequence (s, (seq_of_labeled_statement sl'))

type cont =
| Kstop
| Kseq of statement * cont
| Kloop1 of statement * statement * cont
| Kloop2 of statement * statement * cont
| Kswitch of cont
| Kcall of ident option * coq_function * env * temp_env * cont

(** val call_cont : cont -> cont **)

let rec call_cont k = match k with
| Kseq (_, k0) -> call_cont k0
| Kloop1 (_, _, k0) -> call_cont k0
| Kloop2 (_, _, k0) -> call_cont k0
| Kswitch k0 -> call_cont k0
| _ -> k

type state =
| State of coq_function * statement * cont * env * temp_env * Mem.mem
| Callstate of fundef * coq_val list * cont * Mem.mem
| Returnstate of coq_val * cont * Mem.mem

(** val find_label :
    label -> statement -> cont -> (statement * cont) option **)

let rec find_label lbl s k =
  match s with
  | Ssequence (s1, s2) ->
    (match find_label lbl s1 (Kseq (s2, k)) with
     | Some sk -> Some sk
     | None -> find_label lbl s2 k)
  | Sifthenelse (_, s1, s2) ->
    (match find_label lbl s1 k with
     | Some sk -> Some sk
     | None -> find_label lbl s2 k)
  | Sloop (s1, s2) ->
    (match find_label lbl s1 (Kloop1 (s1, s2, k)) with
     | Some sk -> Some sk
     | None -> find_label lbl s2 (Kloop2 (s1, s2, k)))
  | Sswitch (_, sl) -> find_label_ls lbl sl (Kswitch k)
  | Slabel (lbl', s') ->
    if ident_eq lbl lbl' then Some (s', k) else find_label lbl s' k
  | _ -> None

(** val find_label_ls :
    label -> labeled_statements -> cont -> (statement * cont) option **)

and find_label_ls lbl sl k =
  match sl with
  | LSnil -> None
  | LScons (_, s, sl') ->
    (match find_label lbl s (Kseq ((seq_of_labeled_statement sl'), k)) with
     | Some sk -> Some sk
     | None -> find_label_ls lbl sl' k)
