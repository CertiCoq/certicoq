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

val typeof : expr -> coq_type

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

val fn_return : coq_function -> coq_type

val fn_callconv : coq_function -> calling_convention

val fn_params : coq_function -> (ident * coq_type) list

val fn_vars : coq_function -> (ident * coq_type) list

val fn_temps : coq_function -> (ident * coq_type) list

val fn_body : coq_function -> statement

type fundef = coq_function Ctypes.fundef

val type_of_function : coq_function -> coq_type

val type_of_fundef : fundef -> coq_type

type program = coq_function Ctypes.program

type genv = { genv_genv : (fundef, coq_type) Genv.t; genv_cenv : composite_env }

val genv_genv : genv -> (fundef, coq_type) Genv.t

val genv_cenv : genv -> composite_env

val globalenv : program -> genv

type env = (block * coq_type) PTree.t

val empty_env : env

type temp_env = coq_val PTree.t

val create_undef_temps : (ident * coq_type) list -> temp_env

val bind_parameter_temps :
  (ident * coq_type) list -> coq_val list -> temp_env -> temp_env option

val block_of_binding :
  genv -> (ident * (block * coq_type)) -> (block * int) * int

val blocks_of_env : genv -> env -> ((block * int) * int) list

val set_opttemp : ident option -> coq_val -> temp_env -> coq_val PTree.t

val select_switch_default : labeled_statements -> labeled_statements

val select_switch_case :
  int -> labeled_statements -> labeled_statements option

val select_switch : int -> labeled_statements -> labeled_statements

val seq_of_labeled_statement : labeled_statements -> statement

type cont =
| Kstop
| Kseq of statement * cont
| Kloop1 of statement * statement * cont
| Kloop2 of statement * statement * cont
| Kswitch of cont
| Kcall of ident option * coq_function * env * temp_env * cont

val call_cont : cont -> cont

type state =
| State of coq_function * statement * cont * env * temp_env * Mem.mem
| Callstate of fundef * coq_val list * cont * Mem.mem
| Returnstate of coq_val * cont * Mem.mem

val find_label : label -> statement -> cont -> (statement * cont) option

val find_label_ls :
  label -> labeled_statements -> cont -> (statement * cont) option
