open AST
open Cop
open Ctypes
open Datatypes
open Integers
open List0
open Values

type expr =
| Eval of coq_val * coq_type
| Evar of ident * coq_type
| Efield of expr * ident * coq_type
| Evalof of expr * coq_type
| Ederef of expr * coq_type
| Eaddrof of expr * coq_type
| Eunop of unary_operation * expr * coq_type
| Ebinop of binary_operation * expr * expr * coq_type
| Ecast of expr * coq_type
| Eseqand of expr * expr * coq_type
| Eseqor of expr * expr * coq_type
| Econdition of expr * expr * expr * coq_type
| Esizeof of coq_type * coq_type
| Ealignof of coq_type * coq_type
| Eassign of expr * expr * coq_type
| Eassignop of binary_operation * expr * expr * coq_type * coq_type
| Epostincr of incr_or_decr * expr * coq_type
| Ecomma of expr * expr * coq_type
| Ecall of expr * exprlist * coq_type
| Ebuiltin of external_function * typelist * exprlist * coq_type
| Eloc of block * Ptrofs.int * coq_type
| Eparen of expr * coq_type * coq_type
and exprlist =
| Enil
| Econs of expr * exprlist

val expr_rect :
  (coq_val -> coq_type -> 'a1) -> (ident -> coq_type -> 'a1) -> (expr -> 'a1
  -> ident -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type -> 'a1) -> (expr
  -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type -> 'a1) ->
  (unary_operation -> expr -> 'a1 -> coq_type -> 'a1) -> (binary_operation ->
  expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type
  -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1
  -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr
  -> 'a1 -> coq_type -> 'a1) -> (coq_type -> coq_type -> 'a1) -> (coq_type ->
  coq_type -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) ->
  (binary_operation -> expr -> 'a1 -> expr -> 'a1 -> coq_type -> coq_type ->
  'a1) -> (incr_or_decr -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 ->
  expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> exprlist -> coq_type ->
  'a1) -> (external_function -> typelist -> exprlist -> coq_type -> 'a1) ->
  (block -> Ptrofs.int -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type ->
  coq_type -> 'a1) -> expr -> 'a1

val expr_rec :
  (coq_val -> coq_type -> 'a1) -> (ident -> coq_type -> 'a1) -> (expr -> 'a1
  -> ident -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type -> 'a1) -> (expr
  -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type -> 'a1) ->
  (unary_operation -> expr -> 'a1 -> coq_type -> 'a1) -> (binary_operation ->
  expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type
  -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1
  -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> expr
  -> 'a1 -> coq_type -> 'a1) -> (coq_type -> coq_type -> 'a1) -> (coq_type ->
  coq_type -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) ->
  (binary_operation -> expr -> 'a1 -> expr -> 'a1 -> coq_type -> coq_type ->
  'a1) -> (incr_or_decr -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 ->
  expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> exprlist -> coq_type ->
  'a1) -> (external_function -> typelist -> exprlist -> coq_type -> 'a1) ->
  (block -> Ptrofs.int -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type ->
  coq_type -> 'a1) -> expr -> 'a1

val exprlist_rect : 'a1 -> (expr -> exprlist -> 'a1 -> 'a1) -> exprlist -> 'a1

val exprlist_rec : 'a1 -> (expr -> exprlist -> 'a1 -> 'a1) -> exprlist -> 'a1

val coq_Eindex : expr -> expr -> coq_type -> expr

val coq_Epreincr : incr_or_decr -> expr -> coq_type -> expr

val typeof : expr -> coq_type

type label = ident

type statement =
| Sskip
| Sdo of expr
| Ssequence of statement * statement
| Sifthenelse of expr * statement * statement
| Swhile of expr * statement
| Sdowhile of expr * statement
| Sfor of statement * expr * statement * statement
| Sbreak
| Scontinue
| Sreturn of expr option
| Sswitch of expr * labeled_statements
| Slabel of label * statement
| Sgoto of label
and labeled_statements =
| LSnil
| LScons of int option * statement * labeled_statements

val statement_rect :
  'a1 -> (expr -> 'a1) -> (statement -> 'a1 -> statement -> 'a1 -> 'a1) ->
  (expr -> statement -> 'a1 -> statement -> 'a1 -> 'a1) -> (expr -> statement
  -> 'a1 -> 'a1) -> (expr -> statement -> 'a1 -> 'a1) -> (statement -> 'a1 ->
  expr -> statement -> 'a1 -> statement -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> (expr
  option -> 'a1) -> (expr -> labeled_statements -> 'a1) -> (label ->
  statement -> 'a1 -> 'a1) -> (label -> 'a1) -> statement -> 'a1

val statement_rec :
  'a1 -> (expr -> 'a1) -> (statement -> 'a1 -> statement -> 'a1 -> 'a1) ->
  (expr -> statement -> 'a1 -> statement -> 'a1 -> 'a1) -> (expr -> statement
  -> 'a1 -> 'a1) -> (expr -> statement -> 'a1 -> 'a1) -> (statement -> 'a1 ->
  expr -> statement -> 'a1 -> statement -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> (expr
  option -> 'a1) -> (expr -> labeled_statements -> 'a1) -> (label ->
  statement -> 'a1 -> 'a1) -> (label -> 'a1) -> statement -> 'a1

val labeled_statements_rect :
  'a1 -> (int option -> statement -> labeled_statements -> 'a1 -> 'a1) ->
  labeled_statements -> 'a1

val labeled_statements_rec :
  'a1 -> (int option -> statement -> labeled_statements -> 'a1 -> 'a1) ->
  labeled_statements -> 'a1

type coq_function = { fn_return : coq_type; fn_callconv : calling_convention;
                      fn_params : (ident * coq_type) list;
                      fn_vars : (ident * coq_type) list; fn_body : statement }

val fn_return : coq_function -> coq_type

val fn_callconv : coq_function -> calling_convention

val fn_params : coq_function -> (ident * coq_type) list

val fn_vars : coq_function -> (ident * coq_type) list

val fn_body : coq_function -> statement

val var_names : (ident * coq_type) list -> ident list

type fundef = coq_function Ctypes.fundef

val type_of_function : coq_function -> coq_type

val type_of_fundef : fundef -> coq_type

type program = coq_function Ctypes.program
