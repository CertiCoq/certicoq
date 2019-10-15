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

(** val expr_rect :
    (coq_val -> coq_type -> 'a1) -> (ident -> coq_type -> 'a1) -> (expr ->
    'a1 -> ident -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type -> 'a1) ->
    (expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type -> 'a1) ->
    (unary_operation -> expr -> 'a1 -> coq_type -> 'a1) -> (binary_operation
    -> expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 ->
    coq_type -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> expr
    -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (coq_type -> coq_type ->
    'a1) -> (coq_type -> coq_type -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
    coq_type -> 'a1) -> (binary_operation -> expr -> 'a1 -> expr -> 'a1 ->
    coq_type -> coq_type -> 'a1) -> (incr_or_decr -> expr -> 'a1 -> coq_type
    -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (expr ->
    'a1 -> exprlist -> coq_type -> 'a1) -> (external_function -> typelist ->
    exprlist -> coq_type -> 'a1) -> (block -> Ptrofs.int -> coq_type -> 'a1)
    -> (expr -> 'a1 -> coq_type -> coq_type -> 'a1) -> expr -> 'a1 **)

let rec expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 = function
| Eval (v, ty) -> f v ty
| Evar (x, ty) -> f0 x ty
| Efield (l, f21, ty) ->
  f1 l
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 l) f21 ty
| Evalof (l, ty) ->
  f2 l
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 l) ty
| Ederef (r, ty) ->
  f3 r
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r) ty
| Eaddrof (l, ty) ->
  f4 l
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 l) ty
| Eunop (op, r, ty) ->
  f5 op r
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r) ty
| Ebinop (op, r1, r2, ty) ->
  f6 op r1
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r1) r2
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r2) ty
| Ecast (r, ty) ->
  f7 r
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r) ty
| Eseqand (r1, r2, ty) ->
  f8 r1
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r1) r2
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r2) ty
| Eseqor (r1, r2, ty) ->
  f9 r1
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r1) r2
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r2) ty
| Econdition (r1, r2, r3, ty) ->
  f10 r1
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r1) r2
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r2) r3
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r3) ty
| Esizeof (ty', ty) -> f11 ty' ty
| Ealignof (ty', ty) -> f12 ty' ty
| Eassign (l, r, ty) ->
  f13 l
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 l) r
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r) ty
| Eassignop (op, l, r, tyres, ty) ->
  f14 op l
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 l) r
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r) tyres ty
| Epostincr (id, l, ty) ->
  f15 id l
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 l) ty
| Ecomma (r1, r2, ty) ->
  f16 r1
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r1) r2
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r2) ty
| Ecall (r1, rargs, ty) ->
  f17 r1
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r1) rargs ty
| Ebuiltin (ef, tyargs, rargs, ty) -> f18 ef tyargs rargs ty
| Eloc (b, ofs, ty) -> f19 b ofs ty
| Eparen (r, tycast, ty) ->
  f20 r
    (expr_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 r) tycast ty

(** val expr_rec :
    (coq_val -> coq_type -> 'a1) -> (ident -> coq_type -> 'a1) -> (expr ->
    'a1 -> ident -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type -> 'a1) ->
    (expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> coq_type -> 'a1) ->
    (unary_operation -> expr -> 'a1 -> coq_type -> 'a1) -> (binary_operation
    -> expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 ->
    coq_type -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) ->
    (expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (expr -> 'a1 -> expr
    -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (coq_type -> coq_type ->
    'a1) -> (coq_type -> coq_type -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 ->
    coq_type -> 'a1) -> (binary_operation -> expr -> 'a1 -> expr -> 'a1 ->
    coq_type -> coq_type -> 'a1) -> (incr_or_decr -> expr -> 'a1 -> coq_type
    -> 'a1) -> (expr -> 'a1 -> expr -> 'a1 -> coq_type -> 'a1) -> (expr ->
    'a1 -> exprlist -> coq_type -> 'a1) -> (external_function -> typelist ->
    exprlist -> coq_type -> 'a1) -> (block -> Ptrofs.int -> coq_type -> 'a1)
    -> (expr -> 'a1 -> coq_type -> coq_type -> 'a1) -> expr -> 'a1 **)

let rec expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 = function
| Eval (v, ty) -> f v ty
| Evar (x, ty) -> f0 x ty
| Efield (l, f21, ty) ->
  f1 l
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 l) f21 ty
| Evalof (l, ty) ->
  f2 l
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 l) ty
| Ederef (r, ty) ->
  f3 r
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r) ty
| Eaddrof (l, ty) ->
  f4 l
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 l) ty
| Eunop (op, r, ty) ->
  f5 op r
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r) ty
| Ebinop (op, r1, r2, ty) ->
  f6 op r1
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r1) r2
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r2) ty
| Ecast (r, ty) ->
  f7 r
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r) ty
| Eseqand (r1, r2, ty) ->
  f8 r1
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r1) r2
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r2) ty
| Eseqor (r1, r2, ty) ->
  f9 r1
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r1) r2
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r2) ty
| Econdition (r1, r2, r3, ty) ->
  f10 r1
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r1) r2
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r2) r3
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r3) ty
| Esizeof (ty', ty) -> f11 ty' ty
| Ealignof (ty', ty) -> f12 ty' ty
| Eassign (l, r, ty) ->
  f13 l
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 l) r
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r) ty
| Eassignop (op, l, r, tyres, ty) ->
  f14 op l
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 l) r
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r) tyres ty
| Epostincr (id, l, ty) ->
  f15 id l
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 l) ty
| Ecomma (r1, r2, ty) ->
  f16 r1
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r1) r2
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r2) ty
| Ecall (r1, rargs, ty) ->
  f17 r1
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r1) rargs ty
| Ebuiltin (ef, tyargs, rargs, ty) -> f18 ef tyargs rargs ty
| Eloc (b, ofs, ty) -> f19 b ofs ty
| Eparen (r, tycast, ty) ->
  f20 r
    (expr_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17
      f18 f19 f20 r) tycast ty

(** val exprlist_rect :
    'a1 -> (expr -> exprlist -> 'a1 -> 'a1) -> exprlist -> 'a1 **)

let rec exprlist_rect f f0 = function
| Enil -> f
| Econs (r1, rl) -> f0 r1 rl (exprlist_rect f f0 rl)

(** val exprlist_rec :
    'a1 -> (expr -> exprlist -> 'a1 -> 'a1) -> exprlist -> 'a1 **)

let rec exprlist_rec f f0 = function
| Enil -> f
| Econs (r1, rl) -> f0 r1 rl (exprlist_rec f f0 rl)

(** val coq_Eindex : expr -> expr -> coq_type -> expr **)

let coq_Eindex r1 r2 ty =
  Ederef ((Ebinop (Oadd, r1, r2, (Tpointer (ty, noattr)))), ty)

(** val coq_Epreincr : incr_or_decr -> expr -> coq_type -> expr **)

let coq_Epreincr id l ty =
  Eassignop ((match id with
              | Incr -> Oadd
              | Decr -> Osub), l, (Eval ((Vint Int.one), type_int32s)),
    (typeconv ty), ty)

(** val typeof : expr -> coq_type **)

let typeof = function
| Eval (_, ty) -> ty
| Evar (_, ty) -> ty
| Efield (_, _, ty) -> ty
| Evalof (_, ty) -> ty
| Ederef (_, ty) -> ty
| Eaddrof (_, ty) -> ty
| Eunop (_, _, ty) -> ty
| Ebinop (_, _, _, ty) -> ty
| Ecast (_, ty) -> ty
| Eseqand (_, _, ty) -> ty
| Eseqor (_, _, ty) -> ty
| Econdition (_, _, _, ty) -> ty
| Esizeof (_, ty) -> ty
| Ealignof (_, ty) -> ty
| Eassign (_, _, ty) -> ty
| Eassignop (_, _, _, _, ty) -> ty
| Epostincr (_, _, ty) -> ty
| Ecomma (_, _, ty) -> ty
| Ecall (_, _, ty) -> ty
| Ebuiltin (_, _, _, ty) -> ty
| Eloc (_, _, ty) -> ty
| Eparen (_, _, ty) -> ty

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

(** val statement_rect :
    'a1 -> (expr -> 'a1) -> (statement -> 'a1 -> statement -> 'a1 -> 'a1) ->
    (expr -> statement -> 'a1 -> statement -> 'a1 -> 'a1) -> (expr ->
    statement -> 'a1 -> 'a1) -> (expr -> statement -> 'a1 -> 'a1) ->
    (statement -> 'a1 -> expr -> statement -> 'a1 -> statement -> 'a1 -> 'a1)
    -> 'a1 -> 'a1 -> (expr option -> 'a1) -> (expr -> labeled_statements ->
    'a1) -> (label -> statement -> 'a1 -> 'a1) -> (label -> 'a1) -> statement
    -> 'a1 **)

let rec statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
| Sskip -> f
| Sdo e -> f0 e
| Ssequence (s0, s1) ->
  f1 s0 (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) s1
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1)
| Sifthenelse (e, s0, s1) ->
  f2 e s0 (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) s1
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1)
| Swhile (e, s0) ->
  f3 e s0 (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0)
| Sdowhile (e, s0) ->
  f4 e s0 (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0)
| Sfor (s0, e, s1, s2) ->
  f5 s0 (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) e s1
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) s2
    (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s2)
| Sbreak -> f6
| Scontinue -> f7
| Sreturn o -> f8 o
| Sswitch (e, l) -> f9 e l
| Slabel (l, s0) ->
  f10 l s0 (statement_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0)
| Sgoto l -> f11 l

(** val statement_rec :
    'a1 -> (expr -> 'a1) -> (statement -> 'a1 -> statement -> 'a1 -> 'a1) ->
    (expr -> statement -> 'a1 -> statement -> 'a1 -> 'a1) -> (expr ->
    statement -> 'a1 -> 'a1) -> (expr -> statement -> 'a1 -> 'a1) ->
    (statement -> 'a1 -> expr -> statement -> 'a1 -> statement -> 'a1 -> 'a1)
    -> 'a1 -> 'a1 -> (expr option -> 'a1) -> (expr -> labeled_statements ->
    'a1) -> (label -> statement -> 'a1 -> 'a1) -> (label -> 'a1) -> statement
    -> 'a1 **)

let rec statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 = function
| Sskip -> f
| Sdo e -> f0 e
| Ssequence (s0, s1) ->
  f1 s0 (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) s1
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1)
| Sifthenelse (e, s0, s1) ->
  f2 e s0 (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) s1
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1)
| Swhile (e, s0) ->
  f3 e s0 (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0)
| Sdowhile (e, s0) ->
  f4 e s0 (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0)
| Sfor (s0, e, s1, s2) ->
  f5 s0 (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0) e s1
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s1) s2
    (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s2)
| Sbreak -> f6
| Scontinue -> f7
| Sreturn o -> f8 o
| Sswitch (e, l) -> f9 e l
| Slabel (l, s0) ->
  f10 l s0 (statement_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 s0)
| Sgoto l -> f11 l

(** val labeled_statements_rect :
    'a1 -> (int option -> statement -> labeled_statements -> 'a1 -> 'a1) ->
    labeled_statements -> 'a1 **)

let rec labeled_statements_rect f f0 = function
| LSnil -> f
| LScons (o, s, l0) -> f0 o s l0 (labeled_statements_rect f f0 l0)

(** val labeled_statements_rec :
    'a1 -> (int option -> statement -> labeled_statements -> 'a1 -> 'a1) ->
    labeled_statements -> 'a1 **)

let rec labeled_statements_rec f f0 = function
| LSnil -> f
| LScons (o, s, l0) -> f0 o s l0 (labeled_statements_rec f f0 l0)

type coq_function = { fn_return : coq_type; fn_callconv : calling_convention;
                      fn_params : (ident * coq_type) list;
                      fn_vars : (ident * coq_type) list; fn_body : statement }

(** val fn_return : coq_function -> coq_type **)

let fn_return x = x.fn_return

(** val fn_callconv : coq_function -> calling_convention **)

let fn_callconv x = x.fn_callconv

(** val fn_params : coq_function -> (ident * coq_type) list **)

let fn_params x = x.fn_params

(** val fn_vars : coq_function -> (ident * coq_type) list **)

let fn_vars x = x.fn_vars

(** val fn_body : coq_function -> statement **)

let fn_body x = x.fn_body

(** val var_names : (ident * coq_type) list -> ident list **)

let var_names vars =
  map fst vars

type fundef = coq_function Ctypes.fundef

(** val type_of_function : coq_function -> coq_type **)

let type_of_function f =
  Tfunction ((type_of_params f.fn_params), f.fn_return, f.fn_callconv)

(** val type_of_fundef : fundef -> coq_type **)

let type_of_fundef = function
| Internal fd -> type_of_function fd
| External (_, args, res, cc) -> Tfunction (args, res, cc)

type program = coq_function Ctypes.program
