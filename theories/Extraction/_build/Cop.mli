open AST
open Archi
open Coqlib0
open Ctypes
open Datatypes
open Floats
open Integers
open Memory
open Values

type unary_operation =
| Onotbool
| Onotint
| Oneg
| Oabsfloat

type binary_operation =
| Oadd
| Osub
| Omul
| Odiv
| Omod
| Oand
| Oor
| Oxor
| Oshl
| Oshr
| Oeq
| One
| Olt
| Ogt
| Ole
| Oge

type incr_or_decr =
| Incr
| Decr

type classify_cast_cases =
| Coq_cast_case_pointer
| Coq_cast_case_i2i of intsize * signedness
| Coq_cast_case_f2f
| Coq_cast_case_s2s
| Coq_cast_case_f2s
| Coq_cast_case_s2f
| Coq_cast_case_i2f of signedness
| Coq_cast_case_i2s of signedness
| Coq_cast_case_f2i of intsize * signedness
| Coq_cast_case_s2i of intsize * signedness
| Coq_cast_case_l2l
| Coq_cast_case_i2l of signedness
| Coq_cast_case_l2i of intsize * signedness
| Coq_cast_case_l2f of signedness
| Coq_cast_case_l2s of signedness
| Coq_cast_case_f2l of signedness
| Coq_cast_case_s2l of signedness
| Coq_cast_case_i2bool
| Coq_cast_case_l2bool
| Coq_cast_case_f2bool
| Coq_cast_case_s2bool
| Coq_cast_case_struct of ident * ident
| Coq_cast_case_union of ident * ident
| Coq_cast_case_void
| Coq_cast_case_default

val classify_cast : coq_type -> coq_type -> classify_cast_cases

val cast_int_int : intsize -> signedness -> Int.int -> Int.int

val cast_int_float : signedness -> Int.int -> float

val cast_float_int : signedness -> float -> Int.int option

val cast_int_single : signedness -> Int.int -> float32

val cast_single_int : signedness -> float32 -> Int.int option

val cast_int_long : signedness -> Int.int -> Int64.int

val cast_long_float : signedness -> Int64.int -> float

val cast_long_single : signedness -> Int64.int -> float32

val cast_float_long : signedness -> float -> Int64.int option

val cast_single_long : signedness -> float32 -> Int64.int option

val sem_cast : coq_val -> coq_type -> coq_type -> Mem.mem -> coq_val option

type classify_bool_cases =
| Coq_bool_case_i
| Coq_bool_case_l
| Coq_bool_case_f
| Coq_bool_case_s
| Coq_bool_default

val classify_bool : coq_type -> classify_bool_cases

val bool_val : coq_val -> coq_type -> Mem.mem -> bool option

val sem_notbool : coq_val -> coq_type -> Mem.mem -> coq_val option

type classify_neg_cases =
| Coq_neg_case_i of signedness
| Coq_neg_case_f
| Coq_neg_case_s
| Coq_neg_case_l of signedness
| Coq_neg_default

val classify_neg : coq_type -> classify_neg_cases

val sem_neg : coq_val -> coq_type -> coq_val option

val sem_absfloat : coq_val -> coq_type -> coq_val option

type classify_notint_cases =
| Coq_notint_case_i of signedness
| Coq_notint_case_l of signedness
| Coq_notint_default

val classify_notint : coq_type -> classify_notint_cases

val sem_notint : coq_val -> coq_type -> coq_val option

type binarith_cases =
| Coq_bin_case_i of signedness
| Coq_bin_case_l of signedness
| Coq_bin_case_f
| Coq_bin_case_s
| Coq_bin_default

val classify_binarith : coq_type -> coq_type -> binarith_cases

val binarith_type : binarith_cases -> coq_type

val sem_binarith :
  (signedness -> Int.int -> Int.int -> coq_val option) -> (signedness ->
  Int64.int -> Int64.int -> coq_val option) -> (float -> float -> coq_val
  option) -> (float32 -> float32 -> coq_val option) -> coq_val -> coq_type ->
  coq_val -> coq_type -> Mem.mem -> coq_val option

type classify_add_cases =
| Coq_add_case_pi of coq_type * signedness
| Coq_add_case_pl of coq_type
| Coq_add_case_ip of signedness * coq_type
| Coq_add_case_lp of coq_type
| Coq_add_default

val classify_add : coq_type -> coq_type -> classify_add_cases

val ptrofs_of_int : signedness -> Int.int -> Ptrofs.int

val sem_add_ptr_int :
  composite_env -> coq_type -> signedness -> coq_val -> coq_val -> coq_val
  option

val sem_add_ptr_long :
  composite_env -> coq_type -> coq_val -> coq_val -> coq_val option

val sem_add :
  composite_env -> coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem ->
  coq_val option

type classify_sub_cases =
| Coq_sub_case_pi of coq_type * signedness
| Coq_sub_case_pp of coq_type
| Coq_sub_case_pl of coq_type
| Coq_sub_default

val classify_sub : coq_type -> coq_type -> classify_sub_cases

val sem_sub :
  composite_env -> coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem ->
  coq_val option

val sem_mul :
  coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem -> coq_val option

val sem_div :
  coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem -> coq_val option

val sem_mod :
  coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem -> coq_val option

val sem_and :
  coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem -> coq_val option

val sem_or :
  coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem -> coq_val option

val sem_xor :
  coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem -> coq_val option

type classify_shift_cases =
| Coq_shift_case_ii of signedness
| Coq_shift_case_ll of signedness
| Coq_shift_case_il of signedness
| Coq_shift_case_li of signedness
| Coq_shift_default

val classify_shift : coq_type -> coq_type -> classify_shift_cases

val sem_shift :
  (signedness -> Int.int -> Int.int -> Int.int) -> (signedness -> Int64.int
  -> Int64.int -> Int64.int) -> coq_val -> coq_type -> coq_val -> coq_type ->
  coq_val option

val sem_shl : coq_val -> coq_type -> coq_val -> coq_type -> coq_val option

val sem_shr : coq_val -> coq_type -> coq_val -> coq_type -> coq_val option

type classify_cmp_cases =
| Coq_cmp_case_pp
| Coq_cmp_case_pi of signedness
| Coq_cmp_case_ip of signedness
| Coq_cmp_case_pl
| Coq_cmp_case_lp
| Coq_cmp_default

val classify_cmp : coq_type -> coq_type -> classify_cmp_cases

val cmp_ptr : Mem.mem -> comparison -> coq_val -> coq_val -> coq_val option

val sem_cmp :
  comparison -> coq_val -> coq_type -> coq_val -> coq_type -> Mem.mem ->
  coq_val option

type classify_fun_cases =
| Coq_fun_case_f of typelist * coq_type * calling_convention
| Coq_fun_default

val classify_fun : coq_type -> classify_fun_cases

type classify_switch_cases =
| Coq_switch_case_i
| Coq_switch_case_l
| Coq_switch_default

val classify_switch : coq_type -> classify_switch_cases

val sem_switch_arg : coq_val -> coq_type -> int option

val sem_unary_operation :
  unary_operation -> coq_val -> coq_type -> Mem.mem -> coq_val option

val sem_binary_operation :
  composite_env -> binary_operation -> coq_val -> coq_type -> coq_val ->
  coq_type -> Mem.mem -> coq_val option
