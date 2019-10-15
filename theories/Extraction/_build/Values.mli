open AST
open Archi
open BinInt
open Coqlib0
open Datatypes
open Floats
open Integers

type block = int

val eq_block : int -> int -> bool

type coq_val =
| Vundef
| Vint of Int.int
| Vlong of Int64.int
| Vfloat of float
| Vsingle of float32
| Vptr of block * Ptrofs.int

val coq_Vzero : coq_val

val coq_Vone : coq_val

val coq_Vtrue : coq_val

val coq_Vfalse : coq_val

val coq_Vptrofs : Ptrofs.int -> coq_val

module Val :
 sig
  val eq : coq_val -> coq_val -> bool

  val of_bool : bool -> coq_val

  val cmp_different_blocks : comparison -> bool option

  val cmpu_bool :
    (block -> int -> bool) -> comparison -> coq_val -> coq_val -> bool option

  val cmplu_bool :
    (block -> int -> bool) -> comparison -> coq_val -> coq_val -> bool option

  val load_result : memory_chunk -> coq_val -> coq_val
 end
