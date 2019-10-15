open Archi
open BinInt
open BinPos
open Coqlib0
open Datatypes
open List0
open Zpower

type comparison =
| Ceq
| Cne
| Clt
| Cle
| Cgt
| Cge

module type WORDSIZE =
 sig
  val wordsize : nat
 end

module Make :
 functor (WS:WORDSIZE) ->
 sig
  val wordsize : nat

  val zwordsize : int

  val modulus : int

  val half_modulus : int

  val max_unsigned : int

  val max_signed : int

  val min_signed : int

  type int_ = int
    (* singleton inductive, whose constructor was mkint *)

  val intval : int_ -> int

  type int = int_

  val coq_P_mod_two_p : int -> nat -> int

  val coq_Z_mod_modulus : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val repr : int -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val coq_Zshiftin : bool -> int -> int

  val coq_Zzero_ext : int -> int -> int

  val coq_Zsign_ext : int -> int -> int

  val zero_ext : int -> int -> int

  val sign_ext : int -> int -> int

  val coq_Z_one_bits : nat -> int -> int -> int list

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison -> int -> int -> bool

  val cmpu : comparison -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int -> bool

  val powerserie : int list -> int

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int -> int -> int -> bool

  val coq_Zsize : int -> int

  val size : int -> int
 end

module Wordsize_32 :
 sig
  val wordsize : nat
 end

module Int :
 sig
  val wordsize : nat

  val zwordsize : int

  val modulus : int

  val half_modulus : int

  val max_unsigned : int

  val max_signed : int

  val min_signed : int

  type int_ = int
    (* singleton inductive, whose constructor was mkint *)

  val intval : int_ -> int

  type int = int_

  val coq_P_mod_two_p : int -> nat -> int

  val coq_Z_mod_modulus : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val repr : int -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val coq_Zshiftin : bool -> int -> int

  val coq_Zzero_ext : int -> int -> int

  val coq_Zsign_ext : int -> int -> int

  val zero_ext : int -> int -> int

  val sign_ext : int -> int -> int

  val coq_Z_one_bits : nat -> int -> int -> int list

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison -> int -> int -> bool

  val cmpu : comparison -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int -> bool

  val powerserie : int list -> int

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int -> int -> int -> bool

  val coq_Zsize : int -> int

  val size : int -> int
 end

module Wordsize_8 :
 sig
  val wordsize : nat
 end

module Byte :
 sig
  val wordsize : nat

  val zwordsize : int

  val modulus : int

  val half_modulus : int

  val max_unsigned : int

  val max_signed : int

  val min_signed : int

  type int_ = int
    (* singleton inductive, whose constructor was mkint *)

  val intval : int_ -> int

  type int = int_

  val coq_P_mod_two_p : int -> nat -> int

  val coq_Z_mod_modulus : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val repr : int -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val rol : int -> int -> int

  val ror : int -> int -> int

  val rolm : int -> int -> int -> int

  val shrx : int -> int -> int

  val mulhu : int -> int -> int

  val mulhs : int -> int -> int

  val negative : int -> int

  val add_carry : int -> int -> int -> int

  val add_overflow : int -> int -> int -> int

  val sub_borrow : int -> int -> int -> int

  val sub_overflow : int -> int -> int -> int

  val shr_carry : int -> int -> int

  val coq_Zshiftin : bool -> int -> int

  val coq_Zzero_ext : int -> int -> int

  val coq_Zsign_ext : int -> int -> int

  val zero_ext : int -> int -> int

  val sign_ext : int -> int -> int

  val coq_Z_one_bits : nat -> int -> int -> int list

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison -> int -> int -> bool

  val cmpu : comparison -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int * int) option

  val divmods2 : int -> int -> int -> (int * int) option

  val testbit : int -> int -> bool

  val powerserie : int list -> int

  val int_of_one_bits : int list -> int

  val no_overlap : int -> int -> int -> int -> bool

  val coq_Zsize : int -> int

  val size : int -> int
 end

module Wordsize_64 :
 sig
  val wordsize : nat
 end

module Int64 :
 sig
  val wordsize : nat

  val zwordsize : int

  val modulus : int

  val half_modulus : int

  val max_unsigned : int

  val max_signed : int

  val min_signed : int

  type int_ = int
    (* singleton inductive, whose constructor was mkint *)

  val intval : int_ -> int

  type int = int_

  val coq_P_mod_two_p : int -> nat -> int

  val coq_Z_mod_modulus : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val repr : int -> int

  val zero : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val lt : int -> int -> bool

  val ltu : int -> int -> bool

  val neg : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val mods : int -> int -> int

  val divu : int -> int -> int

  val modu : int -> int -> int

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val not : int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shr : int -> int -> int

  val cmp : comparison -> int -> int -> bool

  val cmpu : comparison -> int -> int -> bool

  val iwordsize' : Int.int

  val loword : int -> Int.int
 end

module Wordsize_Ptrofs :
 sig
  val wordsize : nat
 end

module Ptrofs :
 sig
  val wordsize : nat

  val modulus : int

  val half_modulus : int

  val max_signed : int

  type int_ = int
    (* singleton inductive, whose constructor was mkint *)

  val intval : int_ -> int

  type int = int_

  val coq_P_mod_two_p : int -> nat -> int

  val coq_Z_mod_modulus : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val repr : int -> int

  val zero : int

  val eq_dec : int -> int -> bool

  val eq : int -> int -> bool

  val ltu : int -> int -> bool

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int

  val cmpu : comparison -> int -> int -> bool

  val to_int : int -> Int.int

  val to_int64 : int -> Int64.int

  val of_int : Int.int -> int

  val of_intu : Int.int -> int

  val of_ints : Int.int -> int

  val of_int64 : Int64.int -> int
 end
