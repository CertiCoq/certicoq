
type unit0 =
| Tt

type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val div2 : positive -> positive

  val div2_up : positive -> positive

  val size : positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val ldiff : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val testbit : positive -> n -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive

  val eq_dec : positive -> positive -> sumbool
 end

module N :
 sig
  val succ_double : n -> n

  val double : n -> n

  val succ_pos : n -> positive

  val add : n -> n -> n

  val sub : n -> n -> n

  val mul : n -> n -> n

  val compare : n -> n -> comparison

  val leb : n -> n -> bool

  val pos_div_eucl : positive -> n -> (n, n) prod

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val ldiff : n -> n -> n

  val coq_lxor : n -> n -> n

  val testbit : n -> n -> bool
 end

val nth : nat -> 'a1 list -> 'a1 -> 'a1

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val firstn : nat -> 'a1 list -> 'a1 list

val skipn : nat -> 'a1 list -> 'a1 list

val repeat : 'a1 -> nat -> 'a1 list

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val succ : z -> z

  val pred : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val leb : z -> z -> bool

  val ltb : z -> z -> bool

  val to_nat : z -> nat

  val of_nat : nat -> z

  val of_N : n -> z

  val iter : z -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val pos_div_eucl : positive -> z -> (z, z) prod

  val div_eucl : z -> z -> (z, z) prod

  val div : z -> z -> z

  val modulo : z -> z -> z

  val quotrem : z -> z -> (z, z) prod

  val quot : z -> z -> z

  val rem : z -> z -> z

  val odd : z -> bool

  val div2 : z -> z

  val log2 : z -> z

  val testbit : z -> z -> bool

  val shiftl : z -> z -> z

  val shiftr : z -> z -> z

  val coq_lor : z -> z -> z

  val coq_land : z -> z -> z

  val coq_lxor : z -> z -> z

  val eq_dec : z -> z -> sumbool
 end

val z_lt_dec : z -> z -> sumbool

val z_le_dec : z -> z -> sumbool

val z_le_gt_dec : z -> z -> sumbool

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val n_of_digits : bool list -> n

val n_of_ascii : ascii -> n

type string =
| EmptyString
| String of ascii * string

val zlength_aux : z -> 'a1 list -> z

val zlength : 'a1 list -> z

val shift_nat : nat -> positive -> positive

val shift_pos : positive -> positive -> positive

val two_power_nat : nat -> z

val two_power_pos : positive -> z

val two_p : z -> z

val zeq : z -> z -> sumbool

val zlt : z -> z -> sumbool

val zle : z -> z -> sumbool

val proj_sumbool : sumbool -> bool

val p_mod_two_p : positive -> nat -> z

val zshiftin : bool -> z -> z

val zzero_ext : z -> z -> z

val zsign_ext : z -> z -> z

val z_one_bits : nat -> z -> z -> z list

val p_is_power2 : positive -> bool

val z_is_power2 : z -> z option

val zsize : z -> z

type comparison0 =
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

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> sumbool

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

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int, int) prod option

  val divmods2 : int -> int -> int -> (int, int) prod option

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

module Wordsize_32 :
 sig
  val wordsize : nat
 end

module Int :
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> sumbool

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

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int, int) prod option

  val divmods2 : int -> int -> int -> (int, int) prod option

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

module Wordsize_8 :
 sig
  val wordsize : nat
 end

module Byte :
 sig
  val wordsize : nat

  val zwordsize : z

  val modulus : z

  val half_modulus : z

  val max_unsigned : z

  val max_signed : z

  val min_signed : z

  type int = z
    (* singleton inductive, whose constructor was mkint *)

  val intval : int -> z

  val coq_Z_mod_modulus : z -> z

  val unsigned : int -> z

  val signed : int -> z

  val repr : z -> int

  val zero : int

  val one : int

  val mone : int

  val iwordsize : int

  val eq_dec : int -> int -> sumbool

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

  val zero_ext : z -> int -> int

  val sign_ext : z -> int -> int

  val one_bits : int -> int list

  val is_power2 : int -> int option

  val cmp : comparison0 -> int -> int -> bool

  val cmpu : comparison0 -> int -> int -> bool

  val notbool : int -> int

  val divmodu2 : int -> int -> int -> (int, int) prod option

  val divmods2 : int -> int -> int -> (int, int) prod option

  val testbit : int -> z -> bool

  val int_of_one_bits : int list -> int

  val no_overlap : int -> z -> int -> z -> bool

  val size : int -> z

  val unsigned_bitfield_extract : z -> z -> int -> int

  val signed_bitfield_extract : z -> z -> int -> int

  val bitfield_insert : z -> z -> int -> int -> int
 end

val str_to_bytes : string -> Byte.int list

val shr0 : z -> Int.int -> Int.int

val intlist_to_bytelist : Int.int list -> Byte.int list

val bytes_to_Int : Byte.int -> Byte.int -> Byte.int -> Byte.int -> Int.int

val bytelist_to_intlist : Byte.int list -> Int.int list

val map2 : ('a1 -> 'a2 -> 'a3) -> 'a1 list -> 'a2 list -> 'a3 list

val generate_and_pad : Byte.int list -> Int.int list

val k256 : Int.int list

val ch : Int.int -> Int.int -> Int.int -> Int.int

val maj : Int.int -> Int.int -> Int.int -> Int.int

val rotr : z -> Int.int -> Int.int

val sigma_0 : Int.int -> Int.int

val sigma_1 : Int.int -> Int.int

val sigma_2 : Int.int -> Int.int

val sigma_3 : Int.int -> Int.int

val w : (z -> Int.int) -> z -> Int.int

type registers = Int.int list

val init_registers : registers

val nthi : Int.int list -> z -> Int.int

val rnd_function : registers -> Int.int -> Int.int -> registers

val round : registers -> (z -> Int.int) -> z -> registers

val hash_block : registers -> Int.int list -> registers

val hash_blocks : registers -> Int.int list -> registers

val sHA_256 : Byte.int list -> Byte.int list

val test : string

val sha : unit0 -> Byte.int list
