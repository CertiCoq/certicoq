
type __ = Obj.t

val xorb : bool -> bool -> bool

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type compareSpecT =
| CompEqT
| CompLtT
| CompGtT

val compareSpec2Type : comparison -> compareSpecT

type 'a compSpecT = compareSpecT

val compSpec2Type : 'a1 -> 'a1 -> comparison -> 'a1 compSpecT

val id : 'a1 -> 'a1

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2



type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

val nzhead : uint -> uint

val unorm : uint -> uint

val norm : unit -> unit

val revapp : uint -> uint -> uint

val rev : uint -> uint

module Little :
 sig
  val succ : uint -> uint

  val double : uint -> uint

  val succ_double : uint -> uint
 end

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

val eqb : int -> int -> bool

val leb : int -> int -> bool

val ltb : int -> int -> bool



val eqb0 : bool -> bool -> bool

type reflect =
| ReflectT
| ReflectF

val iff_reflect : bool -> reflect

module type OrderedType =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module type OrderedType' =
 sig
  type t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module OT_to_Full :
 functor (O:OrderedType') ->
 sig
  type t = O.t

  val compare : t -> t -> comparison

  val eq_dec : t -> t -> bool
 end

module OT_to_OrderTac :
 functor (OT:OrderedType) ->
 sig
  module OTF :
   sig
    type t = OT.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  module TO :
   sig
    type t = OTF.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end
 end

module OrderedTypeFacts :
 functor (O:OrderedType') ->
 sig
  module OrderTac :
   sig
    module OTF :
     sig
      type t = O.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> bool
     end

    module TO :
     sig
      type t = OTF.t

      val compare : t -> t -> comparison

      val eq_dec : t -> t -> bool
     end
   end

  val eq_dec : O.t -> O.t -> bool

  val lt_dec : O.t -> O.t -> bool

  val eqb : O.t -> O.t -> bool
 end

module Nat :
 sig
  type t = int

  val zero : int

  val one : int

  val two : int

  val succ : int -> int

  val pred : int -> int

  val add : int -> int -> int

  val double : int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val compare : int -> int -> comparison

  val max : int -> int -> int

  val min : int -> int -> int

  val even : int -> bool

  val odd : int -> bool

  val pow : int -> int -> int

  val tail_add : int -> int -> int

  val tail_addmul : int -> int -> int -> int

  val tail_mul : int -> int -> int

  val of_uint_acc : uint -> int -> int

  val of_uint : uint -> int

  val to_little_uint : int -> uint -> uint

  val to_uint : int -> uint

  val of_int : unit -> int option

  val to_int : int -> unit

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val gcd : int -> int -> int

  val square : int -> int

  val sqrt_iter : int -> int -> int -> int -> int

  val sqrt : int -> int

  val log2_iter : int -> int -> int -> int -> int

  val log2 : int -> int

  val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val div2 : int -> int

  val testbit : int -> int -> bool

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int

  val coq_land : int -> int -> int

  val coq_lor : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val recursion : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  val leb_spec0 : int -> int -> reflect

  val ltb_spec0 : int -> int -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : int -> int -> bool

    val min_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val min_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : int -> int -> bool
   end

  val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val max_dec : int -> int -> bool

  val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val min_dec : int -> int -> bool

  module Private_Parity :
   sig
   end

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : int -> int

  val log2_up : int -> int

  module Private_NZDiv :
   sig
   end

  val lcm : int -> int -> int

  val eqb_spec : int -> int -> reflect

  val b2n : bool -> int

  val setbit : int -> int -> int

  val clearbit : int -> int -> int

  val ones : int -> int

  val lnot : int -> int -> int
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of int
  | IsNeg
 end

module Coq_Pos :
 sig
  type t = int

  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred : int -> int

  val pred_N : int -> int

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val mask_rect : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1

  val mask_rec : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val pred_mask : mask -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val sub : int -> int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val pow : int -> int -> int

  val square : int -> int

  val div2 : int -> int

  val div2_up : int -> int

  val size_nat : int -> int

  val size : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val min : int -> int -> int

  val max : int -> int -> int

  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val sqrtrem_step :
    (int -> int) -> (int -> int) -> (int * mask) -> int * mask

  val sqrtrem : int -> int * mask

  val sqrt : int -> int

  val gcdn : int -> int -> int -> int

  val gcd : int -> int -> int

  val ggcdn : int -> int -> int -> int * (int * int)

  val ggcd : int -> int -> int * (int * int)

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val shiftl_nat : int -> int -> int

  val shiftr_nat : int -> int -> int

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val testbit_nat : int -> int -> bool

  val testbit : int -> int -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_nat : int -> int

  val of_succ_nat : int -> int

  val of_uint_acc : uint -> int -> int

  val of_uint : uint -> int

  val of_int : unit -> int option

  val to_little_uint : int -> uint

  val to_uint : int -> uint

  val to_int : int -> unit

  val eq_dec : int -> int -> bool

  val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  val peano_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  type coq_PeanoView =
  | PeanoOne
  | PeanoSucc of int * coq_PeanoView

  val coq_PeanoView_rect :
    'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1

  val coq_PeanoView_rec :
    'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1

  val peanoView_xO : int -> coq_PeanoView -> coq_PeanoView

  val peanoView_xI : int -> coq_PeanoView -> coq_PeanoView

  val peanoView : int -> coq_PeanoView

  val coq_PeanoView_iter :
    'a1 -> (int -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1

  val eqb_spec : int -> int -> reflect

  val switch_Eq : comparison -> comparison -> comparison

  val mask2cmp : mask -> comparison

  val leb_spec0 : int -> int -> reflect

  val ltb_spec0 : int -> int -> reflect

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : int -> int -> bool

    val min_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val min_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : int -> int -> bool
   end

  val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val max_dec : int -> int -> bool

  val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val min_dec : int -> int -> bool
 end

module N :
 sig
  val succ : int -> int

  val succ_pos : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val to_nat : int -> int

  val of_nat : int -> int

  val eq_dec : int -> int -> bool
 end

val nth : int -> 'a1 list -> 'a1 -> 'a1

val rev_append : 'a1 list -> 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val combine : 'a1 list -> 'a2 list -> ('a1 * 'a2) list

val zero0 : char

val one0 : char

val shift : bool -> char -> char

val ascii_of_pos : int -> char

val ascii_of_N : int -> char

val ascii_of_nat : int -> char

val n_of_digits : bool list -> int

val n_of_ascii : char -> int

val nat_of_ascii : char -> int

val string_dec : char list -> char list -> bool

val append : char list -> char list -> char list

type 'a exception0 =
| Exc of char list
| Ret of 'a

module MakeListOrdering :
 functor (O:OrderedType) ->
 sig
  module MO :
   sig
    module OrderTac :
     sig
      module OTF :
       sig
        type t = O.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> bool
       end

      module TO :
       sig
        type t = OTF.t

        val compare : t -> t -> comparison

        val eq_dec : t -> t -> bool
       end
     end

    val eq_dec : O.t -> O.t -> bool

    val lt_dec : O.t -> O.t -> bool

    val eqb : O.t -> O.t -> bool
   end
 end

type ident = char list

type kername = char list

type name =
| NAnon
| NNamed of ident

type inductive = { inductive_mind : kername; inductive_ind : int }

module Coq_Nat :
 sig
  type t = int

  val zero : int

  val one : int

  val two : int

  val succ : int -> int

  val pred : int -> int

  val add : int -> int -> int

  val double : int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val compare : int -> int -> comparison

  val max : int -> int -> int

  val min : int -> int -> int

  val even : int -> bool

  val odd : int -> bool

  val pow : int -> int -> int

  val tail_add : int -> int -> int

  val tail_addmul : int -> int -> int -> int

  val tail_mul : int -> int -> int

  val of_uint_acc : uint -> int -> int

  val of_uint : uint -> int

  val to_little_uint : int -> uint -> uint

  val to_uint : int -> uint

  val of_int : unit -> int option

  val to_int : int -> unit

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val gcd : int -> int -> int

  val square : int -> int

  val sqrt_iter : int -> int -> int -> int -> int

  val sqrt : int -> int

  val log2_iter : int -> int -> int -> int -> int

  val log2 : int -> int

  val iter : int -> ('a1 -> 'a1) -> 'a1 -> 'a1

  val div2 : int -> int

  val testbit : int -> int -> bool

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val bitwise : (bool -> bool -> bool) -> int -> int -> int -> int

  val coq_land : int -> int -> int

  val coq_lor : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val recursion : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  val eq_dec : int -> int -> bool

  val leb_spec0 : int -> int -> reflect

  val ltb_spec0 : int -> int -> reflect

  module Private_OrderTac :
   sig
    module IsTotal :
     sig
     end

    module Tac :
     sig
     end
   end

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : int -> int -> bool

    val min_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val min_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : int -> int -> bool
   end

  val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val max_dec : int -> int -> bool

  val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val min_dec : int -> int -> bool

  module Private_Parity :
   sig
   end

  module Private_NZPow :
   sig
   end

  module Private_NZSqrt :
   sig
   end

  val sqrt_up : int -> int

  val log2_up : int -> int

  module Private_NZDiv :
   sig
   end

  val lcm : int -> int -> int

  val eqb_spec : int -> int -> reflect

  val b2n : bool -> int

  val setbit : int -> int -> int

  val clearbit : int -> int -> int

  val ones : int -> int

  val lnot : int -> int -> int
 end

type 'a eq =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_Eq *)

val eq_dec0 : 'a1 eq -> 'a1 -> 'a1 -> bool

val inductive_dec : inductive -> inductive -> bool

val nEq : int eq

type cnstr = { cnstrNm : char list; cnstrArity : int }

type ityp = { itypNm : char list; itypCnstrs : cnstr list }

type itypPack = ityp list

type 'm monad = { ret : (__ -> __ -> 'm);
                  bind : (__ -> __ -> 'm -> (__ -> 'm) -> 'm) }

val ret : 'a1 monad -> 'a2 -> 'a1

val bind : 'a1 monad -> 'a1 -> ('a2 -> 'a1) -> 'a1

type 'm pMonad = { pret : (__ -> __ -> __ -> 'm);
                   pbind : (__ -> __ -> __ -> 'm -> (__ -> 'm) -> 'm) }

type ('m, 'x) monP = __

val pbind : 'a1 pMonad -> ('a1, 'a3) monP -> 'a1 -> ('a2 -> 'a1) -> 'a1

val pMonad_Monad : 'a1 monad -> 'a1 pMonad

type ('t, 'm) monadState = { get : 'm; put : ('t -> 'm) }

val get : ('a1, 'a2) monadState -> 'a2

val put : ('a1, 'a2) monadState -> 'a1 -> 'a2

type ('src, 'dst) certicoqTranslation = 'src -> 'dst exception0

module Positive_as_OT :
 sig
  type t = int

  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred : int -> int

  val pred_N : int -> int

  type mask = Pos.mask =
  | IsNul
  | IsPos of int
  | IsNeg

  val mask_rect : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1

  val mask_rec : 'a1 -> (int -> 'a1) -> 'a1 -> mask -> 'a1

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : int -> mask

  val pred_mask : mask -> mask

  val sub_mask : int -> int -> mask

  val sub_mask_carry : int -> int -> mask

  val sub : int -> int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val pow : int -> int -> int

  val square : int -> int

  val div2 : int -> int

  val div2_up : int -> int

  val size_nat : int -> int

  val size : int -> int

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val min : int -> int -> int

  val max : int -> int -> int

  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val sqrtrem_step :
    (int -> int) -> (int -> int) -> (int * mask) -> int * mask

  val sqrtrem : int -> int * mask

  val sqrt : int -> int

  val gcdn : int -> int -> int -> int

  val gcd : int -> int -> int

  val ggcdn : int -> int -> int -> int * (int * int)

  val ggcd : int -> int -> int * (int * int)

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val ldiff : int -> int -> int

  val coq_lxor : int -> int -> int

  val shiftl_nat : int -> int -> int

  val shiftr_nat : int -> int -> int

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val testbit_nat : int -> int -> bool

  val testbit : int -> int -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_nat : int -> int

  val of_succ_nat : int -> int

  val of_uint_acc : uint -> int -> int

  val of_uint : uint -> int

  val of_int : unit -> int option

  val to_little_uint : int -> uint

  val to_uint : int -> uint

  val to_int : int -> unit

  val eq_dec : int -> int -> bool

  val peano_rect : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  val peano_rec : 'a1 -> (int -> 'a1 -> 'a1) -> int -> 'a1

  type coq_PeanoView = Coq_Pos.coq_PeanoView =
  | PeanoOne
  | PeanoSucc of int * coq_PeanoView

  val coq_PeanoView_rect :
    'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1

  val coq_PeanoView_rec :
    'a1 -> (int -> coq_PeanoView -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1

  val peanoView_xO : int -> coq_PeanoView -> coq_PeanoView

  val peanoView_xI : int -> coq_PeanoView -> coq_PeanoView

  val peanoView : int -> coq_PeanoView

  val coq_PeanoView_iter :
    'a1 -> (int -> 'a1 -> 'a1) -> int -> coq_PeanoView -> 'a1

  val eqb_spec : int -> int -> reflect

  val switch_Eq : comparison -> comparison -> comparison

  val mask2cmp : mask -> comparison

  val leb_spec0 : int -> int -> reflect

  val ltb_spec0 : int -> int -> reflect

  module Private_Tac :
   sig
   end

  module Private_Dec :
   sig
    val max_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val max_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val max_dec : int -> int -> bool

    val min_case_strong :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__ ->
      'a1) -> 'a1

    val min_case :
      int -> int -> (int -> int -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1

    val min_dec : int -> int -> bool
   end

  val max_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val max_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val max_dec : int -> int -> bool

  val min_case_strong : int -> int -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1

  val min_case : int -> int -> 'a1 -> 'a1 -> 'a1

  val min_dec : int -> int -> bool
 end

type ('term, 'value) cTerm = 'term

val monad_option : __ option monad

type ienv = (char list * itypPack) list

type ('t, 'classType) varClass = 't -> 'classType

val varClass0 : ('a1, 'a2) varClass -> 'a1 -> 'a2

type ('nVar, 'opid) nTerm =
| Vterm of 'nVar
| Oterm of 'opid * ('nVar, 'opid) bTerm list
and ('nVar, 'opid) bTerm =
| Bterm of 'nVar list * ('nVar, 'opid) nTerm

val getVar : ('a1, 'a2) nTerm -> 'a1 option

type dcon = inductive * int

val digit2ascii : int -> char

val nat2string : int -> int -> char list

val nat2string10 : int -> char list

type l5Opid =
| CLambda
| CKLambda
| CLet
| CFix of int * int
| CDCon of dcon * int
| CHalt
| CRet
| CCall
| CMatch of (dcon * int) list

val varClassP : (int, bool) varClass

val varClassNVar : ('a1, 'a3) varClass -> ('a1 * 'a2, 'a3) varClass

type nVar = int * name

val varClassNVar0 : (nVar, bool) varClass

val peq : int -> int -> bool

val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option

val fromN : int -> int -> int list

val nthN : 'a1 list -> int -> 'a1 option

val max_list : int list -> int -> int

module PTree :
 sig
  type elt = int

  val elt_eq : int -> int -> bool

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  val empty : 'a1 t

  val get : int -> 'a1 t -> 'a1 option

  val set : int -> 'a1 -> 'a1 t -> 'a1 t

  val remove : int -> 'a1 t -> 'a1 t

  val bempty : 'a1 t -> bool

  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val prev_append : int -> int -> int

  val prev : int -> int

  val xmap : (int -> 'a1 -> 'a2) -> 'a1 t -> int -> 'a2 t

  val map : (int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t

  val filter1 : ('a1 -> bool) -> 'a1 t -> 'a1 t

  val xcombine_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val xcombine_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val combine :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val xelements : 'a1 t -> int -> (int * 'a1) list -> (int * 'a1) list

  val elements : 'a1 t -> (int * 'a1) list

  val xkeys : 'a1 t -> int -> int list

  val xfold : ('a2 -> int -> 'a1 -> 'a2) -> int -> 'a1 t -> 'a2 -> 'a2

  val fold : ('a2 -> int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

module M :
 sig
  type elt = int

  val elt_eq : int -> int -> bool

  type 'a tree = 'a PTree.tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  val empty : 'a1 t

  val get : int -> 'a1 t -> 'a1 option

  val set : int -> 'a1 -> 'a1 t -> 'a1 t

  val remove : int -> 'a1 t -> 'a1 t

  val bempty : 'a1 t -> bool

  val beq : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool

  val prev_append : int -> int -> int

  val prev : int -> int

  val xmap : (int -> 'a1 -> 'a2) -> 'a1 t -> int -> 'a2 t

  val map : (int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t

  val map1 : ('a1 -> 'a2) -> 'a1 t -> 'a2 t

  val coq_Node' : 'a1 t -> 'a1 option -> 'a1 t -> 'a1 t

  val filter1 : ('a1 -> bool) -> 'a1 t -> 'a1 t

  val xcombine_l : ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t

  val xcombine_r : ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t

  val combine :
    ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t

  val xelements : 'a1 t -> int -> (int * 'a1) list -> (int * 'a1) list

  val elements : 'a1 t -> (int * 'a1) list

  val xkeys : 'a1 t -> int -> int list

  val xfold : ('a2 -> int -> 'a1 -> 'a2) -> int -> 'a1 t -> 'a2 -> 'a2

  val fold : ('a2 -> int -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2

  val fold1 : ('a2 -> 'a1 -> 'a2) -> 'a1 t -> 'a2 -> 'a2
 end

type var = M.elt

type fTag = M.elt

type iTag = M.elt

type cTag = M.elt

type prim = M.elt

val findtag : (cTag * 'a1) list -> cTag -> 'a1 option

type exp =
| Econstr of var * cTag * var list * exp
| Ecase of var * (cTag * exp) list
| Eproj of var * cTag * int * var * exp
| Efun of fundefs * exp
| Eapp of var * fTag * var list
| Eprim of var * prim * var list * exp
| Ehalt of var
and fundefs =
| Fcons of var * fTag * var list * exp * fundefs
| Fnil

type val0 =
| Vconstr of cTag * val0 list
| Vfun of val0 M.t * fundefs * var
| Vint of int

type cTyInfo = (((name * name) * iTag) * int) * int

type iTyInfo = (cTag * int) list

type cEnv = cTyInfo M.t

type iEnv = iTyInfo M.t

type fTyInfo = int * int list

type fEnv = fTyInfo M.t

val add_cloTag : int -> int -> cEnv -> cEnv

type l5Term = (nVar, l5Opid) nTerm

type color =
| Red
| Black

module Color :
 sig
  type t = color
 end

module Make :
 functor (X:OrderedType) ->
 sig
  module Raw :
   sig
    type elt = X.t

    type tree =
    | Leaf
    | Node of Color.t * tree * X.t * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : X.t -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : X.t list -> tree -> X.t list

    val elements : tree -> X.t list

    val rev_elements_aux : X.t list -> tree -> X.t list

    val rev_elements : tree -> X.t list

    val cardinal : tree -> int

    val maxdepth : tree -> int

    val mindepth : tree -> int

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      X.t -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> X.t -> tree -> bool

    val subsetr : (tree -> bool) -> X.t -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val singleton : elt -> tree

    val makeBlack : tree -> tree

    val makeRed : tree -> tree

    val lbal : tree -> X.t -> tree -> tree

    val rbal : tree -> X.t -> tree -> tree

    val rbal' : tree -> X.t -> tree -> tree

    val lbalS : tree -> X.t -> tree -> tree

    val rbalS : tree -> X.t -> tree -> tree

    val ins : X.t -> tree -> tree

    val add : X.t -> tree -> tree

    val append : tree -> tree -> tree

    val del : X.t -> tree -> tree

    val remove : X.t -> tree -> tree

    val delmin : tree -> elt -> tree -> elt * tree

    val remove_min : tree -> (elt * tree) option

    val bogus : tree * elt list

    val treeify_zero : elt list -> tree * elt list

    val treeify_one : elt list -> tree * elt list

    val treeify_cont :
      (elt list -> tree * elt list) -> (elt list -> tree * elt list) -> elt
      list -> tree * elt list

    val treeify_aux : bool -> int -> elt list -> tree * elt list

    val plength_aux : elt list -> int -> int

    val plength : elt list -> int

    val treeify : elt list -> tree

    val filter_aux : (elt -> bool) -> tree -> X.t list -> X.t list

    val filter : (elt -> bool) -> t -> t

    val partition_aux :
      (elt -> bool) -> tree -> X.t list -> X.t list -> X.t list * X.t list

    val partition : (elt -> bool) -> t -> t * t

    val union_list : elt list -> elt list -> elt list -> elt list

    val linear_union : tree -> tree -> tree

    val inter_list : X.t list -> elt list -> elt list -> elt list

    val linear_inter : tree -> tree -> tree

    val diff_list : elt list -> elt list -> elt list -> elt list

    val linear_diff : tree -> tree -> tree

    val skip_red : tree -> tree

    val skip_black : tree -> tree

    val compare_height : tree -> tree -> tree -> tree -> comparison

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val ltb_tree : X.t -> tree -> bool

    val gtb_tree : X.t -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = X.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> bool
         end

        module TO :
         sig
          type t = OTF.t

          val compare : t -> t -> comparison

          val eq_dec : t -> t -> bool
         end
       end

      val eq_dec : X.t -> X.t -> bool

      val lt_dec : X.t -> X.t -> bool

      val eqb : X.t -> X.t -> bool
     end

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Color.t * tree * X.t * tree
    | R_min_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree
       * X.t * tree * elt option * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Color.t * tree * X.t * tree
    | R_max_elt_2 of tree * Color.t * tree * X.t * tree * Color.t * tree
       * X.t * tree * elt option * coq_R_max_elt

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = X.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> bool
           end

          module TO :
           sig
            type t = OTF.t

            val compare : t -> t -> comparison

            val eq_dec : t -> t -> bool
           end
         end

        val eq_dec : X.t -> X.t -> bool

        val lt_dec : X.t -> X.t -> bool

        val eqb : X.t -> X.t -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    val rcase : (tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1

    val rrcase :
      (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree ->
      'a1

    val rrcase' :
      (tree -> X.t -> tree -> X.t -> tree -> 'a1) -> (tree -> 'a1) -> tree ->
      'a1
   end

  module E :
   sig
    type t = X.t

    val compare : t -> t -> comparison

    val eq_dec : t -> t -> bool
   end

  type elt = X.t

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> int

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val mk_opt_t : (elt * Raw.t) option -> (elt * t) option

  val remove_min : t_ -> (elt * t) option
 end

module PS :
 sig
  module Raw :
   sig
    type elt = int

    type tree =
    | Leaf
    | Node of Color.t * tree * int * tree

    val empty : tree

    val is_empty : tree -> bool

    val mem : int -> tree -> bool

    val min_elt : tree -> elt option

    val max_elt : tree -> elt option

    val choose : tree -> elt option

    val fold : (elt -> 'a1 -> 'a1) -> tree -> 'a1 -> 'a1

    val elements_aux : int list -> tree -> int list

    val elements : tree -> int list

    val rev_elements_aux : int list -> tree -> int list

    val rev_elements : tree -> int list

    val cardinal : tree -> int

    val maxdepth : tree -> int

    val mindepth : tree -> int

    val for_all : (elt -> bool) -> tree -> bool

    val exists_ : (elt -> bool) -> tree -> bool

    type enumeration =
    | End
    | More of elt * tree * enumeration

    val cons : tree -> enumeration -> enumeration

    val compare_more :
      int -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_cont :
      tree -> (enumeration -> comparison) -> enumeration -> comparison

    val compare_end : enumeration -> comparison

    val compare : tree -> tree -> comparison

    val equal : tree -> tree -> bool

    val subsetl : (tree -> bool) -> int -> tree -> bool

    val subsetr : (tree -> bool) -> int -> tree -> bool

    val subset : tree -> tree -> bool

    type t = tree

    val singleton : elt -> tree

    val makeBlack : tree -> tree

    val makeRed : tree -> tree

    val lbal : tree -> int -> tree -> tree

    val rbal : tree -> int -> tree -> tree

    val rbal' : tree -> int -> tree -> tree

    val lbalS : tree -> int -> tree -> tree

    val rbalS : tree -> int -> tree -> tree

    val ins : int -> tree -> tree

    val add : int -> tree -> tree

    val append : tree -> tree -> tree

    val del : int -> tree -> tree

    val remove : int -> tree -> tree

    val delmin : tree -> elt -> tree -> elt * tree

    val remove_min : tree -> (elt * tree) option

    val bogus : tree * elt list

    val treeify_zero : elt list -> tree * elt list

    val treeify_one : elt list -> tree * elt list

    val treeify_cont :
      (elt list -> tree * elt list) -> (elt list -> tree * elt list) -> elt
      list -> tree * elt list

    val treeify_aux : bool -> int -> elt list -> tree * elt list

    val plength_aux : elt list -> int -> int

    val plength : elt list -> int

    val treeify : elt list -> tree

    val filter_aux : (elt -> bool) -> tree -> int list -> int list

    val filter : (elt -> bool) -> t -> t

    val partition_aux :
      (elt -> bool) -> tree -> int list -> int list -> int list * int list

    val partition : (elt -> bool) -> t -> t * t

    val union_list : elt list -> elt list -> elt list -> elt list

    val linear_union : tree -> tree -> tree

    val inter_list : int list -> elt list -> elt list -> elt list

    val linear_inter : tree -> tree -> tree

    val diff_list : elt list -> elt list -> elt list -> elt list

    val linear_diff : tree -> tree -> tree

    val skip_red : tree -> tree

    val skip_black : tree -> tree

    val compare_height : tree -> tree -> tree -> tree -> comparison

    val union : t -> t -> t

    val diff : t -> t -> t

    val inter : t -> t -> t

    val ltb_tree : int -> tree -> bool

    val gtb_tree : int -> tree -> bool

    val isok : tree -> bool

    module MX :
     sig
      module OrderTac :
       sig
        module OTF :
         sig
          type t = int

          val compare : int -> int -> comparison

          val eq_dec : int -> int -> bool
         end

        module TO :
         sig
          type t = int

          val compare : int -> int -> comparison

          val eq_dec : int -> int -> bool
         end
       end

      val eq_dec : int -> int -> bool

      val lt_dec : int -> int -> bool

      val eqb : int -> int -> bool
     end

    type coq_R_min_elt =
    | R_min_elt_0 of tree
    | R_min_elt_1 of tree * Color.t * tree * int * tree
    | R_min_elt_2 of tree * Color.t * tree * int * tree * Color.t * tree
       * int * tree * elt option * coq_R_min_elt

    type coq_R_max_elt =
    | R_max_elt_0 of tree
    | R_max_elt_1 of tree * Color.t * tree * int * tree
    | R_max_elt_2 of tree * Color.t * tree * int * tree * Color.t * tree
       * int * tree * elt option * coq_R_max_elt

    module L :
     sig
      module MO :
       sig
        module OrderTac :
         sig
          module OTF :
           sig
            type t = int

            val compare : int -> int -> comparison

            val eq_dec : int -> int -> bool
           end

          module TO :
           sig
            type t = int

            val compare : int -> int -> comparison

            val eq_dec : int -> int -> bool
           end
         end

        val eq_dec : int -> int -> bool

        val lt_dec : int -> int -> bool

        val eqb : int -> int -> bool
       end
     end

    val flatten_e : enumeration -> elt list

    val rcase : (tree -> int -> tree -> 'a1) -> (tree -> 'a1) -> tree -> 'a1

    val rrcase :
      (tree -> int -> tree -> int -> tree -> 'a1) -> (tree -> 'a1) -> tree ->
      'a1

    val rrcase' :
      (tree -> int -> tree -> int -> tree -> 'a1) -> (tree -> 'a1) -> tree ->
      'a1
   end

  module E :
   sig
    type t = int

    val compare : int -> int -> comparison

    val eq_dec : int -> int -> bool
   end

  type elt = int

  type t_ = Raw.t
    (* singleton inductive, whose constructor was Mkt *)

  val this : t_ -> Raw.t

  type t = t_

  val mem : elt -> t -> bool

  val add : elt -> t -> t

  val remove : elt -> t -> t

  val singleton : elt -> t

  val union : t -> t -> t

  val inter : t -> t -> t

  val diff : t -> t -> t

  val equal : t -> t -> bool

  val subset : t -> t -> bool

  val empty : t

  val is_empty : t -> bool

  val elements : t -> elt list

  val choose : t -> elt option

  val fold : (elt -> 'a1 -> 'a1) -> t -> 'a1 -> 'a1

  val cardinal : t -> int

  val filter : (elt -> bool) -> t -> t

  val for_all : (elt -> bool) -> t -> bool

  val exists_ : (elt -> bool) -> t -> bool

  val partition : (elt -> bool) -> t -> t * t

  val eq_dec : t -> t -> bool

  val compare : t -> t -> comparison

  val min_elt : t -> elt option

  val max_elt : t -> elt option

  val mk_opt_t : (elt * Raw.t) option -> (elt * t) option

  val remove_min : t_ -> (elt * t) option
 end

val union_list0 : PS.t -> PS.elt list -> PS.t

type exp_ctx =
| Hole_c
| Econstr_c of var * cTag * var list * exp_ctx
| Eproj_c of var * cTag * int * var * exp_ctx
| Eprim_c of var * prim * var list * exp_ctx
| Ecase_c of var * (cTag * exp) list * cTag * exp_ctx * (cTag * exp) list
| Efun1_c of fundefs * exp_ctx
| Efun2_c of fundefs_ctx * exp
and fundefs_ctx =
| Fcons1_c of var * cTag * var list * exp_ctx * fundefs
| Fcons2_c of var * cTag * var list * exp * fundefs_ctx

val app_ctx_f : exp_ctx -> exp -> exp

val app_f_ctx_f : fundefs_ctx -> exp -> fundefs

val comp_ctx_f : exp_ctx -> exp_ctx -> exp_ctx

val comp_f_ctx_f : fundefs_ctx -> exp_ctx -> fundefs_ctx

type fVSet = PS.t

val add_list : fVSet -> fVSet -> PS.elt list -> fVSet

val exp_fv_aux : exp -> fVSet -> fVSet -> fVSet

val fundefs_fv_aux : fundefs -> fVSet -> fVSet -> fVSet * fVSet

val fundefs_fv : fundefs -> fVSet

val max_var : exp -> int -> int

val max_var_fundefs : fundefs -> int -> int

type env = val0 M.t

type prims = (val0 list -> val0 option) M.t

val var_dec : int -> int -> bool

type svalue =
| SVconstr of cTag * var list
| SVfun of fTag * var list * exp

type ctx_map = svalue M.t

type r_map = var M.t

type c_map = int M.t

type b_map = bool M.t

val getd : 'a1 -> int -> 'a1 M.t -> 'a1

val term_size : exp -> int

val funs_size : fundefs -> int

val set_list : (M.elt * 'a1) list -> 'a1 M.t -> 'a1 M.t

val apply_r : M.elt M.t -> int -> M.elt

val apply_r_list : M.elt M.t -> int list -> M.elt list

type tag = int

val all_fun_name : fundefs -> var list

val update_census_list :
  r_map -> var list -> (var -> c_map -> int) -> c_map -> c_map

val update_census : r_map -> exp -> (var -> c_map -> int) -> c_map -> c_map

val update_census_f :
  r_map -> fundefs -> (var -> c_map -> int) -> c_map -> c_map

val init_census : exp -> c_map

val dec_census : r_map -> exp -> c_map -> c_map

val dec_census_list : r_map -> var list -> c_map -> c_map

val dec_census_all_case : r_map -> (var * exp) list -> c_map -> c_map

val dec_census_case : r_map -> (var * exp) list -> var -> c_map -> c_map

val update_count_inlined : var list -> var list -> c_map -> c_map

val precontractfun :
  r_map -> c_map -> ctx_map -> fundefs -> (fundefs * c_map) * ctx_map

val contractcases :
  ((exp * ctx_map) * b_map) -> (r_map -> c_map -> ((exp * ctx_map) * b_map)
  -> __ -> ((exp * c_map) * b_map, __) sigT) -> r_map -> c_map -> b_map ->
  ctx_map -> (var * exp) list -> (((var * exp) list * c_map) * b_map, __) sigT

val postcontractfun :
  ((exp * ctx_map) * b_map) -> (r_map -> c_map -> ((exp * ctx_map) * b_map)
  -> __ -> ((exp * c_map) * b_map, __) sigT) -> r_map -> c_map -> b_map ->
  ctx_map -> fundefs -> ((fundefs * c_map) * b_map, __) sigT

val contract_func :
  (r_map, (c_map, (exp, (ctx_map, b_map) sigT) sigT) sigT) sigT ->
  ((exp * c_map) * b_map, __) sigT

val contract :
  r_map -> c_map -> exp -> ctx_map -> b_map -> ((exp * c_map) * b_map, __)
  sigT

val shrink_top : exp -> exp

type l5_conId = dcon

val l5_conId_dec : l5_conId -> l5_conId -> bool

type conId_map = (l5_conId * cTag) list

val dcon_to_info : cTag -> l5_conId -> conId_map -> cTag

val dcon_to_tag : cTag -> l5_conId -> conId_map -> cTag

val fromN0 : int -> int -> int list * int

val ctx_bind_proj : cTag -> int -> int -> var -> int -> exp_ctx * var

type nEnv = name M.t

val n_empty : nEnv

type t_info = fTag

type t_map = t_info M.t

val t_empty : t_map

val get_f : fTag -> var -> t_map -> fTag

type s_map = var M.t

val s_empty : var M.t

val get_s : nVar -> s_map -> var

val set_s_list : nVar list -> var list -> s_map -> s_map

type conv_env = (conId_map * t_map) * nEnv

val set_nt : var -> (name * t_info) -> conv_env -> conv_env

val set_t : var -> t_info -> conv_env -> conv_env

val set_n : var -> name -> conv_env -> conv_env

val set_t_f_list : fTag -> var list -> nVar list -> conv_env -> conv_env

val convert :
  cTag -> fTag -> fTag -> (nVar, l5Opid) nTerm -> s_map -> s_map -> conv_env
  -> var -> ((exp * var) * conv_env) option

type ienv0 = (char list * itypPack) list

val convert_cnstrs :
  char list -> cTag list -> cnstr list -> inductive -> int -> iTag -> cEnv ->
  conId_map -> cEnv * conId_map

val convert_typack :
  ityp list -> char list -> int ->
  ((((iEnv * cEnv) * cTag) * iTag) * conId_map) ->
  (((iEnv * cEnv) * cTag) * iTag) * conId_map

val convert_env' :
  ienv0 -> ((((iEnv * cEnv) * cTag) * iTag) * conId_map) ->
  (((iEnv * cEnv) * cTag) * iTag) * conId_map

val convert_env :
  cTag -> iTag -> ienv0 -> (((iEnv * cEnv) * cTag) * iTag) * conId_map

val convert_top :
  cTag -> iTag -> fTag -> fTag -> (ienv0 * (nVar, l5Opid) nTerm) ->
  (((((cEnv * nEnv) * fEnv) * cTag) * iTag) * exp) option

val get_next : int -> int list -> (int * int) * int list

val get_n_next : int -> int list -> int -> (int list * int) * int list

val freshen_term : exp -> int M.t -> int -> int list -> (exp * int) * int list

val freshen_fun :
  fundefs -> int M.t -> int -> int list -> (fundefs * int) * int list

type ('s, 't) state =
  's -> 't * 's
  (* singleton inductive, whose constructor was mkState *)

val runState : ('a1, 'a2) state -> 'a1 -> 'a2 * 'a1

val monad_state : ('a1, __) state monad

val monadState_state : ('a1, ('a1, __) state) monadState

type 'st inlineHeuristic = { update_funDef : (fundefs -> r_map -> 'st ->
                                             'st * 'st);
                             update_inFun : (var -> tag -> var list -> exp ->
                                            r_map -> 'st -> 'st);
                             update_App : (var -> tag -> var list -> 'st ->
                                          'st * bool) }

val update_funDef :
  'a1 inlineHeuristic -> fundefs -> r_map -> 'a1 -> 'a1 * 'a1

val update_inFun :
  'a1 inlineHeuristic -> var -> tag -> var list -> exp -> r_map -> 'a1 -> 'a1

val update_App :
  'a1 inlineHeuristic -> var -> tag -> var list -> 'a1 -> 'a1 * bool

type 't freshM = (int, 't) state

type r_map0 = var M.t

val freshen_exp : exp -> exp freshM

val add_fundefs :
  fundefs -> ((tag * var list) * exp) M.t -> ((tag * var list) * exp) M.t

val beta_contract_fds :
  'a1 inlineHeuristic -> fundefs -> ('a1 -> exp -> __ -> exp freshM) ->
  fundefs -> r_map0 -> 'a1 -> fundefs freshM

val beta_contract_func :
  'a1 inlineHeuristic -> (int * exp, (var M.t, (((tag * var list) * exp) M.t,
  'a1) sigT) sigT) sigT -> exp freshM

val beta_contract :
  'a1 inlineHeuristic -> (int * exp) -> var M.t -> ((tag * var list) * exp)
  M.t -> 'a1 -> exp freshM

val beta_contract_top : 'a1 inlineHeuristic -> exp -> int -> 'a1 -> exp

val combineInlineHeuristic :
  (bool -> bool -> bool) -> 'a1 inlineHeuristic -> 'a2 inlineHeuristic ->
  ('a1 * 'a2) inlineHeuristic

val postUncurryIH : int M.t inlineHeuristic

val inlineSmallIH : int -> bool M.t inlineHeuristic

val inlineSmallOrUncurried : int -> (bool M.t * int M.t) inlineHeuristic

val inline_uncurry_contract : exp -> int M.t -> int -> int -> exp

type st = int * int M.t

val eq_var : int -> int -> bool

val occurs_in_vars : var -> var list -> bool

val occurs_in_exp : var -> exp -> bool

val occurs_in_fundefs : var -> fundefs -> bool

type arrityMap = fTag M.t

type localMap = bool M.t

type stateType =
  (((((var * bool) * arrityMap) * fEnv) * fTag) * localMap) * st

type 't uncurryM = (stateType, 't) state

val markToInline : int -> var -> var -> unit uncurryM

val copyVar : var -> var uncurryM

val mark_as_uncurried : var -> unit uncurryM

val copyVars : var list -> var list uncurryM

val click : unit uncurryM

val already_uncurried : var -> bool uncurryM

val get_fTag : int -> fTag uncurryM

val uncurry_exp : exp -> exp uncurryM

val uncurry_fundefs : fundefs -> fundefs uncurryM

val uncurry :
  exp -> arrityMap -> fEnv -> fTag -> localMap -> int -> st ->
  ((((((exp * arrityMap) * fEnv) * fTag) * localMap) * var) * st) option

val uncurry_fuel' :
  int -> exp -> arrityMap -> fEnv -> fTag -> localMap -> int -> st ->
  (exp * st) * fEnv

val uncurry_fuel : int -> exp -> fEnv -> (exp * st) * fEnv

val erase_fundefs :
  exp -> fundefs -> ((exp * fundefs) -> exp * fundefs) -> exp * fundefs

val erase_nested_fundefs :
  fundefs -> exp -> fundefs -> ((exp * fundefs) -> exp * fundefs) ->
  exp * fundefs

val exp_hoist : exp -> exp

type varInfo =
| FVar of int
| MRFun of var
| BoundVar

type varInfoMap = varInfo M.t

type state_contents = { next_var : var; nect_cTag : cTag; next_iTag : 
                        iTag; cenv : cEnv; name_env : name M.t }

val cenv : state_contents -> cEnv

val name_env : state_contents -> name M.t

type 't ccstate = (state_contents, 't) state

val get_name_entry : var -> name ccstate

val set_name_entry : var -> name -> unit ccstate

val add_name : var -> char list -> unit ccstate

val add_name_suff : var -> var -> char list -> unit ccstate

val clo_env_suffix : char list

val clo_suffix : char list

val code_suffix : char list

val proj_suffix : char list

val get_name : var -> char list -> var ccstate

val get_name_no_suff : char list -> var ccstate

val make_record_cTag : int -> cTag ccstate

val get_var :
  cTag -> var -> varInfoMap -> cTag -> var -> (var * (exp -> exp)) ccstate

val get_vars :
  cTag -> var list -> varInfoMap -> cTag -> var -> (var list * (exp -> exp))
  ccstate

val add_params : int list -> varInfoMap -> varInfoMap

val make_env :
  cTag -> fVSet -> varInfoMap -> varInfoMap -> cTag -> var -> var ->
  ((cTag * varInfoMap) * (exp -> exp)) ccstate

val make_full_closure :
  cTag -> fundefs -> varInfoMap -> varInfoMap -> var ->
  ((varInfoMap * varInfoMap) * (exp -> exp)) ccstate

val exp_closure_conv :
  cTag -> exp -> varInfoMap -> cTag -> var -> (exp * (exp -> exp)) ccstate

val closure_conversion_hoist :
  cTag -> exp -> cTag -> iTag -> cEnv -> name M.t -> (cEnv * name M.t) * exp

type varInfo0 = var
  (* singleton inductive, whose constructor was FreeVar *)

type funInfo =
| Fun of var * fTag * var list

type varInfoMap0 = varInfo0 PTree.t

type funInfoMap = funInfo PTree.t

type state_contents0 = { next_var0 : var; next_fTag : fTag }

type 't state0 = (state_contents0, 't) state

val get_name0 : var state0

val get_names : int -> var list state0

val get_tag : fTag state0

val rename : varInfoMap0 -> var -> var

val rename_lst : varInfoMap0 -> var list -> var list

val add_functions : fundefs -> var list -> funInfoMap -> funInfoMap state0

val add_free_vars : var list -> varInfoMap0 -> (var list * varInfoMap0) state0

val fundefs_true_fv_aux :
  funInfoMap -> fundefs -> fVSet -> PS.t -> fVSet * PS.t

val fundefs_true_fv : funInfoMap -> fundefs -> PS.t

val exp_lambda_lift : exp -> varInfoMap0 -> funInfoMap -> exp state0

val fundefs_lambda_lift :
  fundefs -> varInfoMap0 -> funInfoMap -> fundefs state0

val lambda_lift : exp -> fTag -> exp

type live_fun =
| Live of var list list * bool list list

val bool_live : live_fun -> bool list list

val get_vars0 : fundefs -> var list list

val get_funs : fundefs -> var list

val get_bool_false : var list -> bool list

val get_bool_true : var list -> bool list

val get_bools : fundefs -> bool list list

val get_live_initial : fundefs -> live_fun

val replace_nth : int -> 'a1 list -> 'a1 -> 'a1 list

val find_fun : var -> var list -> int -> bool * int

val add_escaping : var -> live_fun -> var list -> live_fun

val add_escapings' : var list -> live_fun -> var list -> live_fun

val add_var_helper : var -> var list -> bool list -> bool list

val add_var : var -> live_fun -> int -> live_fun

val add_vars : var list -> live_fun -> int -> live_fun

val add_fun_args : int -> var list -> bool list -> live_fun -> live_fun

val add_fun_vars : var -> var list -> var list -> live_fun -> int -> live_fun

val escaping_fun_exp : exp -> live_fun -> var list -> live_fun

val escaping_fun_fundefs : fundefs -> live_fun -> var list -> live_fun

val live_expr : fundefs -> live_fun -> var list -> int -> exp -> live_fun

val live : fundefs -> live_fun -> var list -> int -> live_fun

val check_list_equality : bool list -> bool list -> bool

val check_list_list_equality : bool list list -> bool list list -> bool

val live_equality : live_fun -> live_fun -> bool

val num_vars : fundefs -> int -> int

val find_live_helper : fundefs -> live_fun -> var list -> int -> live_fun

val find_live : exp -> live_fun

val live_args : var list -> bool list -> var list

val eliminate_expr : live_fun -> var list -> exp -> exp

val eliminate_fundefs : fundefs -> live_fun -> var list -> int -> fundefs

val eliminate : exp -> exp

val print : char list -> unit

type l6env = ((prims * cEnv) * nEnv) * fEnv

type l6term = env * exp

type l6val = val0

val default_cTag : int

val default_iTag : int

val bogus_cloTag : int

val bogus_cloiTag : int

val fun_fTag : int

val kon_fTag : int

val certiL5_t0_L6 :
  ((ienv * l5Term, ienv * l5Term) cTerm, (l6env * l6term, l6val) cTerm)
  certicoqTranslation

type nEnv0 = name M.t

val show_pos : int -> char list

val show_binnat : int -> char list

val sep : 'a1 -> 'a1 list -> 'a1 list

type string_tree =
| Emp
| Str of char list
| App of string_tree * string_tree

val show_tree_c : string_tree -> char list -> char list

val show_tree : string_tree -> char list

val show_var : nEnv0 -> int -> string_tree

val show_con : cEnv -> cTag -> string_tree

val show_ftag : bool -> fTag -> string_tree

val show_vars : nEnv0 -> int list -> string_tree

type 't m = (string_tree, 't) state

val emit : string_tree -> unit m

val tab : int -> unit m

val chr_newline : char

val newline : unit m

val emit_exp : nEnv0 -> cEnv -> bool -> int -> exp -> unit m

val show_exp : nEnv0 -> cEnv -> bool -> exp -> char list

val concat : char list -> char list -> char list

val comp_L6 :
  (ienv * l5Term, ienv * l5Term) cTerm exception0 -> (l6env * l6term, l6val)
  cTerm exception0

val test2_L5 : (ienv * l5Term, ienv * l5Term) cTerm exception0

val compL6_and_print_twice :
  (ienv * l5Term, ienv * l5Term) cTerm exception0 -> unit

val out2 : unit
