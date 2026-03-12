From MetaRocq Require Import Show.
From MetaRocq.Utils Require Import bytestring.
From Corelib Require Import Numbers.Cyclic.Int63.PrimInt63 PrimString.
From CertiRocq.Plugin Require Import Loader PrimInt63 PrimString.

(* https://github.com/ocaml/Zarith/blob/master/z.mli *)

Axiom t : Type.

Axiom zero : t.
Axiom one : t.
Axioms succ pred abs neg : t -> t.
Axioms add sub mul div rem : t -> t -> t.
Axiom pow : t -> t -> t.
Axiom equal : t -> t -> bool.
Axiom compare : t -> t -> int. (* int63 *)

Axiom of_int : int -> t.
Axiom of_string : string -> t.
Axiom to_string : t -> string.

Axioms logand logor logxor : t -> t -> t.
Axiom lognot : t -> t.

Axioms max min : t -> t -> t.
Axioms leq geq lt gt : t -> t -> bool.

CertiRocq Register [
  t => "erased",
  zero => "z_zero",
  one => "z_one",
  succ => "z_succ" with tinfo,
  pred => "z_pred" with tinfo,
  abs => "z_abs" with tinfo,
  neg => "z_neg" with tinfo,
  add => "z_add" with tinfo,
  sub => "z_sub" with tinfo,
  mul => "z_mul" with tinfo,
  div => "z_div" with tinfo,
  rem => "z_rem" with tinfo,
  pow => "z_pow" with tinfo,

  logand => "z_logand" with tinfo,
  logor => "z_logor" with tinfo,
  logxor => "z_logxor" with tinfo,
  lognot => "z_lognot" with tinfo,

  max => "z_max",
  min => "z_min",

  leq => "z_leq",
  geq => "z_geq",
  lt => "z_lt",
  gt => "z_gt",

  compare => "z_compare",

  of_int => "z_of_int",
  of_string => "z_of_string" with tinfo,
  to_string => "z_to_string" with tinfo,

  equal => "z_equal"
]
Include [ Library "certirocq_gmp.h", LibraryPath "/opt/homebrew/lib", Link "gmp" ].

Definition compare_signed x y := wrap_int (compare x y).

From CertiRocq.Plugin Require Import RocqMsgFFI.
Set CertiRocq Build Directory "_build".
(* TODO test presence *)
Definition test_zarith :=
  msg_info (show (equal (add zero one) (add one zero))).

(* CertiRocq Run test_zarith. *)

From MetaRocq.Utils Require Import monad_utils.
Import MonadNotation.

Definition string_of_pstring (s : string) : bytestring.string :=
  bytestring.String.concat bytestring.String.EmptyString (List.map char63_to_string (PrimStringAxioms.to_list s)).
Open Scope bs.

Definition test_zarith2 :=
  (* let x := msg_info ("compare one zero = " ++ show (compare one zero)) in *)
  (* let x := msg_info ("compare zero one = " ++ show (compare_signed zero one)) in *)
  (* let x := msg_info ("compare one one = " ++ show (compare_signed one one)) in *)
   msg_info (show (length (to_string (of_string "40")))).
  (* msg_info ("show pow 2 40 = " ++ string_of_pstring (to_string (pow (add one one) (of_string "40")))). *)
Set Warnings "-primitive-turned-into-axiom".
CertiRocq Eval test_zarith2.
