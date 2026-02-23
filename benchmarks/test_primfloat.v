
From CertiCoq.Plugin Require Import CertiCoq.
From MetaRocq.Utils Require Import utils.
From CertiCoq.Common Require Import Pipeline_utils.

Open Scope bs_scope.

Class Show (A : Type) := show : A -> string.

#[export] Instance nat_show : Show nat := string_of_nat.
Local Open Scope bs.
Definition string_of_bool b :=
  if (b : bool) then "true" else "false".
#[export] Instance bool_show : Show bool := string_of_bool.

#[export] Instance list_show {A} {SA : Show A} : Show (list A) := string_of_list show.
From MetaRocq.Common Require Import Primitive.
From Stdlib Require Import PrimFloat PrimInt63.
#[export] Instance float_show : Show PrimFloat.float := string_of_float.
#[export] Instance prim_int_show : Show PrimInt63.int := string_of_prim_int.
Eval compute in 5.0%float.
(* Definition certicoqc2 := coq_msg_info (show 5%int63). *)
Import SpecFloat.
Definition string_of_specfloat (f : SpecFloat.spec_float) :=
  match f with
  | S754_zero sign => if sign then "-0" else "0"
  | S754_infinity sign => if sign then "-infinity" else "infinity"
  | S754_nan => "nan"
  | S754_finite sign p z =>
  let num := string_of_positive p ++ "p" ++ string_of_Z z in
  if sign then "-" ++ num else num
  end.

#[export] Instance show_specfloat : Show SpecFloat.spec_float := string_of_specfloat.
#[export] Instance show_positive : Show positive := string_of_positive.
#[export] Instance show_Z : Show Z := string_of_Z.

Definition certicoqc2 :=
  coq_msg_info (show (0%float == (-0)%float)).

Time Eval compute in certicoqc2.

Set Warnings "-primitive-turned-into-axiom".
Time CertiCoq Run certicoqc2.
