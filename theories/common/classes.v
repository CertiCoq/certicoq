
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.DecBool.
Require Import Coq.Arith.Arith.


Class Eq (A:Type) :=
  {
    eq_dec : forall (x y:A), {x = y} + {x<>y}
  }.

#[global] Instance NatEq: Eq nat := { eq_dec := eq_nat_dec }.
#[global] Instance AsciiEq: Eq ascii := { eq_dec:= ascii_dec }.
#[global] Instance StringEq: Eq string := { eq_dec:= string_dec }.

