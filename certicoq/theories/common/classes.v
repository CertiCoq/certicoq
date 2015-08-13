
Require Import Lists.List.
Require Import Strings.String.
Require Import Strings.Ascii.
Require Import Bool.Bool.
Require Import Bool.DecBool.
Require Import Omega.


Class Eq (A:Type) :=
  {
    eq_dec : forall (x y:A), {x = y} + {x<>y}
  }.

Instance NatEq: Eq nat := { eq_dec := eq_nat_dec }.
Instance AsciiEq: Eq ascii := { eq_dec:= ascii_dec }.
Instance StringEq: Eq string := { eq_dec:= string_dec }.

