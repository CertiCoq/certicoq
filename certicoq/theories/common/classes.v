
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.DecBool.
Require Import Coq.omega.Omega.


Class Eq (A:Type) :=
  {
    eq_dec : forall (x y:A), {x = y} + {x<>y}
  }.

Instance NatEq: Eq nat := { eq_dec := eq_nat_dec }.
Instance AsciiEq: Eq ascii := { eq_dec:= ascii_dec }.
Instance StringEq: Eq string := { eq_dec:= string_dec }.

