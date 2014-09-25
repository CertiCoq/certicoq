Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Class Injection x t := inject : x -> t.
(*
Class Projection x t := { project : t -> x ; pmodify : (x -> x) -> (t -> t) }.
*)

Instance Injection_refl {T} : Injection T T := { inject := @id T }.

Instance Injection_ascii_string : Injection ascii string :=
  { inject a := String a EmptyString }.
Instance Injection_ascii_string_cons : Injection ascii (string -> string) :=
  { inject := String }.
