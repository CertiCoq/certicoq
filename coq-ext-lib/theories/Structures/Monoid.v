Require Import ExtLib.Core.Type.
Require Import ExtLib.Structures.BinOps.

Set Implicit Arguments.
Set Maximal Implicit Insertion.

Section Monoid.
  Variable S : Type.

  Record Monoid : Type :=
  { monoid_plus : S -> S -> S
  ; monoid_unit : S
  }.

  Context {Type_S : type S}.

  Class MonoidLaws (M : Monoid) : Type :=
  { monoid_assoc :> Associative M.(monoid_plus) equal
  ; monoid_lunit :> LeftUnit M.(monoid_plus) M.(monoid_unit) equal
  ; monoid_runit :> RightUnit M.(monoid_plus) M.(monoid_unit) equal
  }.

End Monoid.
