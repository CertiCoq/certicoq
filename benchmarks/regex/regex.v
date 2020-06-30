Require Import Arith List String.
Require Import ExtLib.Structures.Monad.
From CertiCoq.Plugin Require Import CertiCoq.

Import MonadNotation.
Import ListNotations.
Open Scope monad_scope.

Require Import Coq.Strings.Ascii.

Inductive rgx : Type :=
| empty   : rgx
| epsilon : rgx
| literal : string -> rgx
| or      : rgx -> rgx -> rgx
| and     : rgx -> rgx -> rgx
| star    : rgx -> rgx
| capture : rgx -> rgx.

Fixpoint simplify (r : rgx) : rgx :=
  match r with
  | star epsilon         => epsilon
  | star (star r')       => star (simplify r')
  | or epsilon (star r') => star (simplify r')
  | or empty r'          => simplify r'
  | and  r1 r2           => and (simplify r1) (simplify r2)
  | or   r1 r2           => or (simplify r1) (simplify r2)
  | star r'              => star (simplify r')
  | capture r'           => capture (simplify r')
  | _                    => r
  end.

Infix "⊕" := or (right associativity, at level 60).
Infix "·" := and (right associativity, at level 60).

Class RegexFFI : Type :=
  Build_RegexFFI
    { test : rgx -> string -> bool
    ; exec : rgx -> string -> option (list string)
    }.

Fixpoint literals (l : list string) : rgx :=
  match l with
  | nil => empty
  | x :: xs => literal x ⊕ literals xs
  end.

Definition numeric := literals ["0";"1";"2";"3";"4";"5";"6";"7";"8";"9"]%string.

Definition alpha :=
  or (literals ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m"]%string)
     (literals ["n";"o";"p";"q";"r";"s";"t";"u";"v";"w";"x";"y";"z"]%string).

Definition alphanumeric :=
  or alpha numeric.

Definition email :=
    capture (star alphanumeric)
  · literal "@"
  · capture (star alphanumeric)
  · literal "."
  · capture (literals ["com";"net";"org";"edu"]%string).

Definition prog `{RegexFFI} :=
  exec email "name@example.com".

CertiCoq Compile -args 5 prog.
CertiCoq FFI -prefix "rgx_" RegexFFI.
