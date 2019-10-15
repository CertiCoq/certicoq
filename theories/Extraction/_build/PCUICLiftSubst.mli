open Datatypes
open List0
open Nat0
open PCUICAst
open PCUICAstUtils
open Utils

val lift : nat -> nat -> term -> term

val subst : term list -> nat -> term -> term

val subst1 : term -> nat -> term -> term
